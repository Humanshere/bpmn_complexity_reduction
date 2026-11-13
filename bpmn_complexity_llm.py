#!/usr/bin/env python3
"""
bpmn_complexity_llm.py  --  Detect and reduce unnecessary complexity in BPMN models,
with a rule-based pass followed by a verified Gemini (LLM) pass.

Pure standard library (Python 3.8+). Control flow only: events, tasks, gateways,
sequence flows and sub-processes.

Usage
-----
  python bpmn_complexity_llm.py analyze samples/                 # metrics + guideline checks
  python bpmn_complexity_llm.py analyze samples/ -v --csv m.csv  # list every violation, save CSV
  python bpmn_complexity_llm.py reduce  samples/ --out reduced/  # rules + Gemini + checks
  python bpmn_complexity_llm.py reduce  samples/ --no-llm        # rules only (same as the old script)
  python bpmn_complexity_llm.py reduce  samples/ --dry-run       # print the prompt, no API call

Gemini key: set the environment variable GEMINI_API_KEY, or put the line
GEMINI_API_KEY=... in a file called .env next to where you run the script.
The key is never printed, logged or written to any output file.

Pipeline
--------
  parse BPMN XML -> metrics + 7PMG checks                    (DETECT)
                 -> rule rewrites R1-R4                      (REDUCE)
                 -> Gemini rewrites what is left             (REDUCE MORE)
                 -> lint + trace comparison with the ORIGINAL (VERIFY)
                 -> keep the LLM result only if it is verified and strictly simpler,
                    otherwise keep the rule result          (EVALUATE)
"""
import argparse
import copy
import csv
import glob
import json
import os
import re
import socket
import sys
import time
import urllib.error
import urllib.request
import xml.etree.ElementTree as ET
from collections import Counter, defaultdict
from itertools import combinations
from xml.sax.saxutils import quoteattr

sys.setrecursionlimit(10000)

# ----------------------------------------------------------------------------
# 1. Model representation
# ----------------------------------------------------------------------------
TASK_TAGS = {"task", "userTask", "serviceTask", "sendTask", "receiveTask", "manualTask",
             "scriptTask", "businessRuleTask", "callActivity"}
SUBPROC_TAGS = {"subProcess", "transaction", "adHocSubProcess"}
GATE_TAGS = {"exclusiveGateway": "xor", "eventBasedGateway": "xor",
             "parallelGateway": "and", "inclusiveGateway": "or", "complexGateway": "or"}
EVENT_TAGS = {"intermediateCatchEvent", "intermediateThrowEvent", "boundaryEvent"}
GATES = ("xor", "and", "or")


class Node:
    def __init__(self, id, kind, label="", plain=True, child=None):
        self.id, self.kind, self.label, self.plain, self.child = id, kind, label, plain, child


class Graph:
    """One scope (a process or an expanded sub-process). edges = [id, src, tgt, label]."""

    def __init__(self, name=""):
        self.name, self.nodes, self.edges = name, {}, []

    def add(self, id, kind, label="", plain=True, child=None):
        self.nodes[id] = Node(id, kind, label, plain, child)

    def ins(self, n):
        return [e for e in self.edges if e[2] == n]

    def outs(self, n):
        return [e for e in self.edges if e[1] == n]


def local(tag):
    return tag.rsplit("}", 1)[-1]


def parse_scope(elem, name=""):
    g, flows = Graph(name), []
    for ch in elem:
        t, i = local(ch.tag), ch.get("id")
        lab = re.sub(r"\s+", " ", ch.get("name") or "").strip()
        plain = not any(local(c.tag).endswith("EventDefinition") for c in ch)
        if t == "startEvent":
            g.add(i, "start", lab, plain)
        elif t == "endEvent":
            g.add(i, "end", lab, plain)
        elif t in EVENT_TAGS:
            g.add(i, "event", lab, plain)
        elif t in GATE_TAGS:
            g.add(i, GATE_TAGS[t], lab)
        elif t in SUBPROC_TAGS:
            g.add(i, "task", lab, True, parse_scope(ch, name=lab or i))
        elif t in TASK_TAGS:
            g.add(i, "task", lab)
        elif t == "sequenceFlow":
            flows.append([i, ch.get("sourceRef"), ch.get("targetRef"), ch.get("name") or ""])
    g.edges = [f for f in flows if f[1] in g.nodes and f[2] in g.nodes]
    return g


def parse_bpmn(path):
    root = ET.parse(path).getroot()
    procs = [e for e in root.iter() if local(e.tag) == "process"]
    return [parse_scope(p, p.get("name") or p.get("id") or "process") for p in procs]


def scopes(g, depth=0):
    yield g, depth
    for n in g.nodes.values():
        if n.child is not None:
            yield from scopes(n.child, depth + 1)


def degrees(g):
    ind, outd = Counter(), Counter()
    for _, s, t, _ in g.edges:
        outd[s] += 1
        ind[t] += 1
    return ind, outd


def norm(label):
    return re.sub(r"\s+", " ", label.strip().lower())


def flatten(g):
    """Inline every sub-process so the simulator sees one flat graph. Start and end events of
    a sub-process become silent pass-through nodes. A sub-process without a start or end
    event cannot be inlined and stays a single task."""
    out = Graph(g.name)
    edges = [list(e) for e in g.edges]
    for nid, n in g.nodes.items():
        if n.child is None:
            out.add(nid, n.kind, n.label, n.plain)
            continue
        sub = flatten(n.child)
        starts = [k for k, x in sub.nodes.items() if x.kind == "start"]
        ends = [k for k, x in sub.nodes.items() if x.kind == "end"]
        if not starts or not ends:
            out.add(nid, "task", n.label)
            continue
        p = f"{nid}/"
        for k, x in sub.nodes.items():
            out.add(p + k, "event" if x.kind in ("start", "end") else x.kind, x.label, x.plain)
        edges += [[p + e[0], p + e[1], p + e[2], e[3]] for e in sub.edges]
        out.add(p + "in", "event")
        out.add(p + "out", "event")
        edges += [[f"{p}in>{s}", p + "in", p + s, ""] for s in starts]
        edges += [[f"{p}{t}>out", p + t, p + "out", ""] for t in ends]
        for e in edges:
            if e[2] == nid:
                e[2] = p + "in"
            if e[1] == nid:
                e[1] = p + "out"
    out.edges = edges
    return out


# ----------------------------------------------------------------------------
# 2. DETECT: metrics
# ----------------------------------------------------------------------------
def metrics(roots):
    c = Counter()
    labels = Counter()
    depth = maxscope = maxfan = cfc = unmatched = 0
    for root in roots:
        for g, d in scopes(root):
            ind, outd = degrees(g)
            depth, maxscope = max(depth, d), max(maxscope, len(g.nodes))
            c["nodes"] += len(g.nodes)
            c["arcs"] += len(g.edges)
            splits, joins = Counter(), Counter()
            for nid, n in g.nodes.items():
                k = n.kind
                if k == "start":
                    c["starts"] += 1
                elif k == "end":
                    c["ends"] += 1
                elif k == "task":
                    c["tasks"] += 1
                    if norm(n.label):
                        labels[norm(n.label)] += 1
                elif k in GATES:
                    c["gateways"] += 1
                    c[k] += 1
                    o, i = outd[nid], ind[nid]
                    maxfan = max(maxfan, o, i)
                    if o > 1:
                        splits[k] += 1
                        cfc += o if k == "xor" else 1 if k == "and" else 2 ** o - 1
                    if i > 1:
                        joins[k] += 1
            unmatched += sum(abs(splits[k] - joins[k]) for k in GATES)
    return {
        "nodes": c["nodes"], "arcs": c["arcs"], "tasks": c["tasks"], "gateways": c["gateways"],
        "xor": c["xor"], "and": c["and"], "or": c["or"],
        "starts": c["starts"], "ends": c["ends"], "max_fanout": maxfan,
        "cfc": cfc, "dup_copies": sum(v - 1 for v in labels.values() if v > 1),
        "unmatched_gateways": unmatched, "nesting_depth": depth, "max_scope_nodes": maxscope,
    }


# ----------------------------------------------------------------------------
# 3. DETECT: the seven guidelines (7PMG) as automatic checks
# ----------------------------------------------------------------------------
NOUNISH = ("ing", "tion", "sion", "ment", "ness", "ity", "ance", "ence")
VERB_EXCEPTIONS = {"document", "implement", "supplement", "comment"}  # verbs that look like nouns


def label_ok(label):
    """Heuristic verb-object test for G6 (no NLP library): >=2 words, does not start
    with an article or a noun-like suffix, and is not 'Noun gerund' like 'Order handling'.
    Verbs that look like nouns (document, implement) are listed in VERB_EXCEPTIONS."""
    w = re.findall(r"[a-z']+", label.lower())
    if len(w) < 2 or w[0] in ("the", "a", "an"):
        return False
    if w[0].endswith(NOUNISH) and w[0] not in VERB_EXCEPTIONS:
        return False
    return not (len(w) == 2 and w[1].endswith("ing"))   # "Claim handling" is a noun phrase


def is_structured(g):
    """G4. Graph-reduction test: a scope is structured if it reduces to start->end using
    (1) series removal, (2) merging parallel edges between same-type split/join,
    (3) removal of a simple XOR loop. Multiple starts/ends get a virtual XOR split/join;
    tasks with several in/out flows get an implicit XOR join / AND split."""
    kinds = {n: x.kind for n, x in g.nodes.items()}
    edges = [(e[1], e[2]) for e in g.edges]
    starts = [n for n, k in kinds.items() if k == "start"]
    ends = [n for n, k in kinds.items() if k == "end"]
    if not starts or not ends:
        return True  # nothing to judge (e.g. ad-hoc sub-process)
    ind, outd = Counter(t for _, t in edges), Counter(s for s, _ in edges)
    for n in list(kinds):                                  # make implicit gateways explicit
        if kinds[n] in GATES:
            continue
        if ind[n] > 1:
            kinds[f"~j{n}"] = "xor"
            edges = [(s, f"~j{n}" if t == n else t) for s, t in edges] + [(f"~j{n}", n)]
        if outd[n] > 1:
            kinds[f"~s{n}"] = "and"
            edges = [(f"~s{n}" if s == n else s, t) for s, t in edges] + [(n, f"~s{n}")]
    if len(starts) > 1:
        kinds["~S"] = "xor"
        edges += [("~S", s) for s in starts]
    if len(ends) > 1:
        kinds["~E"] = "xor"
        edges += [(e, "~E") for e in ends]
    changed = True
    while changed:
        changed = False
        ind, outd = Counter(t for _, t in edges), Counter(s for s, _ in edges)
        for v in list(kinds):                              # rule 1: series
            if ind[v] == 1 and outd[v] == 1:
                ein = next(e for e in edges if e[1] == v)
                eout = next(e for e in edges if e[0] == v)
                if ein == eout:
                    continue
                edges.remove(ein)
                edges.remove(eout)
                edges.append((ein[0], eout[1]))
                del kinds[v]
                changed = True
                break
        if changed:
            continue
        for (u, v), cnt in Counter(edges).items():         # rule 2: matched split/join block
            if cnt >= 2 and u != v and kinds[u] in GATES and kinds[u] == kinds[v]:
                for _ in range(cnt - 1):
                    edges.remove((u, v))
                changed = True
                break
        if changed:
            continue
        for (j, s) in set(edges):                          # rule 3: XOR loop
            if (j != s and kinds[j] == kinds[s] == "xor" and (s, j) in edges
                    and ind[j] >= 2 and outd[s] >= 2):
                edges.remove((s, j))
                changed = True
                break
    return len(kinds) == 2 and len(edges) == 1


def check_guidelines(roots, cfg, m=None):
    m = m or metrics(roots)
    v = []
    if m["dup_copies"]:
        v.append(("G1", f"{m['dup_copies']} repeated task copies -> merge duplicates"))
    if m["nodes"] > cfg["g1"]:
        v.append(("G1", f"{m['nodes']} elements (> {cfg['g1']}) -> remove detail / decompose"))
    if m["max_fanout"] > cfg["g2"]:
        v.append(("G2", f"gateway with degree {m['max_fanout']} (> {cfg['g2']}) -> split the decision"))
    for root in roots:
        for g, d in scopes(root):
            s = sum(x.kind == "start" for x in g.nodes.values())
            e = sum(x.kind == "end" for x in g.nodes.values())
            if (s != 1 or e != 1) and not (d > 0 and s == 0 and e == 0):
                v.append(("G3", f"[{g.name}] {s} start and {e} end events -> use exactly one of each"))
            if not is_structured(g):
                v.append(("G4", f"[{g.name}] not block-structured -> give every split a matching join of the same type"))
            for x in g.nodes.values():
                if x.kind == "task" and not label_ok(x.label):
                    v.append(("G6", f"[{g.name}] task label '{x.label or x.id}' is not verb + object"))
    if m["or"]:
        v.append(("G5", f"{m['or']} OR gateway(s) -> replace by XOR/AND if the process allows"))
    if m["max_scope_nodes"] > cfg["g7"]:
        v.append(("G7", f"largest diagram has {m['max_scope_nodes']} elements (> {cfg['g7']}) -> decompose into sub-processes"))
    return v


def codes(viol):
    return sorted({c for c, _ in viol})


def evaluate(roots, cfg):
    """(score, violations). Lower score is simpler. Compared left to right: guidelines broken,
    violation count, control-flow complexity, nodes, arcs."""
    m = metrics(roots)
    v = check_guidelines(roots, cfg, m)
    return (len(codes(v)), len(v), m["cfc"], m["nodes"], m["arcs"]), v


# ----------------------------------------------------------------------------
# 4. REDUCE (rules): behaviour-preserving rewrites
# ----------------------------------------------------------------------------
def drop_node(g, n):
    g.edges = [e for e in g.edges if e[1] != n and e[2] != n]
    del g.nodes[n]


def redirect(g, old, new):
    for e in g.edges:
        if e[2] == old:
            e[2] = new


def merge_ends(g):
    """R1: several plain end events -> one. Tokens reaching an end are simply consumed,
    so one end with several incoming flows has the same behaviour."""
    ends = [n for n, x in g.nodes.items() if x.kind == "end" and x.plain]
    if len(ends) < 2:
        return []
    labs = sorted({g.nodes[n].label for n in ends if g.nodes[n].label})
    for n in ends[1:]:
        redirect(g, n, ends[0])
        drop_node(g, n)
    g.nodes[ends[0]].label = " / ".join(labs)
    return [f"R1 [{g.name}] merged {len(ends)} end events into one"]


def merge_dup_tasks(g):
    """R2: tasks with the same label AND the same set of successors are interchangeable
    (the future of a token depends only on where it is), so keep one copy.
    Skipped when a successor is an AND/OR join (it counts tokens per incoming flow)."""
    groups, log = defaultdict(list), []
    for n, x in g.nodes.items():
        if x.kind == "task" and x.child is None and norm(x.label):
            groups[norm(x.label)].append(n)
    for lab, ids in groups.items():
        part = defaultdict(list)
        for n in ids:
            part[tuple(sorted(e[2] for e in g.outs(n)))].append(n)
        for succ, mem in part.items():
            if len(mem) < 2 or set(succ) & set(mem):
                continue
            ind, _ = degrees(g)
            if any(g.nodes[s].kind in ("and", "or") and ind[s] > 1 for s in succ):
                log.append(f"R2 [{g.name}] kept copies of '{lab}' (successor is an AND/OR join)")
                continue
            for n in mem[1:]:
                redirect(g, n, mem[0])
                drop_node(g, n)
            log.append(f"R2 [{g.name}] merged {len(mem)} copies of '{lab}' into one")
    return log


def merge_starts(g):
    """R3: plain start events with identical successors -> one start (labels joined)."""
    part = defaultdict(list)
    for n, x in g.nodes.items():
        if x.kind == "start" and x.plain:
            part[tuple(sorted(e[2] for e in g.outs(n)))].append(n)
    log = []
    for succ, mem in part.items():
        if len(mem) < 2:
            continue
        labs = [g.nodes[n].label for n in mem if g.nodes[n].label]
        g.nodes[mem[0]].label = " / ".join(dict.fromkeys(labs))
        for n in mem[1:]:
            drop_node(g, n)
        log.append(f"R3 [{g.name}] merged {len(mem)} start events into one ('{g.nodes[mem[0]].label}')")
    return log


def drop_trivial_gateways(g):
    """R4: a gateway with one in and one out flow does nothing -> bypass it."""
    log = []
    for n, x in list(g.nodes.items()):
        if x.kind in GATES:
            ins, outs = g.ins(n), g.outs(n)
            if len(ins) == 1 and len(outs) == 1 and ins[0] is not outs[0]:
                ins[0][2] = outs[0][2]
                g.edges.remove(outs[0])
                del g.nodes[n]
                log.append(f"R4 [{g.name}] removed redundant {x.kind.upper()} gateway {n}")
    return log


def reduce_scope(g):
    """Apply R1-R4 repeatedly until nothing changes (each rewrite can enable the next)."""
    log = []
    for _ in range(5):
        step = merge_ends(g) + merge_dup_tasks(g) + merge_starts(g) + drop_trivial_gateways(g)
        log += [s for s in step if s not in log]
        if not [s for s in step if "kept copies" not in s]:
            break
    return log


def reduce_model(roots):
    new, log = copy.deepcopy(roots), []
    for root in new:
        for g, _ in scopes(root):
            log += reduce_scope(g)
    return new, log


# ----------------------------------------------------------------------------
# 5. VERIFY: compare the sets of task traces (bounded token-game simulation)
# ----------------------------------------------------------------------------
def trace_language(g, max_len=30, max_states=400000):
    """All complete task-label sequences. XOR=choose one, AND=all (sync at AND joins),
    OR split=any non-empty subset, OR join treated like XOR join (approximation).
    Sub-processes must be inlined first (see flatten).
    Returns (traces, deadlock?, cut_by_length?, cut_by_state_cap?). A cut by length is
    harmless for comparing two models; a cut by the state cap makes the result unreliable."""
    ins, outs = defaultdict(list), defaultdict(list)
    for e in g.edges:
        outs[e[1]].append(e[0])
        ins[e[2]].append(e[0])

    def mk(d):
        return tuple(sorted((k, v) for k, v in d.items() if v > 0))

    def put(d, edges_):
        for e in edges_:
            d[e] = d.get(e, 0) + 1

    def moves(marking):
        d = dict(marking)
        for n, x in g.nodes.items():
            if x.kind == "start":
                continue
            tok = [e for e in ins[n] if d.get(e, 0) > 0]
            if not tok:
                continue
            if x.kind == "and":
                if len(tok) < len(ins[n]):
                    continue
                b = dict(d)
                for e in ins[n]:
                    b[e] -= 1
                put(b, outs[n])
                yield None, mk(b)
                continue
            for e in tok:
                b = dict(d)
                b[e] -= 1
                if x.kind == "xor":
                    if not outs[n]:
                        yield None, mk(b)
                    for o in outs[n]:
                        b2 = dict(b)
                        put(b2, [o])
                        yield None, mk(b2)
                elif x.kind == "or":
                    if not outs[n]:
                        yield None, mk(b)
                    for r in range(1, len(outs[n]) + 1):
                        for sub in combinations(outs[n], r):
                            b2 = dict(b)
                            put(b2, sub)
                            yield None, mk(b2)
                else:  # task / event / end
                    put(b, outs[n])
                    yield (x.label or n if x.kind == "task" else None), mk(b)

    stack = [(mk(Counter(outs[s])), ()) for s, x in g.nodes.items() if x.kind == "start"]
    seen, traces, dead, cut_len, cut_states = set(), set(), False, False, False
    while stack:
        m, t = stack.pop()
        if (m, t) in seen:
            continue
        seen.add((m, t))
        if len(seen) > max_states:
            cut_states = True
            break
        if not m:
            traces.add(t)
            continue
        nxt = list(moves(m))
        if not nxt:
            dead = True
            continue
        for lab, m2 in nxt:
            t2 = t + ((lab,) if lab else ())
            if len(t2) > max_len:
                cut_len = True
                continue
            stack.append((m2, t2))
    return traces, dead, cut_len, cut_states


def languages(roots, max_len, max_states):
    return [trace_language(flatten(g), max_len, max_states) for g in roots]


def canon(label, rmap):
    return norm(rmap.get(norm(label), label))


def behaviour_report(before, after, max_len, max_states, rmap=None, before_lang=None):
    """Compare the task-trace sets of two models, one entry per process. rmap maps old task
    labels to new ones (declared renames) and is applied to the 'before' side."""
    rmap = rmap or {}
    before_lang = before_lang or languages(before, max_len, max_states)
    out = []
    for b, a, (tb, db, lb, sb) in zip(before, after, before_lang):
        ta, da, la, sa = trace_language(flatten(a), max_len, max_states)
        tb2 = {tuple(canon(x, rmap) for x in t) for t in tb}
        ta2 = {tuple(canon(x, {}) for x in t) for t in ta}
        approx = any(x.kind == "or" and len(b.ins(n)) > 1 for n, x in b.nodes.items())
        out.append(dict(equal=tb2 == ta2, n_before=len(tb2), n_after=len(ta2), dead=db or da,
                        new_deadlock=da and not db, truncated=lb or la, inconclusive=sb or sa,
                        approx_or_join=approx, missing=sorted(tb2 - ta2)[:3],
                        extra=sorted(ta2 - tb2)[:3]))
    return out


def verdict_line(b):
    verdict = "SAME task traces" if b["equal"] else "DIFFERENT traces -> REVIEW"
    extra = (" [bounded search]" if b["truncated"] else "") + \
            (" [OR-join approximated]" if b["approx_or_join"] else "") + \
            (" [deadlock found]" if b["dead"] else "") + \
            (" [state cap hit, result unreliable]" if b["inconclusive"] else "")
    return f"  behaviour: {verdict} ({b['n_before']} before, {b['n_after']} after){extra}"


def behaviour_ok(beh):
    return all(b["equal"] and not b["new_deadlock"] and not b["inconclusive"] for b in beh)


# ----------------------------------------------------------------------------
# 6. Write BPMN (with a simple automatic layout so bpmn.io can display it)
# ----------------------------------------------------------------------------
SIZE = {"start": (36, 36), "end": (36, 36), "event": (36, 36), "xor": (50, 50),
        "and": (50, 50), "or": (50, 50), "task": (100, 80)}
OUT_TAG = {"start": "startEvent", "end": "endEvent", "event": "intermediateCatchEvent",
           "xor": "exclusiveGateway", "and": "parallelGateway", "or": "inclusiveGateway"}


def scope_xml(g, ind=2):
    pad, out = " " * ind, []
    for n, x in g.nodes.items():
        tag = OUT_TAG.get(x.kind) or ("subProcess" if x.child is not None else "task")
        name = f" name={quoteattr(x.label)}" if x.label else ""
        if x.child is not None:
            out.append(f'{pad}<{tag} id="{n}"{name}>')
            out += scope_xml(x.child, ind + 2)
            out.append(f"{pad}</{tag}>")
        else:
            out.append(f'{pad}<{tag} id="{n}"{name} />')
    for eid, s, t, lab in g.edges:
        name = f" name={quoteattr(lab)}" if lab else ""
        out.append(f'{pad}<sequenceFlow id="{eid}" sourceRef="{s}" targetRef="{t}"{name} />')
    return out


def layout(g):
    succ, idx = defaultdict(list), {n: i for i, n in enumerate(g.nodes)}
    for e in g.edges:
        succ[e[1]].append(e[2])
    state, back = {}, set()

    def dfs(u):
        state[u] = 1
        for v in succ[u]:
            if state.get(v) == 1:
                back.add((u, v))
            elif v not in state:
                dfs(v)
        state[u] = 2

    for n in [n for n, x in g.nodes.items() if x.kind == "start"] + list(g.nodes):
        if n not in state:
            dfs(n)
    indeg, fw = Counter(), defaultdict(list)
    for e in g.edges:
        if (e[1], e[2]) not in back and e[1] != e[2]:
            fw[e[1]].append(e[2])
            indeg[e[2]] += 1
    layer, q = {n: 0 for n in g.nodes}, [n for n in g.nodes if indeg[n] == 0]
    while q:
        u = q.pop(0)
        for v in fw[u]:
            layer[v] = max(layer[v], layer[u] + 1)
            indeg[v] -= 1
            if indeg[v] == 0:
                q.append(v)
    rows, pos = Counter(), {}
    for n in sorted(g.nodes, key=lambda n: (layer[n], idx[n])):
        w, h = SIZE[g.nodes[n].kind]
        cx, cy = 70 + layer[n] * 160, 60 + rows[layer[n]] * 110
        rows[layer[n]] += 1
        pos[n] = (cx - w // 2, cy - h // 2, w, h)
    return pos


def diagrams_xml(roots):
    """One BPMNDiagram per process, plus one per sub-process (bpmn.io drill-down)."""
    out, k = [], 0
    todo = [(g, f"Process_{i}") for i, g in enumerate(roots)]
    while todo:
        g, element = todo.pop(0)
        k += 1
        pos = layout(g)
        out.append(f'  <bpmndi:BPMNDiagram id="Diagram_{k}"><bpmndi:BPMNPlane id="Plane_{k}" bpmnElement="{element}">')
        for n, (x, y, w, h) in pos.items():
            ex = ' isExpanded="false"' if g.nodes[n].child is not None else ""
            out.append(f'    <bpmndi:BPMNShape id="{n}_di" bpmnElement="{n}"{ex}>'
                       f'<dc:Bounds x="{x}" y="{y}" width="{w}" height="{h}" /></bpmndi:BPMNShape>')
        for eid, s, t, _ in g.edges:
            (sx, sy, sw, sh), (tx, ty, tw, th) = pos[s], pos[t]
            out.append(f'    <bpmndi:BPMNEdge id="{eid}_di" bpmnElement="{eid}">'
                       f'<di:waypoint x="{sx + sw}" y="{sy + sh // 2}" />'
                       f'<di:waypoint x="{tx}" y="{ty + th // 2}" /></bpmndi:BPMNEdge>')
        out.append("  </bpmndi:BPMNPlane></bpmndi:BPMNDiagram>")
        todo += [(x.child, n) for n, x in g.nodes.items() if x.child is not None]
    return out


def bpmn_string(roots, with_di=True):
    L = ['<?xml version="1.0" encoding="UTF-8"?>',
         '<definitions xmlns="http://www.omg.org/spec/BPMN/20100524/MODEL" '
         'xmlns:bpmndi="http://www.omg.org/spec/BPMN/20100524/DI" '
         'xmlns:dc="http://www.omg.org/spec/DD/20100524/DC" '
         'xmlns:di="http://www.omg.org/spec/DD/20100524/DI" id="Defs" '
         'targetNamespace="http://example.org/bpmn">']
    for i, g in enumerate(roots):
        L.append(f'  <process id="Process_{i}" name={quoteattr(g.name)} isExecutable="false">')
        L += scope_xml(g, 4)
        L.append("  </process>")
    if with_di:
        L += diagrams_xml(roots)
    L.append("</definitions>")
    return "\n".join(L)


def write_bpmn(roots, path):
    with open(path, "w", encoding="utf-8") as f:
        f.write(bpmn_string(roots))


# ----------------------------------------------------------------------------
# 7. LLM pass (Gemini): prompt, API call, lint, verify, retry
# ----------------------------------------------------------------------------
API_ROOT = "https://generativelanguage.googleapis.com/v1beta/models"
DEFAULT_MODEL = "gemini-2.5-flash"

RESPONSE_SCHEMA = {
    "type": "OBJECT",
    "properties": {
        "changes": {"type": "ARRAY", "items": {"type": "STRING"}},
        "label_renames": {"type": "ARRAY", "items": {
            "type": "OBJECT",
            "properties": {"old": {"type": "STRING"}, "new": {"type": "STRING"}},
            "required": ["old", "new"]}},
        "bpmn_xml": {"type": "STRING"},
    },
    "required": ["changes", "label_renames", "bpmn_xml"],
}

ALLOWED_TAGS = TASK_TAGS | SUBPROC_TAGS | EVENT_TAGS | set(GATE_TAGS) | \
    {"startEvent", "endEvent", "sequenceFlow"}
PASSIVE_TAGS = {"documentation", "extensionElements", "incoming", "outgoing"}


class LLMError(Exception):
    pass


RELAX_EDIT = """
- RELAXED MODE: you may also replace an inclusive (OR) gateway by an exclusive (XOR) or parallel (AND) one when that is the most plausible business meaning, even if the checker sees a difference. Say "needs review" in the change note for each such edit. The checker will still reject missing or added tasks."""


def system_prompt(cfg, relax=False):
    extra = RELAX_EDIT if relax else ""
    return f"""You are an expert in Business Process Management and BPMN 2.0. You remove unnecessary complexity from BPMN process models. Unnecessary complexity comes from how a model was drawn, not from the real process. Remove it, but never change what the process does.

HOW YOUR ANSWER IS CHECKED
An automatic checker simulates the process and compares every complete sequence of task labels with the current model. Any difference rejects your answer. Simulation rules: a task with several outgoing flows starts all of them in parallel; a task with several incoming flows runs once per arriving token; an exclusive (XOR) gateway picks one branch; a parallel (AND) gateway takes all branches and waits for all; an inclusive (OR) split takes any non-empty subset of its branches.

GUIDELINES USED TO MEASURE THE RESULT (fewer broken is better)
G1 few elements (at most {cfg['g1']} in total) and no repeated copies of a task
G2 every gateway has at most {cfg['g2']} incoming flows and at most {cfg['g2']} outgoing flows (a join with more incoming flows breaks it too)
G3 exactly one start event and one end event per diagram
G4 block-structured: every split has a matching join of the same type
G5 avoid inclusive (OR) gateways
G6 task labels are verb + object, for example "Check stock"
G7 a diagram has at most {cfg['g7']} elements, otherwise group tasks into a subProcess

ALLOWED EDITS
- Merge copies of a task, and merge start or end events, when behaviour stays identical.
- Remove gateways that route nothing.
- Make the model block-structured, but only if this adds no task copies and keeps behaviour identical.
- Replace an OR gateway by XOR or AND only when behaviour is provably identical (for example the branches are mutually exclusive, or all are always taken). If unsure, keep the OR.
- Reduce the degree of a large gateway by nesting gateways of the same type.
- Group a coherent block of tasks into a subProcess (with its own start and end event) when a diagram is too large.
- Rename a task whose label is not verb + object, for example "Claim handling" becomes "Handle claim". List every rename in label_renames. Change no other label.{extra}

FORBIDDEN
- Deleting a task, adding a task, merging different tasks, or changing the order or conditions of the process.
- Elements other than startEvent, endEvent, task, exclusiveGateway, parallelGateway, inclusiveGateway, subProcess and sequenceFlow. No diagram interchange (bpmndi), pools or lanes.

XML RULES
- Return a complete <definitions> document with xmlns="http://www.omg.org/spec/BPMN/20100524/MODEL" and one <process> per process in the input, keeping the process ids.
- Every id is unique in the whole document. Every sequenceFlow has sourceRef and targetRef pointing to nodes in the same scope. Keep the name of a sequenceFlow when it holds a condition.
- Every node is reachable from a start event and can reach an end event.

If the model cannot be simplified safely, return it unchanged and say so in "changes".
Reply with JSON only: "changes" (one short plain sentence per edit you actually made, ASCII punctuation only; if you made no edit, one sentence saying why), "label_renames" (old and new label pairs), "bpmn_xml" (the full XML as a string)."""


def build_prompt(roots, m, viol, cfg):
    info = {"metrics": m,
            "thresholds": {"G1_max_elements": cfg["g1"], "G2_max_gateway_degree": cfg["g2"],
                           "G7_decompose_above": cfg["g7"]},
            "violations_left": [{"guideline": c, "detail": d} for c, d in viol]}
    return ("Simplify the BPMN process below. Fix the listed violations wherever this is possible "
            "without changing behaviour.\n\n" + json.dumps(info, indent=2) +
            "\n\nBPMN XML:\n" + bpmn_string(roots, with_di=False))


def load_api_key(cli_key=None):
    key = cli_key or os.environ.get("GEMINI_API_KEY") or os.environ.get("GOOGLE_API_KEY")
    if key:
        return key.strip()
    here = os.path.dirname(os.path.abspath(__file__))
    for path in (".env", os.path.join(here, ".env")):
        if os.path.isfile(path):
            with open(path, encoding="utf-8") as fh:
                for line in fh:
                    k, _, v = line.strip().partition("=")
                    if k.strip() in ("GEMINI_API_KEY", "GOOGLE_API_KEY") and v.strip():
                        return v.strip().strip("\"'")
    return None


def gemini_generate(key, model, system, contents, temperature=0.2, timeout=180, tries=4):
    """One generateContent call over plain HTTPS. The key goes in a header, never in the URL."""
    url = f"{API_ROOT}/{model}:generateContent"
    body = {"systemInstruction": {"parts": [{"text": system}]},
            "contents": contents,
            "generationConfig": {"temperature": temperature, "maxOutputTokens": 32768,
                                 "responseMimeType": "application/json",
                                 "responseSchema": RESPONSE_SCHEMA}}
    data = json.dumps(body).encode("utf-8")
    headers = {"Content-Type": "application/json", "x-goog-api-key": key}
    last = ""
    for i in range(tries):
        req = urllib.request.Request(url, data=data, headers=headers, method="POST")
        try:
            with urllib.request.urlopen(req, timeout=timeout) as r:
                payload = json.loads(r.read().decode("utf-8"))
            break
        except urllib.error.HTTPError as e:
            last = f"HTTP {e.code}: {e.read().decode('utf-8', 'replace')[:300]}"
            if e.code not in (429, 500, 502, 503, 504):
                raise LLMError(last.replace(key, "***"))
        except (urllib.error.URLError, socket.timeout, TimeoutError, ConnectionError) as e:
            last = f"network error: {e}"
        except ValueError as e:
            last = f"bad JSON from server: {e}"
        if i < tries - 1:
            time.sleep(2 ** (i + 1))
    else:
        raise LLMError(f"gave up after {tries} tries ({last})".replace(key, "***"))
    cands = payload.get("candidates") or []
    if not cands:
        raise LLMError(f"empty response ({payload.get('promptFeedback') or payload.get('error')})")
    c = cands[0]
    if c.get("finishReason") not in (None, "STOP"):
        raise LLMError(f"model stopped early: {c.get('finishReason')}")
    text = "".join(p.get("text", "") for p in (c.get("content") or {}).get("parts", [])
                   if not p.get("thought"))
    if not text.strip():
        raise LLMError("empty text in response")
    return text


def parse_answer(text):
    """JSON answer -> (xml text, {old label: new label}, [change notes])."""
    try:
        data = json.loads(text)
    except ValueError:
        raise ValueError("the answer is not valid JSON")
    if not isinstance(data, dict) or not isinstance(data.get("bpmn_xml"), str):
        raise ValueError('the JSON has no string field "bpmn_xml"')
    xml = re.sub(r"^```(?:xml)?\s*|\s*```$", "", data["bpmn_xml"].strip())
    rmap = {}
    for r in data.get("label_renames") or []:
        if isinstance(r, dict) and r.get("old") and r.get("new"):
            rmap[norm(str(r["old"]))] = re.sub(r"\s+", " ", str(r["new"])).strip()
    changes = [str(c).strip() for c in (data.get("changes") or []) if str(c).strip()]
    return xml, rmap, changes


def lint_xml(root):
    errs, seen = [], Counter()
    for e in root.iter():
        if e.get("id"):
            seen[e.get("id")] += 1
    errs += [f"duplicate id '{i}'" for i, c in seen.items() if c > 1]
    for scope in root.iter():
        if local(scope.tag) != "process" and local(scope.tag) not in SUBPROC_TAGS:
            continue
        ids = {c.get("id") for c in scope if c.get("id") and local(c.tag) != "sequenceFlow"}
        for c in scope:
            t = local(c.tag)
            if t == "sequenceFlow":
                for attr in ("sourceRef", "targetRef"):
                    if c.get(attr) not in ids:
                        errs.append(f"flow '{c.get('id')}' has {attr} '{c.get(attr)}', "
                                    "which is not a node in the same scope")
            elif t not in ALLOWED_TAGS and t not in PASSIVE_TAGS:
                errs.append(f"unsupported element <{t}>")
    return errs


def reach(g, seeds, forward=True):
    adj = defaultdict(list)
    for _, s, t, _ in g.edges:
        if forward:
            adj[s].append(t)
        else:
            adj[t].append(s)
    seen, stack = set(seeds), list(seeds)
    while stack:
        u = stack.pop()
        for v in adj[u]:
            if v not in seen:
                seen.add(v)
                stack.append(v)
    return seen


def wellformed(root):
    errs = []
    for g, _ in scopes(root):
        tag = f"[{g.name}]"
        starts = [n for n, x in g.nodes.items() if x.kind == "start"]
        ends = [n for n, x in g.nodes.items() if x.kind == "end"]
        if not starts or not ends:
            errs.append(f"{tag} needs at least one start event and one end event")
            continue
        fwd, bwd = reach(g, starts, True), reach(g, ends, False)
        for n in g.nodes:
            if n not in fwd:
                errs.append(f"{tag} '{n}' is not reachable from a start event")
            elif n not in bwd:
                errs.append(f"{tag} '{n}' cannot reach an end event")
    return errs


def load_candidate(xml_text):
    """XML text -> (roots, []) or (None, [reasons])."""
    if "<!DOCTYPE" in xml_text or "<!ENTITY" in xml_text:
        return None, ["DOCTYPE and ENTITY declarations are not allowed"]
    try:
        root = ET.fromstring(xml_text.strip())
    except ET.ParseError as e:
        return None, [f"the XML does not parse: {e}"]
    errs = lint_xml(root)
    procs = [e for e in root.iter() if local(e.tag) == "process"]
    if not procs:
        errs.append("no <process> element found")
    if errs:
        return None, errs[:8]
    roots = [parse_scope(p, p.get("name") or p.get("id") or "process") for p in procs]
    for g in roots:
        errs += wellformed(g)
    return (None, errs[:8]) if errs else (roots, [])


def fmt_trace(t):
    return " > ".join(t) if t else "(empty)"


def describe_behaviour(beh):
    why = []
    for b in beh:
        if b["inconclusive"]:
            why.append("the checker hit its state cap, so the behaviour could not be confirmed; "
                       "avoid adding parallel branches or loops that multiply states")
        if b["missing"]:
            why.append("these task sequences are possible in the current model but not in yours: "
                       + "; ".join(fmt_trace(t) for t in b["missing"]))
        if b["extra"]:
            why.append("these task sequences are possible in your model but not in the current one: "
                       + "; ".join(fmt_trace(t) for t in b["extra"]))
        if b["new_deadlock"]:
            why.append("your model can deadlock (a token gets stuck, for example at an AND join)")
    return why


def feedback(reasons):
    return ("Your answer was rejected by the automatic checker:\n- " + "\n- ".join(reasons) +
            "\nReturn a corrected answer in the same JSON format. If you cannot fix it safely, "
            "return the current model unchanged.")


def llm_round(base, orig, before_lang, cfg, a, key):
    """One round: ask Gemini to simplify `base` (up to --attempts tries, each rejection is fed
    back), verify every answer against the ORIGINAL model `orig`.
    Returns (roots, status, changes, behaviour, log, accepted)."""
    log = {"attempts": []}
    m, viol = metrics(base), check_guidelines(base, cfg)
    if not viol:
        return base, "skipped: no guideline violations left", [], None, log, False
    if m["nodes"] > a.max_llm_nodes:
        return base, f"skipped: {m['nodes']} nodes is above --max-llm-nodes {a.max_llm_nodes}", \
            [], None, log, False
    system, prompt = system_prompt(cfg, a.relax), build_prompt(base, m, viol, cfg)
    log["prompt"] = prompt
    if a.dry_run:
        print("  --- user prompt that would be sent (the fixed system prompt comes before it) ---")
        print(prompt)
        return base, "dry run", [], None, log, False
    contents = [{"role": "user", "parts": [{"text": prompt}]}]
    base_score, base_viol = evaluate(base, cfg)
    reasons = []
    for attempt in range(1, a.attempts + 1):
        entry = {"attempt": attempt}
        log["attempts"].append(entry)
        try:
            text = gemini_generate(key, a.model, system, contents, a.temperature)
        except LLMError as e:
            entry["error"] = str(e)
            print(f"  attempt {attempt}: API error: {e}")
            return base, f"error: {e}", [], None, log, False
        entry["response"] = text
        cand, beh, changes, rmap, reasons = None, None, [], {}, []
        try:
            xml, rmap, changes = parse_answer(text)
        except ValueError as e:
            reasons = [str(e)]
        else:
            cand, reasons = load_candidate(xml)
            if cand is not None and len(cand) != len(base):
                cand, reasons = None, [f"expected {len(base)} process(es), got {len(cand)}"]
        accept, review = False, False
        if cand is not None:
            for gn, go in zip(cand, base):
                gn.name = go.name
            beh = behaviour_report(orig, cand, a.max_len, a.max_states, rmap, before_lang)
            new_score, new_viol = evaluate(cand, cfg)
            worse = sorted(set(codes(new_viol)) - set(codes(base_viol)))
            entry["score"] = list(new_score)
            entry["behaviour_same"] = behaviour_ok(beh)
            if not behaviour_ok(beh):
                if a.relax and not worse and new_score < base_score \
                        and not any(b["inconclusive"] for b in beh):
                    accept = review = True
                else:
                    reasons = describe_behaviour(beh)
            elif worse:
                reasons = [f"your model breaks {', '.join(worse)}, which the current model satisfies: "
                           + "; ".join(f"{c}: {d}" for c, d in new_viol if c in worse)]
            elif new_score < base_score:
                accept = True
            elif new_score == base_score:
                entry["status"] = "no improvement"
                entry["changes"] = changes
                print(f"  attempt {attempt}: no further safe simplification found")
                return base, "no further safe simplification found", changes, beh, log, False
            else:
                reasons = [f"your model is more complex than the current one "
                           f"(score {new_score} against {base_score}; compared in order: "
                           "guidelines broken, violations, CFC, nodes, arcs; lower is better)"]
        entry["changes"], entry["reasons"] = changes, reasons
        if accept:
            status = "accepted (behaviour differs, needs review)" if review else "accepted"
            entry["status"] = status
            print(f"  attempt {attempt}: {status}")
            return cand, status, changes, beh, log, True
        entry["status"] = "rejected"
        print(f"  attempt {attempt}: rejected -> {reasons[0] if reasons else 'unknown'}")
        contents += [{"role": "model", "parts": [{"text": text}]},
                     {"role": "user", "parts": [{"text": feedback(reasons)}]}]
    return base, f"failed after {a.attempts} attempts: {reasons[0] if reasons else 'unknown'}", \
        [], None, log, False


def llm_pass(base, orig, before_lang, cfg, a, key):
    """Up to --rounds rounds. A round that is accepted becomes the starting point of the next
    one while violations remain. Returns (roots, status, changes, behaviour, log, accepted)."""
    log = {"model": a.model, "rounds": []}
    cur, changes_all, beh, status, ok_any = base, [], None, "", False
    for rnd in range(1, a.rounds + 1):
        if rnd > 1:
            left = check_guidelines(cur, cfg)
            if not left:
                break
            print(f"  round {rnd}: {len(left)} violation(s) left, asking again")
        res, st, changes, b, rlog, ok = llm_round(cur, orig, before_lang, cfg, a, key)
        log["rounds"].append(rlog)
        if not ok:
            if not ok_any:
                return base, st, changes, b, log, False
            break
        cur, beh, ok_any = res, b, True
        changes_all += changes
        status = st if "review" in st or not status else status
    return cur, status, changes_all, beh, log, ok_any


# ----------------------------------------------------------------------------
# 8. Command-line interface
# ----------------------------------------------------------------------------
COLS = ["nodes", "arcs", "tasks", "gateways", "xor", "and", "or", "starts", "ends",
        "max_fanout", "cfc", "dup_copies", "unmatched_gateways", "nesting_depth", "max_scope_nodes"]
SHOWN = ["nodes", "arcs", "starts", "ends", "max_fanout", "dup_copies", "cfc"]


def find_models(path):
    if os.path.isdir(path):
        files = glob.glob(os.path.join(path, "**", "*.bpmn"), recursive=True)
        files += glob.glob(os.path.join(path, "**", "*.xml"), recursive=True)
        return sorted(files)
    return [path]


def cmd_analyze(a):
    cfg = dict(g1=a.g1_limit, g2=a.g2_limit, g7=a.g7_limit)
    rows = []
    for f in find_models(a.path):
        roots = parse_bpmn(f)
        m = metrics(roots)
        v = check_guidelines(roots, cfg, m)
        rows.append((os.path.basename(f), m, v))
    rows.sort(key=lambda r: (-len(codes(r[2])), -r[1]["cfc"]))
    print(f"{'model':28} {'nodes':>5} {'arcs':>4} {'gw':>3} {'S/E':>5} {'fan':>3} {'CFC':>4} {'dup':>3}  violated")
    for name, m, v in rows:
        print(f"{name[:28]:28} {m['nodes']:5} {m['arcs']:4} {m['gateways']:3} "
              f"{str(m['starts']) + '/' + str(m['ends']):>5} {m['max_fanout']:3} {m['cfc']:4} {m['dup_copies']:3}  "
              f"{len(codes(v))}/7 {','.join(codes(v))}")
        if a.verbose:
            for c, msg in v:
                print(f"      {c}: {msg}")
    if a.csv:
        with open(a.csv, "w", newline="", encoding="utf-8") as fh:
            w = csv.writer(fh)
            w.writerow(["model"] + COLS + ["guidelines_violated", "n_violated"])
            for name, m, v in rows:
                w.writerow([name] + [m[c] for c in COLS] + [";".join(codes(v)), len(codes(v))])
        print(f"\nSaved {a.csv}")


def print_left(viol):
    if viol:
        print("  still to fix by hand:")
        for c, msg in viol:
            print(f"    - {c}: {msg}")


def cmd_reduce(a):
    cfg = dict(g1=a.g1_limit, g2=a.g2_limit, g7=a.g7_limit)
    os.makedirs(a.out, exist_ok=True)
    use_llm, key = not a.no_llm, None
    if use_llm and not a.dry_run:
        key = load_api_key(a.api_key)
        if not key:
            print("note: no Gemini key found (set GEMINI_API_KEY); running the rule-based pass only.")
            use_llm = False
    table = []
    for f in find_models(a.path):
        name = os.path.splitext(os.path.basename(f))[0]
        before = parse_bpmn(f)
        after, log = reduce_model(before)
        mb, ma = metrics(before), metrics(after)
        vb, va = check_guidelines(before, cfg, mb), check_guidelines(after, cfg, ma)
        before_lang = languages(before, a.max_len, a.max_states)
        beh = behaviour_report(before, after, a.max_len, a.max_states, None, before_lang)
        write_bpmn(after, os.path.join(a.out, f"{name}_reduced.bpmn"))
        print(f"\n=== {name} ===")
        print(f"{'metric':22}{'before':>8}{'after':>8}")
        for c in SHOWN:
            print(f"{c:22}{mb[c]:8}{ma[c]:8}")
        print(f"{'guidelines violated':22}{len(codes(vb)):>5}/7{len(codes(va)):>5}/7   "
              f"({','.join(codes(vb)) or '-'} -> {','.join(codes(va)) or '-'})")
        for line in log or ["no automatic reduction applicable"]:
            print("  change:", line)
        for b in beh:
            print(verdict_line(b))
        print_left(va)

        final, mf, vf, behf, status, beh_llm_same = after, ma, va, beh, "not run", None
        if use_llm:
            print(f"\n  --- LLM pass ({a.model}) ---")
            final, status, changes, behl, llog, accepted = llm_pass(after, before, before_lang,
                                                                    cfg, a, key)
            if any(r["attempts"] for r in llog["rounds"]):
                logdir = os.path.join(a.out, "llm_log")
                os.makedirs(logdir, exist_ok=True)
                llog["status"] = status
                with open(os.path.join(logdir, f"{name}.json"), "w", encoding="utf-8") as fh:
                    json.dump(llog, fh, indent=2)
            if accepted:
                review = "REVIEW" in status.upper()
                write_bpmn(final, os.path.join(a.out, f"{name}_llm{'_REVIEW' if review else ''}.bpmn"))
                mf, vf = metrics(final), check_guidelines(final, cfg)
                for line in changes:
                    print("  llm change:", line[:300])
                for b in behl:
                    print(verdict_line(b))
                print(f"  {'metric':20}{'rules':>8}{'llm':>8}")
                for c in SHOWN:
                    print(f"  {c:20}{ma[c]:8}{mf[c]:8}")
                print(f"  {'guidelines violated':20}{len(codes(va)):>5}/7{len(codes(vf)):>5}/7   "
                      f"({','.join(codes(va)) or '-'} -> {','.join(codes(vf)) or '-'})")
                print_left(vf)
                beh_llm_same = behaviour_ok(behl)
                behf = behl
            else:
                for line in changes:
                    print("  llm note:", line[:300])
                print(f"  result: {status}; keeping the rule-based model")
                final, mf, vf = after, ma, va
        table.append([name] + [mb[c] for c in COLS] + [ma[c] for c in COLS] + [mf[c] for c in COLS]
                     + [len(codes(vb)), len(codes(va)), len(codes(vf)),
                        all(b["equal"] for b in beh),
                        beh_llm_same if beh_llm_same is not None else all(b["equal"] for b in beh),
                        status])
    csv_path = os.path.join(a.out, "before_after.csv")
    with open(csv_path, "w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        w.writerow(["model"] + [f"{c}_before" for c in COLS] + [f"{c}_after" for c in COLS]
                   + [f"{c}_llm" for c in COLS]
                   + ["violated_before", "violated_after", "violated_llm",
                      "behaviour_same", "behaviour_same_llm", "llm_status"])
        w.writerows(table)
    print(f"\nSaved {csv_path} and reduced .bpmn files in {a.out}/")


def main():
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(errors="replace")
        except (AttributeError, ValueError):
            pass
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)
    for name, fn in (("analyze", cmd_analyze), ("reduce", cmd_reduce)):
        s = sub.add_parser(name)
        s.add_argument("path", help="a .bpmn file or a folder of them")
        s.add_argument("--g1-limit", type=int, default=31, help="G1 element limit (check Paper 3)")
        s.add_argument("--g2-limit", type=int, default=3, help="G2 max gateway degree")
        s.add_argument("--g7-limit", type=int, default=50, help="G7 decomposition threshold")
        if name == "analyze":
            s.add_argument("--csv", help="write metrics to this CSV")
            s.add_argument("-v", "--verbose", action="store_true", help="list every violation")
        else:
            s.add_argument("--out", default="reduced")
            s.add_argument("--max-len", type=int, default=30, help="max trace length for behaviour check")
            s.add_argument("--max-states", type=int, default=400000, help="state cap of the simulator")
            s.add_argument("--no-llm", action="store_true", help="rule-based pass only")
            s.add_argument("--dry-run", action="store_true", help="print the LLM prompt, make no API call")
            s.add_argument("--model", default=DEFAULT_MODEL, help="Gemini model name")
            s.add_argument("--attempts", type=int, default=3, help="LLM tries per round (each rejection is fed back)")
            s.add_argument("--rounds", type=int, default=2,
                           help="LLM rounds per model; a later round starts from the accepted result")
            s.add_argument("--temperature", type=float, default=0.2)
            s.add_argument("--max-llm-nodes", type=int, default=120,
                           help="skip the LLM step for models bigger than this")
            s.add_argument("--relax", action="store_true",
                           help="also accept a simpler LLM model whose behaviour differs; "
                                "saved as *_llm_REVIEW.bpmn for manual review")
            s.add_argument("--api-key", help="Gemini key (prefer the GEMINI_API_KEY variable)")
        s.set_defaults(fn=fn)
    a = p.parse_args()
    a.fn(a)


if __name__ == "__main__":
    main()
