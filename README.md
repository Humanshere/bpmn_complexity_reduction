# BPMN Complexity Reduction

This project analyzes BPMN process models and reduces unnecessary control-flow
complexity. It performs deterministic rule-based rewrites and can optionally
use Gemini for additional reductions. Candidate changes are checked against
the original model before they are accepted.

## Requirements

- Python 3.8 or newer
- No third-party Python packages are required
- A Gemini API key is optional and only needed for the LLM pass

The tool supports BPMN control-flow elements including events, tasks, gateways,
sequence flows, and sub-processes.

## Usage

Analyze one model or all `.bpmn` files in a directory:

```bash
python3 bpmn_complexity_llm.py analyze samples/
python3 bpmn_complexity_llm.py analyze samples/ --verbose --csv metrics.csv
```

Reduce models using the deterministic rules and optional Gemini pass:

```bash
python3 bpmn_complexity_llm.py reduce samples/ --out reduced/
```

Run only the deterministic rules:

```bash
python3 bpmn_complexity_llm.py reduce samples/ --out reduced/ --no-llm
```

Preview the LLM prompt without making an API call:

```bash
python3 bpmn_complexity_llm.py reduce samples/ --dry-run
```

Run `python3 bpmn_complexity_llm.py <command> --help` for all thresholds,
verification limits, and LLM options.

## Gemini configuration

Set `GEMINI_API_KEY` in the environment, or add it to a local `.env` file:

```bash
export GEMINI_API_KEY="your-key"
```

The key is not printed, logged, or written to generated output. If no key is
available, `reduce` automatically runs the rule-based pass only.

## Output

`analyze --csv` writes the requested metrics to the specified CSV file.
`reduce` writes reduced BPMN files and `before_after.csv` to its `--out`
directory. When LLM attempts are made, diagnostic logs are stored under
`<out>/llm_log/`.

The included sample models are in [`samples/`](samples/).
