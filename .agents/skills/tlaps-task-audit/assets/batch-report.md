# Batch <NN> task audit

## Scope

- Repository commit: `<commit>`
- Benchmark mode: `<mode>`
- Task-list source: `<task-list>`
- Inventory file: `<path>`
- Assigned tasks: `<first ordinal>` to `<last ordinal>`

## Summary

| Axis | Counts |
|---|---|
| Task integrity | `<counts>` |
| Provability evidence | `<counts>` |
| Answer leakage | `<counts>` |
| Difficulty | `<counts>` |
| Source-reference quality | `<counts>` |
| Run alignment | `<counts>` |
| Model outcome | `<counts>` |

## Task results

| Ordinal | Canonical task ID | Integrity | Provability | Leakage | Difficulty | Source reference | Run alignment | Model outcome |
|---:|---|---|---|---|---|---|---|---|
| `<n>` | `<exact task ID>` | `<value>` | `<value>` | `<value>` | `<value>` | `<value>` | `<value>` | `<value>` |

## Findings

### `<ordinal>. <canonical task ID>`

- Result: `<one-sentence result>`
- Observed evidence: `<direct evidence>`
- Interpretation: `<inference, or None>`
- Checker command: `<exact command, or Not run>`
- Checker result: `<exit code and concise result>`
- Evidence files: `<durable paths>`
- Next action: `<required action, or None>`

## Commands

```bash
<exact commands>
```

## Limits

State all checks that did not finish. State all evidence that was not available.

Write the matching machine-readable file as `batch-<NN>.json`. Copy the structure from `assets/batch-report.json`.
