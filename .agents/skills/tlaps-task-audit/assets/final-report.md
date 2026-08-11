# TLAPS benchmark task audit

## Executive summary

State the exact cohort, commit, and audit date.

Give the number of audited tasks. List confirmed faults first. Keep possible issues separate.

Do not describe source-proof defects or easy tasks as task faults.

## Scope and method

- Repository commit: `<commit>`
- Benchmark mode: `<mode>`
- Task-list source: `<task-list>`
- Inventory file: `<path>`
- Tasks audited: `<count>`
- Stored runs audited: `<count or Not included>`
- Checker setup: `<version, container mode, and timeout>`

Explain the audit method in short steps.

## Results

| Axis | Value | Count |
|---|---|---:|
| Task integrity | `PASS` | `<n>` |
| Task integrity | `NEEDS_REVIEW` | `<n>` |
| Task integrity | `CONFIRMED_FAULT` | `<n>` |
| Provability | `<value>` | `<n>` |
| Leakage | `<value>` | `<n>` |
| Difficulty | `<value>` | `<n>` |
| Source reference | `<value>` | `<n>` |
| Run alignment | `<value>` | `<n>` |
| Model outcome | `<value>` | `<n>` |

## Confirmed task faults

For each fault, include:

1. The canonical task ID.
2. The exact defect.
3. The minimal reproduction.
4. The checker result.
5. The effect on benchmark validity.
6. The recommended correction.

If there are no confirmed faults, write `No confirmed task faults.`

## Items that need review

For each item, state the evidence gap and the next decisive check.

If there are no review items, write `No unresolved task-quality items.`

## Source-reference findings

List source proofs that omit steps, fail, time out, or are missing.

State clearly that these findings do not establish task faults.

## Difficulty findings

List trivial candidates and the evidence for each one.

Treat removal as a separate benchmark-policy choice.

## Model behavior

Include this section only when the scope includes stored runs.

Separate syntax failures, unproved obligations, infrastructure failures, protocol failures, and resource limits.

Describe repeated observable patterns. Do not claim access to hidden reasoning.

## Coverage and quality controls

State whether the coverage validator passed.

State how many findings received independent review.

List stale inputs and incomplete checks.

## Commands

```bash
<exact commands used during the audit>
```

## Recommended actions

Order actions by benchmark impact. Separate required corrections from optional policy changes.

## Limits

State all timeouts, unavailable evidence, and untested assumptions.
