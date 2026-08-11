---
name: tlaps-task-audit
description: Audit TLAPS Bench proof-completion tasks and cohorts for task integrity, theorem provability evidence, answer leakage, source-reference quality, difficulty signals, stale run artifacts, and model failure causes. Use when reviewing TLAPS task quality, trimming benchmark cohorts, investigating suspicious tasks, analyzing one-shot or agentic results, or preparing a shareable task-audit report.
---

# TLAPS Task Audit

Audit each task with evidence from the task, its scaffold, its context, and the checker. Keep task faults separate from source-proof defects, model failures, and difficulty.

## Read the audit rules

Read [references/audit-rubric.md](references/audit-rubric.md) before you classify a task.

Read [references/repository-workflow.md](references/repository-workflow.md) before you run repository commands.

Read [references/trace-analysis.md](references/trace-analysis.md) when the scope includes stored model runs.

Use the files in `assets/` when you write batch and final reports.

## Protect the audit target

Treat the benchmark, source, results, and session files as read-only.

Write audit outputs under `.notes/<audit-id>/` unless the user gives another path.

Do not repair or remove a task during an audit. Ask for a separate change after the report.

Record the current commit, benchmark mode, task-list source, and checker command.

## Build an exact inventory

Run the inventory script before a cohort audit:

```bash
python3 .agents/skills/tlaps-task-audit/scripts/build_audit_inventory.py \
  --repo . \
  --mode proof-completion \
  --task-list core \
  --batch-size 10 \
  --output .notes/<audit-id>/inventory.json
```

The script rejects empty lists, duplicate IDs, unknown IDs, and missing task files. It records file hashes and exact batch assignments.

Do not hard-code a task count. Use the generated inventory.

## Audit each task

For each task, do these checks:

1. Confirm that the inventory maps the task to the correct specification and context files.
2. Inspect the target theorem and every trusted statement in the scaffold.
3. Run a SANY check on the unchanged task.
4. Search for a formula-equivalent theorem or direct answer in the trusted context.
5. Stage the exact manifest context with `scripts/stage_audit_case.py`.
6. Test each suspected shortcut with the authoritative checker.
7. Inspect the original source proof and record its status on a separate axis.
8. Establish theorem provability with a checker-valid proof when one is available.
9. Inspect run artifacts only after the task audit when the scope includes results.

Use the exact classification axes from the rubric. Do not replace them with one mixed verdict.

## Use strong evidence

Report a confirmed fault only when direct evidence proves the fault.

A model failure does not prove a task fault.

A failed, omitted, or incomplete source proof does not prove a task fault.

Do not repair every historical source proof to make the validator pass. Record its status and continue unless provability is the audit question.

A task that is easy can still be correct. Report difficulty as a separate benchmark-policy signal.

Treat stale run input as a run-alignment issue. Audit the current task separately.

For a confirmed answer leak, save the minimal checker-valid proof and its checker result.

Separate observed facts from explanations that you infer.

## Audit a large cohort

Use the inventory batch assignments when several agents share the audit.

Give each agent exact task IDs. Require one Markdown note and one JSON sidecar per batch.

Do not let batch agents edit benchmark files, source files, result files, or other batch reports.

After all batches finish, run:

```bash
python3 .agents/skills/tlaps-task-audit/scripts/validate_audit_coverage.py \
  --inventory .notes/<audit-id>/inventory.json \
  --reports-dir .notes/<audit-id>/batches \
  --summary-output .notes/<audit-id>/coverage-summary.json
```

Independently review every `NEEDS_REVIEW` and `CONFIRMED_FAULT` result. Also review all pass results with unusually short proofs.

## Deliver the report

Use [assets/final-report.md](assets/final-report.md) for the final report.

State the exact cohort and current commit. Give counts for every classification axis.

Put confirmed faults first. Put review items next. Keep model behavior in a separate section.

Include commands, concise checker output, and file locations. Explain the effect of each fault on benchmark validity.

Do not claim access to hidden or encrypted reasoning. Analyze only observable prompts, outputs, tool events, usage, and checker logs.
