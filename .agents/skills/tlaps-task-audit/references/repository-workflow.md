# Repository workflow

This reference describes the current TLAPS Bench file layout and audit commands.

## Task structure

Proof-completion files are under `benchmark/proof-completion/`.

`manifest.json` maps each task ID to its source specification and context files.

A task ID is relative to the mode directory. Example:

```text
Allocator/Allocator_AllocateMutex.tla
```

The task file contains the target theorem. The agent proof is between these markers:

```text
\* BEGIN AGENT PROOF
...
\* END AGENT PROOF
```

The task usually extends a scaffold module. The scaffold contains definitions and trusted earlier lemmas.

Some trusted earlier lemmas use `PROOF OMITTED`. This is intentional task context. It is not a fault by itself.

The mapped original specification is under `source/<spec_id>`.

## Inventory commands

Create an inventory for the registered Core list:

```bash
python3 .agents/skills/tlaps-task-audit/scripts/build_audit_inventory.py \
  --repo . --mode proof-completion --task-list core \
  --batch-size 10 --output .notes/<audit-id>/inventory.json
```

Use `--task-list full` to select every task in the mode manifest.

You can also pass a task-list file path.

## Task checks

Run the fast syntax check on one unchanged task:

```bash
uv run python -m src.common.check_proof \
  --mode proof-completion --sany-only --no-git-track \
  --benchmark-dir benchmark/proof-completion/<module-dir> \
  benchmark/proof-completion/<task-id>
```

Stage the exact manifest context before you test a candidate:

```bash
audit_case_dir=$(mktemp -d)
python3 .agents/skills/tlaps-task-audit/scripts/stage_audit_case.py \
  --repo . --mode proof-completion --task '<task-id>' \
  --output-dir "$audit_case_dir"
```

The script creates `canonical/` and `candidate/` directories. It copies only the target and the context files from the manifest.

Edit only the target file in `candidate/`. Then run the authoritative proof check:

```bash
COMMUNITY_LIB="$PWD/lib/community" uv run python -m src.common.check_proof \
  --mode proof-completion --no-git-track --no-cache \
  --canonical-replay-required \
  --benchmark-dir "$audit_case_dir/canonical" \
  "$audit_case_dir/candidate/<target-file>.tla"
```

Use the same container mode and timeout as the benchmark run when you compare results.

Do not edit the canonical task or the staged canonical directory. Do not add unrelated sibling tasks to the staged context.

Set `COMMUNITY_LIB` for temporary candidates. A file under `/tmp` does not find the repository community library automatically.

Record the candidate proof, exit code, proved-obligation count, failed-obligation count, and relevant diagnostics.

## Source-reference checks

Run the repository validator when the audit includes source-reference quality:

```bash
uv run tlaps-bench validate \
  --filter '<task-or-spec-pattern>' --jobs 1 --timeout 900 \
  --output .notes/<audit-id>/source-validation.md
```

This command tests the extracted reference proof. It does not prove that a task is invalid when the reference fails.

Record placeholders, failed obligations, parser errors, and timeouts as source-reference results.

## Leakage checks

Compare the target formula with all trusted scaffold statements.

Ignore theorem names, whitespace, comments, and harmless formatting differences during the first comparison.

Inspect substitutions, bound-variable renaming, module instances, and definition expansion before you claim equivalence.

If a possible shortcut exists, create the smallest candidate proof. Run it through the same checker path as a benchmark submission.

Classify the leak as `CONFIRMED` only after the checker accepts the shortcut.

## Stored-run checks

Compare these captured inputs with the audited commit when they are available:

- Task file
- Scaffold file
- All manifest context files
- Mode and task-list metadata
- Checker and container version

Classify mismatched captured input as `STALE`.

Use only observable trace data. This data includes prompts, responses, tool calls, usage events, final files, and checker logs.

Do not claim access to encrypted reasoning text.

## Large-cohort controls

Use exact inventory batches. Give each worker its canonical task IDs.

Require one JSON sidecar per batch. The coverage script reads these files.

For one task, create a one-line task-list file in the audit output directory. Build a one-task inventory, and name the sidecar `batch-01.json`.

Run the coverage script after all batch reports exist:

```bash
python3 .agents/skills/tlaps-task-audit/scripts/validate_audit_coverage.py \
  --inventory .notes/<audit-id>/inventory.json \
  --reports-dir .notes/<audit-id>/batches \
  --summary-output .notes/<audit-id>/coverage-summary.json
```

The script checks exact task IDs, duplicates, omissions, batch assignments, enum values, and required evidence fields.

Review every non-pass finding independently. Replay each confirmed fault from a clean temporary directory.

## Known reporting traps

Do not use an abbreviated file name when the report can use the canonical task ID.

Do not call an admitted helper lemma a leak unless it gives the target answer.

Do not treat contradictory informational text from a checker as the final result. Use its exit code and final structured result.

Do not store the only copy of important evidence under `/tmp`.

Do not add root-cause counts when one failed proof has several overlapping causes.
