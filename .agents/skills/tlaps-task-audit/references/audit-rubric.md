# TLAPS task-audit rubric

Use all classification axes. Do not combine them into one verdict.

## 1. Task integrity

Choose one value.

### `PASS`

Use `PASS` when the task structure is correct and you found no direct task defect.

The original source proof can omit steps or fail with the current TLAPM version. That source condition does not make the extracted theorem invalid.

### `NEEDS_REVIEW`

Use `NEEDS_REVIEW` when evidence indicates a possible task defect, but you cannot prove it.

State the missing evidence. Give the next command or analysis that can resolve the item.

### `CONFIRMED_FAULT`

Use `CONFIRMED_FAULT` only when direct evidence establishes one of these conditions:

- The unchanged task, scaffold, or required context cannot parse.
- Required context is missing or mapped to the wrong task.
- A valid counterexample or formal contradiction disproves the target theorem.
- A trusted scaffold statement gives a checker-valid answer to the target.
- The task target does not match its intended source theorem.
- The checker accepts a forbidden solution.
- The checker rejects a known-valid proof because the task package is broken.

Save the smallest reproducible case. Include the exact checker command and result.

## 2. Provability evidence

Choose one value.

### `CHECKER_PROVED`

A known proof of the target passes the authoritative checker in the canonical task context.

### `SUPPORTED`

A maintainer or expert supports the theorem, but no current checker-valid proof is available in this audit.

Name the source of this support. Do not present it as a checker result.

### `NOT_DEMONSTRATED`

The audit did not establish or disprove the theorem.

This value does not mean that the theorem is false.

### `DISPROVED`

A valid counterexample or formal contradiction disproves the theorem.

Use `CONFIRMED_FAULT` for task integrity when you use this value.

## 3. Answer leakage

Choose one value.

### `NONE_FOUND`

The audit found no direct answer in the trusted task context.

### `CANDIDATE`

A trusted statement appears equivalent to the target, but the shortcut did not pass the authoritative checker.

Use `NEEDS_REVIEW` for task integrity until the audit resolves this candidate.

### `CONFIRMED`

A minimal shortcut uses trusted context and passes the authoritative checker.

Use `CONFIRMED_FAULT` for task integrity. Save the minimal proof and checker output.

Do not classify normal helper lemmas as leaks. A helper is valid when the target still needs material proof work.

## 4. Difficulty and benchmark value

Choose one value.

### `INFORMATIVE`

Available evidence indicates that the task gives useful model separation or requires material proof work.

### `TRIVIAL_CANDIDATE`

The task accepts a very short valid proof or has a high pass rate across relevant models.

This value is not a task fault. Task removal needs a separate benchmark-policy decision.

### `NOT_ASSESSED`

The audit did not assess difficulty.

Do not infer difficulty from one model result alone.

## 5. Source-reference quality

Choose one value.

### `PASSES`

The extracted source proof passes the selected current checker.

### `OMITS_STEPS`

The source intentionally or historically leaves proof steps incomplete.

### `FAILS_CURRENT_TLAPM`

The source proof reaches TLAPM but does not prove all obligations with the current setup.

### `TIMEOUT`

The source-proof check exceeded its stated time limit.

### `MISSING`

The audit cannot locate the mapped source theorem or proof.

### `NOT_ASSESSED`

The audit did not check the source proof.

These values describe reference quality only. `OMITS_STEPS` and `FAILS_CURRENT_TLAPM` do not establish a task fault.

## 6. Run alignment

Use this axis only when the audit includes stored runs.

- `CURRENT`: The captured task, scaffold, and context match the audited commit.
- `STALE`: One or more captured inputs differ from the audited commit.
- `MISSING`: Required run input is absent.
- `NOT_ASSESSED`: The audit does not include stored runs.

If a run is stale, do not use its outcome as the current task result.

## 7. Model outcome

Use this axis only when the audit includes model runs.

- `PASS`: The submitted proof passed the grader.
- `SANY_SYNTAX`: SANY rejected the submitted module.
- `TLAPS_UNPROVED`: SANY accepted the module, but TLAPM left obligations unproved.
- `INFRA`: Infrastructure prevented a valid grading result.
- `PROTOCOL`: The run violated the expected agent or output protocol.
- `RESOURCE`: A time or memory limit prevented completion.
- `UNKNOWN`: Evidence does not identify the failure stage.
- `NOT_ASSESSED`: The audit does not include a model run.

Model outcome is diagnostic evidence. It does not decide task integrity.

## Evidence strength

Use this evidence order from strongest to weakest:

1. An authoritative checker replay in the canonical task context.
2. A direct parse result, exact file comparison, or manifest comparison.
3. A valid formal counterexample or proof.
4. A maintainer statement about theorem intent or provability.
5. Source comments, historical proofs, or repository history.
6. A model result or model-generated explanation.

Label inferences. Do not convert a repeated model failure into a confirmed task fault.

## Project policy examples

Use these examples to prevent known audit errors.

- If the source target says `PROOF OMITTED`, classify source quality as `OMITS_STEPS`. Do not reject the task for this reason alone.
- If the historical source proof fails a few obligations, classify source quality as `FAILS_CURRENT_TLAPM`. Investigate provability separately.
- If the scaffold exposes a formula-identical lemma and `PROOF BY ThatLemma` passes, report a confirmed answer leak and a confirmed task fault.
- If a valid theorem is too easy, report `TRIVIAL_CANDIDATE`. Keep task integrity as `PASS`.
- If a stored run used an old scaffold, report `STALE`. Audit the current task before you report its present quality.
