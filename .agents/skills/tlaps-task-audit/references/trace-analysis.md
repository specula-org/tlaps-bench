# Observable model-trace analysis

Use this reference only when the audit includes stored runs.

Audit task quality first. Analyze model behavior after you establish the current task state.

## Confirm run alignment

Compare the captured task and context with the audited commit.

If any input differs, classify the run as `STALE`. Do not report that run as the current task result.

Confirm the model, approach, reasoning effort, timeout, checker version, and benchmark mode.

## Use observable evidence

You can analyze these artifacts:

- The exact prompt and task files
- The model response
- Tool-call and tool-result events
- The final materialized module
- SANY and TLAPM output
- Grader results
- Token, request, time, and cost records

Do not claim access to hidden or encrypted reasoning.

## Find the first decisive failure

Start at the earliest stage that prevents success.

Use one primary model-outcome class from the audit rubric.

Then describe one or more observed failure patterns. Pattern labels can overlap, so do not add their counts as if they were exclusive.

## Common failure patterns

### Syntax and proof-language errors

Look for missing separators, malformed proof levels, invalid `QED` placement, and duplicate bound names.

Run SANY on a temporary copy to recover full diagnostics when a stored log truncates them.

### Invented or incorrect names

Check every operator, theorem, tactic, fairness rule, and module name against the available context.

Common failures include plausible but nonexistent helper names and the wrong variant of a real theorem.

### Hierarchical context loss

Inspect nested `ASSUME`, `CASE`, `SUFFICES`, `PICK`, and `TAKE` steps.

Facts from a parent step do not always enter a child obligation automatically. Check whether the proof cites the enclosing step or introduces the premise again.

Do not call this pattern from proof shape alone. Confirm it in the failed obligation context.

### Automation without prerequisites

Look for broad `SMT`, `BY`, or backend calls that omit definitions, witnesses, type facts, or enclosing assumptions.

Enabledness, temporal reasoning, fairness, and quantified witnesses often need explicit intermediate steps.

### Definition or API mismatch

Check whether the proof expands an unavailable definition or applies a theorem with the wrong statement.

Compare the submitted name with the exact trusted context before you call it a hallucination.

### Cascading obligations

A large failed-obligation count can come from one early missing fact.

Find the first independent failure. Separate it from later cascade failures.

### Infrastructure and resource failures

Keep network, authentication, quota, timeout, memory, and process failures separate from proof failures.

Rerun only affected infrastructure cases when the user asks for recovery.

## Checker-log cautions

Use the exit code, structured result, and final gate verdict as primary evidence.

Some logs can contain contradictory informational lines about cheating. Do not classify a run from one such line.

Confirm whether SANY parsed the final module before you classify a result as `TLAPS_UNPROVED`.

## Cross-task analysis

Group tasks by exact, evidence-backed patterns.

Give representative task IDs and concise diagnostics for each pattern.

Report the denominator for every rate. Exclude stale or non-comparable runs from current-result rates.

Keep task faults, model failures, and infrastructure failures in separate totals.

Describe successful counterexamples when they weaken a broad failure claim.

## Report language

Use `observed` for direct artifact evidence.

Use `likely` only when the explanation is an inference.

State what additional check can confirm each unresolved explanation.
