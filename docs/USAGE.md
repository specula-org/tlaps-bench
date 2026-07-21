# Usage Guide

## Getting Started

Requirements: [uv](https://docs.astral.sh/uv/) and [Docker](https://docs.docker.com/get-docker/). Works on Linux x86-64 and Windows through WSL2; native Windows is not supported. macOS ARM works through Docker's emulation layer but is slower.

```bash
git clone https://github.com/specula-org/tlaps-bench.git
cd tlaps-bench
export OPENAI_API_KEY=sk-...
uv run tlaps-bench run --backend codex --model gpt-5.5 --filter GCD_GCD3
```

On the first run, the tool builds a Docker image that includes tlapm, SANY, and the proof checker. Subsequent runs reuse the cached image.

Results are saved to `results/proof-completion/codex/<timestamp>/`. Nothing else to install.

### Full benchmark suite

```bash
uv run tlaps-bench run --backend codex --model gpt-5.5 --jobs 10 --timeout 7200
```

### Different backend and model

```bash
export ANTHROPIC_API_KEY=sk-ant-...
uv run tlaps-bench run --backend claude_code --model claude-opus-4-8 --jobs 10
```

### Proof-from-scratch mode

```bash
uv run tlaps-bench run --backend codex --model gpt-5.5 --mode proof-from-scratch --jobs 10
```

---

## Backends

A backend is the model integration that attempts the proof. Seven are included:

| Backend | CLI Name | Default Model |
|---------|----------|---------------|
| OpenAI Codex | `codex` | `gpt-5.5` |
| Claude Code | `claude_code` | `claude-opus-4-8` |
| GitHub Copilot | `copilot` | `claude-opus-4.8` |
| GitHub Copilot SDK (one-shot) | `copilot_oneshot` | `claude-opus-4.8` |
| LiteLLM | `litellm` | `claude-sonnet-4-6` |
| LiteLLM (one-shot) | `litellm_oneshot` | `claude-sonnet-4-6` |
| Pi | `pi` | `openai/gpt-5.5` |

Select a backend with `--backend`:

```bash
uv run tlaps-bench run --backend claude_code --model claude-opus-4-8
uv run tlaps-bench run --backend pi --model anthropic/claude-sonnet-4-6
uv run tlaps-bench run --backend litellm --model claude-sonnet-4-6
uv run tlaps-bench run --backend litellm_oneshot --model claude-sonnet-4-6
```

### OpenAI-compatible endpoints

To target any OpenAI-compatible endpoint (a self-hosted gateway, a vendor's
inference API, etc.), use the LiteLLM backend with an `openai/<model>` model id
and point `OPENAI_API_BASE` (or `OPENAI_BASE_URL`) at the endpoint. The host is
forwarded into the container and automatically added to the firewall allow-list:

```bash
export OPENAI_API_KEY=...
export OPENAI_API_BASE=https://inference-api.somecompany.com/v1
uv run tlaps-bench run --backend litellm --model openai/somecompany/some-model
```

The leading `openai/` selects LiteLLM's OpenAI-compatible transport; everything
after it is sent to the endpoint as the wire model id.

### Reasoning effort

Use the optional `--reasoning-effort` flag to override a model's reasoning budget:

```bash
uv run tlaps-bench run --backend codex --model gpt-5.6-sol --reasoning-effort low
```

### Output token limit

`copilot_oneshot` accepts an explicit positive per-request output limit. When
set, the wire guard replaces the Copilot runtime's output limit and records
both values in the result audit:

```bash
uv run tlaps-bench run --backend copilot_oneshot --model claude-opus-4.8 --max-output-tokens 64000
```

Omit `--max-output-tokens` to preserve the runtime's default. Other backends
currently reject this option instead of silently ignoring it.

### Authentication

The runner passes credentials into the container in two ways:

1. **Environment variables** set on the host are forwarded into the container.
2. **Host credential directories** (`~/.aws/`, `~/.codex/`, `~/.pi/`, `~/.claude/`) are mounted into the container automatically when the backend needs them.

If you are already logged in to an agent on your host machine (e.g. `codex login`, or credentials saved in `~/.codex/`), the runner picks those up and transfers them to the container. You do not need to re-authenticate.

**Per-backend credentials:**

| Backend | Environment Variable | Host Credentials (auto-mounted) |
|---------|---------------------|----------------------------------|
| `codex` | `OPENAI_API_KEY` or `AZURE_OPENAI_API_KEY` + `AZURE_OPENAI_HOST` | `~/.codex/` (logged-in session) |
| `claude_code` | `ANTHROPIC_API_KEY` | `~/.claude/` |
| `copilot` | `COPILOT_GITHUB_TOKEN` or `GH_TOKEN`. BYOK: `COPILOT_PROVIDER_BASE_URL` + `COPILOT_PROVIDER_API_KEY` + `COPILOT_PROVIDER_TYPE` | |
| `copilot_oneshot` | `COPILOT_GITHUB_TOKEN`, `GH_TOKEN`, or `GITHUB_TOKEN` | |
| `litellm` | Model-dependent: `ANTHROPIC_API_KEY`, `OPENAI_API_KEY`, `GEMINI_API_KEY`, `DEEPSEEK_API_KEY` | `~/.aws/` (for Bedrock models) |
| `litellm_oneshot` | Model-dependent: `ANTHROPIC_API_KEY`, `OPENAI_API_KEY`, `GEMINI_API_KEY`, `DEEPSEEK_API_KEY` | `~/.aws/` (for Bedrock models) |
| `pi` | Provider-dependent: `OPENAI_API_KEY`, `ANTHROPIC_API_KEY`, etc. | `~/.pi/` (auth.json), `~/.aws/` (for Bedrock) |

For the `pi` backend, the model format is `provider/model` (e.g. `openai/gpt-5.5`, `anthropic/claude-sonnet-4-6`). The provider prefix determines which credentials are used.

### Strict one-shot backends

`litellm_oneshot` and `copilot_oneshot` use the same provider-neutral one-shot contract. The target module and its dependencies are embedded in one user prompt, only one provider request is forwarded per attempt, and the requested response is either one complete TLA+ module or exactly one `tla` code fence containing that module. The runner materializes the sole non-empty response as `solution.tla` and leaves syntax and proof validity to the normal grader; there is no agent tool loop or opportunity to inspect and edit the workspace.

```bash
export ANTHROPIC_API_KEY=sk-ant-...
uv run tlaps-bench run --backend litellm_oneshot --model claude-sonnet-4-6 --filter GCD_GCD3

export COPILOT_GITHUB_TOKEN=github_pat_...
uv run tlaps-bench run --backend copilot_oneshot --model claude-opus-4.8 --max-output-tokens 64000 --filter GCD_GCD3
```

The LiteLLM backend makes one non-streaming `litellm.completion` invocation per attempt with the prompt as its sole user message and no tools or system message. LiteLLM-level retries are disabled, but provider transport behavior below that adapter boundary is not wire-audited. Its normalized `model_requests: 1` therefore means one logical completion invocation, not an observed wire-request count. The Copilot backend uses the official Python Copilot SDK. Its request handler rebuilds the SDK's outbound inference request from endpoint-specific control-field allowlists before forwarding it: system and developer messages, tool definitions and tool choice, and SDK-added current date/time context are removed. The handler blocks unknown model-layer endpoints and any second inference attempt within the same attempt. This is an auditable exactly-one-request-per-attempt guarantee at the SDK-to-Copilot-API boundary; it does not claim control over prompts or processing that GitHub's gateway may apply after receiving the request.

Copilot receives the benchmark's absolute deadline, so SDK and session startup count against the same wall-clock budget as inference. At the deadline an independent watchdog freezes the wire guard, cancels in-flight forwarding, emits and flushes usage plus request-audit evidence, and only then attempts the SDK's abort/teardown; the host allows a bounded 10-second drain window before a hard kill. The frozen guard rejects any late SDK inference attempt, so that window is cleanup time only: the verdict is already `TIMEOUT`, and recorded model runtime is capped at the benchmark timeout.

Strict one-shot runs automatically skip the model preflight because it would consume another inference. Like agentic backends, they default to three outer infrastructure retries. A one-shot attempt is replayed only when it has no output tokens, reasoning tokens, or persisted model-output evidence and either failed during empty nonzero startup or emitted an explicit transient provider/transport classification. Authentication and invalid-request errors, request-contract violations, clean empty exits, malformed event streams, and attempts with model output are never replayed. Each retry starts a fresh workspace and retains the failed evidence under `agent/attempts/`. LiteLLM adapter retries are disabled; within a Copilot attempt, the first inference request may be forwarded and any later SDK retry attempt is blocked. When that sole forwarded request has explicit transient failure evidence, the blocked SDK retries may be replaced by an outer fresh-workspace retry; otherwise the guard violation is permanent. `--max-continuations` must remain `0`. `copilot_oneshot` accepts only an explicit `COPILOT_GITHUB_TOKEN`, `GH_TOKEN`, or `GITHUB_TOKEN`; it does not probe a Copilot CLI login, mount stored session credentials, or accept the agentic backend's BYOK settings.

With `--no-container`, the runner uses its source-tree path instead of `/opt`. LiteLLM is already a project dependency; native Copilot runs additionally require `github-copilot-sdk==1.0.7` and its runtime (`python3 -m copilot download-runtime`) in the active environment.

---

## Modes

A mode defines what the agent is asked to do.

| Mode | What the agent sees | What it must do |
|------|---------------------|-----------------|
| `proof-completion` | Full scaffolding. Preceding proofs marked `PROOF OMITTED`. Last theorem has `PROOF OBVIOUS`. | Replace `PROOF OBVIOUS` with a valid proof. Cannot change anything above it. |
| `proof-from-scratch` | Only the model (definitions, constants, variables) and the target theorem statement with `PROOF OBVIOUS`. | Invent the entire proof structure, including helper lemmas. |

Select a mode with `--mode`:

```bash
uv run tlaps-bench run --backend codex --model gpt-5.5 --mode proof-completion
uv run tlaps-bench run --backend codex --model gpt-5.5 --mode proof-from-scratch
```

Benchmark files live in `benchmark/proof-completion/` and `benchmark/proof-from-scratch/` respectively.

---

## CLI Reference

### `tlaps-bench run`

Run one or more benchmarks with an evaluator backend.

```bash
uv run tlaps-bench run [flags]
```

| Flag | Default | Description |
|------|---------|-------------|
| `--backend` | `codex` | Evaluator backend to use |
| `--mode` | `proof-completion` | Benchmark mode |
| `--model` | (backend default) | Override the model |
| `--reasoning-effort` | (backend behavior) | Pass a backend/model-specific reasoning effort |
| `--max-output-tokens` | (backend behavior) | Positive per-request output limit; currently supported by `copilot_oneshot` |
| `--filter` | (all benchmarks) | Substring match on path, comma-separated |
| `--jobs` | `1` | Number of parallel backend runs |
| `--timeout` | `28800` | Per-benchmark backend timeout in seconds |
| `--check-timeout` | `600` | Per-benchmark checker (tlapm) timeout in seconds |
| `--output-dir` | auto-generated | Output directory |
| `--resume` | off | Skip benchmarks already marked `SKIP` or genuine `PASS` (first-attempt or continuation) |
| `--infra-retries` | `3` | Extra attempts after a backend-approved transient startup/infra failure with no model output evidence |
| `--max-continuations` | `0` | Run up to N same-workspace continuation attempts after the first attempt completes without PASS; strict one-shot backends require `0` (see [Continuation runs](#continuation-runs)) |
| `--force-build` | off | Rebuild the Docker image |
| `--no-container` | off | Run without Docker (requires native setup) |
| `--keep-container` | off | Retain each agent container after it exits (drop `--rm`) for debugging (see [Debugging a run](#debugging-a-run-keep-container)) |
| `--session-dir` | off (default `~/.tlaps-bench/sessions` under `--keep-container`) | Persist each run's agent session state to this persistent host path (survives container removal and reboot; restore with `scripts/restore-session.sh`) |

Run `uv run tlaps-bench run --help` for the full flag list.

### `tlaps-bench check`

Check a single proof file for correctness and cheating.

```bash
uv run tlaps-bench check path/to/file.tla --mode proof-completion
uv run tlaps-bench check path/to/file.tla --mode proof-from-scratch
uv run tlaps-bench check path/to/file.tla --sany-only
```

By default, `check` reuses `<target-dir>/.tlacache`; use `--no-cache` for a cold check, or `--timeout 0` for no checker deadline.

Cheating is checked before proving: a detected cheat fails fast and skips the tlapm run (`--keep-verifying` verifies anyway). Each run also snapshots the workspace to a hidden git ref — browse it with `git log refs/tlaps-check/history`; `--no-git-track` disables.

Huge proofs are verified in parallel shards (`tlapm --toolbox` line ranges split at theorem boundaries, one cache dir per shard). Sharding is automatic above `TLAPS_SHARD_MIN_LINES` (5000) lines at nproc/2 shards capped by available memory (`TLAPS_SHARD_MEM_MB` per shard); `--shards N` forces a count, `--shards 1` forces a single run.

Exit codes: `0` = PASS, `1` = FAIL, `3` = ERROR.

### `tlaps-bench score`

Compute pass rates from one or more result files.

```bash
uv run tlaps-bench score results/proof-from-scratch/pi/20260626_220712/results.json
uv run tlaps-bench score results/proof-completion/*/results.json
```

Pass rate = passed tasks / scored tasks. `SKIP`, `INFRA_ERROR`, and `QUOTA_EXHAUSTED` results are excluded from scoring and reported separately; cheating verdicts count as failures.

### `tlaps-bench validate`

Verify that source proofs (before `PROOF OBVIOUS` replacement) pass tlapm.

```bash
uv run tlaps-bench validate --jobs 10
uv run tlaps-bench validate --filter Paxos --jobs 10
```

### `tlaps-bench generate`

Regenerate benchmark files from annotated source specs.

```bash
uv run tlaps-bench generate
uv run tlaps-bench generate --mode proof-from-scratch
```

---

## Output Structure

Each run writes results to a timestamped directory:

```
results/<mode>/<backend>/<timestamp>/
├── results.json              # All verdicts, timing, token counts
├── summary.md                # Headline pass rate
└── <Module>/<Theorem>/
    ├── result.json           # Per-benchmark verdict and metadata
    ├── input/
    │   ├── benchmark.tla     # Original benchmark file (copied in)
    │   ├── *.tla             # Dependency modules it EXTENDS (copied in)
    │   └── prompt.txt        # Prompt sent to the agent
    ├── agent/
    │   ├── solution.tla      # The agent's final output
    │   ├── output.jsonl      # Raw agent stdout capture
    │   ├── copilot-otel.jsonl # Copilot CLI only: official usage telemetry
    │   ├── stderr.txt        # Agent stderr, if any — start here to debug a 0-token run
    │   └── transcript.txt    # Parsed transcript with token summary
    └── grading/
        ├── check.result        # Checker verdict and details
        └── agent_check.result  # Agent's own in-workspace check, if it ran one
```

With `--max-continuations`, each continuation round also writes a `continuations/round-N/` directory with that round's prompt, output, solution, and checker result.

### Usage and cost telemetry

Each `result.json` keeps the existing top-level `input_tokens`, `output_tokens`, and `time_secs` fields for compatibility. It also includes a versioned `usage` record with provider-neutral totals and, when the provider exposes them, one entry per model request:

- input, output, cache-read, cache-write, and reasoning tokens
- model request count and summed model-call duration
- requested/resolved model, provider request IDs, retry attempt, and continuation round
- provider-reported cost values, preserving their native unit and source
- `complete`, `lower_bound`, `incomplete`, or `unavailable` status plus validation warnings

An unavailable value is `null`, not zero. The legacy top-level token fields still use zero when a value is unavailable, so new analysis should read `usage` and its status. Cache tokens classify input tokens and reasoning tokens classify output tokens; they are not added to the input/output totals a second time.

`time_secs` remains the active wall time for that benchmark task, including agent and tool work but excluding quota waits and infra-retry backoff. Retries and continuation rounds are added to the task total. Parallel tasks can overlap, so summing `time_secs` across a run gives task-time, not the experiment's wall-clock duration. `usage.model_time_secs` separately sums completed model-call spans and can also exceed wall-clock time when requests overlap.

Copilot uses GitHub's supported telemetry surfaces rather than inferring usage from text:

- The agentic CLI writes [official OpenTelemetry JSONL](https://docs.github.com/en/copilot/reference/copilot-cli-reference/cli-command-reference#opentelemetry-monitoring) to `copilot-otel.jsonl`. Every completed `chat` span is counted once, including sub-agent requests; each `invoke_agent` span cross-checks only its direct chats, and the top-level root indicates that the trace finished. If a timeout prevents that root from being flushed, completed chats are retained as a lower bound. Message-content capture is explicitly disabled.
- The one-shot backend records the official SDK's [`assistant.usage` event](https://docs.github.com/en/copilot/how-tos/copilot-sdk/features/streaming-events#assistantusage).

Native Copilot cost values use provider accounting units: CLI `github.copilot.cost` and SDK `assistant.usage.cost` are stored as `model_multiplier`, CLI `github.copilot.aiu` as `aiu`, and nano-AIU values as `nano_aiu`. These are auditable provider values rather than a claimed invoice total or a locally reconstructed USD price. If an agent or sub-agent request omits a cost field that other requests report, the known amount is explicitly marked as a lower bound.

---

## Resuming a Run

If a run is interrupted or you want to retry only the failures:

```bash
uv run tlaps-bench run --backend codex --model gpt-5.5 --output-dir results/proof-completion/codex/20260626_120000 --resume
```

The runner skips benchmarks already recorded as `SKIP` or as a genuine `PASS` in that directory (first-attempt or via a continuation round), and reruns the rest.

Inline infra retries are intentionally short: the default `--infra-retries 3` gives the original attempt plus three retries with brief backoff. If a longer provider or network outage leaves `INFRA_ERROR` / `QUOTA_EXHAUSTED` results, rerun later with the same `--output-dir --resume`; those non-genuine results are not skipped.

---

## Continuation Runs

Use `--max-continuations N` to give the agent extra chances to finish a proof it already started:

```bash
uv run tlaps-bench run --backend codex --model gpt-5.5 --max-continuations 3
```

Each benchmark still starts with the normal first attempt. If that attempt completes without PASS, the runner starts up to `N` more attempts in the same workspace. Each continuation sees the partial proof from the previous attempt. The chain stops once a continuation passes or the limit is reached.

The first-attempt verdict stays in `check_verdict`. Continuation rounds are saved under `continuations` in `results.json`, and reports show them separately as `Pass rate with continuations (≤N)`.

---

## Docker Details

Each run spins up an isolated container that installs the agent CLI, applies a network firewall (only LLM API hosts are reachable), and mounts benchmarks read-only to prevent tampering.

The runner fingerprints the Docker inputs and automatically rebuilds when the
embedded source or checker changes. Use `--force-build` only when you need to
rebuild the current fingerprint explicitly:

```bash
uv run tlaps-bench run --backend codex --model gpt-5.5 --force-build
```

To skip Docker entirely (for debugging, requires native setup):

```bash
uv run tlaps-bench run --backend codex --model gpt-5.5 --no-container
```

### Debugging a run (`--keep-container`)

By default each agent container is started with `--rm`, so it (and its writable layer, where the agent's session state such as `.copilot` / `.codex` lives) is deleted the moment the run finishes or is interrupted. That makes it impossible to resume the agent or ask it follow-up questions afterwards.

Pass `--keep-container` to retain the container instead:

```bash
uv run tlaps-bench run --backend copilot --keep-container --filter my_benchmark
```

Each run prints the retained container's name, e.g.:

```text
[keep-container] retaining container 'tlaps-bench-my_benchmark-1a2b3c4d'. After it exits: `docker exec -it tlaps-bench-my_benchmark-1a2b3c4d bash` to inspect (start it first if stopped: `docker start ...`), `docker commit ... <img>` to snapshot, `docker rm -f ...` to remove.
```

The name is unique per attempt, so parallel jobs, infra retries and continuation rounds never collide.

`--keep-container` also **persists the session state to the host by default** (see below), so a single flag is enough for debugging and the state survives even a host reboot. Clean up when done — retained containers are **not** auto-removed:

```bash
docker ps -a --filter name=tlaps-bench- --format '{{.Names}}' | xargs -r docker rm -f
```

`--keep-container` only applies in container mode (it is ignored with `--no-container`).

### Persisting session state to the host (`--session-dir`)

Session state lives inside the container, and for backends that authenticate from a mounted credential file (`codex` / `claude_code` / `pi`) it is written into a `/tmp` tempdir — so a reboot (e.g. after an OOM) clears it even if the container is kept. To avoid that, the agent's session state is bind-mounted straight to a **persistent host directory**.

With `--keep-container` this happens automatically under `~/.tlaps-bench/sessions/`. Pass `--session-dir` to choose the location explicitly (and to persist without keeping the container):

```bash
uv run tlaps-bench run --backend copilot --session-dir ./sessions --filter my_benchmark
```

Each run writes its state to `<session-dir>/<backend>/<benchmark>/` (or `<...>/<container-name>/` under `--keep-container`, one dir per retained container). For `codex`/`claude_code`/`pi` the credential files are stored there too, so a single mount holds both auth and session. Because it is a real host path — not `/tmp` and not tied to the container's lifetime — the state survives container removal *and* reboot, and can be moved to another machine. A `.gitignore` (`*`) is written at the session root so this credential-bearing data can't be accidentally committed. `--session-dir` is ignored with `--no-container`.

### Restoring a session into a container

To resume or inspect a persisted session, mount it back into a fresh container:

```bash
scripts/restore-session.sh --backend copilot ~/.tlaps-bench/sessions/copilot/<container-name>
```

This starts an interactive `tlaps-bench-base` shell with the session mounted at the backend's session path (e.g. `/root/.copilot`), so you can read the transcript or run the agent CLI's own resume command (e.g. `copilot --resume`). The container is removed on exit; the host session directory is not. (Network egress is not firewalled in this debug shell, and no benchmark files are mounted — it is for inspecting/continuing the agent session, not for grading.)

---

## Native Setup (Optional)

Only needed if you run with `--no-container` or develop the tooling itself.

**Additional requirements:** GNU Make, `curl`, `tar`, Python 3.12+, JDK 21+, and Linux x86-64 with glibc ≥ 2.38 (Ubuntu 24.04+, Debian 13+) or macOS arm64. On older Linux, use Docker instead.

```bash
make setup
```

This installs the Python environment, downloads tlapm 1.6, compiles the checker binary, and runs a SANY smoke test. Safe to rerun. Uses about 3 GB of disk.

---

## Backend Architecture

All entries in the backend registry share the neutral `Backend` lifecycle. Tool-using workspace editors inherit `AgenticBackend`; strict single-request implementations inherit the sibling `OneShotBackend`. Prompt construction, command/deadline propagation, option validation, result metadata, request-audit validation, and submission preparation are polymorphic backend hooks, so the common runner and termination classifier do not special-case one-shot names or provider names. Runtime one-shot providers implement the `OneShotProvider` protocol and are selected through a registry; each one-shot backend cross-checks the common request contract against its provider's raw audit evidence. A provider may report one `usage_details` entry per model request; each entry must explicitly include both `input_tokens` and `output_tokens` to be complete. Providers without per-request details can return exact aggregate token counts instead. Unavailable counts must be `None`, which becomes `null` and makes the record a lower bound; explicit zeroes remain exact zeroes.

## Adding a New Agentic Backend

To add support for a new coding agent, create a Python file in `src/evaluator/backends/` that subclasses `AgenticBackend`.

### 1. Create the backend file

`src/evaluator/backends/my_agent.py`:

```python
"""My agent backend."""

from __future__ import annotations

import json
import os

from .agentic import AgenticBackend
from .base import detect_firewall_hosts


class MyAgentBackend(AgenticBackend):
    name = "my_agent"
    install_script = "install-my-agent.sh"
    env_keys = ["MY_AGENT_API_KEY"]

    def __init__(self, model: str | None = None):
        self.model = model or "default-model"

    def build_command(self, workspace: str, result_dir: str) -> list[str]:
        return ["my-agent", "--model", self.model, "--workspace", workspace]

    def parse_output(self, jsonl_path: str) -> tuple[str, int, int]:
        transcript, in_tok, out_tok = "", 0, 0
        try:
            with open(jsonl_path) as f:
                for line in f:
                    event = json.loads(line)
                    transcript += event.get("text", "")
                    in_tok += event.get("input_tokens", 0)
                    out_tok += event.get("output_tokens", 0)
        except FileNotFoundError:
            pass
        return transcript, in_tok, out_tok

    def check_auth(self) -> str | None:
        if not os.environ.get("MY_AGENT_API_KEY"):
            return "my_agent: MY_AGENT_API_KEY not set"
        return None

    def firewall_hosts(self) -> list[str]:
        return detect_firewall_hosts(self.model)
```

### 2. Register it

In `src/evaluator/backends/__init__.py`, add:

```python
from .my_agent import MyAgentBackend

_REGISTRY = {
    # ... existing backends ...
    MyAgentBackend.name: MyAgentBackend,
}
```

### 3. Add an install script (if needed)

Create `docker/install-scripts/install-my-agent.sh`:

```bash
#!/bin/bash
set -e
npm install -g my-agent-cli --cache /tmp/.npm && rm -rf /tmp/.npm
```

This script runs inside the container with full network access before the firewall is applied. Use it to install your agent's CLI.

### Interface reference

| Method | What it does |
|--------|-------------|
| `name` | String used as the `--backend` CLI value |
| `install_script` | Filename in `docker/install-scripts/` to run at container start. Set `None` if pre-installed. |
| `env_keys` | List of host environment variables forwarded into the container |
| `credential_mounts` | List of credential directory names to mount (see below) |
| `get_credential_mounts()` | Override this for dynamic credential logic |
| `build_command(workspace, result_dir)` | Returns the agent command as a list. The prompt is piped to stdin. The agent works in `workspace/` where the `.tla` file lives. |
| `parse_output(jsonl_path)` | Reads the captured stdout file. Returns `(transcript, input_tokens, output_tokens)`. |
| `parse_usage(jsonl_path, *, input_tokens, output_tokens)` | Returns a structured `UsageSummary`. The default implementation adapts the legacy token pair, so existing backends remain compatible. |
| `execution_environment(result_dir)` | Returns per-execution environment additions, such as an isolated telemetry output path. |
| `attempt_output_files()` | Lists backend-owned artifacts that must be preserved and cleared across infra retries. |
| `check_auth()` | Fast host-side check before launching a container. Return `None` if OK, or an error string. |
| `firewall_hosts()` | List of API hostnames the container must allow. Use `detect_firewall_hosts(model)` to allow all known LLM API endpoints. |

### Credential mount names

| Name | Mounts from host | Into container |
|------|------------------|----------------|
| `"aws"` | `~/.aws/` | `~/.aws/` |
| `"codex"` | `~/.codex/` | `~/.codex/` |
| `"pi"` | `~/.pi/` | `~/.pi/` |
| `"claude"` | `~/.claude/` | `~/.claude/` |

---
