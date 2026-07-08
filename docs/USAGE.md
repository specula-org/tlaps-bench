# Usage Guide

## Getting Started

Requirements: [uv](https://docs.astral.sh/uv/) and [Docker](https://docs.docker.com/get-docker/). Works on Linux and Windows (x86-64). macOS ARM works through Docker's emulation layer but is slower.

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

A backend is the AI agent that attempts the proof. Five are included:

| Backend | CLI Name | Default Model |
|---------|----------|---------------|
| OpenAI Codex | `codex` | `gpt-5.5` |
| Claude Code | `claude_code` | `claude-opus-4-8` |
| GitHub Copilot | `copilot` | `claude-opus-4.8` |
| LiteLLM | `litellm` | `claude-sonnet-4-6` |
| Pi | `pi` | `openai/gpt-5.5` |

Select a backend with `--backend`:

```bash
uv run tlaps-bench run --backend claude_code --model claude-opus-4-8
uv run tlaps-bench run --backend pi --model anthropic/claude-sonnet-4-6
uv run tlaps-bench run --backend litellm --model claude-sonnet-4-6
```

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
| `litellm` | Model-dependent: `ANTHROPIC_API_KEY`, `OPENAI_API_KEY`, `GEMINI_API_KEY`, `DEEPSEEK_API_KEY` | `~/.aws/` (for Bedrock models) |
| `pi` | Provider-dependent: `OPENAI_API_KEY`, `ANTHROPIC_API_KEY`, etc. | `~/.pi/` (auth.json), `~/.aws/` (for Bedrock) |

For the `pi` backend, the model format is `provider/model` (e.g. `openai/gpt-5.5`, `anthropic/claude-sonnet-4-6`). The provider prefix determines which credentials are used.

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

Run one or more benchmarks with an agent backend.

```bash
uv run tlaps-bench run [flags]
```

| Flag | Default | Description |
|------|---------|-------------|
| `--backend` | `codex` | Agent backend to use |
| `--mode` | `proof-completion` | Benchmark mode |
| `--model` | (backend default) | Override the model |
| `--filter` | (all benchmarks) | Substring match on path, comma-separated |
| `--jobs` | `1` | Number of parallel agent runs |
| `--timeout` | `28800` | Per-benchmark agent timeout in seconds |
| `--check-timeout` | `600` | Per-benchmark checker (tlapm) timeout in seconds |
| `--output-dir` | auto-generated | Output directory |
| `--resume` | off | Skip benchmarks already marked `SKIP` or genuine `PASS` (first-attempt or continuation) |
| `--infra-retries` | `3` | Extra attempts after a transient agent startup/infra failure (0 output tokens); `0` = no inline retries |
| `--max-continuations` | `0` | Run up to N same-workspace continuation attempts after the first attempt completes without PASS (see [Continuation runs](#continuation-runs)) |
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
    │   ├── stderr.txt        # Agent stderr, if any — start here to debug a 0-token run
    │   └── transcript.txt    # Parsed transcript with token summary
    └── grading/
        ├── check.result        # Checker verdict and details
        └── agent_check.result  # Agent's own in-workspace check, if it ran one
```

With `--max-continuations`, each continuation round also writes a `continuations/round-N/` directory with that round's prompt, output, solution, and checker result.

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

To force a rebuild after changing source code:

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

## Adding a New Agent Backend

To add support for a new coding agent, create a Python file in `src/evaluator/backends/` that subclasses `AgentBackend`.

### 1. Create the backend file

`src/evaluator/backends/my_agent.py`:

```python
"""My agent backend."""

from __future__ import annotations

import json
import os

from .base import AgentBackend, detect_firewall_hosts


class MyAgentBackend(AgentBackend):
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
