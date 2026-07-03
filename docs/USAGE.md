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
| `--resume` | off | Skip benchmarks already marked `SKIP` or genuine `PASS` |
| `--infra-retries` | `3` | Extra attempts after a transient agent startup/infra failure (0 output tokens); `0` = no inline retries |
| `--force-build` | off | Rebuild the Docker image |
| `--no-container` | off | Run without Docker (requires native setup) |

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

---

## Resuming a Run

If a run is interrupted or you want to retry only the failures:

```bash
uv run tlaps-bench run --backend codex --model gpt-5.5 --output-dir results/proof-completion/codex/20260626_120000 --resume
```

The runner skips benchmarks already recorded as `SKIP` or as a genuine `PASS` in that directory, and reruns the rest.

Inline infra retries are intentionally short: the default `--infra-retries 3` gives the original attempt plus three retries with brief backoff. If a longer provider or network outage leaves `INFRA_ERROR` / `QUOTA_EXHAUSTED` results, rerun later with the same `--output-dir --resume`; those non-genuine results are not skipped.

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
