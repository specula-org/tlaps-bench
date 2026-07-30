"""LiteLLM agent with tool-calling loop. Runs inside container.

Tools: read_file, write_file, bash
Loops until model stops calling tools or max iterations hit.
"""

import argparse
import json
import math
import os
import subprocess
import sys
import time

# Use LiteLLM's bundled model-cost map instead of fetching it at runtime: the
# container firewall blocks the remote fetch, and a failed fetch both emits a
# warning the runner misreads as a transient infra failure and changes provider
# param handling. Must be set before importing litellm.
os.environ.setdefault("LITELLM_LOCAL_MODEL_COST_MAP", "True")

try:
    import litellm
except ImportError:
    print(json.dumps({"type": "error", "message": "litellm not installed"}), flush=True)
    sys.exit(1)

# Drop provider-unsupported params (e.g. temperature for gpt-5 reasoning models)
# rather than raising, so one agent loop works across model families.
litellm.drop_params = True

TOOLS = [
    {
        "type": "function",
        "function": {
            "name": "read_file",
            "description": "Read contents of a file",
            "parameters": {
                "type": "object",
                "properties": {"path": {"type": "string", "description": "File path"}},
                "required": ["path"],
            },
        },
    },
    {
        "type": "function",
        "function": {
            "name": "write_file",
            "description": "Write content to a file (overwrites)",
            "parameters": {
                "type": "object",
                "properties": {
                    "path": {"type": "string", "description": "File path"},
                    "content": {"type": "string", "description": "File content"},
                },
                "required": ["path", "content"],
            },
        },
    },
    {
        "type": "function",
        "function": {
            "name": "bash",
            "description": "Run a bash command and return stdout/stderr",
            "parameters": {
                "type": "object",
                "properties": {"command": {"type": "string", "description": "Command to run"}},
                "required": ["command"],
            },
        },
    },
]


def _token_detail(details: object, *keys: str) -> int | None:
    """Read an optional token sub-count from a LiteLLM usage details object."""

    if details is None:
        return None
    for key in keys:
        value = getattr(details, key, None)
        if value is None and isinstance(details, dict):
            value = details.get(key)
        if isinstance(value, int) and not isinstance(value, bool) and value >= 0:
            return value
    return None


def _response_cost(response: object) -> tuple[float, str] | None:
    """Return LiteLLM's provider-reported USD cost for one response."""

    hidden = getattr(response, "_hidden_params", None)
    if isinstance(hidden, dict):
        cost = hidden.get("response_cost")
        if isinstance(cost, (int, float)) and not isinstance(cost, bool) and cost >= 0 and math.isfinite(float(cost)):
            return float(cost), "litellm.response_cost"
    return None


def _emit_request_usage(response: object, iteration: int, elapsed: float) -> None:
    """Emit one structured usage record per model request.

    Unavailable counts are omitted rather than reported as zero so the
    evaluator can tell "not reported" apart from "genuinely zero".
    """

    usage = getattr(response, "usage", None)
    event: dict = {"type": "request_usage", "iteration": iteration}
    prompt_tokens = getattr(usage, "prompt_tokens", None) if usage is not None else None
    completion_tokens = getattr(usage, "completion_tokens", None) if usage is not None else None
    if isinstance(prompt_tokens, int) and not isinstance(prompt_tokens, bool):
        event["input_tokens"] = prompt_tokens
    if isinstance(completion_tokens, int) and not isinstance(completion_tokens, bool):
        event["output_tokens"] = completion_tokens

    prompt_details = getattr(usage, "prompt_tokens_details", None) if usage is not None else None
    completion_details = getattr(usage, "completion_tokens_details", None) if usage is not None else None
    cache_read = _token_detail(prompt_details, "cached_tokens")
    if cache_read is not None:
        event["cache_read_input_tokens"] = cache_read
    cache_write = _token_detail(prompt_details, "cache_creation_tokens")
    if cache_write is not None:
        event["cache_write_input_tokens"] = cache_write
    reasoning = _token_detail(completion_details, "reasoning_tokens")
    if reasoning is not None:
        event["reasoning_output_tokens"] = reasoning

    model = getattr(response, "model", None)
    if isinstance(model, str) and model:
        event["model"] = model
    request_id = getattr(response, "id", None)
    if isinstance(request_id, str) and request_id:
        event["request_id"] = request_id
    try:
        finish_reason = response.choices[0].finish_reason
    except (AttributeError, IndexError, TypeError):
        finish_reason = None
    if isinstance(finish_reason, str) and finish_reason:
        event["finish_reason"] = finish_reason
    if elapsed >= 0:
        event["duration_secs"] = elapsed

    cost_evidence = _response_cost(response)
    if cost_evidence is not None:
        cost, source = cost_evidence
        event["costs"] = [{"amount": cost, "unit": "usd", "source": source}]
    print(json.dumps(event), flush=True)


def exec_tool(name: str, args: dict, workspace: str) -> str:
    try:
        if name == "read_file":
            path = args["path"]
            if not os.path.isabs(path):
                path = os.path.join(workspace, path)
            with open(path) as f:
                return f.read()
        elif name == "write_file":
            path = args["path"]
            if not os.path.isabs(path):
                path = os.path.join(workspace, path)
            with open(path, "w") as f:
                f.write(args["content"])
            return "OK"
        elif name == "bash":
            r = subprocess.run(
                args["command"],
                shell=True,
                capture_output=True,
                text=True,
                timeout=300,
                cwd=workspace,
            )
            out = ""
            if r.stdout:
                out += r.stdout[-4000:]
            if r.stderr:
                out += "\nSTDERR:\n" + r.stderr[-2000:]
            out += f"\nexit code: {r.returncode}"
            return out
        else:
            return f"ERROR: unknown tool '{name}'"
    except Exception as e:
        return f"ERROR: {e}"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--workspace", required=True)
    parser.add_argument("--model", required=True)
    parser.add_argument("--reasoning-effort", default=None)
    parser.add_argument("--max-iterations", type=int, default=0)
    args = parser.parse_args()

    prompt = sys.stdin.read()
    if not prompt:
        print(json.dumps({"type": "error", "message": "empty prompt on stdin"}), flush=True)
        sys.exit(1)

    messages = [{"role": "user", "content": prompt}]
    total_in = 0
    total_out = 0
    i = 0
    requests_made = 0
    failed = False

    while args.max_iterations == 0 or i < args.max_iterations:
        i += 1
        started = time.monotonic()
        requests_made += 1
        try:
            completion_options = dict(
                model=args.model,
                messages=messages,
                tools=TOOLS,
                max_tokens=16384,
                num_retries=0,
            )
            if args.reasoning_effort is not None:
                completion_options["reasoning_effort"] = args.reasoning_effort
            response = litellm.completion(**completion_options)
        except Exception as e:
            print(json.dumps({"type": "error", "message": str(e), "iteration": i}), flush=True)
            failed = True
            break

        _emit_request_usage(response, i, time.monotonic() - started)

        usage = getattr(response, "usage", None)
        prompt_tokens = getattr(usage, "prompt_tokens", None) if usage is not None else None
        completion_tokens = getattr(usage, "completion_tokens", None) if usage is not None else None
        if isinstance(prompt_tokens, int) and not isinstance(prompt_tokens, bool) and prompt_tokens >= 0:
            total_in += prompt_tokens
        if isinstance(completion_tokens, int) and not isinstance(completion_tokens, bool) and completion_tokens >= 0:
            total_out += completion_tokens

        msg = response.choices[0].message
        # Append assistant message to conversation
        messages.append(msg.model_dump())

        tool_calls = msg.tool_calls
        if not tool_calls:
            # Model is done
            if msg.content:
                print(json.dumps({"type": "response", "text": msg.content, "iteration": i}), flush=True)
            break

        # Execute tool calls
        for tc in tool_calls:
            fn_name = tc.function.name
            try:
                fn_args = json.loads(tc.function.arguments)
            except (json.JSONDecodeError, TypeError):
                fn_args = {}
                err_result = f"ERROR: malformed JSON in tool arguments: {tc.function.arguments[:200]}"
                print(
                    json.dumps({"type": "tool_result", "name": fn_name, "result": err_result, "iteration": i}),
                    flush=True,
                )
                messages.append({"role": "tool", "tool_call_id": tc.id, "content": err_result})
                continue
            print(json.dumps({"type": "tool_call", "name": fn_name, "args": fn_args, "iteration": i}), flush=True)
            result = exec_tool(fn_name, fn_args, args.workspace)
            print(
                json.dumps({"type": "tool_result", "name": fn_name, "result": result[:2000], "iteration": i}),
                flush=True,
            )
            messages.append(
                {
                    "role": "tool",
                    "tool_call_id": tc.id,
                    "content": result,
                }
            )

    print(
        json.dumps(
            {
                "type": "usage",
                "input_tokens": total_in,
                "output_tokens": total_out,
                "model_requests": requests_made,
            }
        ),
        flush=True,
    )
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
