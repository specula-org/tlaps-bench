"""LiteLLM agent with tool-calling loop. Runs inside container.

Tools: read_file, write_file, bash
Loops until model stops calling tools or max iterations hit.
"""

import argparse
import json
import os
import subprocess
import sys

# Use LiteLLM's bundled model-cost map instead of fetching it at runtime: the
# container firewall blocks the remote fetch, and a failed fetch both emits a
# warning the runner misreads as a transient infra failure and changes provider
# param handling. Must be set before importing litellm.
os.environ.setdefault("LITELLM_LOCAL_MODEL_COST_MAP", "True")

try:
    import litellm
except ImportError:
    print(json.dumps({"type": "error", "message": "litellm not installed"}))
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
        print(json.dumps({"type": "error", "message": "empty prompt on stdin"}))
        sys.exit(1)

    messages = [{"role": "user", "content": prompt}]
    total_in = 0
    total_out = 0
    i = 0
    failed = False

    while args.max_iterations == 0 or i < args.max_iterations:
        i += 1
        try:
            completion_options = dict(
                model=args.model,
                messages=messages,
                tools=TOOLS,
                max_tokens=16384,
            )
            if args.reasoning_effort is not None:
                completion_options["reasoning_effort"] = args.reasoning_effort
            response = litellm.completion(**completion_options)
        except Exception as e:
            print(json.dumps({"type": "error", "message": str(e), "iteration": i}))
            failed = True
            break

        usage = response.usage
        if usage:
            total_in += usage.prompt_tokens or 0
            total_out += usage.completion_tokens or 0

        msg = response.choices[0].message
        # Append assistant message to conversation
        messages.append(msg.model_dump())

        tool_calls = msg.tool_calls
        if not tool_calls:
            # Model is done
            if msg.content:
                print(json.dumps({"type": "response", "text": msg.content, "iteration": i}))
            break

        # Execute tool calls
        for tc in tool_calls:
            fn_name = tc.function.name
            try:
                fn_args = json.loads(tc.function.arguments)
            except (json.JSONDecodeError, TypeError):
                fn_args = {}
                err_result = f"ERROR: malformed JSON in tool arguments: {tc.function.arguments[:200]}"
                print(json.dumps({"type": "tool_result", "name": fn_name, "result": err_result, "iteration": i}))
                messages.append({"role": "tool", "tool_call_id": tc.id, "content": err_result})
                continue
            print(json.dumps({"type": "tool_call", "name": fn_name, "args": fn_args, "iteration": i}))
            result = exec_tool(fn_name, fn_args, args.workspace)
            print(json.dumps({"type": "tool_result", "name": fn_name, "result": result[:2000], "iteration": i}))
            messages.append(
                {
                    "role": "tool",
                    "tool_call_id": tc.id,
                    "content": result,
                }
            )

    print(json.dumps({"type": "usage", "input_tokens": total_in, "output_tokens": total_out}))
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
