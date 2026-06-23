#!/usr/bin/env python3
"""Standalone LiteLLM agent script. Runs inside container or locally.

Reads prompt from stdin, calls model via litellm, writes proof to .tla file.
Outputs JSONL to stdout for the runner to capture.
"""

import argparse
import glob
import json
import os
import re
import subprocess
import sys

try:
    import litellm
except ImportError:
    print(json.dumps({"type": "error", "message": "litellm not installed"}))
    sys.exit(1)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--workspace", required=True)
    parser.add_argument("--model", required=True)
    parser.add_argument("--max-attempts", type=int, default=1)
    args = parser.parse_args()

    prompt = sys.stdin.read()
    if not prompt:
        print(json.dumps({"type": "error", "message": "empty prompt on stdin"}))
        sys.exit(1)

    tla_files = glob.glob(os.path.join(args.workspace, "*.tla"))
    if not tla_files:
        print(json.dumps({"type": "error", "message": "no .tla file in workspace"}))
        sys.exit(1)

    benchmark_file = tla_files[0]
    with open(benchmark_file) as f:
        benchmark_content = f.read()

    messages = [{"role": "user", "content": prompt}]
    total_in = 0
    total_out = 0

    for attempt in range(args.max_attempts):
        try:
            response = litellm.completion(
                model=args.model,
                messages=messages,
                temperature=0.0,
                max_tokens=16384,
            )
        except Exception as e:
            print(json.dumps({"type": "error", "message": str(e)}))
            sys.exit(1)

        usage = response.usage
        if usage:
            total_in += usage.prompt_tokens or 0
            total_out += usage.completion_tokens or 0

        text = response.choices[0].message.content or ""
        print(json.dumps({"type": "response", "text": text, "attempt": attempt + 1}))

        proof_content = extract_proof(text, benchmark_content)
        with open(benchmark_file, "w") as f:
            f.write(proof_content)

        if args.max_attempts == 1 or attempt == args.max_attempts - 1:
            break

        # Multi-turn: run tlapm and check result
        tlapm_bin = "/opt/tlapm/bin/tlapm"
        tlapm_lib = "/opt/tlapm/lib/tlapm/stdlib"
        check = subprocess.run(
            [tlapm_bin, "-I", tlapm_lib, os.path.basename(benchmark_file)],
            capture_output=True,
            text=True,
            timeout=300,
            cwd=args.workspace,
        )
        if check.returncode == 0:
            break

        error_msg = (check.stderr or check.stdout or "")[:3000]
        messages.append({"role": "assistant", "content": text})
        messages.append({
            "role": "user",
            "content": f"tlapm verification failed:\n{error_msg}\n\nFix the proof and return the complete file.",
        })

    print(json.dumps({"type": "usage", "input_tokens": total_in, "output_tokens": total_out}))


def extract_proof(response_text: str, original_content: str) -> str:
    """Extract the complete .tla file content from model response."""
    match = re.search(r"```(?:tla\+?|TLA\+?)?\s*\n(.+?)```", response_text, re.DOTALL)
    if match:
        extracted = match.group(1).strip()
        if "----" in extracted and "MODULE" in extracted:
            return extracted

    if "----" in response_text and "MODULE" in response_text:
        lines = response_text.split("\n")
        start = next((i for i, line in enumerate(lines) if "----" in line and "MODULE" in line), 0)
        end = len(lines)
        for i in range(len(lines) - 1, start, -1):
            if lines[i].startswith("===="):
                end = i + 1
                break
        return "\n".join(lines[start:end])

    return response_text


if __name__ == "__main__":
    main()
