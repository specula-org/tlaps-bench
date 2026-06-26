import sys

# (subcommand, one-line help) — order is the order shown in --help.
SUBCOMMANDS = [
    ("run", "Run an agent backend (codex / claude_code / copilot / litellm) on the benchmarks"),
    ("check", "Check a single benchmark proof for correctness and cheating"),
    ("validate", "Batch-validate source proofs with tlapm"),
    ("generate", "Generate benchmarks (--level level1|level2; default level1)"),
    ("score", "Score results (pass rate, per-module breakdown) from results.json"),
]

PROG = "tlaps-bench"


def _top_help() -> str:
    width = max(len(name) for name, _ in SUBCOMMANDS)
    lines = [
        f"usage: {PROG} <command> [args...]",
        "",
        "A benchmark for evaluating AI's ability to write TLAPS proofs.",
        "",
        "commands:",
    ]
    lines += [f"  {name.ljust(width)}  {desc}" for name, desc in SUBCOMMANDS]
    lines += [
        "",
        f"Run '{PROG} <command> --help' for a command's full flag set.",
    ]
    return "\n".join(lines)


def _dispatch(prog: str, module_name: str, attr: str, passthrough: list[str]) -> int:
    """Import ``module_name`` lazily, set argv, and call its entry function.

    Lazy import keeps one tool's import errors from breaking the others, and
    avoids paying for a tool's dependencies when running a different subcommand.
    """
    import importlib

    module = importlib.import_module(module_name)
    entry = getattr(module, attr)
    saved_argv = sys.argv
    sys.argv = [prog, *passthrough]
    try:
        rc = entry()
    finally:
        sys.argv = saved_argv
    return rc if isinstance(rc, int) else 0


def _extract_level(args: list[str]) -> tuple[str, list[str]]:

    level = "level1"
    rest: list[str] = []
    i = 0
    while i < len(args):
        a = args[i]
        if a == "--level":
            if i + 1 >= len(args):
                raise SystemExit(f"{PROG} generate: argument --level: expected one argument")
            level = args[i + 1]
            i += 2
            continue
        if a.startswith("--level="):
            level = a.split("=", 1)[1]
            i += 1
            continue
        rest.append(a)
        i += 1
    norm = {"1": "level1", "level1": "level1", "2": "level2", "level2": "level2"}
    if level not in norm:
        raise SystemExit(f"{PROG} generate: argument --level: invalid choice: {level!r} (choose level1 or level2)")
    return norm[level], rest


def main(argv: list[str] | None = None) -> int:
    argv = list(sys.argv[1:]) if argv is None else list(argv)

    if not argv or argv[0] in ("-h", "--help"):
        print(_top_help())
        return 0

    sub = argv[0]
    rest = argv[1:]
    names = {name for name, _ in SUBCOMMANDS}
    if sub not in names:
        sys.stderr.write(f"{PROG}: unknown command {sub!r}\n\n{_top_help()}\n")
        return 2

    if sub == "run":
        return _dispatch(f"{PROG} run", "evaluator.runner", "main", rest)
    if sub == "check":
        return _dispatch(f"{PROG} check", "common.check_proof", "main", rest)
    if sub == "validate":
        return _dispatch(f"{PROG} validate", "common.validate", "main", rest)
    if sub == "generate":
        # --help before --level: show which levels exist plus the level1 flags
        # (the default) — the level-specific flags then come from that module.
        level, gen_args = _extract_level(rest)
        module = "dataset.level1.generate" if level == "level1" else "dataset.level2.generate"
        return _dispatch(f"{PROG} generate --level {level}", module, "main", gen_args)
    if sub == "score":
        return _dispatch(f"{PROG} score", "evaluator.score", "main", rest)

    return 2  # unreachable


if __name__ == "__main__":
    sys.exit(main())
