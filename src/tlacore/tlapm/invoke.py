"""Run tlapm with a wall-clock timeout that kills the whole backend tree.

tlapm spawns backend solvers (z3, cvc4, zenon, isabelle, ...) as separate
processes. A naive timeout would kill only tlapm, orphaning the solvers — they
keep running, steal tens of GB of RAM, and the accumulated tax stalls every
later verification. We defend in two layers: ``start_new_session=True`` puts
tlapm in its own process group and ``killpg`` SIGKILLs every member; that covers
z3/cvc4/zenon. It does NOT catch Isabelle, whose ``bash_process`` wrapper
``setsid``'s into its own session — so we additionally snapshot tlapm's
PPid-chain descendants *before* killing and SIGKILL each one, leaves-first.
"""

from __future__ import annotations

import contextlib
import os
import signal
import subprocess


def _descendant_pids(root_pid: int) -> list[int]:
    """Snapshot every descendant of ``root_pid`` by walking /proc PPid chains.

    Returned leaves-first so the deepest survivors die before any parent can
    fork a replacement. Robust against descendants that escaped root_pid's
    process group/session — only the PPid chain matters, which holds as long as
    we snapshot before any kills land.
    """
    parents: dict[int, int] = {}
    for entry in os.listdir("/proc"):
        if not entry.isdigit():
            continue
        try:
            with open(f"/proc/{entry}/status") as f:
                for line in f:
                    if line.startswith("PPid:"):
                        parents[int(entry)] = int(line.split()[1])
                        break
        except (FileNotFoundError, PermissionError, ProcessLookupError):
            continue
    children: dict[int, list[int]] = {}
    for child, parent in parents.items():
        children.setdefault(parent, []).append(child)
    order, stack = [], list(children.get(root_pid, []))
    while stack:
        pid = stack.pop()
        order.append(pid)
        stack.extend(children.get(pid, []))
    return list(reversed(order))


def run_killgroup(cmd: list[str], timeout: float, cwd: str) -> tuple[str, str, int]:
    """Run ``cmd`` with a wall-clock ``timeout``; kill tlapm + all backends on
    timeout. Returns (stdout, stderr, returncode); re-raises
    ``subprocess.TimeoutExpired`` after cleanup.
    """
    proc = subprocess.Popen(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        cwd=cwd,
        start_new_session=True,
    )
    try:
        out, err = proc.communicate(timeout=timeout)
        return out, err, proc.returncode
    except subprocess.TimeoutExpired:
        escapees = _descendant_pids(proc.pid)
        with contextlib.suppress(ProcessLookupError, PermissionError):
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        for pid in escapees:
            with contextlib.suppress(ProcessLookupError, PermissionError):
                os.kill(pid, signal.SIGKILL)
        with contextlib.suppress(Exception):
            proc.communicate(timeout=10)
        raise
