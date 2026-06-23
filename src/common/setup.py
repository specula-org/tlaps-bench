"""Shared setup utilities for ensuring host dependencies exist."""

import os
import subprocess
import sys

REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))


def ensure_build_deps() -> None:
    """Ensure check_proof_bin, SANY assets, and lib/ deps exist on the host.

    Needed by: `run` (grading), `check` (is the checker), `generate` (L2 SANY dump).
    """
    # Install tla2tools.jar + community modules if missing
    install_deps = os.path.join(REPO_ROOT, "scripts", "install_deps.sh")
    tla2tools = os.path.join(REPO_ROOT, "lib", "tla2tools.jar")
    if os.path.isfile(install_deps) and not os.path.isfile(tla2tools):
        print("[setup] Installing dependencies (tla2tools.jar, community modules)...")
        r = subprocess.run(["bash", install_deps], cwd=REPO_ROOT)
        if r.returncode != 0:
            print("ERROR: Failed to install deps. Run `bash scripts/install_deps.sh` manually.")
            sys.exit(1)

    # Build check_proof_bin if missing
    check_proof = os.path.join(REPO_ROOT, "check_proof_bin")
    if not os.path.isfile(check_proof):
        print("[setup] Compiling check_proof_bin...")
        r = subprocess.run(["make", "build"], cwd=REPO_ROOT)
        if r.returncode != 0:
            print("ERROR: Failed to compile check_proof_bin (need pyinstaller).")
            sys.exit(1)

    # Compile SANY DumpSemantics if missing
    sany_class = os.path.join(REPO_ROOT, "src", "dataset", "sany-dump", "build", "DumpSemantics.class")
    sany_build = os.path.join(REPO_ROOT, "src", "dataset", "sany-dump", "build.sh")
    if os.path.isfile(sany_build) and not os.path.isfile(sany_class):
        print("[setup] Compiling SANY DumpSemantics...")
        r = subprocess.run(["bash", sany_build], cwd=REPO_ROOT)
        if r.returncode != 0:
            print("ERROR: Failed to compile SANY (need javac + lib/tla2tools.jar).")
            sys.exit(1)
