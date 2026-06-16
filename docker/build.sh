#!/bin/bash
# Build the tlaps-bench image. Run from anywhere.
#
# The cheat checker (check_proof_bin) and the SANY assets are baked into the
# image, so the build context is the repo root. check_proof_bin is a compiled
# PyInstaller artifact (cheat-detection logic must never ship as source the
# agent could read); we rebuild it here when pyinstaller is available, else we
# require a prebuilt binary to already be present.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$REPO_ROOT"

if command -v pyinstaller >/dev/null 2>&1; then
  echo "[build] (re)compiling check_proof_bin via pyinstaller..."
  make build
elif [ ! -f check_proof_bin ]; then
  echo "[build] ERROR: check_proof_bin missing and pyinstaller not installed." >&2
  echo "[build]        Install pyinstaller (pip install pyinstaller) or provide a prebuilt binary." >&2
  exit 1
else
  echo "[build] pyinstaller not found — using existing check_proof_bin."
fi

# Precompile the SANY DumpSemantics driver on the host. The image ships a
# JRE only (no javac), so the .class files must already exist in the build
# context; the Dockerfile just COPYs them in.
if command -v javac >/dev/null 2>&1; then
  echo "[build] precompiling SANY DumpSemantics (host javac)..."
  bash src/dataset/sany-dump/build.sh
elif [ ! -f src/dataset/sany-dump/build/DumpSemantics.class ]; then
  echo "[build] ERROR: SANY DumpSemantics.class missing and javac not installed." >&2
  echo "[build]        Install a JDK (apt-get install default-jdk) or provide prebuilt classes." >&2
  exit 1
else
  echo "[build] javac not found — using existing DumpSemantics.class."
fi

echo "[build] docker build (context: repo root)..."
docker build -t tlaps-bench -f docker/Dockerfile "$REPO_ROOT"
echo "[build] done: tlaps-bench"
