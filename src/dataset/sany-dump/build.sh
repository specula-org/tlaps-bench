#!/usr/bin/env bash
# Compile DumpSemantics.java against the vendored tla2tools.jar.
# Use: ./build.sh                  -> just compile
#      ./run.sh <input.tla>        -> compile (if needed) and run.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
TLA2TOOLS="$REPO_ROOT/lib/tla2tools.jar"
if [[ ! -f "$TLA2TOOLS" ]]; then
  echo "error: $TLA2TOOLS not found — run scripts/install_deps.sh first" >&2
  exit 1
fi
BUILD="$SCRIPT_DIR/build"
mkdir -p "$BUILD"
# Target Java 21 bytecode: the docker image ships a Java 21 JRE, so compiling
# with a newer JDK (e.g. 25) would emit class files the container can't load
# (UnsupportedClassVersionError). --release 21 pins the bytecode version.
if ! compiler_output="$(javac --release 21 -cp "$TLA2TOOLS" -d "$BUILD" "$SCRIPT_DIR/DumpSemantics.java" 2>&1)"; then
  echo "$compiler_output" >&2
  exit 1
fi
echo "built: $BUILD/DumpSemantics.class"
