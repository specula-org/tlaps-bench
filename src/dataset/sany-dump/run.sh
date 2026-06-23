#!/usr/bin/env bash
# Compile if needed, then dump JSON for a single .tla file to stdout.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
TLA2TOOLS="$REPO_ROOT/lib/tla2tools.jar"
BUILD="$SCRIPT_DIR/build"
if [[ ! -f "$BUILD/DumpSemantics.class" \
      || "$SCRIPT_DIR/DumpSemantics.java" -nt "$BUILD/DumpSemantics.class" \
      || "$TLA2TOOLS" -nt "$BUILD/DumpSemantics.class" ]]; then
  bash "$SCRIPT_DIR/build.sh" >&2
fi
# TLAPS stdlib must be on the SANY search path so EXTENDS TLAPS resolves.
# The input file's own directory is also added so INSTANCE/EXTENDS of sibling
# modules (e.g. Paxos -> Consensus) resolves.
TLAPS_LIB="${TLAPS_LIB:-$HOME/.tlapm/lib/tlapm/stdlib}"
# Vendored CommunityModules (lib/community/) so EXTENDS SequencesExt / BagsExt /
# SequencesExtTheorems / ... resolves for the tlaplus/Examples imports.
COMMUNITY_LIB="${COMMUNITY_LIB:-$REPO_ROOT/lib/community}"
INPUT_DIR=""
for arg in "$@"; do
  if [[ -f "$arg" ]]; then INPUT_DIR="$(dirname "$(realpath "$arg")")"; break; fi
done
LIB_PATH="$TLAPS_LIB"
[[ -d "$COMMUNITY_LIB" ]] && LIB_PATH="$LIB_PATH:$COMMUNITY_LIB"
[[ -n "$INPUT_DIR" ]] && LIB_PATH="$INPUT_DIR:$LIB_PATH"
exec java -DTLA-Library="$LIB_PATH" \
  -cp "$TLA2TOOLS:$BUILD" DumpSemantics "$@"
