#!/usr/bin/env bash
# Install host-side dependencies for tlaps-bench:
#   - tlapm 1.6 pre-release  -> ~/.tlapm
#   - Apalache 0.57.0        -> ~/.apalache
#   - tla2tools.jar (SANY)   -> <repo>/lib/tla2tools.jar
#
# Idempotent: skips downloads when the target is already present.
# Docker installs are handled inside docker/base.Dockerfile and are not touched here.

set -euo pipefail

# Detect the host platform. tlapm ships a separate binary per platform; the
# other deps (Apalache, tla2tools, CommunityModules) are JVM/text artifacts and
# are platform-agnostic, so only the tlapm asset name is conditional below.
HOST_OS="$(uname -s)"
HOST_ARCH="$(uname -m)"

# Tool versions — bump deliberately, then re-run. TLAPM_TAG is a rolling
# pre-release whose asset follows upstream main; only the platform-specific
# asset name differs. The release publishes Linux x86_64 and macOS arm64
# binaries — there is no Intel (x86_64) macOS build. A usable ~/.tlapm is kept
# as-is (the download is 850 MB); delete it to pull the current build.
TLAPM_TAG="1.6.0-pre"
case "${HOST_OS} ${HOST_ARCH}" in
  "Linux x86_64") TLAPM_ASSET="tlapm-${TLAPM_TAG}-x86_64-linux-gnu.tar.gz" ;;
  "Darwin arm64") TLAPM_ASSET="tlapm-${TLAPM_TAG}-arm64-darwin.tar.gz" ;;
  *)
    echo "[install_deps] ERROR: unsupported platform '${HOST_OS} ${HOST_ARCH}'." >&2
    echo "[install_deps]        tlapm ${TLAPM_TAG} provides binaries for Linux x86_64 and macOS arm64 only." >&2
    exit 1
    ;;
esac
TLAPM_URL="https://github.com/tlaplus/tlapm/releases/download/${TLAPM_TAG}/${TLAPM_ASSET}"

APALACHE_TAG="v0.57.0"
APALACHE_VERSION="${APALACHE_TAG#v}"
APALACHE_ASSET="apalache-${APALACHE_VERSION}.tgz"
APALACHE_URL="https://github.com/apalache-mc/apalache/releases/download/${APALACHE_TAG}/${APALACHE_ASSET}"

TLATOOLS_TAG="v1.8.0"
TLATOOLS_URL="https://github.com/tlaplus/tlaplus/releases/download/${TLATOOLS_TAG}/tla2tools.jar"

COMMUNITY_TAG="202607181436"
COMMUNITY_URL="https://github.com/tlaplus/CommunityModules/archive/refs/tags/${COMMUNITY_TAG}.tar.gz"

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LIB_DIR="${REPO_ROOT}/lib"

TMP_DIRS=()
cleanup() {
  local path
  # macOS ships bash 3.2, where "${arr[@]}" on an empty array trips `set -u`
  # ("unbound variable"). On a rerun where every download is skipped TMP_DIRS
  # stays empty, so guard the expansion to keep the EXIT trap from failing.
  for path in ${TMP_DIRS[@]+"${TMP_DIRS[@]}"}; do
    rm -rf "${path}"
  done
}
trap cleanup EXIT

die() {
  echo "[install_deps] ERROR: $*" >&2
  exit 1
}

download() {
  local url="$1"
  local destination="$2"
  local description="$3"
  local progress=(--silent)
  if [[ -t 2 ]]; then
    progress=(--progress-bar)
  fi
  echo "[install_deps] downloading ${description}..."
  if ! curl --fail --location --show-error "${progress[@]}" \
    --output "${destination}" "${url}"; then
    die "failed to download ${description} from ${url}"
  fi
}

apalache_version() {
  "$1" version 2>/dev/null | sed -n '1p'
}

valid_tla2tools() {
  local output
  output="$(java -cp "$1" tla2sany.SANY -help 2>&1 || true)"
  [[ "${output}" == *"SANY - provides parsing"* ]]
}

require_disk_space() {
  local path="$1"
  local required_kb="$2"
  local description="$3"
  local available_kb
  available_kb="$(df -Pk "${path}" | awk 'NR == 2 { print $4 }')"
  if [[ "${available_kb}" =~ ^[0-9]+$ ]] && (( available_kb < required_kb )); then
    die "${description} requires at least $((required_kb / 1024 / 1024)) GB free at ${path}; only $((available_kb / 1024 / 1024)) GB is available"
  fi
}

# --- tlapm ---
# Gate on the capability the grader needs, not on the tag or a pinned commit.
# check_proof and validate run `tlapm --strict` (tlaplus/tlapm#278) on every
# obligation; a build predating it rejects the flag and exits non-zero, which
# grades every task FAIL. Since 1.6.0-pre is a *rolling* tag, "a tlapm is
# present" says nothing about whether it is usable — so probe --strict and
# re-install when it is missing. This refreshes a stale ~/.tlapm while still
# following upstream rebuilds of the tag.
tlapm_supports_strict() {
  # Capture, then match: a `| grep -q` pipeline can trip `pipefail` via SIGPIPE.
  local help_text
  help_text="$("$1" --help 2>&1)" || true
  [[ "${help_text}" == *"--strict"* ]]
}

existing_tlapm=""
if [[ -x "${HOME}/.tlapm/bin/tlapm" ]] && tlapm_supports_strict "${HOME}/.tlapm/bin/tlapm"; then
  existing_tlapm="$("${HOME}/.tlapm/bin/tlapm" --version 2>/dev/null | sed -n '1p' || true)"
fi
if [[ -n "${existing_tlapm}" ]]; then
  echo "[install_deps] tlapm ${existing_tlapm} already at ~/.tlapm — skipping"
  echo "[install_deps] (delete ~/.tlapm to pull the current ${TLAPM_TAG} build)"
else
  if [[ -x "${HOME}/.tlapm/bin/tlapm" ]]; then
    echo "[install_deps] the tlapm at ~/.tlapm does not support --strict, which the"
    echo "[install_deps] grader requires — replacing it with the current build."
  fi
  echo "[install_deps] installing latest tlapm ${TLAPM_TAG};"
  echo "[install_deps] the download is about 850 MB and may take several minutes."
  require_disk_space "${HOME}" $((2 * 1024 * 1024)) "The tlapm installation"
  require_disk_space "${TMPDIR:-/tmp}" $((3 * 1024 * 1024)) "Downloading and extracting tlapm"
  TLAPM_TMP="$(mktemp -d)"
  TMP_DIRS+=("${TLAPM_TMP}")
  download "${TLAPM_URL}" "${TLAPM_TMP}/${TLAPM_ASSET}" "tlapm ${TLAPM_TAG}"
  tar -xzf "${TLAPM_TMP}/${TLAPM_ASSET}" -C "${TLAPM_TMP}/"

  STAGED_TLAPM="${TLAPM_TMP}/tlapm"
  if [[ ! -x "${STAGED_TLAPM}/bin/tlapm" ]]; then
    echo "[install_deps] ERROR: downloaded archive does not contain an executable bin/tlapm." >&2
    exit 1
  fi
  # Capture stderr so a binary that fails to *run* (e.g. host glibc too old for
  # the prebuilt asset) is reported as an environment problem, not swallowed and
  # misattributed to a moved release asset.
  version_err="${TLAPM_TMP}/version.err"
  if version_out="$("${STAGED_TLAPM}/bin/tlapm" --version 2>"${version_err}")"; then
    version_ok=1
  else
    version_ok=0
  fi
  installed="$(printf '%s' "${version_out}" | sed -n '1p')"
  if [[ "${version_ok}" -ne 1 || -z "${installed}" ]]; then
    echo "[install_deps] ERROR: the downloaded tlapm binary failed to run." >&2
    echo "[install_deps]        The prebuilt asset needs a compatible host: Linux x86_64" >&2
    echo "[install_deps]        with glibc >= 2.38 (Ubuntu 24.04+, Debian 13+) or macOS arm64." >&2
    echo "[install_deps]        On older Linux, use the Docker workflow instead." >&2
    if [[ -s "${version_err}" ]]; then
      echo "[install_deps]        'tlapm --version' reported:" >&2
      sed 's/^/[install_deps]          /' "${version_err}" >&2
    fi
    echo "[install_deps]        Any existing ~/.tlapm installation was left unchanged." >&2
    exit 1
  fi
  # The rolling asset moves with upstream main, so it can in principle lose the
  # flag the grader is built on. Refuse the download rather than install a tlapm
  # that would fail every task.
  if ! tlapm_supports_strict "${STAGED_TLAPM}/bin/tlapm"; then
    echo "[install_deps] ERROR: the downloaded tlapm ('${installed}') does not support" >&2
    echo "[install_deps]        --strict, which the grader requires (tlaplus/tlapm#278)." >&2
    echo "[install_deps]        The rolling ${TLAPM_TAG} asset appears to have regressed." >&2
    echo "[install_deps]        Any existing ~/.tlapm installation was left unchanged." >&2
    exit 1
  fi

  rm -f "${STAGED_TLAPM}/bin/tlapm_lsp" 2>/dev/null || true
  rm -rf "${HOME}/.tlapm"
  mv "${STAGED_TLAPM}" "${HOME}/.tlapm"
fi

# --- Apalache ---
APALACHE_MARKER="${HOME}/.apalache/.tlaps-bench-version"
existing_apalache=""
if [[ -x "${HOME}/.apalache/bin/apalache-mc" ]]; then
  if [[ -f "${APALACHE_MARKER}" ]]; then
    existing_apalache="$(<"${APALACHE_MARKER}")"
  else
    existing_apalache="$(apalache_version "${HOME}/.apalache/bin/apalache-mc" || true)"
  fi
fi
if [[ "${existing_apalache}" == "${APALACHE_VERSION}" ]]; then
  printf '%s\n' "${APALACHE_VERSION}" > "${APALACHE_MARKER}"
  echo "[install_deps] Apalache ${APALACHE_VERSION} already at ~/.apalache — skipping"
else
  APALACHE_TMP="$(mktemp -d)"
  TMP_DIRS+=("${APALACHE_TMP}")
  download "${APALACHE_URL}" "${APALACHE_TMP}/${APALACHE_ASSET}" "Apalache ${APALACHE_TAG}"
  tar -xzf "${APALACHE_TMP}/${APALACHE_ASSET}" -C "${APALACHE_TMP}/"
  STAGED_APALACHE="${APALACHE_TMP}/apalache-${APALACHE_VERSION}"
  [[ -x "${STAGED_APALACHE}/bin/apalache-mc" ]] \
    || die "downloaded Apalache archive does not contain bin/apalache-mc"
  installed_apalache="$(apalache_version "${STAGED_APALACHE}/bin/apalache-mc" || true)"
  [[ "${installed_apalache}" == "${APALACHE_VERSION}" ]] \
    || die "downloaded Apalache version '${installed_apalache:-unknown}' != expected ${APALACHE_VERSION}; existing installation was left unchanged"
  printf '%s\n' "${APALACHE_VERSION}" > "${STAGED_APALACHE}/.tlaps-bench-version"
  rm -rf "${HOME}/.apalache"
  mv "${STAGED_APALACHE}" "${HOME}/.apalache"
fi

# --- tla2tools.jar (SANY) ---
mkdir -p "${LIB_DIR}"
TLATOOLS_MARKER="${LIB_DIR}/.tla2tools-version"
if [[ -f "${LIB_DIR}/tla2tools.jar" \
      && -f "${TLATOOLS_MARKER}" \
      && "$(<"${TLATOOLS_MARKER}")" == "${TLATOOLS_TAG}" ]] \
      && valid_tla2tools "${LIB_DIR}/tla2tools.jar"; then
  echo "[install_deps] tla2tools.jar ${TLATOOLS_TAG} already at lib/ — skipping"
else
  TLATOOLS_TMP="$(mktemp -d)"
  TMP_DIRS+=("${TLATOOLS_TMP}")
  download "${TLATOOLS_URL}" "${TLATOOLS_TMP}/tla2tools.jar" "tla2tools.jar ${TLATOOLS_TAG}"
  valid_tla2tools "${TLATOOLS_TMP}/tla2tools.jar" \
    || die "downloaded tla2tools.jar failed the SANY validation check; existing file was left unchanged"
  mv -f "${TLATOOLS_TMP}/tla2tools.jar" "${LIB_DIR}/tla2tools.jar"
  printf '%s\n' "${TLATOOLS_TAG}" > "${TLATOOLS_MARKER}"
fi

# --- CommunityModules (.tla) ---
COMMUNITY_MARKER="${LIB_DIR}/community/.tlaps-bench-version"
if [[ -f "${LIB_DIR}/community/SequencesExt.tla" \
      && -f "${LIB_DIR}/community/Graphs.tla" \
      && -f "${LIB_DIR}/community/GraphTheorems.tla" \
      && -f "${COMMUNITY_MARKER}" \
      && "$(<"${COMMUNITY_MARKER}")" == "${COMMUNITY_TAG}" ]]; then
  echo "[install_deps] CommunityModules ${COMMUNITY_TAG} already at lib/community/ — skipping"
else
  CM_TMP="$(mktemp -d)"
  TMP_DIRS+=("${CM_TMP}")
  download "${COMMUNITY_URL}" "${CM_TMP}/community.tar.gz" "CommunityModules ${COMMUNITY_TAG}"
  tar -xzf "${CM_TMP}/community.tar.gz" -C "${CM_TMP}/"
  STAGED_COMMUNITY="${CM_TMP}/community"
  mkdir -p "${STAGED_COMMUNITY}"
  cp "${CM_TMP}/CommunityModules-${COMMUNITY_TAG}/modules/"*.tla "${STAGED_COMMUNITY}/"
  [[ -f "${STAGED_COMMUNITY}/SequencesExt.tla" ]] \
    || die "downloaded CommunityModules archive is missing SequencesExt.tla"
  [[ -f "${STAGED_COMMUNITY}/Graphs.tla" ]] \
    || die "downloaded CommunityModules archive is missing Graphs.tla"
  [[ -f "${STAGED_COMMUNITY}/GraphTheorems.tla" ]] \
    || die "downloaded CommunityModules archive is missing GraphTheorems.tla"
  printf '%s\n' "${COMMUNITY_TAG}" > "${STAGED_COMMUNITY}/.tlaps-bench-version"
  rm -rf "${LIB_DIR}/community"
  mv "${STAGED_COMMUNITY}" "${LIB_DIR}/community"
fi

echo "[install_deps] done."
echo
echo "Versions:"
# Never let the closing summary fail a run that already installed everything.
tlapm_version="$("${HOME}/.tlapm/bin/tlapm" --version 2>/dev/null | sed -n '1p' || true)"
echo "  tlapm:           ${TLAPM_TAG} (${tlapm_version:-version unavailable})"
echo "  Apalache:        ${APALACHE_VERSION}"
echo "  tla2tools/SANY:  ${TLATOOLS_TAG}"
echo "  CommunityModules: ${COMMUNITY_TAG}"
