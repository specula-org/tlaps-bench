#!/usr/bin/env bash
# Install host-side dependencies for tlaps-bench:
#   - tlapm 1.6 pre-release  -> ~/.tlapm
#   - Apalache 0.58.3        -> ~/.apalache
#   - tla2tools.jar (SANY)   -> <repo>/lib/tla2tools.jar
#
# Idempotent: skips downloads when the target is already present.
# Docker installs are handled inside docker/base.Dockerfile and are not touched here.

set -euo pipefail

# Detect the host platform. TLAPM has a separately locked release artifact for
# each supported platform; the JVM artifacts are platform-independent.
HOST_OS="$(uname -s)"
HOST_ARCH="$(uname -m)"
case "${HOST_OS} ${HOST_ARCH}" in
  "Linux x86_64") TLAPM_PLATFORM="linux-x86_64" ;;
  "Darwin arm64") TLAPM_PLATFORM="darwin-arm64" ;;
  *)
    echo "[install_deps] ERROR: unsupported platform '${HOST_OS} ${HOST_ARCH}'." >&2
    echo "[install_deps]        locked tlapm artifacts support Linux x86_64 and macOS arm64 only." >&2
    exit 1
    ;;
esac

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LIB_DIR="${REPO_ROOT}/lib"
TOOLCHAIN_LOCK="${REPO_ROOT}/config/verification-toolchain.json"
PYTHON_BIN="${REPO_ROOT}/.venv/bin/python"
if [[ ! -x "${PYTHON_BIN}" ]]; then
  PYTHON_BIN="python3"
fi

APALACHE_TAG="v0.58.3"
APALACHE_VERSION="${APALACHE_TAG#v}"
APALACHE_ASSET="apalache-${APALACHE_VERSION}.tgz"
APALACHE_URL="https://github.com/apalache-mc/apalache/releases/download/${APALACHE_TAG}/${APALACHE_ASSET}"

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

toolchain() {
  PYTHONPATH="${REPO_ROOT}/src" "${PYTHON_BIN}" -m common.verification_toolchain \
    --lock "${TOOLCHAIN_LOCK}" "$@"
}

toolchain_value() {
  toolchain value "$@"
}

TLAPM_TAG="$(toolchain_value tlapm tag --platform "${TLAPM_PLATFORM}")"
TLAPM_ASSET="$(toolchain_value tlapm asset --platform "${TLAPM_PLATFORM}")"
TLAPM_SHA256="$(toolchain_value tlapm sha256 --platform "${TLAPM_PLATFORM}")"
TLAPM_URL="$(toolchain_value tlapm url --platform "${TLAPM_PLATFORM}")"
TLATOOLS_TAG="$(toolchain_value sany tag)"
TLATOOLS_SHA256="$(toolchain_value sany sha256)"
TLATOOLS_URL="$(toolchain_value sany url)"

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
# Require both the locked artifact provenance and the capability the grader
# needs. A same-name upstream release replacement must never silently change a
# benchmark run.
# check_proof and validate run `tlapm --strict` (tlaplus/tlapm#278) on every
# obligation; a build predating it rejects the flag and exits non-zero, which
# grades every task FAIL.
tlapm_supports_strict() {
  # Capture, then match: a `| grep -q` pipeline can trip `pipefail` via SIGPIPE.
  local help_text
  help_text="$("$1" --help 2>&1)" || true
  [[ "${help_text}" == *"--strict"* ]]
}

TLAPM_MARKER="${HOME}/.tlapm/.tlaps-bench-toolchain.json"
existing_tlapm=""
if [[ -x "${HOME}/.tlapm/bin/tlapm" \
      && -f "${TLAPM_MARKER}" ]] \
      && toolchain verify-tlapm "${HOME}/.tlapm/bin/tlapm" "${TLAPM_MARKER}" \
        --platform "${TLAPM_PLATFORM}" >/dev/null 2>&1 \
      && tlapm_supports_strict "${HOME}/.tlapm/bin/tlapm"; then
  existing_tlapm="$("${HOME}/.tlapm/bin/tlapm" --version 2>/dev/null | sed -n '1p' || true)"
fi
if [[ -n "${existing_tlapm}" ]]; then
  echo "[install_deps] locked tlapm ${TLAPM_TAG} (${existing_tlapm}) already at ~/.tlapm — skipping"
else
  if [[ -x "${HOME}/.tlapm/bin/tlapm" ]]; then
    echo "[install_deps] the tlapm at ~/.tlapm does not match the locked artifact or"
    echo "[install_deps] grader capabilities — replacing it."
  fi
  echo "[install_deps] installing locked tlapm ${TLAPM_TAG} (${TLAPM_SHA256});"
  echo "[install_deps] the download is about 850 MB and may take several minutes."
  require_disk_space "${HOME}" $((2 * 1024 * 1024)) "The tlapm installation"
  require_disk_space "${TMPDIR:-/tmp}" $((3 * 1024 * 1024)) "Downloading and extracting tlapm"
  TLAPM_TMP="$(mktemp -d)"
  TMP_DIRS+=("${TLAPM_TMP}")
  download "${TLAPM_URL}" "${TLAPM_TMP}/${TLAPM_ASSET}" "tlapm ${TLAPM_TAG}"
  toolchain verify-artifact tlapm "${TLAPM_TMP}/${TLAPM_ASSET}" --platform "${TLAPM_PLATFORM}" \
    || die "downloaded tlapm artifact does not match config/verification-toolchain.json"
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
  if ! tlapm_supports_strict "${STAGED_TLAPM}/bin/tlapm"; then
    echo "[install_deps] ERROR: the downloaded tlapm ('${installed}') does not support" >&2
    echo "[install_deps]        --strict, which the grader requires (tlaplus/tlapm#278)." >&2
    echo "[install_deps]        The locked ${TLAPM_TAG} artifact is unusable." >&2
    echo "[install_deps]        Any existing ~/.tlapm installation was left unchanged." >&2
    exit 1
  fi

  rm -f "${STAGED_TLAPM}/bin/tlapm_lsp" 2>/dev/null || true
  toolchain write-tlapm-marker \
    "${STAGED_TLAPM}/bin/tlapm" "${STAGED_TLAPM}/.tlaps-bench-toolchain.json" \
    --platform "${TLAPM_PLATFORM}"
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
if [[ -f "${LIB_DIR}/tla2tools.jar" ]] \
      && toolchain verify-artifact sany "${LIB_DIR}/tla2tools.jar" >/dev/null 2>&1 \
      && valid_tla2tools "${LIB_DIR}/tla2tools.jar"; then
  printf '%s\n' "${TLATOOLS_TAG}" > "${TLATOOLS_MARKER}"
  echo "[install_deps] tla2tools.jar ${TLATOOLS_TAG} already at lib/ — skipping"
else
  TLATOOLS_TMP="$(mktemp -d)"
  TMP_DIRS+=("${TLATOOLS_TMP}")
  download "${TLATOOLS_URL}" "${TLATOOLS_TMP}/tla2tools.jar" "tla2tools.jar ${TLATOOLS_TAG}"
  toolchain verify-artifact sany "${TLATOOLS_TMP}/tla2tools.jar" \
    || die "downloaded tla2tools.jar does not match config/verification-toolchain.json"
  valid_tla2tools "${TLATOOLS_TMP}/tla2tools.jar" \
    || die "downloaded tla2tools.jar failed the SANY validation check; existing file was left unchanged"
  mv -f "${TLATOOLS_TMP}/tla2tools.jar" "${LIB_DIR}/tla2tools.jar"
  printf '%s\n' "${TLATOOLS_TAG}" > "${TLATOOLS_MARKER}"
fi

# --- Official proof libraries (.tla) ---
"${PYTHON_BIN}" "${REPO_ROOT}/scripts/install_proof_libraries.py" install --root "${LIB_DIR}"
"${PYTHON_BIN}" "${REPO_ROOT}/scripts/install_proof_libraries.py" check-upstream

echo "[install_deps] done."
echo
echo "Versions:"
# Never let the closing summary fail a run that already installed everything.
tlapm_version="$("${HOME}/.tlapm/bin/tlapm" --version 2>/dev/null | sed -n '1p' || true)"
echo "  tlapm:           ${TLAPM_TAG} (${tlapm_version:-version unavailable})"
echo "  Apalache:        ${APALACHE_VERSION}"
echo "  tla2tools/SANY:  ${TLATOOLS_TAG} (${TLATOOLS_SHA256})"
echo "  toolchain lock:  config/verification-toolchain.json"
echo "  proof libraries: config/proof-library-sources.json"
