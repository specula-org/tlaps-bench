#!/usr/bin/env bash
# Install host-side dependencies for tlaps-bench:
#   - tlapm 1.6 pre-release  -> ~/.tlapm
#   - Apalache 0.57.0        -> ~/.apalache
#   - tla2tools.jar (SANY)   -> <repo>/lib/tla2tools.jar
#
# Idempotent: skips downloads when the target is already present.
# Docker installs are handled inside docker/Dockerfile and are not touched here.

set -euo pipefail

# Pinned versions — bump deliberately, then re-run.
# 1.6.0-pre is a *rolling* tag (the asset is rebuilt in place), so the tag alone
# is not reproducible — pin by the expected `tlapm --version` commit and
# re-download on mismatch. 80172c6 is the first rolling build carrying `--strict`
# (tlaplus/tlapm#278); bump TLAPM_COMMIT deliberately when upgrading.
TLAPM_TAG="1.6.0-pre"
TLAPM_COMMIT="80172c6"
TLAPM_ASSET="tlapm-${TLAPM_TAG}-x86_64-linux-gnu.tar.gz"
TLAPM_URL="https://github.com/tlaplus/tlapm/releases/download/${TLAPM_TAG}/${TLAPM_ASSET}"

APALACHE_TAG="v0.57.0"
APALACHE_VERSION="${APALACHE_TAG#v}"
APALACHE_ASSET="apalache-${APALACHE_VERSION}.tgz"
APALACHE_URL="https://github.com/apalache-mc/apalache/releases/download/${APALACHE_TAG}/${APALACHE_ASSET}"

TLATOOLS_TAG="v1.8.0"
TLATOOLS_URL="https://github.com/tlaplus/tlaplus/releases/download/${TLATOOLS_TAG}/tla2tools.jar"

COMMUNITY_TAG="202604221529"
COMMUNITY_URL="https://github.com/tlaplus/CommunityModules/archive/refs/tags/${COMMUNITY_TAG}.tar.gz"

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LIB_DIR="${REPO_ROOT}/lib"

TMP_DIRS=()
cleanup() {
  local path
  for path in "${TMP_DIRS[@]}"; do
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
# Pin by commit, not mere presence: the rolling tag means an existing ~/.tlapm
# may be an older build (e.g. one without --strict), so re-install on mismatch.
if [[ -x "${HOME}/.tlapm/bin/tlapm" ]] \
   && "${HOME}/.tlapm/bin/tlapm" --version 2>/dev/null | grep -q "${TLAPM_COMMIT}"; then
  echo "[install_deps] tlapm ${TLAPM_COMMIT} already at ~/.tlapm — skipping"
else
  echo "[install_deps] installing tlapm ${TLAPM_TAG} (${TLAPM_COMMIT});"
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
  installed="$("${STAGED_TLAPM}/bin/tlapm" --version 2>/dev/null | sed -n '1p' || true)"
  if [[ "${installed}" != *"${TLAPM_COMMIT}"* ]]; then
    echo "[install_deps] ERROR: downloaded tlapm version '${installed:-unknown}'" >&2
    echo "[install_deps]        does not contain expected commit ${TLAPM_COMMIT}." >&2
    echo "[install_deps]        The rolling ${TLAPM_TAG} asset has moved. Run 'git pull'" >&2
    echo "[install_deps]        and retry; if this persists, TLAPM_COMMIT and the" >&2
    echo "[install_deps]        Dockerfile pin must be updated together." >&2
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
  printf '%s\n' "${COMMUNITY_TAG}" > "${STAGED_COMMUNITY}/.tlaps-bench-version"
  rm -rf "${LIB_DIR}/community"
  mv "${STAGED_COMMUNITY}" "${LIB_DIR}/community"
fi

echo "[install_deps] done."
echo
echo "Versions:"
echo "  tlapm:           ${TLAPM_TAG} (${TLAPM_COMMIT})"
echo "  Apalache:        ${APALACHE_VERSION}"
echo "  tla2tools/SANY:  ${TLATOOLS_TAG}"
echo "  CommunityModules: ${COMMUNITY_TAG}"
