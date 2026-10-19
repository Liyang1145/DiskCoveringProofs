# Portable path roots for hark-archive shell scripts (source this file; bash).
# Same variables and defaults as hark-archive/_paths.py:
#   DCP_N26_ROOT  (default <hark-archive>/n26)   DCP_N11_ROOT (default <hark-archive>/n11)
#   DCP_MAIN_REPO (default $DCP_N26_ROOT/repo)   DCP_TMP      (default ${TMPDIR:-/tmp})
#   LEAN_TOOLCHAIN (default ${ELAN_HOME:-~/.elan}/toolchains/leanprover--lean4---v4.33.1,
#                   else `lean --print-prefix`)   LEAN (default $LEAN_TOOLCHAIN/bin/lean)
_DCP_HA="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
: "${DCP_N26_ROOT:=$_DCP_HA/n26}"
: "${DCP_N11_ROOT:=$_DCP_HA/n11}"
: "${DCP_MAIN_REPO:=$DCP_N26_ROOT/repo}"
: "${DCP_TMP:=${TMPDIR:-/tmp}}"
DCP_LEAN_VERSION=v4.33.1
if [ -z "${LEAN_TOOLCHAIN:-}" ]; then
  _dcp_c="${ELAN_HOME:-$HOME/.elan}/toolchains/leanprover--lean4---$DCP_LEAN_VERSION"
  if [ -d "$_dcp_c" ]; then LEAN_TOOLCHAIN="$_dcp_c"
  elif command -v "${LEAN:-lean}" >/dev/null 2>&1; then
    LEAN_TOOLCHAIN="$("${LEAN:-lean}" --print-prefix 2>/dev/null)"; : "${LEAN_TOOLCHAIN:=$_dcp_c}"
  else LEAN_TOOLCHAIN="$_dcp_c"; fi
fi
: "${LEAN:=$LEAN_TOOLCHAIN/bin/lean}"
export DCP_N26_ROOT DCP_N11_ROOT DCP_MAIN_REPO DCP_TMP LEAN_TOOLCHAIN LEAN
