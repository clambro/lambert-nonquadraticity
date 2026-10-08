#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
case "${1:-}" in
  '') replay=false ;;
  --replay) replay=true ;;
  *) echo 'Usage: bash verification/check.sh [--replay]' >&2; exit 2 ;;
esac
if (( $# > 1 )); then
  echo 'Usage: bash verification/check.sh [--replay]' >&2
  exit 2
fi
if ! command -v lake >/dev/null 2>&1 && [[ -x "$HOME/.elan/bin/lake" ]]; then
  export PATH="$HOME/.elan/bin:$PATH"
fi
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-3}"
lake build
lake env lean verification/Audit.lean
if [[ "$replay" == true ]]; then
  lake env lean verification/KernelCheck.lean
fi
