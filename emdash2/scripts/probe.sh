#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
if [[ $# -ne 1 ]]; then
  printf 'usage: %s path/to/probe.lp\n' "$0" >&2
  exit 2
fi
exec python3 scripts/run_lambdapi.py --quiet "$1"
