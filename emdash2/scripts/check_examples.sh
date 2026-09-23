#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

# checks.json owns suite membership and per-target routing.
exec python3 scripts/check_targets.py --suite reviewers "$@"
