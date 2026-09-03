#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
exec ./scripts/check_abelian_snake_six_term.sh "$@"
