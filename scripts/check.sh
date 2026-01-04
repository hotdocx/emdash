#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

# lambdapi check -w emdash.lp
lambdapi check -w emdash2.lp
