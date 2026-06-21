#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

ghost_args=()
png_file=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --ghost)
      ghost_args=(--ghost)
      shift
      ;;
    --png)
      if [[ $# -lt 2 ]]; then
        printf '%s: --png requires an output path\n' "$0" >&2
        exit 2
      fi
      png_file="$2"
      shift 2
      ;;
    --help|-h)
      printf 'usage: %s [--ghost] [--png OUTPUT.png] SYMBOL\n' "$0"
      exit 0
      ;;
    --)
      shift
      break
      ;;
    -*)
      printf '%s: unknown option: %s\n' "$0" "$1" >&2
      exit 2
      ;;
    *)
      break
      ;;
  esac
done

if [[ $# -ne 1 ]]; then
  printf 'usage: %s [--ghost] [--png OUTPUT.png] SYMBOL\n' "$0" >&2
  printf 'example: %s fapp1_func          # expands under emdash.emdash3_2\n' "$0" >&2
  printf 'example: %s --png /tmp/fapp1.png fapp1_func\n' "$0" >&2
  exit 2
fi

symbol="$1"
if [[ "$symbol" != *.* ]]; then
  symbol="emdash.emdash3_2.${symbol}"
fi

if [[ -n "$png_file" ]]; then
  if ! command -v dot >/dev/null 2>&1; then
    printf '%s: Graphviz dot is required for --png\n' "$0" >&2
    exit 2
  fi
  dot_file="$(mktemp)"
  trap 'rm -f "$dot_file"' EXIT
  mkdir -p "$(dirname "$png_file")"
  lambdapi decision-tree --no-warnings "${ghost_args[@]}" "$symbol" >"$dot_file"
  if [[ ! -s "$dot_file" ]]; then
    printf '%s: no decision tree was emitted for %s\n' "$0" "$symbol" >&2
    exit 1
  fi
  dot -Tpng "$dot_file" >"$png_file"
  printf 'wrote %s\n' "$png_file"
else
  lambdapi decision-tree --no-warnings "${ghost_args[@]}" "$symbol"
fi
