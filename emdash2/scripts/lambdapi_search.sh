#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

if [[ $# -eq 0 ]]; then
  printf 'usage: %s QUERY\n' "$0" >&2
  printf "example: %s 'name = hom_int'\n" "$0" >&2
  printf "example: %s 'type >= Prof_imply_cov'\n" "$0" >&2
  exit 2
fi

query="$*"
: "${EMDASH_SEARCH_DB:=.cache/lambdapi-search.db}"

mkdir -p "$(dirname "$EMDASH_SEARCH_DB")"

if [[ ! -f "$EMDASH_SEARCH_DB" || emdash3_2.lp -nt "$EMDASH_SEARCH_DB" ]]; then
  printf 'refreshing Lambdapi search index: %s\n' "$EMDASH_SEARCH_DB" >&2
  lambdapi index -w --no-colors --db="$EMDASH_SEARCH_DB" emdash3_2.lp
fi

lambdapi search -w --no-colors \
  --db="$EMDASH_SEARCH_DB" \
  --require=emdash.emdash3_2 \
  "$query"
