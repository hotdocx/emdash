#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

if [[ ! -d logs ]]; then
  printf 'logs/ does not exist; nothing to prune\n'
  exit 0
fi

before="$(du -sh logs | awk '{print $1}')"

if [[ -n "${EMDASH_LOG_KEEP_DAYS:-}" ]]; then
  if [[ ! "$EMDASH_LOG_KEEP_DAYS" =~ ^[0-9]+$ ]]; then
    printf 'EMDASH_LOG_KEEP_DAYS must be a non-negative integer\n' >&2
    exit 2
  fi
  printf 'deleting .log files older than %s day(s)\n' "$EMDASH_LOG_KEEP_DAYS"
  find logs -type f -name '*.log' -mtime "+$EMDASH_LOG_KEEP_DAYS" -print -delete
else
  printf 'deleting all .log files under logs/\n'
  find logs -type f -name '*.log' -print -delete
fi

find logs -depth -type d -empty -delete
after="$(du -sh logs 2>/dev/null | awk '{print $1}' || printf '0')"
printf 'log usage: %s -> %s\n' "$before" "$after"
