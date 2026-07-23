#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git -C "$(dirname "${BASH_SOURCE[0]}")/.." rev-parse --show-toplevel)"

"$repo_root/scripts/pnpmw" install --frozen-lockfile
"$repo_root/scripts/pnpmw" run workspace:check

store_path="$("$repo_root/scripts/pnpmw" store path)"
printf 'Worktree ready: %s\n' "$repo_root"
printf 'Shared pnpm store: %s\n' "$store_path"
