<INSTRUCTIONS>
## Goal
This repo contains Lambdapi developments for “m— / emdash” functorial programming, focusing on strict/lax ω-categories, ω-functors, ω-transformations (transfors), and normalization via rewrite/unification rules.

## Fast commands
- Typecheck the current development: `make check`
- Watch+recheck on save: `make watch` (logs to `logs/typecheck.log`)
- Typecheck only omega version: `lambdapi check -w emdash2.lp`
- Typecheck only 1-category version: `lambdapi check -w emdash.lp`
- Remove compilation artefacts: `make clean`

## SOP: Continuous typecheck (watch mode)
Recommended workflow (2 terminals):
- Terminal A: `make watch`
- Terminal B: `tail -f logs/typecheck.log`

One-shot check (useful in scripts/CI):
- `python3 scripts/watch_typecheck.py --once`

Tuning / troubleshooting:
- Increase/decrease polling interval: `python3 scripts/watch_typecheck.py --interval 0.2`
- Disable screen clears: `python3 scripts/watch_typecheck.py --no-clear`

Background daemon-style (then tail the log):
- `nohup make watch >/dev/null 2>&1 &`

## Conventions
- Keep the repo in a state where `make check` succeeds.
- Prefer small, composable files/modules once the theory grows (split out kernel/infrastructure vs. examples).
- When adding rewrite/unif rules, also add a small “sanity” term (or query) exercising the rule.

## Debugging Lambdapi
- Print goals/contexts by adding `#check`/`#print` queries (see `docs/lambdapi_docs_queries.rst.txt`).
- Inspect rewrite compilation via decision trees: `lambdapi decision-tree <Module>.<symbol>`.

## Notes for Codex CLI iteration
- Keep `make watch` running and let the agent read `logs/typecheck.log` to see current typecheck failures while editing.
</INSTRUCTIONS>
