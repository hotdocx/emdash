<INSTRUCTIONS>
## Goal
This repo contains Lambdapi developments for “m— / emdash” functorial programming, focusing on strict/lax ω-categories, ω-functors, ω-transformations (transfors), and normalization via rewrite/unification rules.

## Fast commands
- Typecheck the current development: `make check`
- Typecheck only omega version: `lambdapi check -w emdash2.lp`
- Typecheck only 1-category version: `lambdapi check -w emdash.lp`
- Remove compilation artefacts: `make clean`

## Conventions
- Keep the repo in a state where `make check` succeeds.
- Prefer small, composable files/modules once the theory grows (split out kernel/infrastructure vs. examples).
- When adding rewrite/unif rules, also add a small “sanity” term (or query) exercising the rule.

## Debugging Lambdapi
- Print goals/contexts by adding `#check`/`#print` queries (see `docs/lambdapi_docs_queries.rst.txt`).
- Inspect rewrite compilation via decision trees: `lambdapi decision-tree <Module>.<symbol>`.
</INSTRUCTIONS>
