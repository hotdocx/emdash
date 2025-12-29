Our goal is to write a Lambdapi specification for a programming language (and proof assistant) for ω-categories (strict/lax), ω-functors, ω-transformations (“transfors”), and related dependent-type structures (fibrations, comma/arrow categories).

The proof assistant is inspired by the functorial programming approach of Kosta Došen, using Lambdapi rewrite and unification rules for normalization.

The proof assistant is called `m—` (read “emdash”).

## Layout
- `emdash.lp`: earlier 1-category-oriented development (baseline).
- `emdash2.lp`: ω-category-oriented development (current focus).
- `lambdapi.pkg`: package config for Lambdapi.
- `docs/`: local copies of key Lambdapi documentation snippets (commands/syntax/queries/patterns).

## Quick start
Prereq: `lambdapi` on PATH (tested with `lambdapi 3.0.0`).

- Check everything: `make check`
- Check just ω version: `lambdapi check -w emdash2.lp`

## Notes
- Alternative/related approaches exist in `cartierSolution13.lp` and `cartierSolution16_short.lp` (see `Kosta_Dosen_omega_categories.pdf`).
