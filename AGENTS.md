# Repository Guidelines

## Purpose
This document is the contributor guide for the root repository. Use it to choose the right workspace, run the correct validation commands, and follow the project’s expected review and submission workflow.

## Project Structure & Module Organization
- `src/`: TypeScript core kernel and elaboration pipeline (`parser.ts`, `elaboration.ts`, `reduction.ts`, `unification.ts`, `proof.ts`).
- `tests/`: TypeScript test suites using Node’s built-in `node:test` runner.
- `spec/`: Lambdapi specification snapshots and reference `.lp` files.
- `docs/`: long-form theory/implementation docs and generated PDFs.
- `emdash2/`: active Lambdapi workspace for the `m—`/emdash2 development.
- `emdash2/print/`: React + Vite renderer for paper output, diagrams, and PDF export checks.
- `emdash-template/`: template app scaffold; not the primary development target.

## Guidance Index (Cross-References You Should Read)
- `README.md`: top-level architecture and component overview for the full monorepo.
- `emdash2/AGENTS.md`: core Lambdapi SOP (development goals, fast commands, timeout/watch workflow) plus a long embedded Lambdapi usage reference/tutorial.  
  It explicitly includes copy-pasted sections from official/manual-style sources (for example syntax, commands, queries, and tutorial excerpts copied from local docs and `lambdapi-examples`).
- `emdash2/README.md`: concise quickstart for daily `emdash2` typechecking.
- `emdash2/print/AGENTS.md`: print pipeline SOP; how paper markdown is rendered and validated, plus Arrowgram authoring rules.
- `emdash2/scripts/check.sh`: timeout-aware wrapper used by `make check`.
- `emdash2/scripts/watch_typecheck.py`: polling watcher for continuous Lambdapi checks.
- `emdash2/print/scripts/validate_paper.mjs`: validates embedded Arrowgram/Vega-Lite JSON blocks in `print/public/index*.md`.
- `emdash2/print/scripts/check_console.mjs`: Playwright smoke test that fails on runtime/console/render errors.

Rule of thumb:
- Editing `src/` or `tests/`: read this file and `README.md`.
- Editing `emdash2/*.lp`: read `emdash2/AGENTS.md` first.
- Editing paper content or render behavior: read `emdash2/print/AGENTS.md` first.

## Build, Test, and Development Commands
Root TypeScript workspace:
- `npm test`: run all root TS tests via `tests/main_tests.ts`.
- `npm start`: alias for the root test command.
- `npx tsc --noEmit`: type-check the TS codebase only.
- `npx eslint .`: lint TS/JS files with repo ESLint config.

Lambdapi workspace (`emdash2/`):
- `cd emdash2 && make check`: standard full typecheck path.
- `cd emdash2 && EMDASH_TYPECHECK_TIMEOUT=60s make check`: recommended bounded run when debugging loops.
- `cd emdash2 && make watch`: continuous check loop; logs to `logs/typecheck.log`.
- `cd emdash2 && lambdapi check -w emdash2.lp`: check the omega-focused file directly.

Print workspace (`emdash2/print/` or workspace form from root):
- `cd emdash2 && npm run dev`: start print preview app.
- `cd emdash2 && npm run build`: build configured workspaces.
- `npm run validate:paper -w print`: validate embedded diagram/chart JSON.
- `npm run check:console -w print`: browser runtime smoke check.
- `npm run check:render -w print`: validate + build + console checks (preferred pre-PDF gate).

## Coding Style & Naming Conventions
- Languages in active use: TypeScript and Lambdapi (`.lp`).
- Preserve local style in touched files; avoid broad reformatting in unrelated areas.
- Use descriptive module filenames in lowercase snake style already used by the repo (example: `higher_order_unification_tests.ts`).
- Keep tests explicitly named with `_tests.ts` suffix where applicable.
- In Lambdapi files, follow established conventions from local docs: uppercase-leading names for types and lowercase-leading names for terms/functions where practical.
- Keep comments focused on non-obvious logic, especially around rewrite rules, unification behavior, and proof/elaboration edge cases.

## Testing Guidelines
- Any behavioral change in `src/` should include or update tests in `tests/`.
- Ensure new test files are imported by `tests/main_tests.ts`; otherwise they will not run in the default command.
- Before opening a PR that touches Lambdapi logic, run `cd emdash2 && make check`.
- Before opening a PR that touches `emdash2/print`, run `npm run check:render -w print`.
- When diagnosing long or unstable Lambdapi checks, prefer timeout-bounded runs and inspect `emdash2/logs/typecheck.log`.

## Commit & Pull Request Guidelines
Observed history includes mixed styles (`init`, topical summaries like `omega iteration, lax clarifications`, and occasional conventional commits such as `chore: add emdash2 to workspaces`). For new work, use a clearer baseline:
- Prefer short imperative subjects.
- Optional conventional prefixes are allowed (`feat:`, `fix:`, `chore:`, `docs:`).
- Keep each commit focused on one concern (TS core, Lambdapi logic, or print pipeline).

PR checklist:
- State what changed and why.
- List affected paths (example: `src/`, `tests/`, `emdash2/`, `emdash2/print/`).
- Include exact verification commands run.
- For print/layout changes, attach screenshots and/or exported PDF evidence.
- Note follow-up work explicitly if scope is intentionally partial.

## Configuration & Environment Notes
- Root uses npm workspaces; `emdash2` is a workspace and has its own nested workspace entries.
- Lambdapi must be installed and available on `PATH` (the repo docs note `lambdapi 3.0.0` as tested).
- `emdash2/print` depends on local/linked toolchain components; if dependency resolution fails, re-check workspace install commands and local package paths before debugging app code.
