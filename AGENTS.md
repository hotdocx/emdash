# Repository Guidelines

## Project Structure & Module Organization
- `src/`: TypeScript core (parser, elaboration, reduction, unification, proof utilities).
- `tests/`: Node `node:test` suites for the TS core. Test files follow `*_tests.ts` naming.
- `spec/`: Lambdapi specification snapshots (`emdash2.lp`, baseline specs).
- `docs/`: long-form markdown/PDF docs for theory and implementation notes.
- `emdash2/`: Lambdapi-focused workspace (`emdash2.lp`, `Makefile`, scripts, reports).
- `emdash2/print/`: React + Vite app for print/render artifacts.

## Build, Test, and Development Commands
- `npm test`: run the root TypeScript test suite (`tests/main_tests.ts`) via `ts-node` + `node:test`.
- `npm start`: alias of the root test command.
- `npx tsc --noEmit`: type-check the TS core without generating output.
- `cd emdash2 && make check`: run Lambdapi checks (default path for logic validation).
- `cd emdash2 && make watch`: poll for changes and log typecheck results to `logs/typecheck.log`.
- `cd emdash2 && npm run dev`: start the `print` dev server through workspace scripts.
- `cd emdash2 && npm run build`: build `emdash2` workspaces.

## Coding Style & Naming Conventions
- Language: TypeScript (core) and `.lp` (Lambdapi development).
- Match existing style in touched files; do not reformat unrelated code.
- Prefer descriptive, lower-case module filenames in `src/` (for example `unification.ts`, `reduction.ts`).
- Keep test filenames explicit and suffixed with `_tests.ts` (for example `parser_tests.ts`).
- Linting is configured in `eslint.config.mjs`; rules are intentionally permissive. Run `npx eslint .` when making broad TS changes.

## Testing Guidelines
- Add or update tests in `tests/` for any core behavior change.
- Ensure new test files are imported by `tests/main_tests.ts`.
- For Lambdapi changes, treat `cd emdash2 && make check` as required before submitting.
- For rendering changes, run `cd emdash2/print && npm run check:render`.

## Commit & Pull Request Guidelines
- Follow concise, imperative commit subjects; optional conventional prefix is acceptable (for example `chore: ...`).
- Keep commits focused by concern (TS core, Lambdapi logic, or print app).
- PRs should include:
  - What changed and why.
  - Affected paths (for example `src/`, `emdash2/`, `emdash2/print/`).
  - Verification commands run and results.
  - Screenshots/PDF evidence for `emdash2/print` visual changes.
