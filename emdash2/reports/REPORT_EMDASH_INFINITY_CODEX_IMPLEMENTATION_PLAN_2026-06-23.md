# Infinity Codex: Controlled Final-Response Archiving

Date: 2026-06-23

Plan-ID: EMDASH-INFINITY-CODEX-2026-06-23
Depends-On: EMDASH-MATHOPS-DEVOPS-2026-06-16
Supersedes: none
Side-Task-Ledger: none
Infinity-Codex-Origin: pending
Infinity-Codex-Decision-Responses: pending

Status: implementation complete; local hook trust and first restarted-session
smoke test remain operator activation steps.

## Summary

Implement a repository-local Codex hook system that:

- Archives only the main agent’s completed final response, verbatim.
- Stores archives locally under ignored `tmp/ai-responses/`.
- Injects file pointers—not response contents—after session resume or compaction.
- Excludes user prompts, commentary, tool calls, subagents, and historical sessions.
- Remains independent of Codex Memories and plugins.

Create a dedicated Infinity Codex implementation report rather than expanding the existing MathOps/DevOps report.

## Implementation

- Add tracked `.codex/hooks.json` handlers:
  - `Stop`: pass `last_assistant_message`, session ID, and turn ID to the archiver.
  - `SessionStart` matching `resume|compact`: inject pointers to the session archive index, latest response, `reports/INDEX.md`, and the active-plan recovery SOP.
- Add `scripts/infinity_codex.py`, using only the Python standard library.
- Add `tmp/ai-responses/` to `.gitignore`; create files with private permissions and perform no network access.
- Use this local layout:

```text
tmp/ai-responses/
  INDEX.md
  sessions/
    2026-06-23_019ef43a0c30/
      session.json
      INDEX.md
      responses/
        0001_2026-06-23T11-40-10Z_<turn-id>.md
      metadata/
        <full-turn-id>.json
```

- Markdown response files contain exactly `last_assistant_message`, with no front matter or added newline.
- Sidecar metadata records full session/turn IDs, UTC capture time, model, SHA-256, byte count, and logical response ID:

```text
infinity-codex:<session-id>:<turn-id>
```

- Writes are atomic and idempotent by turn ID. Existing content is never overwritten; mismatches produce a visible hook warning and diagnostic record.
- Global session ordinals and automatic titles are omitted because they require unstable transcript parsing or unsafe concurrent counters.

## Interfaces and Report Management

Provide commands:

```text
infinity_codex.py list
infinity_codex.py latest-id
infinity_codex.py resolve <logical-id>
infinity_codex.py show <logical-id>
infinity_codex.py verify
infinity_codex.py reindex
infinity_codex.py prune --dry-run ...
infinity_codex.py annotate-plan --origin|--decision <logical-id> <report>
```

Standardize active plan headers with:

```text
Plan-ID:
Status:
Depends-On:
Supersedes:
Side-Task-Ledger:
Infinity-Codex-Origin:
Infinity-Codex-Decision-Responses:
```

- Existing plans use `pre-infinity-codex` where provenance cannot be established.
- New plans initially use `pending`; the next controlled turn explicitly attaches the captured logical ID.
- Only milestone decisions are linked. Raw archived responses remain historical evidence, never authoritative instructions.
- Side-task ledgers use stable IDs, dependencies, status, resume trigger, next action, and optional response evidence. `reports/INDEX.md` identifies the owning plan.
- Update `AGENTS.md`, `README.md`, the current SOP, report index, and existing MathOps plan with the authority order:

```text
active code/SOP → active plan and side-task ledger → linked decision responses → raw response archive
```

No changes are required in `emdash3_2.lp` or its checks.

## Validation and Rollout

- Unit-test exact Unicode preservation, absence of added newlines, null messages, duplicate turns, conflicting duplicates, resumed sessions, indexing, logical-ID resolution, permissions, and corrupt metadata.
- Test both hooks with synthetic stdin payloads in temporary directories.
- Add the Infinity Codex tests and hook/config validation to `make ci`.
- Run one live smoke-test turn after installation, trust the project hook through `/hooks`, then test resume or manual compaction and verify pointer injection.
- Document recovery and deletion procedures; pruning remains explicit and dry-run by default.

## Assumptions

- Codex CLI `0.142.0` is the current baseline; its `hooks` feature is stable and enabled.
- No historical import from `~/.codex/sessions` will be performed.
- The archive is local-only and therefore not protected against machine or directory loss.
- Codex Memories may inspire review and retention controls but will not generate, summarize, consolidate, or inject Infinity Codex data.
- A reusable plugin is deferred until the repo-local workflow is proven across real sessions.

Official references: [Codex Hooks](https://developers.openai.com/codex/hooks), [Codex Memories](https://developers.openai.com/codex/memories), and [Building Plugins](https://developers.openai.com/codex/plugins/build).

## Implementation Record

Implemented on 2026-06-23:

- `.codex/hooks.json` installs the turn-scoped `Stop` archiver and the
  `SessionStart` recovery-pointer hook for `resume|compact`.
- `scripts/infinity_codex.py` implements exact response capture, immutable
  metadata, idempotency/conflict diagnostics, generated indexes, logical-ID
  lookup, verification, reindexing, explicit pruning, and plan annotation.
- `.gitignore` keeps `tmp/ai-responses/` local.
- `tests/test_infinity_codex.py` covers exact Unicode bytes, no added newline,
  null messages, duplicate and conflicting turns, resumed sessions, logical
  IDs, pointer-only recovery, permissions, corruption, pruning, plan
  annotation, and hook shape.
- `AGENTS.md`, `README.md`, the current v3.2 SOP, the MathOps plan, and active
  plan metadata now document the workflow and authority order.
- `make infinity-codex-test` is the focused gate; `make ci` runs it.

Validation:

```text
make infinity-codex-test
12 tests passed

EMDASH_TYPECHECK_TIMEOUT=60s make ci
8 Lambdapi targets passed
Infinity Codex tests passed
active-reference lint passed
rewrite-LHS audit passed
strict check-catalog freshness passed
```

Activation after this change:

1. Restart Codex in this repository.
2. Open `/hooks`, inspect the project-local definitions, and trust them.
3. Complete one disposable turn and verify it with
   `python3 scripts/infinity_codex.py list` and `verify`.
4. Resume or compact the session and confirm that Codex receives pointers
   rather than archived response contents.

The current thread cannot perform that live lifecycle test because its hook
set was loaded before `.codex/hooks.json` existed.
