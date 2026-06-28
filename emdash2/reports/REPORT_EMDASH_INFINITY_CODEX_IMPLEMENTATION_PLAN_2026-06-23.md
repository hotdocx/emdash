# Infinity Codex: Controlled Final-Response Archiving

Date: 2026-06-23

Plan-ID: EMDASH-INFINITY-CODEX-2026-06-23
Depends-On: EMDASH-MATHOPS-DEVOPS-2026-06-16
Supersedes: none
Side-Task-Ledger: none
Infinity-Codex-Origin: pre-infinity-codex
Infinity-Codex-Decision-Responses: none

Status: implementation complete with 2026-06-28 compaction-recovery hardening.
The initial live Stop-hook test exposed and corrected nested-project path
resolution: this Codex project is `emdash2`, while the enclosing Git root is
`emdash1`.

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

## Activation Correction: Nested Project Root

The first live Stop-hook invocation on 2026-06-23 failed because the original
command used:

```text
git rev-parse --show-toplevel
```

That resolves to the enclosing repository `/home/user1/emdash1`, not this
Codex project `/home/user1/emdash1/emdash2`, so it looked for the archiver in
the wrong `scripts/` directory.

Both hook commands now start from the Codex session working directory and walk
upward to the nearest ancestor containing `.codex/hooks.json`. This preserves
subdirectory launches while selecting the nested Codex project rather than
the enclosing Git root. The hook-configuration unit test rejects a regression
back to Git-root-only resolution.

Because changing a hook command changes its trust hash, review and trust the
updated definition through `/hooks` before repeating the live smoke test.

## Hardening Update: Compaction Fallback And Audit

Updated on 2026-06-28:

- `.codex/hooks.json` now registers `PostCompact` and `UserPromptSubmit` in
  addition to `Stop` and `SessionStart`.
- `PostCompact` records a private pending recovery marker. Since Codex does not
  add hook-specific context from `PostCompact`, the next `UserPromptSubmit`
  consumes that marker and injects the same pointer-only recovery context once.
- After the 2026-06-28 live auto-compaction smoke test, `PostCompact` also
  returns a `systemMessage` warning with the marker and archive index, because
  that is the only immediate UI/event-stream channel supported by Codex for
  this hook.
- `SessionStart source=compact` still injects pointers directly and clears any
  pending post-compaction fallback marker.
- Recovery context now distinguishes the latest archived final for the current
  session from the latest archived final globally, and lists pending
  post-compaction markers from other sessions so a resumed or forked session can
  find the final response from the compacted session that just ended.
- `tmp/ai-responses/events.jsonl` records hook event name, session id, turn id,
  source/trigger, status, and whether pointer context was emitted. It does not
  record prompts, final-response text, tool calls, or transcript contents.
- The pre-hardening first archive record with mismatched metadata was preserved
  under `tmp/ai-responses/quarantine/` and removed from the active generated
  indexes; `verify` now succeeds on the remaining active archive.
- `scripts/lint_report_headers.py` and `make ci` now enforce current-plan
  header fields, including non-pending Infinity Codex provenance values.
- `make infinity-codex-test` now covers 16 tests, including the post-compaction
  fallback path and prompt/response exclusion from the event audit.
