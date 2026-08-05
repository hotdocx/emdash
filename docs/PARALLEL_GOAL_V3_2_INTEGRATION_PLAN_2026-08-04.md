# Parallel v3.2 Goal Integration Plan

Date: 2026-08-04
Status: active; final qualification complete; commit, integration archive, and
local-main fast-forward pending
Branch: `integration/v3.2-parallel-goals`
Worktree: `/home/user1/emdash1-integration-v3.2`

## Objective

Integrate the completed TypeScript-elaborator development and the completed
presheaves/sites/schemes development into one locally validated history, then
fast-forward local `main` so future work can continue from a single branch and
worktree. Preserve both histories, combined behavior, mathematical and
cross-layer contracts, generated evidence, and useful ignored development
artifacts.

This document is the implementation, decision, validation, and recovery ledger
for the persistent integration goal. Update it whenever observed repository
state changes a decision, a check changes status, or a plan row advances.

The accepted pre-mutation design is frozen at:

`/home/user1/emdash1/backups/PARALLEL_GOAL_V3_2_INTEGRATION_PLAN_2026-08-04.md`

That ignored baseline is 492 lines with SHA-256
`e8ed8aa6c4abd65a39d069e66c2fba030f3f97e3883394f93943f1246b2b76ac`.
The original accepted response is archived at:

`/home/user1/emdash1/emdash2/tmp/ai-responses/sessions/2026-08-04_019fce9e1b28/responses/0001_2026-08-04T21-38-49Z_019fcea6-e457-7bb0-9adc-f1fd1e6aff86.md`

Active code and SOP outrank this plan; this plan outranks archived response
evidence.

## Authorization Boundary

The user accepted the integration proposal and explicitly authorized its
implementation and a persistent `/goal`. This goal may:

- create and bootstrap this dedicated local branch/worktree;
- perform an initially uncommitted non-fast-forward merge of the two completed
  tips;
- resolve textual and semantic conflicts and update owned tests/reports;
- regenerate evidence and requalify exact cross-layer contracts;
- create one validated local merge commit; and
- fast-forward local `main` to that merge commit.

The goal must not push, publish, release, create a PR, rebase, amend, squash,
reset away checkpoints, force-delete anything, delete branches, remove
worktrees, or perform destructive cleanup. Artifact preservation is allowed;
removal of source artifacts/worktrees is not.

## Immutable Inputs And Topology

| Role | Ref | Commit |
| --- | --- | --- |
| Common baseline/current initial `main` | `main` | `cea2605ca4fe6a3023b46c26c5997956cc4e9f03` |
| First/direct parent: completed elaborator | `goal/typescript-elaborator-v3.2` | `e7352ba2493825453d08292fd162121121590dda` |
| Second/direct parent: completed PSSS | `goal/presheaves-sites-schemes-v3.2` | `1281efeb4da70b011e7b51846909dba638fa2d84` |

The common baseline is the exact merge base. The completed tips contain 165
and 101 commits from it. They must remain immutable.

This integration branch was created directly at the elaborator tip. Merge the
PSSS tip with:

```bash
git -c merge.conflictStyle=zdiff3 merge \
  --no-ff --no-commit \
  1281efeb4da70b011e7b51846909dba638fa2d84
```

Keep `HEAD` at the elaborator tip and `MERGE_HEAD` at the PSSS tip until the
fully reviewed merge commit is created. Do not introduce a preliminary plan
commit, because the final integration commit must have the two completed tips
as direct parents.

## Preflight Findings

- All seven original worktrees were clean in staged, unstaged, and ordinary
  untracked state immediately before this branch was created.
- Local `main` and its local `origin/main` tracking ref were both `cea2605c`;
  no remote fetch was performed or implied.
- The elaborator changes 126 paths and PSSS changes 154 paths from main.
- Only 11 paths overlap; 115 and 143 changed paths are unique to each line.
- Read-only merge analysis predicts five textual conflicts.
- No patch-equivalent commits, duplicate newly declared Lambdapi symbols, or
  duplicate newly introduced catalog area names were found.
- Both branch-range `git diff --check` invocations passed.
- No tracked-new path collides with known ignored/untracked source artifacts.
- The fresh worktree bootstrap passed with Node 24.11.1 and pnpm 11.16.0.

## Conflict Resolution Matrix

| File | Integration rule | State |
| --- | --- | --- |
| `docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md` | Combine both histories; retain the elaborator completion boundary; record inherited adjunction/record work and PSSS as completed, not isolated active work. | resolved and staged |
| `emdash2/emdash3_2.lp` | Retain generic identity owner, narrow `Op_cat` runtime bridge, and rule-free `fapp1_id_path`; reconcile ordering/comments. | resolved and staged; combined kernel check passed |
| `emdash2/reports/INDEX.md` | Manually union current orientations and completion state; route to this plan; remove stale active-continuation claims. | resolved and staged |
| `emdash2/reports/REPORT_EMDASH_CHECK_CATALOG.md` | Provisional conflict resolution only, then regenerate with owner. Expected diagnostic scale: about 2,090 checks, 98 areas, zero unclassified. | resolved by owner regeneration and staged: 2,091 checks, 98 areas, zero legacy tags, zero unclassified |
| `emdash2/reports/REPORT_EMDASH_HEALTH.md` | Provisional conflict resolution only, then regenerate from fresh combined source. | resolved by owner regeneration and staged: 162/162 current targets exit zero |

Explicitly review the automatically merged overlap paths:

- `emdash2/emdash3_2_checks.lp`;
- `emdash2/reports/EMDASH_FOUNDATIONS.md`;
- `emdash2/reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`;
- `emdash2/reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`;
- `src/v3_2/index.ts`; and
- `tests/main_tests.ts`.

Also review merged `AGENTS.md` guidance: the PSSS branch expands the authority
map and timeout policy, while elaborator-specific owner/graduation conclusions
must remain discoverable.

### Automatic overlap audit result

- `emdash3_2_checks.lp` is the exact assertion-level union plus the one new
  integration identity assertion: PSSS `2,036` + elaborator `1,779` - common
  baseline `1,725` + integration `1` = combined `2,091`. The corresponding
  line arithmetic is exact after the seven-line integration block:
  `22,849 + 20,964 - 19,425 + 7 = 24,395`.
- `src/v3_2/index.ts` is an exact additive line-level union:
  `180 + 175 - 173 = 182`; both LF macro exports and all elaborator
  categorical transfer exports are present.
- `tests/main_tests.ts` is an exact additive line-level union:
  `239 + 221 - 219 = 241`; both LF macro tests and all elaborator categorical
  tests are registered.
- The canonical-syntax report is an exact structural union before its
  integration review-date refresh: `714 + 1,295 - 693 = 1,316` lines.
- Foundations is the structural union plus the deliberate three-line net
  identity-boundary reconciliation; the elaborator fixed-head action and
  constant-middle sections and every PSSS section are retained.
- The living SOP retains both branches' substantive sections, qualifies
  tranche-local warning counts as historical, and replaces the stale
  `exact-current` health paragraph with the combined 2026-08-04 evidence.
- Root and nested `AGENTS.md` match the PSSS tip exactly; its expanded active
  authority map and 90-second policy therefore survive unchanged.
- No conflict marker remains, and `git diff --check` passes.

## Semantic Integration Decision: Identity Action

The elaborator intentionally added and retained the narrow opposite-source
runtime bridge:

```lambdapi
rule @fapp1_fapp0
      (Op_cat $K) $D $F $x $x (@id $K $x)
  ↪ @id $D (@fapp0 (Op_cat $K) $D $F $x);
```

PSSS independently added rule-free theorem `fapp1_id_path` and comments saying
the comparison adds no second runtime computation and does not change the
generic whole-arrow normal form. Combined, the narrow bridge already selects
an opposite-source identity runtime path, so those claims need qualification.

Selected resolution:

1. keep the generic `fapp1` identity computation;
2. keep the narrow bridge at its reviewed generic-owner position;
3. keep `fapp1_id_path` as theorem/equality evidence;
4. add no competing broad or constructor-specific functoriality rule;
5. update kernel/presheaf comments, SOP, Foundations, decision ledgers, and
   checks to distinguish the theorem from the pre-existing narrow runtime
   bridge; and
6. preserve intended carrier-level restriction opacity/non-collapse.

Focused evidence must include positive theorem and bridge consumers, relevant
reduction-order interaction, and the existing negative
`comm_ring_psh_restrict ... ≡ s` carrier-opacity assertion.

Files to relocate and audit with `rg` after the merge:

- `emdash2/emdash3_2.lp`;
- `emdash2/emdash3_2_checks.lp`;
- `emdash2/emdash3_2_commutative_algebra_presheaves.lp`;
- current SOP and Foundations;
- the PSSS decision/closure reports; and
- the elaborator handoff.

## Cross-Layer Contract Requalification

The elaborator's Lambdapi acquisition/conformance layer contains exact
whole-source digests, declaration ordinals/counts, and export-shape contracts.
PSSS changes the active sources, and the elaborator handoff already records
some stale aggregate source pins at its final retirement boundary.

Preflight found older digest `sha256:4d847...` in or consumed by:

- `src/v3_2/scale_stress_1_acquisition.ts`;
- `src/v3_2/scale_stress_2_acquisition.ts`;
- `src/v3_2/scale_stress_3_acquisition.ts`;
- `tests/v3_2_lf_transfer_runtime_tests.ts`; and
- `tests/v3_2_lf_transfer_tests.ts`.

At least one test hashes all of `emdash2/emdash3_2.lp`. Requalification must:

- locate every digest, ordinal, declaration-count, export hash, and source
  identity assertion;
- run its owning acquisition/conformance route;
- inspect the combined observed export before changing expected values;
- preserve drift-detecting negative coverage rather than weakening it; and
- record every old/new value, rationale, command, and result below.

Do not use the final aggregate as the discovery loop. Make focused acquisition,
LF-transfer, runtime, scale-stress, and conformance checks green first.

### Contract transition ledger

| Owner/test | Old contract | Combined contract | Evidence | State |
| --- | --- | --- | --- | --- |
| Active core source/export identity | Source `4d847383...`; export `91f0deb7...` | Source `0a117742...`; export `b16839b4...` | Live export inventory plus independent 13-contract acquisition verifier | pass |
| Active core export vocabulary | 1,472 commands: `symbol=764`, `rule=621`, `unif_rule=61`; shape `definitions=479`, `assumptions=285`, `runtimeClauses=657` | 1,531 commands: `symbol=781`, `rule=652`, `unif_rule=72`; shape `definitions=488`, `assumptions=293`, `runtimeClauses=688`; all other kind/shape counts unchanged | `check:scale-inventory`, 14/14 | pass |
| Backend-neutral transfer module specifications | Historical active-source pins `4d847383...`, `bdb04532...`, or `ef3e77cc...`; active export pins `91f0deb7...` or `bdb04532...` | All 69 exported module specifications targeting `emdash3_2.lp` pin source `0a117742...`; all 19 carrying a canonical-export contract pin `b16839b4...` | Runtime enumeration and absence search for every retired hash; transfer/compiler/runtime suite 36/36 | pass |
| SCALE-1 acquisition | Core source/export identities stale; seven selected command ordinals/texts unchanged | Current core source/export identities; exact seven command texts and ordinals preserved. Nat source/export and its three commands are byte-identical | `check:scale-inventory` and 13-contract verifier | pass |
| SCALE-2 acquisition and derivative ledgers | Exact command texts with pre-PSSS source ordinals | Same exact command texts at requalified ordinals listed below | proof and telescope stress suites, 20/20 | pass |
| SCALE-3 acquisition and derivative ledgers | Exact command texts with pre-PSSS source ordinals | Same exact command texts at requalified ordinals listed below | profunctor stress suite 14/14 | pass |
| Displayed-ND higher acquisition | Core source/export stale; 17 affected ordinals stale | Current source/export and 17 requalified ordinals listed below; all 18 selected command texts unchanged | live higher probe 7/7 | pass |
| Protected hom-action module | Source `d6e5e9ca...`; export `a1d73d0...`; 77 definitions; closure ordinals `1...58` | Source `e5ff82d4...`; export `000dd93e...`; 78 definitions; selected 58-command closure `1...56,58,59` | module-scale suite 8/8; exact dependency-closure verifier | pass |
| Other active exported authorities | Nat, equality-evidence, and walking-end source/export contracts | Byte-identical (`2fc30099...`, `83075b38...`, and `6b7f...` exports respectively) | Live five-module inventory | pass |

Full SHA-256 transitions:

- core source:
  `4d8473837cbdd031ad4af4e9f41e9330243fff4929db4860919a81228804de82`
  to
  `0a117742d326bad82fe72cc73c624a0c174e3b48dd4047ebd8f6ed6ff7837860`;
- core canonical export:
  `91f0deb710b93acc55aa3a6f947505de973b9deaa94d68e1a213037dfcc9c3d3`
  to
  `b16839b44dfec845fdc007884f82fea63156a273759fba4e9a8842c0c0312ccb`;
- protected hom-action source:
  `d6e5e9cade4d756a413a813d35a54024e1d6e9388215803ca267e242b70624d3`
  to
  `e5ff82d49d26d60fa20f28cc3eea5915c70a0379768076912f617d4ae5da5356`;
  and
- protected hom-action canonical export:
  `a1d73d0aac76ca1c5b57c6dd1e9407b3f3eb431839d88484f278fc0ac109c0e2`
  to
  `000dd93e025ebb9e6efe2621fa74257a2ffe547107f353f590c31088aa9b0be0`.

Every selected command digest/text remained byte-identical. The exact changed
ordinal transitions are:

- SCALE-2A uncurrying: `389->391`, `393->395`, `977->988`,
  `997->1008`, `1008->1019`, `1013->1026`;
- SCALE-2B1 internal Pi: `394->396`, `538->540`, `928->935`,
  `929->938`, `932->941`, `933->942`, `938->947`, `941->950`,
  `943->952`, `985->996`, `986->997`, `988->999`, `989->1000`,
  `990->1001`, `991->1002`, `992->1003`; ordinals `236` and `238`
  are unchanged;
- SCALE-2B2 Pi base action: `512->514`, `927->934`, `1098->1134`,
  `1099->1135`, `1119->1158`, `1218->1261`, `1226->1270`,
  `1227->1271`;
- SCALE-2B3 Sigma transfor: `401->403`, `402->404`, `1028->1043`,
  `1029->1044`, `1031->1046`, `1080->1108`, `1082->1110`,
  `1092->1122`;
- SCALE-3A1 boundary: `578->580`, `1229->1273`, `1233->1277`,
  `1263->1322`, `1293->1352`;
- SCALE-3A2A comparison: `406->408`, `407->409`, `547->549`,
  `579->581`, `580->582`, `1235->1279`, `1264->1323`,
  `1265->1324`; ordinals `230` and `232` are unchanged;
- SCALE-3A2B tensor: `662->668`, `664->670`, `681->687`,
  `1295->1354`, `1296->1355`, `1297->1356`, `1298->1357`;
  ordinals `59`, `61`, `184`, and `185` are unchanged; and
- displayed-ND higher: `398->400`, `505->507`, `540->542`,
  `648->651`, `951->960`, `958->969`, `1036->1053`, `1049->1076`,
  `1050->1077`, `1051->1078`, `1053->1080`, `1054->1081`,
  `1073->1101`, `1074->1102`, `1075->1103`, `1076->1104`, and
  `1077->1105`; ordinal `232` is unchanged.

These are requalification edits, not semantic relaxations: exact source and
export identities, command kinds, names, source order, command bytes,
dependency closure, policy coverage, positive behavior, and negative near
misses all remain enforced.

## Validation Strategy

Use bounded, dependency-ordered gates. The effective nested SOP in the merged
tree controls the timeout; expected integration timeout is 90 seconds.

### Kernel semantic inner loop

```bash
EMDASH_TYPECHECK_TIMEOUT=90s make -C emdash2 check
EMDASH_TYPECHECK_TIMEOUT=90s make -C emdash2 warning-summary
make -C emdash2 audit-rules
```

Run focused owner-position probes/checks before these broad targets when a
semantic source edit is needed. Record warning counts and explain relevant
differences; do not treat totals as automatic approval or rejection.

### Generated evidence and examples

```bash
make -C emdash2 catalog
make -C emdash2 toc
EMDASH_TYPECHECK_TIMEOUT=90s make -C emdash2 examples
EMDASH_TYPECHECK_TIMEOUT=90s make -C emdash2 health
EMDASH_TYPECHECK_TIMEOUT=90s make -C emdash2 ci
```

Regenerate catalog and health through their owners. Never hand-edit their final
combined values.

### Root cross-layer qualification

```bash
./scripts/pnpmw run check:browser-reviewer
# affected focused acquisition/conformance commands identified after merge
./scripts/pnpmw run check:all
git diff --check
```

Run root workspace/typecheck/lint/tests or `check:ts` as required while fixing
shared TypeScript behavior. Run the costly repository aggregate once after all
bounded known failures are green.

### Validation evidence ledger

| Gate | Result | Evidence / observed counts |
| --- | --- | --- |
| Fresh worktree bootstrap | pass | Node 24.11.1; pnpm 11.16.0; workspace contract passed |
| Elaborator-parent kernel baseline | pass | `EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check` at `e7352ba...` |
| Focused identity/presheaf checks | pass (covered by stronger gate) | Combined central diagnostics and presheaf owners passed within full `make check`; positive whole-arrow identity, theorem-path, and carrier-opacity assertions all checked. |
| Kernel check | pass | `EMDASH_TYPECHECK_TIMEOUT=90s make -C emdash2 check` completed successfully on the uncommitted combined tree, including every active source target. |
| Warning summary | pass / reviewed diagnostic | Combined: 1,241 = 1,082 unjoinable critical-pair + 159 replaceable-pattern warnings, all structurally classified. Same-command parent measurements: elaborator 1,245 = 1,086 + 159; PSSS 1,175 = 1,016 + 159. The merge is -4 critical pairs from the elaborator parent and +66 from the PSSS parent, with pattern advisories unchanged; this is consistent with preserving the elaborator runtime package alongside the PSSS kernel changes and is not a confluence claim. |
| Strict rule audit | pass | `make -C emdash2 audit-rules`: 0 reconstructible compound slots across 0 unreviewed clauses; 58 annotated slots across 34 intentional clauses. |
| Catalog | pass | Owner regeneration: 2,091 checks across 98 areas; zero legacy tags and zero unclassified checks. |
| TOC | pass | Owner check: 86 headings; sections 0 through 20 sequential. |
| Examples | pass | The first contended sweep hit exit 124 without a source diagnostic; isolated affine-basis then passed in 49.21s. The contention-free full owner rerun subsequently passed all 93 examples. |
| Health | pass | Fresh non-resumed owner regeneration: all 162 source/reviewer targets exit zero; source snapshot `4cd8c818...`, checked-content snapshot `728c7d812...`; slowest target central diagnostics at 66.584s under the 90s ceiling. |
| Kernel CI | pass | Final aggregate `make -C emdash2 ci` passed: fresh health regeneration checked 162/162 files in 1,640.820s; 42 Python tests and 5 document-registry tests passed; TOC, active-reference, report-header, book evidence/typography/KaTeX/assembly/source, strict rule-audit, and strict catalog checks all passed. |
| Affected TypeScript acquisition/conformance | pass | Transfer/compiler/runtime 36/36; inventory/acquisition 14/14; mixed phase 15/15; proof stress 5/5; telescope stress 15/15; profunctor stress 14/14; module stress 8/8; proposal 7/7; live higher audit 7/7. Independent exact verification passed all 13 acquisition contracts. |
| Browser reviewer | pass | Root typecheck/lint and standalone reviewer typecheck/Vite production build passed. Fresh fixture `npm ci` used its retained lock; lock SHA-256 stayed `27488ae4...`. Existing Vite large-chunk advisory and npm audit report (1 moderate/3 high) were not auto-fixed. |
| Root `check:ts` if shared TS changes | pass | Workspace/typecheck/lint passed. The first untruncated 31.2-minute run executed 1,424 tests/216 suites and exposed exactly two integration contracts after 1,369 passes/53 skips: stale `83/15` method counts and a README line-wrap policy. Both were corrected, focused suites passed 9/9, and the clean aggregate advanced through `check:ts` via its `&&` chain, confirming the full corrected rerun passed (1,371 pass, 53 skip). |
| Repository `check:all` | pass | One final `timeout --signal=INT 7200s ./scripts/pnpmw run check:all` completed with exit 0 on the fully staged combined code tree. It passed workspace, TypeScript, conformance, and complete Lambdapi CI; the final CI tail independently records 162/162 fresh health files, 42 Python tests, 5 registry tests, and all audit/catalog/book gates green. This ledger-only status synchronization followed and received its proportional document/diff checks. |
| `git diff --check` and exact staged diff | pass | Pre-final-ledger prospective-tree snapshot `24899a29037dc68ca84744c254ac24bc00c2baec`: 190 staged paths (130 additions, 60 modifications); zero unmerged entries, unstaged paths, ordinary untracked paths, ignored/forbidden staged artifacts, or newly added conflict markers. Cached diff check passed; both goal refs still equal the exact named tips; root and nested `AGENTS.md` exactly match the PSSS parent. The only later change was this plan's evidence synchronization, followed by the same index/document checks. |

## Artifact Preservation Lane

Ignored files cannot be Git-merged. Preserve useful evidence independently and
never overlay goal worktrees into `main`.

Preflight estimates:

- elaborator: about 306 MB logs, 9.6 MB probes, 1.5 MB browser snapshots, plus
  selected rendered evidence;
- PSSS: about 994 MB logs, 8.5 MB probes, and 6.4 MB temporary/rendered PDFs.

Known colliding relative paths with differing bytes:

- `emdash2/logs/check-metrics.jsonl`;
- `emdash2/logs/warnings/latest.log`.

Create provenance-labelled per-worktree archives and SHA-256 manifests. Include
useful logs, probes, warnings, browser snapshots, and optionally rendered
evidence. Exclude `node_modules`, pnpm stores/caches, compiled Lambdapi output,
generic `dist`/build products, `__pycache__`, and bytecode. Archive this
integration worktree's new evidence too. Verify manifests, but do not remove
any original artifact or worktree under this goal.

### Artifact ledger

| Source | Commit | Archive/manifest | Verification | State |
| --- | --- | --- | --- | --- |
| Elaborator worktree | `e7352ba...` | `backups/parallel-v3.2-artifacts-2026-08-04/typescript-elaborator-v3.2_e7352ba..._artifacts.tar.gz`; adjacent provenance and SHA-256 manifests | 15,489,319 bytes; 378 entries; `gzip -t`, full TOC read, SHA-256 `c5299dcc...` | pass |
| PSSS worktree | `1281efe...` | `backups/parallel-v3.2-artifacts-2026-08-04/presheaves-sites-schemes-v3.2_1281efe..._artifacts.tar.gz`; adjacent provenance and SHA-256 manifests | 46,645,412 bytes; 1,276 entries; `gzip -t`, full TOC read, SHA-256 `e02b3436...` | pass |
| Integration worktree | final merge | — | — | pending |

Additional reachability facts to preserve:

- adjunction `dd8a82e...` and record structure `ba4fe3c...` are ancestors of
  the PSSS tip;
- detached `3f9ee5f...` is already an ancestor of initial main;
- detached `fc98d670...` is a separate unmerged kernel experiment and must be
  left in place (or preserved by a separately authorized future tag/bundle).

## Decision Ledger

| ID | Decision | State/evidence |
| --- | --- | --- |
| INT-001 | Preserve both completed tips as direct merge parents. | accepted |
| INT-002 | Use this elaborator-based dedicated integration worktree. | implemented: worktree bootstrapped at `e7352ba...` |
| INT-003 | Keep merge uncommitted through resolution/qualification. | implemented: `HEAD=e7352ba...`, `MERGE_HEAD=1281efe...`; full qualification completed before commit |
| INT-004 | Keep narrow `Op_cat` bridge plus theorem; correct combined claims/tests. | implemented in kernel/checks/presheaf owner/SOP/Foundations/PSSS ledger; full kernel check passed |
| INT-005 | Regenerate catalog and health with owners. | implemented: catalog and fresh 162-target health report generated, reviewed, and staged |
| INT-006 | Requalify exact TypeScript contracts through owners. | implemented: exact identities, inventories, ordinals, derivative ledgers, and live probes green |
| INT-007 | Focused gates first, one final repository aggregate. | implemented: focused kernel and TypeScript gates green; one clean final `check:all` exited 0 |
| INT-008 | Fast-forward local main only after green merge commit. | accepted; pending |
| INT-009 | Preserve ignored evidence by provenance and manifests. | accepted; pending |
| INT-010 | No push, publication, rewrite, cleanup, deletion, or worktree removal. | active constraint |

## Progress Ledger

| Phase | State | Evidence / next action |
| --- | --- | --- |
| 0. Freeze and bind plan | complete | Ignored baseline frozen; worktree bootstrapped; living plan installed; `/goal` active; parent kernel baseline passed. |
| 1. Establish uncommitted merge | complete | Merge opened with exact parents; five predicted conflicts were the complete actual inventory; all authored conflicts were resolved and both generated conflicts were regenerated through their owners. |
| 2. Kernel semantic integration | complete | Bridge/theorem/check/owner-doc reconciliation implemented; full kernel check green; warning delta measured against both parents; strict rule audit clean. |
| 3. Reports and overlap review | complete | Handoff/index resolved; catalog, TOC, and fresh health green; all automatic overlap paths audited quantitatively; living SOP synchronized to combined evidence. |
| 4. TypeScript contract requalification | complete | All active core/eq1 hashes, inventories, exact acquisitions, derivative ordinal ledgers, and module-spec evidence requalified; all focused owners and live probes green. |
| 5. Final qualification | complete | Kernel/examples/health/browser/focused TS green; two full-TS integration contracts corrected and focused 9/9; one clean final `check:all` exited 0; exact staged review passed in phase 6. |
| 6. Commit and fast-forward local main | ready | Exact staged review passed; local `main` is clean at `cea2605...`; create the authorized direct-parent merge commit, then recheck and fast-forward local `main` only. |
| 7. Preserve ignored evidence | in progress | Elaborator and PSSS archives/manifests verified; integration archive waits for the exact merge-commit identity; all sources remain intact. |

## Final Commit And Main Advancement

Before committing, inspect status, unstaged diff, staged diff, both-parent merge
diff, generated ownership, and `git diff --cached --check`. Ensure no ignored
logs, probes, dependency trees, caches, or assembled output are staged.

The final merge commit's direct parents must be exactly `e7352ba...` and
`1281efe...`. Recheck `/home/user1/emdash1` is clean and still at its expected
baseline, then run only:

```bash
git -C /home/user1/emdash1 merge \
  --ff-only integration/v3.2-parallel-goals
```

Verify both tips are ancestors of main and both worktree trees match. Do not
push and do not remove the integration worktree.

## Completion Definition

The persistent goal is complete only when every scoped row is implemented,
rejected with durable evidence, or explicitly deferred behind a concrete
user-approved prerequisite; all affected authorities and final gates are
synchronized; a reviewed local merge commit directly joins both tips; local
main is fast-forwarded to it; useful ignored evidence has verified per-source
provenance manifests/archives; original worktrees remain intact; and no
excluded external or destructive operation occurred.
