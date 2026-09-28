# Action-Profile Main Integration Review

Date: 2026-09-27 (America/Toronto)

Status: review and book/artifact qualification complete; local fast-forward pending

Owner: [completed integration plan](EMDASH_ACTION_PROFILE_INTEGRATION_PLAN.md).
Qualified implementation: `8ea6c86bda894b32a33db13b52ba51b92fd701f5`.
Completed handoff: `ba7f77731b3325e2cf7b7519e6ec23680e86d836`.
Pre-integration main: `37ce19d5c727f8d1c5579445981a8f4f6d3f32d4`.

The user's post-completion request asks for a book review, an account of
regressions or compromises, and local fast-forward integration into main.
This follow-up preserves the earlier acceptance snapshot and its evidence.
It makes no mathematical, TypeScript, checker, resource-profile or dependency
change. Remote publication and the plugin merge are separate operations.

## Functionality And Computational Changes

No unresolved loss of the selected qualified main consumers was identified.
This is not a claim that every old interface or conversion is unchanged.
The initial objective explicitly removed generic strict composition and
naturality; source compatibility with those operations is intentionally broken.

| Boundary | Result and cost |
| --- | --- |
| Ambient versus classified computation | Ambient composition/naturality retain their lax cells. Stable classified views and qualified named constructors provide stricter computation. Normal identity computation remains. Raw evidence supplies paths and does not automatically rewrite its carrier. This is the planned semantic change. |
| Opaque classifiers and Gray arrows | Admission proofs are hidden; stable and raw views are distinct. `StrictFunctor_cat` retains ambient transfors, while `GrayHom_lax` has classified `LaxTransfor` arrows. Both interfaces and the shared higher tower are present. The former transparent package/projection behavior is deliberately retired. |
| Additional generic leaks discovered during integration | `API-04R/V/P/T` restrict pre/post accumulation, mixed vertical folds and higher telescope accumulation. Four interchange/Eckmann-Hilton proof interfaces require actual profiles. These repairs went beyond the initially identified rule list. They are real compatibility restrictions needed for the selected lax baseline, not missing implementations deferred to make CI pass. |
| Generic observation helpers | Selected-map, inverse-mate and other ordinary observations now take actual strictness or OneCat evidence. Existing ordinary callers forward their existing witness; generic callers cannot rely on the former unqualified equations. The whole K/Q/H constructions are not replaced by those ordinary observations. |
| Proof and computation mode | Some formerly reflexive observations use derived equality paths or narrowly scoped proof-time comparisons. Five of the 33 original Hom-introduction reviewer proofs use paths/congruence while preserving their statements. Runtime, proof-time and propositional equality must not be conflated. |
| Internal construction adaptations | The Gamma target comparison retains its post/pre cospan and inserts the chosen inverse of the ordinary observed pre-cell. Its public ordinary interface is preserved, but that internal term is not byte-identical. The nucleus adds a canonical Sigma base-change pre-cell component beta; this is supplied constructor-specific normality, not a derived whole-Sigma strictness theorem. Guarded projection/comparison rules are part of the reviewed implementation. |
| Pointwise-to-whole assembly | The user's accepted baseline preserves the inherited ordinary/displayed primitive, both selected inverse slots, component betas and assumed cancellation. The explicit-profile replacement is deferred as `API-05R`; the derived retained-member proof remains. This does not introduce a new blanket strictness assumption. |
| Operational cost | The registry contains 98 exact-target resource overrides, with some checks requiring 6–8 GiB and longer bounded deadlines. Full formal CI took 9,430.511 seconds. Some failures were reproduced on byte-identical original main closures, so these measurements do not establish that all resource cost was caused by the migration or quantify a comparative performance regression. Defaults remain 2 GiB/90s. |

The [owner inventory](EMDASH_ACTION_PROFILE_INTEGRATION_INVENTORY.md) accounts
for all 114 donor paths. All 81 LP paths have dispositions: 68 exact donor,
ten adapted and three retained from main. Every donor-added library symbol
has an owner. The omitted `strict_zero_comm_ring_psh` was an example-local
fixture; the original raw-presheaf consumer is retained through actual
CommRing OneCat evidence.

The [acceptance audit](EMDASH_ACTION_PROFILE_INTEGRATION_FINAL_AUDIT.md)
records six byte-identical primary main owners, preservation of original
K/Q/H and actual inverse/model data, arbitrary outer snake maps, all 1,388
formal targets and the original 94-assertion proof–CAS corpus. TypeScript's
134 audited semantic module records are unchanged; full TypeScript and
selected live conformance evidence keep their documented snapshots.

The inherited cubical limit remains native dimensions 0–2 and conditional
dimension 3, with the recorded readback/groupoidality boundary. Full Kan
structure, general Cartesian substitution and unrestricted higher readback
were not lost during integration. Op/duality and the other pre-existing
excluded research remain excluded. Passing these checks is not a proof of
global consistency, confluence, normalization or semantic adequacy.

The detailed internal adaptations are recorded in the
[Gamma/H review](EMDASH_ACTION_PROFILE_GAMMA_H_FEASIBILITY.md),
[native-snake review](EMDASH_ACTION_PROFILE_NATIVE_SNAKE_FEASIBILITY.md),
[vertical-fold review](EMDASH_ACTION_PROFILE_VERTICAL_FOLD_AUDIT.md),
[production continuation](EMDASH_ACTION_PROFILE_PRODUCTION_CONTINUATION.md)
and [resource qualification](EMDASH_ACTION_PROFILE_RESOURCE_QUALIFICATION.md).
Their early prototype states are historical; the acceptance audit owns the
completed production qualification.

## Book And Authority Review

The earlier integration updated the principal chapters and generated a
qualified local 416-page book, but did not update the tracked distribution
copies. This follow-up also found stale prose in appendices D–G and one
right-closure paragraph: global strict cuts, exposed strictness packages and
ambient Gray arrows were still described in those locations. Automated
evidence/link/render checks did not catch those semantic prose errors.

The corrections describe the implemented opaque classifiers, classified
Gray arrows, retained normal identities, profile-dependent computation,
constructor-specific recursor computation and inherited assembly assumption.
Two repeated standing-report passages are corrected too: the old Gray hom
description and the claim that the retained-member proof was still opaque.
The draft book metadata advances to `0.9.3-dev`, dated 2026-09-27.

Validation uses the repository-owned `book:release` sequence, which includes
source/evidence/typography/KaTeX checks, bounded browser validation and PDF
export/check. Selected changed pages receive visual review. The owning
promotion scripts then copy the checked book and already qualified overview
Markdown/PDF pairs into their tracked `docs/` paths. No generated Markdown
or PDF is hand-edited. No mathematical or TypeScript aggregate is repeated
for these documentation/artifact-only changes.

Fresh `book:release` passed with 187 evidence claims, 46 source files,
3,124 math spans, 416 rendered/PDF pages and 18 embedded fonts. Browser
validation reported no console, page, request or render errors. Visual
inspection of pages 1, 234, 365, 372–373, 377–378, 388–389, 392, 396 and 407
found the corrected prose, equations, code and tables legible and unclipped.
This is selected-page review, not a claim to have visually inspected all 416
pages in this follow-up.

`publication:promote` passed using the owning scripts and verified exact
source/destination identity. The overview remains the earlier qualified
19-page, 14-font artifact; its PDF check passed afresh. The resulting tracked
artifacts are:

| Artifact | SHA-256 |
| --- | --- |
| `docs/emdash-book.pdf` | `5873ca0eda082dbd54d79604c0a504c1612670faf8eade80d4adb9db0faba193` |
| `docs/emdash-book.md` | `a8c0beb91654a5d9a99943696a3d764f1c49fa39678b541000f4ee9837ca954d` |
| `docs/emdash3_2.pdf` | `2e779d2da03740b62af707739cf07721090f9241ca05d57636e2f5fe566ad9b6` |
| `docs/emdash3_2.md` | `c9b44fda0e2d8083d39e2926896ee45ecd54a2beaf26c7014acedeb4e38d5059` |

Logs: `emdash2/logs/api-main-book-release.log`,
`api-main-artifact-promotion.log` and `api-main-docs-check.log`.
The documentation gate initially caught the completed plan still registered
under Active Plans. Moving it to Completed Current-Architecture Ledgers
corrects that lifecycle inconsistency; the subsequent docs gate passes.
These corrections change no mathematical source or TypeScript semantic IR.

## Plugin Branch Compatibility

Plugin tip: `50ccee2f8d15e6a62f5db8748805e03ec485581f` on
`goal/algebra-goal-assistant-plugin-v3.2`.
It has five commits and 34 changed paths since shared main `37ce19d5`.
At the completed integration tip `ba7f7773`, the only changed-path overlap is
`README.md` and `docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md`.
`git merge-tree --write-tree` succeeds without conflicts, producing trial
tree `432e6bd75559518d61169b6a3d982f52ccd2d530` without changing either branch.

This supports a small textual integration effort. It does not qualify the
combined program: the plugin adds an MCP SDK dependency and lockfile changes,
goal CLI/MCP/workspace code, runtime packaging and tests, and refactors module
reuse. Its eventual merge should run frozen workspace setup, focused goal
and module-reuse tests, typecheck/lint, one complete TypeScript gate and
affected package/runtime checks. No Lambdapi source overlap was found.

## Local Integration Receipt

Book gates, visual review, promotion and documentation checks are complete.
The documentation/artifact checkpoint and fast-forward remain pending.
Main is a verified ancestor of the integration branch; both worktrees were
clean before this follow-up. All 67 worktrees had no tracked changes. A final
clean-state and ancestry check precedes `git merge --ff-only`.
