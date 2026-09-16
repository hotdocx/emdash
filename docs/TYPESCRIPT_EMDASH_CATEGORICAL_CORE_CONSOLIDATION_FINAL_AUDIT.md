# Categorical Core And Homology Consolidation: Final Audit

Date: 2026-09-16
Status: scoped implementation qualified; explicit follow-ups retained
Plan-ID: TS-EMDASH-CATEGORICAL-CORE-CONSOLIDATION

The [living plan](TYPESCRIPT_EMDASH_CATEGORICAL_CORE_CONSOLIDATION_REVIEW.md)
is complete under the user's selected scope. The
[execution ledger](TYPESCRIPT_EMDASH_CATEGORICAL_CORE_CONSOLIDATION_LEDGER.md)
retains decisions, rejected probes, warning comparisons and resource receipts.
This audit extends the preceding
[native-universality audit](TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_FINAL_AUDIT.md);
it does not reopen its completed proof obligations.

Implementation branch: `goal/categorical-core-consolidation-v3.2`.
Baseline: `df9b4778584121c3ad6ef7575093bd6d84be89e8`.
Final semantic checkpoint: `5a9abf912181b085f83f33a7623179621cd8ad45`.
Book/document checkpoint: `1cca1d876702f5f9b72c4faf20d5852e82aff04f`.
The final audit checkpoint adds documentation only.

## Qualified Outcome

The primary interface remains whole J⊣K and Q⊣I, whole H and direct δ,
canonical categorical exactness, and the native snake with its native
LES/sign comparison. The nonsplit proof–CAS LES and snake still compute and
retain their selected objects, arrows, inverses and exactness certificates
under the original explicit contracts. Output exactness is derived.

Consolidation has separated shared inputs and ordinary record observations
from former selection algorithms, retired unused implementations and facades,
placed reusable categorical interfaces at their own owners, and shortened the
standing documentation. The new whole Γ/H comparison is a meaningful
architectural refinement, explicitly deferred by the user after the consumer
audit. No failed Γ test is being represented as a regression or as a theorem.

| Tranche | Qualified result | Checkpoint |
| --- | --- | --- |
| CC-0 | Initial main fast-forward, push and verified existing Pages deployment; isolated continuation worktree. | `df9b4778` |
| CC-1a | Four unchanged raw presentation chain declarations extracted from Freyd homology. | `3778c1c9` |
| CC-1b | Generic chain-pair data and native boundary observations separated from optional records. | `d35cc98e` |
| CC-2a/b | Unused retained-column comparisons and superseded snake-derived connecting route retired. | `5829e76c`, `af24ef60` |
| CC-2c | Shared TypeScript raw/window signatures separated; old model facades retired; complete native workflows qualified. | `739c045d`, `38e2e7c0` |
| CC-2d | Ordinary H records and raw annihilator test data separated from selected algorithms. | `8a73f84c` |
| CC-3 | Whole categorical contractions and guarded ordinary terminal/initial adjunction presentations. | `5c575800` |
| CC-4 | Actual comparison consumers audited; two unused leaves retired; two displayed-identity projection guards corrected. Γ retained by explicit user choice. | `07e3f5d6`, `5a9abf91` |
| CC-5 | Current owner map/history split, READMEs and email draft, book 0.9.1-dev and deterministic generated artifacts. | `1cca1d87` |
| CC-6 | Final source/API/trust inventory, dependency audit, final-kernel 94-assertion replay and documentation checks. | This audit |

## Source Ownership And Retirement

The baseline-to-final inventory covers 143 changed root LP owners. Across
that inventory, all surviving common symbol declarations retain their bodies
and types modulo comments/whitespace. Moved declarations have a single current
owner. There are 21 new symbols: 19 definitions and two structural declarations.
The rule changes are separately identified below.

The aggregate retirement removes 118 root LP files, 365 obsolete formal
symbols and 46 reviewer files. This includes the old snake-derived connecting
closure, legacy homology model wrappers and unused comparison leaves. The
ledger records the bounded inventories, dependent consumers, TypeScript
facades/exports and check registrations removed in each tranche. Deleted
source remains recoverable from Git, not copied into an untracked alternative
library. Retained ordinary references are explicitly identified rather than
silently treated as the primary native implementation.

Shared owners now include
[raw presentation chain inputs](../emdash2/emdash3_2_commutative_algebra_presentation_chain_inputs.lp),
[chain-pair data](../emdash2/emdash3_2_chain_pair_data.lp),
[native boundary data](../emdash2/emdash3_2_homology_adjunction_input_data.lp),
and [ordinary H records](../emdash2/emdash3_2_homology_records.lp).
Ordinary selected H/family/record-connecting/window algorithms remain with the
separate reference iterator. Useful polynomial, matrix, presentation and
universal-provider algorithms remain available to their actual consumers.
No new native-versus-retired compatibility obligation was introduced.

A final textual import-graph audit finds no missing root-library imports.
The three protected native roots have closures of 329, 220 and 175 modules:
LES certificate views, native snake exactness, and the general native
six-term result. Their union is 360 modules, versus 382 at the initial review.
It excludes `computational_homology`, `homology_families` and
`homology_record_connecting`. These counts describe dependencies, not a proof
of semantic independence from every inherited categorical qualification.

## Structural And Computational Trust Boundary

The only new body-free structural declarations in this consolidation are:

| Symbol | Contract |
| --- | --- |
| `one_cat_terminal_adjunction` | From the original terminal capability and OneCat(C), supplies p:C→1 ⊣ t:1→C. |
| `one_cat_initial_adjunction` | From the original initial capability and OneCat(C), supplies t:1→C ⊣ p:C→1. |

Both live in the
[ordinary terminal adjunction owner](../emdash2/emdash3_2_one_cat_terminal_adjunctions.lp).
They are explicit structural extensions, not theorems derived from the old
terminal β rules. Ten companion definitions use the existing whole adjunction
unit/counit, diagram comparisons, Hom DefIso/Ω evidence and ordinary
contraction observations. Their existing normalizers retain the original
terminal/initial choices and computational forms.

The nine definitions in
[categorical contractions](../emdash2/emdash3_2_categorical_contractions.lp)
use the existing `OmegaEquivAlong` interface. CatContraction fixes the canonical
D→1; CatdContraction fixes the whole family map E→const₁. Their inverses remain
whole functors and dependent functors. Object/core contractibility is derived
as an observation. No second equivalence type, new contraction axiom, or
reconstruction of directed action from object paths was added.

Earlier ordinary adjunction-family lifting, diagram reconstruction,
terminal-family comparisons, product/biproduct adjunctions and normality
contracts remain as qualified in the preceding audit. This consolidation does
not retroactively turn their structural declarations into derived theorems.
It adds no output-exactness axiom, opaque computational inverse, closed
concrete model, or claim that finite CAS equations establish whole provider
semantics. The native signature environment's 365 entries were unchanged
through the TypeScript retirement and have not changed since its qualification.

The nucleus differs from the baseline at exactly two existing projection
clauses. The `tapp0_fapp0` identity component and `fdapp1_int_hom_fapp0`
identity action infer redundant family presentations from their identity
head instead of requiring those presentations to match twice. Their RHSs and
semantic owners are unchanged. There is no new rewrite/unification rule or
Op migration. The original `hom_int`/`homd_int` foundations remain owners.

These fixes have owner-position checks, an old-source failing control, three
positive presentation cases and one negative arbitrary-functor case. Final
nucleus diagnostics pass in 89.38s at 6GiB/90s, `OCAMLRUNPARAM=o=20,v=1024`;
peak RSS is 3,568,160KiB with no swaps. The earlier 2GiB allocation failure is
retained in the ledger. Replaceable-variable warnings stay at 157; critical
pairs decrease from 1146 to 1144. The strict inferred-slot audit has zero
unreviewed candidates. These measurements do not establish confluence or
resolve the deferred higher-variance/profile defects.

Final nucleus SHA-256:

```text
99cf8c04132eb9c9c9da3a43ec3f54b9e032c62745b140c4f81782ddb0d41ab6
```

## Remaining Equations And The Γ Boundary

The current H point comparison applies whole Q to an actual diagram map and
retains its selected inverse. It does not compute H by casting a functor along
an object equality. The actual incoming/outgoing Freyd column callers derive
cycle compatibility from existing diagram action. They do not ask end users
to carry an extra naturality-square proof.

The generic point bridge additionally accepts independently selected
N₀,N₁,n₀,n₁,v. Agreement of that arbitrary supplied data is a real interpretation
contract; naturality of a future Γ alone would not establish it. Paths remain
appropriate for fixed ordinary arrow equations, inverse laws, discrete-Hom
coherence and proposition-valued finite observation matching. The displayed
exactness transporter keeps canonical equivalence evidence and its inverse
data literally, extending only the observation path.

For coherent A,D,h:J∘A⇒D, a whole classifying Γ into the native zero-cone
category would support a whole comparison H_family⇒H_native∘Γ. The retained
[candidate](../emdash2/audits/categorical-family-introduction-boundary/README.md)
has checked constructor/object/source observations, but its target action and
further whole comparison are unqualified. The user selected finishing this
consolidation first. Future promotion needs target action, retained higher
Hom/triangle data, actual H specialization and focused warning/consumer
qualification. The fragment remains outside the positive library graph.

The review yields no established root cause or demonstrated fix for the
separate six-term comparison allocation boundary. Categorical maps are useful
where operational casts hid endpoint action, but that does not prove the same
cause for a different package comparison. That experiment was not resumed.

## Native Proof–CAS Verification

The complete compiled nonsplit LES suite passed all three tests in 392.22s;
the native snake passed all nine in 47.77s at checkpoint `38e2e7c0`. They use
2GiB OS limits, a 512MiB V8 heap and 4MiB semispace, with 600s/300s deadlines.
The earlier ts-node failure and successful unchanged compiled-JS control are
recorded as runner evidence. The final audit verifies no `src/` or `tests/`
change since that checkpoint, so those runtime results remain applicable.

The LES preserves 12 degree points, eight induced maps, three windows, eight
displayed points/seven arrows, and nine original whole exactness terms. It
separates 20 computed equations from 13 interpretation claims. The snake
preserves all six terms/five arrows, with nine equations and five arrow
interpretations, then derives four pair certificates and the whole displayed
certificate. Both reuse computations without homology/connecting replays or
universal reselection. The example remains R=ℚ[x], S=R/(x), including
0→R ─x→ R→S→0 and its nonzero connecting computation.

All eight unchanged emitted LP artifacts were replayed under the final kernel
with warnings and subject reduction enabled. Each uses the established serial
6GiB/180s guard, 64MiB file limit, no-swap scope and `o=20,v=1024`. No limit,
source, opacity or contract change was needed for this final replay.

| Artifact | Assertions | Seconds | Source SHA-256 |
| --- | ---: | ---: | --- |
| `cc2c2_les_compiled/diagram.lp` | 48 | 20.906 | `0698e8e0280ececb7583c9ed9a5f242f1f4fdb271c12285b18991d37c68d3263` |
| `cc2c2_les_compiled/displayed_exactness.lp` | 7 | 70.495 | `4f91a168ea065b7cf11f53a5d08ea1bae7dc6fbc7089daaaea8e57857e5bcea0` |
| `cc2c2_les_compiled/exactness_0.lp` | 3 | 20.892 | `706cccd47ea2ac09645e3c3190b0674792be8d55e6dc8bd521c9a3d1fc7cd599` |
| `cc2c2_les_compiled/exactness_1.lp` | 3 | 20.974 | `cc1d65ef79cb432f87fada7176458cca83e9fb45b401cbb6a4967b17e4a1b656` |
| `cc2c2_les_compiled/exactness_2.lp` | 3 | 20.868 | `a5e292a8fcfb82e8a1a3ab8b00239fe8c8344da6d75b0e15a3cc8c27714ca295` |
| `cc2c2_snake.lp` | 15 | 15.952 | `c945f7724d3b7d6fb86d0f52683b99e136ed2e8b7dc07d2d416d3d35e975a08d` |
| `cc2c2_snake_certificate_signatures.lp` | 10 | 66.505 | `5e6d28633802e5109ab14b2ac0d44e2b804d4c2c185985e46d05ccdcc960f617` |
| `cc2c2_snake_certificate.lp` | 5 | 63.322 | `865108ca2edcb904cebfe83198278460448d09b50f6368c05338c60e45d80c47` |

All 94 assertions pass. Against the prior exact-source warning inventories,
every artifact has the same two expected critical-pair removals at nucleus
locations 14888 and 17898, and no additions in category, location, head,
rule-family or parser inventories. These are affected end-to-end checks,
not a repository-wide typecheck. No paused six-term comparison was included.

Generated artifacts can be reproduced from the affected native diagram/snake
TypeScript tests. The exact emitted sources, log hashes and per-target results
are retained locally in `emdash2/tmp/probes/cc6_native_formal_replay.json`;
source/dependency inventories are `cc6_source_audit.json` and
`cc6_dependency_audit.json`. Each LP artifact can be checked from `emdash2`:

```bash
EMDASH_LP_MEMORY_MIB=6144 EMDASH_PROBE_TIMEOUT=180s \
OCAMLRUNPARAM=o=20,v=1024 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh path/to/emitted-artifact.lp
```

The source-only health snapshot remains
`0aaa980207f23307ea2f65558b68ae1744bbbdecfe256cfe4489d35ed1383e03`
for 1257 files. Health-source identity, strict check catalogue, source TOC and
book evidence checks pass. This does not claim fresh checking of every
registered file. No repo-wide TypeScript/Lambdapi aggregate was run.

## Documentation, Book And Publication

Book 0.9.1-dev updates Chapters 12, 30 and 31 and adds four checked evidence
entries. All 182 claims are cited, 46 sources assemble, and 3122 math spans
pass typography/KaTeX checks. The complete rendering is 407 pages with no
console/page/request/render errors. PDF metadata/font checks pass with 18
embedded fonts. Two exports have identical SHA-256:

```text
50db5ad839915eb04e48b8ac6aaea535410ffcfd3bad53ff3060fda66642cbfa
```

Visual review covers title/contents, all chapter/appendix openings, revised
sections, wide evidence tables, bibliography, credits and license. Generated
Markdown/PDF were promoted only through the owning scripts. The source,
manifest, evidence and generated artifact agree. No renderer or dependency
change was introduced.

The root/package READMEs, book README, current status, Foundations, report
index, instruction-file status and local email appendices have been updated.
Historical milestone narratives and the obsolete source catalogue have one
clearly marked recovery report; their six pre-extraction hashes verify
preservation. The plan owns current scope and its linked ledger owns history.
Local links, inbound moved-document fragments, owner existence and diff
hygiene pass. Email was not sent. At goal completion, the main worktree had
only the mirrored draft update; the post-completion integration below resolves
that working change without losing any content.

The initial authorized main/Pages publication remains `df9b4778`, with book
0.9.0-dev. Its successful deployment is
[run 35131972244](https://github.com/hotdocx/emdash/actions/runs/35131972244).
The user then explicitly authorized publication of the completed consolidation.
Main fast-forwarded to c3792b67 and was pushed; Pages
[run 35164455142](https://github.com/hotdocx/emdash/actions/runs/35164455142)
succeeded. The live book 0.9.1-dev PDF matches the checked SHA-256 above.
The [publication receipt](TYPESCRIPT_EMDASH_CATEGORICAL_CORE_CONSOLIDATION_LEDGER.md#post-completion-main-integration-and-pages-publication)
records the email reconciliation and exact deployment boundary. The following
receipt commit changes documentation only, not deployed source or artifacts.

## Exact Follow-Up Scope

- **Γ/whole H comparison:** preserve the meaningful candidate and its exact
  target-action boundary; qualify the complete whole consumer before promotion.
- **General higher terminality:** specify the whole represented-Hom owner,
  profiles, inverse/coherence data and cuts; distinguish computational DefIso
  adjunction data from weaker higher equivalence. Do not just remove OneCat.
- **Six-term package comparison and older endpoint experiments:** retain the
  existing constructors, inverse observations and failure receipts. A new
  bounded hypothesis is needed before resumption; neither is an unfinished
  obligation of this consolidation.
- **Op/duality and action-profile integration:** remain separate future goals.
  No new Empty audits or migration work was performed here.
- **Closed model/provider construction and algorithm verification:** the finite
  frontend assembly is automated, while the supplied mathematical contracts
  remain explicit. They have not become closed derived implementations.
- **Larger homological/derived developments:** unbounded complexes, Ext,
  general normalization theorems and spectral/stabilization research remain
  outside the present scope. No future extension is claimed by this audit.

No required scoped item remains blocked. Completion records the qualified
consolidation and its preserved native computations, with these boundaries
explicit rather than silently converted into claimed results.
