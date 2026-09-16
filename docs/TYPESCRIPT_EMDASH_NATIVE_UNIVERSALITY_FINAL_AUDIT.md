# Native Universality And Homology: Final Audit

Date: 2026-09-16

Status: complete — revised goal scope implemented and qualified; explicit deferrals retained

Parent: [living implementation plan](TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_AND_HOMOLOGY_PLAN.md)

Baseline: `cbef77e76fc292453c8814b5ecc6d62e84132f01`

Implementation checkpoint: `5df9292c`; bounded-review/deferral checkpoint: `b68469cd`

## Scope And Current Decision

The governing user directions require computational internal categorical
universality, whole K/Q/H/maps/δ and native exactness, direct proof–CAS use,
the general native snake and its comparison with the new LES, and preservation
of the foundational Hom owners. They withdraw old/new formulation comparison
requirements and defer Op/duality to a separate later goal. Spectral and
stabilization research, the other strictness branch and old endpoint-debugging
experiments remain outside this work.

D-NUH-080 authorizes explicit deferral of the remaining six-term observation
comparison after one bounded review and requires an updated book. That review
has completed. The large comparison is deferred, not proved. This audit must
retain that distinction when assessing the goal.

## Requirement Ledger

| Requirement | Current evidence and qualification | Result |
| --- | --- | --- |
| Preserve hom_int/homd_int as foundations | No replacement of either owner. The nucleus diff adds only two whole-transformation exchange cancellation rules; the Hom declarations remain in place. | Implemented; rule qualifications retained |
| Make categorical universality primary | `KernelAdjunctionStructure` and `CokernelAdjunctionStructure` contain the actual functors and adjunctions J ⊣ K and Q ⊣ I. The whole-family owners take these structures without old W/V dictionaries. | Qualified at the recorded ordinary-target boundary |
| Keep whole action and generic coherence | Units, counits, mates and fapp/tapp own action and naturality. Whole Coim⇒Im, H, δ and exactness consumers are retained; callers do not supply their naturality squares. | Qualified under declared structural profiles |
| Derive ordinary views only when needed | The native adjunction record views derive operational kernel/cokernel data at the same objects. Old presentations are optional adapters, not prerequisites of the native workflow. | Qualified; not a legacy comparison obligation |
| Use actual categorical presentation comparisons | H point and column comparisons now use actual diagram/native-input maps and retained inverses, with whole K/Q/H action. Operational functor transport through object/category equality was removed from the affected comparisons. | Qualified at the actual endpoints |
| Define the LES directly | The whole connecting transformation is constructed by native universal descents. All three whole window exactness comparisons use the original K/Q and normality. | Qualified; no assumed output exactness |
| Preserve a general native snake | Arbitrary whole a,b,c with cba=0, without monic-a or epic-c hypotheses; all six terms, five maps and four canonical exactness witnesses are retained. | Qualified |
| Compare new snake and new LES | The native four-row specialization, endpoint equivalences, surrounding maps and positive connecting-map sign are checked. | Qualified; no comparison with the retired snake is required |
| Use the native model directly with the CAS | Native rational context v8 uses the supplied `FreydAdjunctionModel` and normality. H/maps/δ observations retain the selected CAS presentations. | Qualified under explicit model/interpretation contracts |
| Automate mechanical integration | Preparation, equation reuse, row/map term assembly, complete-arrow observations, finite-diagram matching and displayed exactness construction are frontend operations. | Qualified for the retained workflow |
| Retain the nonsplit example | R=ℚ[x], S=R/(x), with nonsplit rows 0→R─x→R→S→0. Native LES and snake consumers retain nonzero connecting computations and actual quotient presentations. | Qualified conditionally on the recorded contracts |
| Certify the displayed CAS LES | Six actual adjacent-pair certificates plus one proof indexed by the complete coherent diagram; all original canonical data retained. | Qualified at `5df9292c`; public flag true |
| Retain data from the assembled six-term result | Twenty typed consumers cover four comparison/evidence packages and both inverse slots. | Qualified |
| Normalize the large direct six-term comparisons | The first isolated step comparison passes. The full observed-package comparison still allocation-fails after fresh parent compilation at 6GiB. | Explicitly deferred by D-NUH-080; not qualified |
| Maintain indexing discipline | Retain the existing checked field/window iterator and shared boundary arrows. Flattening is a display operation. No unqualified replacement iterator or arbitrary endpoint cast is promoted. | Retained |
| Keep Došen-style computation claims bounded | Whole adjunction cuts, transformations and universal descents are computational owners. No general homological normalization or theorem-proving theorem is claimed. | Boundary retained |
| Update the book since 0.8.3-dev | Edition 0.9.0-dev: Chapter 31, Chapter 12 and related appendices updated; 178 evidence claims/46 sources, browser/PDF gates and visual inspection pass. Owning tools promote identical checked PDF/Markdown artifacts. | Qualified |
| Document resource practice | Root guidance links the repository-wide Lambdapi SOP procedure for scoped OCaml GC tuning, measured memory/deadline overrides and exact-source replay. | Documented; no global-default increase |
| Respect Git and validation scope | Dedicated authorized goal worktree; local checkpoints; focused checks and measured resource profiles. No push, merge or remote publication. Closing staged review binds the owned files. | Observed |

## Declared Structural Boundary

The redesign does not derive every structural presentation from the old β
rules. A baseline-to-current inventory of library owners finds these ten new
body-free structural symbols (reviewer parameters are excluded):

| Owner | Declared structural instance |
| --- | --- |
| `emdash3_2_discrete_functor_paths.lp` | `discrete_functor_category` |
| `emdash3_2_one_cat_adjunction_families.lp` | `one_cat_functor_category`, `one_cat_postcomp_adjunction` |
| `emdash3_2_one_cat_biproduct_adjunction.lp` | `one_cat_biproduct_adjunction` |
| `emdash3_2_one_cat_diagram_reconstruction.lp` | `one_cat_diagram_reconstruction_iso` |
| `emdash3_2_one_cat_product_adjunction.lp` | `one_cat_product_category`, `one_cat_binary_product_adjunction` |
| `emdash3_2_one_cat_slice_paths.lp` | `one_cat_slice_category` |
| `emdash3_2_one_cat_terminal_family_universality.lp` | `one_cat_terminal_arrow_family_iso`, `one_cat_initial_arrow_family_iso` |

These are the recorded ordinary/discrete structural presentations and
adjunction lifts, not new axioms asserting homology or output exactness.
Their stated guards and original terminal/initial capabilities remain part
of the interface. In particular, the reconstruction DefIso for D∘E is not
silently a claimed unrestricted equivalence between strict diagrams and
higher lax arrows.

The nucleus has ten added source lines: two cancellation rules for exchanging
a whole transformation twice, including the projected outer component. Its
foundational Hom owners are not replaced. Exact rule-position and warning
qualification is recorded in the earlier owner ledger; this audit does not
claim an unchanged nucleus or a general normalization/consistency theorem.

## Proof–CAS Trust Boundary

The native backend registration supplies three semantic contracts: coefficient
interpretation, the whole adjunction model, and its normality. Model-side row
short-exactness and complete-arrow realization remain explicit interpretations.
Computed matrix equations and those interpretations have distinct adoption
classifications. The native proofs derive output exactness from that context.

The complete nonsplit LES replay retains twelve degree H points, eight induced
maps, three connecting windows, eight displayed points/seven arrows and nine
original whole exactness terms. Its original workflow adds twenty computed
equations and thirteen interpretation claims. The new certificate constructor
adds zero assumptions and zero trust decisions. A second run reuses the whole
source and the same proof/input terms without another decision or CAS
reselection.

This is not a closed construction of every universal provider or of the whole
Freyd model from raw matrices. The automation removes mechanical assembly;
it does not turn an unproved semantic contract into a theorem. General CAS
correctness, quotient effectiveness beyond the qualified interfaces, and a
general Došen-style homology normalizer remain separate work.

## Validation Evidence

The owner ledger and linked subplans preserve earlier tranches and their
source/log identities. The final displayed LES integration adds sixteen
transparent formal definitions, with no new primitive, rewrite/unification
rule or opacity. Its validation includes:

- focused TypeScript dependency compilation and affected-file lint;
- five selected signature/context tests, including all thirteen new private
  signature telescopes and native contract rejection;
- the complete nonsplit assembly, coverage rejection, reuse and emission
  workflow: three passing tests in 524.23s under the reviewed 600s/2GiB guard;
- all sixty-four emitted concrete assertions, six assembly assertions
  (including a negative input-substitution case), and thirteen signature
  conformance assertions;
- matching warning categories, locations, heads, rule families and parser
  inventories against exact import controls;
- body/LHS audit, catalogue/TOC and documentation hygiene, and a 1411-file
  source-health snapshot without a repository-wide typecheck.

Three missing observer-import issues were corrected in the test emitter.
The final endpoint-import repair was replayed through the owning header
function; all seven concrete assertion bodies stayed byte-identical. The
saved original artifact and hashes distinguish this emission repair from a
change to mathematical terms or model contracts. The final profile metadata
was enabled after proof qualification and checked separately, without
rerunning the 524s computation for a Boolean/version change.

The local exact receipt is
`emdash2/tmp/probes/nuh5g3b2c4b_qualification.json`; its staged hashes bind the
`5df9292c` tranche. The [bounded-review bundle](../emdash2/audits/native-six-term-observation-boundary/README.md)
preserves both successful and failed observation evidence as non-library
snapshots. No failed reviewer is registered as a passing example.

## Completion Decision

The required implementation, direct native proof–CAS qualification, final
scope/trust audit and local book update are complete under the user's revised
scope. The two bounded C3b2 approaches were executed and preserved; its large
direct comparison remains explicitly deferred under D-NUH-080. Op/duality and
the other enumerated research boundaries remain outside this goal. Neither
boundary is presented as solved. No required implementation or book work is
left hidden behind a completion claim.

## Qualified Book Update

The local edition is `0.9.0-dev`, dated 2026-09-16. Chapter 31 now presents
whole K/Q adjunctions as primary, canonical Coim⇒Im and exactness, whole H and
actual categorical presentation comparisons, direct δ, the general snake,
the new snake–LES comparison, and both nonsplit displayed CAS certificates.
Its ordinary iterator is explicitly identified as the retained earlier
interface, not an unqualified native migration or a required compatibility
route. The supplied model and interpretation contracts, structural primitives,
symbolic endpoint boundary and deferred large comparison remain visible.

Chapter 12 and Appendices A, B, D, E, F and G are aligned with that account.
The evidence register replaces eighteen retired presentation claims with
twelve native-owner entries; no formal library source is removed. All 178
registered claims are cited and their owner/reviewer links pass. Unrelated
Appendix G sections are retained. Source anchors, provenance, typography,
KaTeX and document validation pass for all 46 manifest sources.

The final `book:release` gate passes all source/evidence/typography checks,
the 405-page browser/pagination check with no console, page, request or render
errors, and PDF structure, metadata, text and font checks. The PDF has 18
embedded fonts. Twenty-three selected pages were rendered and inspected,
covering Chapter 31 and the changed adjunction, notation, glossary, status and
interface passages. Layout corrections were made before the final gate;
unchanged page images were compared with previously inspected renders.

`book:promote` rechecks the PDF and copies only the checked manifest-owned
artifacts. The distribution PDF and Markdown exactly match those generated
sources. No remote upload, release or publication occurred. Their final hashes
are:

- PDF: `3064cdf8bffc6ba5eb2b63815e96903d4bc0b2c10f52efa76eb71c2278f48c7e`
- Markdown: `2eb6f5e000ebf430e7a235245b51062d85b5121ad3708286cb8c141a78bd87fa`

The artifact receipt is `emdash2/tmp/probes/nuh7b_qualification.json`, with
render/PDF logs and page-image hashes. The two full library/theory scopes are
not conflated: the book reports the successful conditional native results and
the still-unqualified comparisons separately. The final exact staged review
and local checkpoint complete the authorized Git work.
