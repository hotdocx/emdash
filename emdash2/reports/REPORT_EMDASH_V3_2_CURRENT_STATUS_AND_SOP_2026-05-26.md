# EMDASH v3.2 Current Status And SOP

Date: 2026-05-26
Last consolidated: 2026-07-17
Status: living current-state and kernel-development authority

This report describes the active `emdash3_2.lp` architecture and the procedure
for changing it safely. It intentionally records the current selected design,
not the chronological sequence of earlier candidates. Dated implementation
plans in `reports/INDEX.md` retain decision history, rejected orientations, and
detailed probe evidence.

## Sources Of Truth

- `emdash3_2.lp`: active kernel definitions and runtime/proof-time behavior.
- `emdash3_2_eq1_hom_action.lp`: one-way derived native-EQ1 hom-action,
  groupoidality, and structured-transport layer; it imports the kernel and is
  imported by diagnostics/examples, never by the kernel.
- `emdash3_2_eq1_evidence_property.lp`: one-way transparent native-EQ1
  evidence-property, retract-truncation, and finite-`NCat` object-truncation
  layer; it imports the kernel and hom-action extension, never conversely.
- `emdash3_2_sum_observational_action.lp`: one-way library module retaining
  the componentwise Sum `ObsAction`, its equality comparison, and four
  proof-time bases; no kernel or univalence consumer imports it.
- `emdash3_2_checks.lp`: executable diagnostics and regressions.
- `EMDASH_FOUNDATIONS.md`: mathematical reading guide.
- `REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`: notation
  authority for comments, examples, and future parser work.
- `INDEX.md`: active plans, completed decision records, audits, and generated
  reports.
- `REPORT_EMDASH_CHECK_CATALOG.md`: generated map of the diagnostic suite.
- `REPORT_EMDASH_HEALTH.md`: generated source metrics and bounded timings.

The active source outranks every report if they disagree. Correct the report
as part of the same maintenance task rather than preserving a known stale
description.

Ignored `.scratchpad/` material is historical recovery data, not a normal
authority. Use the v2 retirement audit when an obsolete-baseline summary is
needed.

## Validated Current Baseline

The 2026-07-17 baseline is:

```text
make check                         pass
make examples                      pass
make ci                            pass
checked files/examples            51
diagnostic checks                1,917 (1,684 assert + 233 assertnot)
unclassified checks                0
strict LHS audit                   0 unreviewed candidates
intentional LHS annotations        45 slots across 27 clauses
warning inventory                  1,128
  unjoinable critical pairs          971
  replaceable pattern variables      157
```

The adopted equality-valued omega-equivalence overlay is implemented at its
selected operational MVP boundary. This includes the abstract/rigid-universe,
stable Product, uniform explicit-cast, decoder-independent native theorem
chain, homwise groupoidality, literal structured-action/J, equivalence-valued
displayed transport, unrestricted evidence-property, and unconditional
finite-`NCat` object-truncation results. The native next-hom owner is a one-way
derived extension with protected transparent proof helpers and one ordinary
public hom-action constructor; it is not an opaque theorem capability.
`OmegaEquivAlong_EQ1(f)` decodes to a native
one-constructor record with separate left/right inverse arrows, ordinary
equality-valued cancellation laws in the two endomorphism hom-categories,
four computational observers, an indexed eliminator, and reflexive evidence.
`OmegaEquiv_EQ1(x,y)` is now a stable abstract record-like facade with an
injective package constructor, forward/evidence observations, a primitive
dependent eliminator with constructor beta, propositional eta, and a
transparent Sigma comparison with two propositional round trips. The general
`object_path_equiv_EQ1(p)` computational adapter is defined from
`path_to_hom`, `path_sym`, and J-derived laws; it is not an opaque encoder.

The facade and eliminator are primitive kernel interface, but they are not
observationally opaque: their documented constructor/projection/eliminator
betas expose the data. The generic proof-time comparison between
`OmegaEquiv_EQ1(C,x,y)` and object equality is now active while `C` remains
syntactically abstract; it does not make the classifiers runtime-convertible
or add raw-path observer beta. The rigid Cat and Grpd universe equalities now
runtime-reduce to EQ1, and explicit EQ1 reflexivity packages compute. The
explicit D0 migration adapters described below remain a distinct
compatibility layer.

A specialization audit rejects the earlier abstract `lambda p, p` experiment
as a general public cast. Product repairs the measured specialization failure
by making `ProductPathView` its stable equality normal form while decoding its
carrier to the previous constant-family `SigmaPathView`. It has explicit
construction, projections, elimination, reflexivity, carrier adapters, and a
shaped EQ1 comparison. Generic `eq_refl` remains distinct from canonical
`product_path_refl` even though both expose the expected components.

Opposite retains `Obj(Op_cat(C)) -> Obj(C)`. A direct EQ1 comparison against
that reduced equality passed abstractly but failed at composite Product and
literal-path specializations. The Phase-6 opposite-only intermediary proved
that typed-let staging works, but is now retired in favor of the uniform
`ObjectPathCastView_EQ1(C,x,y)`. Its carrier reduces to object equality and a
single direct unification rule compares it with EQ1. The public casts in both
directions use a typed `let`, beta-reduce to their input, and have definitional
round trips after abstract, Product, opposite/nested, literal-path, functor,
Cat, and Grpd specialization. Product/opposite compatibility names route
through these general casts. Cast terms do not reify a package, so their
facade observers remain stuck; use `object_path_equiv_EQ1(p)` when projection
computation is required. No primitive nonreducing cast term is active. These
are current architecture facts owned by the July 17 plan, not new repository-
wide SOP rules. Warnings remain 971/157 and the strict audit remains
zero/45/27.

The literal-path Phase-3 slice adds two narrow proof-time comparisons without
promoting generic direct univalence. `OmegaEquiv_EQ1(Path_cat A,x,y)` compares
with `x =_A y`, while `Core_incl_func(Path_cat A)` compares with the identity
functor. `path_equiv_EQ1(p)` is the explicit computational package with
forward arrow `p`, two `path_sym(p)` inverse choices, J-derived laws, facade
elimination, and a next-hom reification consumer. `IsGroupoidalCat_EQ1(C)` is
equivalence evidence for `Core_cat(C) -> C`; this is the internally univalent/
complete groupoidality notion, not merely the external statement that arrows
have inverses. `Path_cat(A)` has canonical evidence. A bare path is accepted
at the facade type, but its observers deliberately remain stuck. Adding a raw
projection rule reproduces the package/path critical pair at 972/160 and
breaks a consumer, so the explicit package remains required.

The Phase-4 groupoid-universe boundary now makes
`Hom_cat(Grpd_cat,A,B)` the path category of ordinary functions. Stable
`grpd_id_function` and `grpd_comp_function` heads compute pointwise and compare
with the generic category identity/composition owners only at proof time.
Explicit defined adapters connect `TypeEquiv(A,B)` and
`OmegaEquiv_EQ1(Grpd_cat,A,B)`: the forward adapter uses the selected
contractible-fibre inverse, while the reverse proves the two omega inverse
choices agree and then supplies `EquivByInverse`. Selected maps, inverse
fields, cancellation laws, and the forward-map round trip compute. This adds
no decoder or bridge axiom. `is_equiv_map_by_inverse` is now a fully
transparent theorem: left-oriented path induction and the generic
half-adjoint triangle contract every homotopy fibre, after which the result is
re-centred at the historically selected inverse/right-law witness. The old
selected-centre computation is preserved without its former rewrite rule, and
the contraction proof is real propositional structure rather than an opaque
capability or proof-erasure equation.

The Phase-5 migration bridge makes the retained D0/new-EQ1 relationship
executable in both directions. Old D0 evidence is observed as EQ1 inverse
fields plus decoder-derived ordinary laws. New EQ1 evidence enters legacy D0
through a stable compatibility constructor whose four D0 observations are
specified: inverse fields project directly, and recursive cells apply the
defined `object_path_equiv_EQ1` adapter to the equality laws before recurring.
Thus two levels of recursive observation compute without `idtoequiv_cat`.
The primitive compatibility head is required only because D0 itself has no
constructor; it is migration surface, not a foundational encoder requirement.
D0 still has no eta/extensionality theorem, so neither evidence round trip is
claimed and both remain negative controls.

Phase-7 migration has retired the redundant standalone
`cat_univalence(C) : CatUnivalence(C)` inhabitant. It had no kernel consumer;
the two diagnostics that mentioned it now use the existing
`cat_univalence_from_decoder(C)`. The computational `idtoequiv_cat` and
`omega_equiv_path` operations, the specified-inverse
`cat_univalence_by_decoder`, and their groupoid counterparts remain while
their real rules and theorem consumers are migrated. No opaque EQ1 encoder or
decoder term was introduced. The new carrier-view rewrite and direct
unification equation are explicitly trusted cast infrastructure, while the
two term operations are transparent identities. This is the current
architecture of the July 17 plan, not a repository-wide rule that all explicit
casts must use this representation.

The transparent `object_path_equiv_D0(p)` compatibility operation is now the
defined route from an object path into retained D0: it composes the general
EQ1 package with the observation-complete migration constructor. Both
ordinary-isomorphism recursive cells and the D1 category-path next-hom
consumer use it instead of `idtoequiv_cat`. The latter's selected functor now
computes to `path_to_hom(Cat_cat,p)`. This reduces, but does not yet eliminate,
the encoder dependency *inside the legacy compatibility surface*;
compatibility round trips, shaped Product computation, OneCat theorems, and
other inventoried consumers remain. The native hom-action and
evidence-property modules and their public examples contain no Cat/Grpd
decoder, D0/D0b, or D0/EQ1 migration reference. Thus decoder migration is
complete at the selected foundational boundary even though full legacy API
retirement is not.

The general-groupoidality layer now lives with the native derived hom-action
owner in `emdash3_2_eq1_hom_action.lp`. For
`g : IsGroupoidalCat_EQ1(C)`, `groupoidal_core_homwise_EQ1` applies
`omega_equiv_along_fapp1_EQ1` directly to `Core_incl_func(C)`, with no
EQ1-to-D0, D0b, or D0-to-EQ1 step. Its selected right inverse sends a directed
arrow to an object path, and the equality-valued right law proves
propositionally that re-including that path recovers the arrow. Existing exact
`IsDiscreteCat` evidence and packaged `ZeroCat` carriers provide nonliteral
groupoidal witnesses. The public groupoidality names were relocated from the
kernel to the one-way extension without changing their types.

The first slice also checks the existing `path_ind_sec` computation for a
structured Sigma-pullback motive in a groupoidal context. Groupoidality is not
used by that computation: this is the intended specialization-by-weakening
result, showing that structured action needs no second eliminator.

The next slice establishes the exact literal `Path_cat(A)` comparison.
`path_cat_structured_transport_EQ1` is displayed functor action;
`path_cat_ind_eqr_transport_EQ1` is primitive right J with a function-valued
motive; and `path_cat_path_ind_app_EQ1` evaluates the existing
`path_ind_sec`. Two `ind_eqr` proofs and transitivity compare all three. Only
primitive J runtime-reduces to `u` at reflexivity. The two directed
presentations retain negative conversion controls, while narrow proof-time
joins reconcile the Path-category identity and the reflexive
PathOut/Sigma-pullback component order. Broad runtime repairs were rejected;
the selected rules leave warnings at 971/157 and add no decoder, encoder, or
parallel eliminator. This is a current architecture fact for the July 17
plan, not a new general SOP requirement for casts or transport.

The third Phase-9 slice proves the promised equivalence-valued transport
without adding another transport primitive. Ordinary functor action maps
`OmegaEquivAlong_EQ1` by applying the functor to both inverse arrows and both
equality laws. The groupoidality-selected object path and its reversal then
construct explicit native equivalence evidence for every arrow, using the
pointwise re-inclusion theorem and the existing J-derived path-cancellation
laws. Specializing functor preservation to `D : Catd(C)` equips the existing
`fapp1_fapp0(D,f)` fibre transport with EQ1 evidence; its inverse projections
compute. The construction is transparent and adds no rewrite, unifier,
encoder, decoder, or transport axiom. Selection of the arrow-to-path map now
uses the native EQ1 hom-action owner; no D0b compatibility step remains in
this consumer chain. This classification is specific to the July 17
implementation plan and does not amend the general SOP.

The reusable coherence prerequisite for that migration is now active.
`half_adjoint_counit` adjusts separate equality-valued left/right inverse
homotopies, and `half_adjoint_triangle` derives the standard triangle from
primitive `ind_eqr`, `eq_ap`, homotopy naturality, and path cancellation.
Both are transparent theorems: the adjusted counit and triangle proof compute
on reflexive identity data. No rewrite, unification rule, primitive symbol, or
opaque theorem capability was added. The complete theorem is promoted as
`omega_equiv_along_fapp1_EQ1` in the one-way extension. Its 56 implementation
lemmas are protected and transparent, its public package projections compute,
and reflexive input normalizes to the identity hom functor. A public
transparent definition could not retain `private` helpers under Lambdapi's
module exposition rules; `protected` helpers passed both the minimal probe and
the full external consumer, so this is not an opacity boundary.

`AllArrowsEquiv_EQ1(C)` records the pointwise statement that every directed
arrow has native EQ1 evidence, and `groupoidal_all_arrows_equiv_EQ1` computes
from coherent core groupoidality to that view. The converse is not active:
arbitrary pointwise choices do not yet assemble the coherent omega-functor
`C -> Core_cat(C)` required by `IsGroupoidalCat_EQ1`. This is a structured
functor assembly/extensionality gate, not a decoder gap.

A direct one-`J` shortcut through the uniform identity cast was measured and
rejected as a computational replacement. The cast gives a raw path the facade
type, but does not reify a package head, so `omega_equiv_to_EQ1` remains stuck
even on primitive reflexivity. Explicit `object_path_equiv_EQ1` reification
does compute to `path_to_hom`. This is a July 17 plan-local implementation
fact, not a general requirement that other subsystems introduce encoders or
decoders.

The generic half-adjoint inverse at a literal path category is still
intentionally not definitionally the input path; use the direct
`path_equiv_EQ1(p)` package for that computation.

The downstream transparent module `emdash3_2_eq1_evidence_property.lp` now
closes the native fixed-arrow evidence-property and finite-dimension
truncation obligations. It first exposes the native record as independent
left- and right-inverse homotopy fibres and proves record eta through the
indexed eliminator. Given any native witness, composition with its forward
arrow is an ordinary equivalence on each inverse-candidate hom classifier;
the transparent `is_equiv_map_by_inverse` theorem therefore contracts both
fibres and then the record. Consequently
`omega_equiv_along_evidence_is_prop_EQ1(C,x,y,f)` holds for every category and
fixed arrow, with no truncation assumption, axiom, decoder, rewrite, unifier,
or proof erasure. Literal path, discrete, and locally-set proofs remain useful
independent specializations.

The same module proves arbitrary truncation closure under explicit
retractions and uses it twice—Sigma facade to stable facade, then stable
facade to object equality. Transparent `CatDim` recursion combines the hom
induction hypothesis, same-level Sigma truncation, and the general evidence
property to define
`ncat_obj_trunc_EQ1(n,C,h) : IsObjTruncCat(cat_dim_trunc_level(n),C)` for every
finite native dimension. Its zero equation reduces to
`is_discrete_cat_obj_set`; its successor exposes the expected hom recursion.
The older `OmegaEquivAlongEvidenceProp_D0` and
`ncat_obj_trunc_from_evidence_prop` remain public compatibility experiments
for the opaque D0 certificate, but they are no longer the active native-EQ1
proof boundary and no inhabitant of the D0 capability is claimed.

The former-specific componentwise Sum action has been demoted without a
semantic rewrite. `sum_map` remains the ordinary eliminator-owned kernel map;
the two action bases, four proof-time comparisons, componentwise `eq_ap`
theorems, and registered `sum_obs_action` were mechanically relocated to
`emdash3_2_sum_observational_action.lp`. Only its diagnostics and reviewer
example import that one-way module. This preserves the useful library example
while removing action-specific proof-time authority from the foundational
kernel; focused kernel/module/check/example probes all pass.

The final selected-MVP catalog has 1,917 checks across 70 areas. The kernel has
21,762 lines, 887 symbols, 596 rewrite rules, and 63 unification rules. The
native hom-action extension has 2,791 lines/69 symbols; the evidence-property
extension has 1,407 lines/60 symbols and adds no explicit rewrite or
unification authority; the downstream Sum library has 430 lines/12 symbols
and owns the four extracted proof-time comparisons. The synchronized 51-file
health and reviewer sweeps pass. The diagnostic suite has 1,684 positive and
233 negative statements. Warnings remain 971/157 and the strict audit remains
zero/45/27. Synchronized 51-file CI passes with 100.845s of measured checking
time; the active July 17 plan records the phase evidence and selected
completion boundary.

The largest warning families are headed by `comp_fapp0`,
`hom_postcomp_fapp0`, `fapp1_fapp0`, and `tapp0_fapp0`. These reports are
diagnostic evidence for locating overlap families. They are not an automatic
veto on semantically required computation and are not a confluence proof.
The path-category E0 repair removed the path-specific
`comp_fapp0(Path_cat)->eq_trans` fold and the false definitional
self-opposite collapse. Two measured `eq_refl` projection-order bridges retain
the shared category-composition owner and reduce the inventory by 37
critical-pair reports; minimizing their recoverable endpoints also removes
four replaceable-variable advisories net. Four proposed oriented-action
runtime bridges were rejected after their owner-position variant added five
critical-pair reports and six replaceable-variable advisories. Typed
proof-time comparisons plus negative conversion controls cover those units
without changing the distinct post/pre runtime owners.
The path-symmetry E1 core now represents reversal by
`Path_sym_func(A) : Path(A)^op -> Path(A)`, with identity object action, one
measured reflexivity projection bridge, generic anti-composition, and
J-derived propositional agreement, involution, and the pointwise Core/opposite
square. Of the twelve E1 warning blocks, typed both-order consumers join the
post/pre action and naturality families, while two Product projection cases
are rejected as untyped rigid-head combinations. The other six exposed
over-specified object endpoints in generic mapped-`DefIso` cancellation:
inferring those endpoints makes both pre- and post-projection spellings
compute and removes 110 critical-pair reports. E1 itself retains six
classified reports, so the net active inventory falls by 98. Open
`path_sym`/`eq_sym` and double-symmetry terms remain non-convertible; no
path-specific composition or cancellation owner was added.
Candidate C now gives the canonical dependent `PathRecord_grpd(A)` a direct
observational equality view through its nested-Sigma presentation. Literal
record reflexivity reduces to the stable `PathRecordPathRefl(A,r)` head;
source and dependent-tail projections compute, and a specialized `ind_eqr`
clause computes only at that reflexive head. The closed registry covers the
shared path-category units, PathSym, Core inclusion, `idtoiso_cat`, and
`idtoequiv_cat`. It does not add arbitrary structural action, arbitrary-
constructor J computation, or runtime record eta. Explicit PathSym category
guards remove four spurious owner matches; five inferred-slot refinements
remove five replaceable advisories. The remaining 17 critical-pair reports
are covered by literal/shaped joins, typed post/pre/naturality diamonds, and
one negative displayed-target control. Relative to E1, the active inventory
therefore changes from 974/159 to 991/157.
Candidate H adds stable `PiHapply`/`PiFunext` owners over the existing
related-input `PiPathView`, pointwise runtime beta, generic-J propositional
eta, and a `TypeEquiv` package for the diagonal observation. Its one
two-rigid-head `unif_rule` preserves the reflexive computation of the
transparent presentation as a generic structurally justified proof-time law;
typed reflexivity tests firing, while negative conversion and arbitrary-J
checks preserve the runtime boundary. A reviewed opaque
`is_equiv_map_by_inverse` theorem capability converts the explicitly supplied
round trips to contractible fibres. Only the selected fibre centre computes;
the contraction path remains opaque. The 29 new diagnostics and reviewer Pi
example pass owner/application-order checks without changing the 991/157
warning inventory or the 45-slot/27-clause LHS audit.
The structural-path compatibility slice adds arbitrary propositional
`sigma_path_decode_encode` and `sigma_path_encode_decode` theorems while
preserving the existing componentwise/J owners and rejecting open runtime
eta. Constructor-exposed reflexivity computes. A distinct literal-reflexivity
base is retained because the proof-time Sigma-reflexivity comparison does not
propagate through nested decode during generic J. Since `PathRecord` equality
already is `PathRecordPathView`, its named encode/decode maps are transparent
identity views; both round trips, shaped reflexivity, the dependent-tail
observer, and one nested PathRecord case compute. The 21 new diagnostics and
reviewer example add no rewrite or unification rule, leave warnings at
991/157, and leave the strict audit at 45 annotated slots across 27 clauses
with zero unreviewed candidates.
The ordinary `TypeEquiv` algebra slice retains `type_equiv_refl` and adds
transparent `type_equiv_sym` and categorical-order `type_equiv_comp` packages.
Their `*_is_equiv` evidence is derived from explicit selected inverse paths
through `is_equiv_map_by_inverse`; no new rewrite or unification rule is
needed. Forward maps, selected inverse maps, right paths, forward-map units,
and forward-map associativity compute. Contraction-derived left paths and
package-level double-symmetry/unit eta stay non-runtime. Twenty-nine new
diagnostics and the reviewer algebra example leave warnings at 991/157 and
the strict audit at 45 annotated slots across 27 clauses with zero unreviewed
candidates.
The groupoid decoder slice names both round trips already carried by
`grpd_univalence_by_decoder`, derives `grpd_univalence_from_decoder`, and makes
its selected contractible-fibre inverse compute to the single operational
`grpd_equiv_path` owner. It deliberately does not identify an arbitrary
legacy `ua_grpd(U,e)` with that decoder. `coe_grpd_idtoequiv` is derived by J;
combined with the decoder right round trip it gives the propositional
`grpd_equiv_path_coe` square and a Pi-universe action consumer. A measured
generic runtime `coe(grpd_equiv_path(e))` orientation was rejected because
the Product-decoder-first branch leaves `coe(product_grpd_path(...))` stuck.
The 16 new diagnostics and reviewer decoder example add no rule or unification
equation, leave warnings at 991/157, and leave the strict audit unchanged.
The first Phase-13 groupoid-universe slice now exposes the same decoder through
the finite named view `GrpdPathView(A,B) := TypeEquiv(A,B)`.
`grpd_path_encode`, `grpd_path_decode`, their two propositional inverse laws,
and `grpd_path_decode_coe` route through the existing decoder owners; Product
diamonds, Pi action, and same-base Sigma formation reuse their existing bodies.
Public universe equality remains opaque. The direct canonical-owner rule was
warning-neutral and passed the full existing suite, but its unstratified
self-universe normalization recursively reopened universe equality and timed
out at 20 seconds, while both baseline equality and the named view normalize
within the bound. The earlier spelling on reducible `Grpd_grpd` also added one
avoidable alias-unfold critical pair; the canonical `(Obj Grpd_cat)` spelling
removed it. Seventeen positive/seven negative diagnostics and a fourteen-
positive/five-negative reviewer example are active. Seven semantic aliases
add no rule or `unif_rule`; warnings remain 971/157 and the strict audit remains
zero/45/27. Quiet view source/check logs end in `20260716-053946`/`054135`,
warning logs in `20260716-054151`/`054233`, the direct self-universe timeout
ends in `20260716-053636`, controls end in `20260716-053720`, and the active
reviewer log ends in `20260716-054558`. The catalog has 1,509 checks across 52
areas; health checks 34 files with a 17,838-line/738-symbol/574-rule/51-
unification-rule kernel and 1,367 positive diagnostics. Synchronized 34-file
CI passes with 182.160s of measured checking time (189.18s wall time).
The next Phase-13 slice selects a different boundary at the categorical
universe. The canonical rule makes `@=(Obj Cat_cat,A,B)` reduce directly to
`OmegaEquiv(Cat_cat,A,B)`; the readable `CatPathView` alias, canonical package
reflexivity, decoder-owned encode/decode and round trips, selected
functor/evidence projections, reflexive Product action, and D0b next-hom
package are active. Self-universe normalization terminates at the opaque
`OmegaEquivAlong_D0` certificate boundary, and the canonical `(Obj Cat_cat)`
spelling is warning-neutral at 971/157; the reducible `Cat_grpd` spelling adds
one avoidable report. Generic `eq_refl` is deliberately retained. Collapsing
it to `omega_equiv_refl` adds three reports and breaks the existing
`omega_equiv_along_obj_path` reflexive action before the outer `eq_ap` beta can
fire. Twenty-two positive/eight negative diagnostics and a fifteen-positive/
six-negative reviewer are active, with no `unif_rule`. The catalog has 1,539
checks across 53 areas; health checks 35 files with a 17,989-line/750-symbol/
575-rule/51-unification-rule kernel and 1,389 positive diagnostics. The full
reviewer sweep passes, and synchronized CI passes with 165.477s of measured
checking time (171.88s wall time). Any future representation of the currently
opaque fixed-arrow certificate must reopen the self-universe normalization
gate.
The next Phase-13 boundary now exposes a finite one-layer observation record
for that certificate. `OmegaEquivAlongObservation_D0(f)` is the nested
Sigma/Product of the selected left/right inverse arrows and recursive
left/right cell packages; `omega_equiv_along_observe_D0(u)` fills it through
the existing D0 owners, and `OmegaEquivAlongPathView_D0(u,v)` is equality of
the two records. Canonical view reflexivity and one-way action of a genuine
certificate path are active, including a D0b next-hom consumer. Directly
installing the view as certificate equality is rejected: the owner-position
source exceeds 30 seconds, and an append-only canonical self-universe control
exceeds 20 seconds, while the finite view control finishes. Thirteen positive/
three negative diagnostics and a ten-positive/three-negative reviewer are
active; five semantic symbols add no rule or `unif_rule`, warnings remain
971/157, and the strict audit remains zero/45/27. The catalog has 1,555 checks
across 54 areas; health checks 36 files with an 18,104-line/755-symbol/575-
rule/51-unification-rule kernel and 1,402 positive diagnostics. The full
reviewer sweep passes, and synchronized CI passes with 186.423s of measured
checking time (193.35s wall time). The view supplies neither a reverse decoder
nor evidence eta/property-valuedness. The next bounded theorem slice separates
the now-ready `IsNCat` induction/Sigma/univalence transport from its still-
missing certificate-property inhabitant: the former must take the latter as
an explicit capability rather than postulate it or infer it from the finite
view.
That conditional theorem spine is now active. The uninhabited classifier
`OmegaEquivAlongEvidenceProp_D0` states the exact global fixed-arrow
property-valuedness premise. `prop_is_trunc_cat_dim` lifts such a proposition
to every native dimension level, and
`ncat_obj_trunc_from_evidence_prop(P,n,h)` computes at zero to the stored
object-set factor and at successor through the homwise induction, same-level
Sigma closure of `OmegaEquiv`, and `cat_univalence_type_equiv`. Eleven
positive/four negative diagnostics and an eight-positive/four-negative
reviewer are active. The typed proof-time negative retains distinct capability
inputs, so no `unif_rule` is added; warnings remain 971/157 and the strict
audit remains zero/45/27. The catalog has 1,570 checks across 55 areas; health
checks 37 files with an 18,173-line/758-symbol/577-rule/51-unification-rule
kernel and 1,413 positive diagnostics. The full reviewer sweep passes, and
synchronized CI passes with 198.816s of measured checking time (206.34s wall
time). Bare `IsNCat` evidence still does not inhabit the theorem, and the
finite observation view still does not construct the capability.
The recursion-safe representation continuation is now completed/promoted.
`OmegaEquivAlongDimObservation_D0(n,h,f)` computes
to Unit at zero and at a successor stores both selected inverse arrows plus
the forward arrow and smaller-dimensional observation of each D0 inverse-cell
package. `omega_equiv_along_dim_observe_D0` reuses the four existing D0 owners;
`OmegaEquivAlongDimPathView_D0` adds only reflexivity and one-way `eq_ap`
action. ZeroCat erasure and OneCat next-cell termination compute. Seventeen
positive/five negative diagnostics and a twelve-positive/four-negative
reviewer pass; six symbols and two two-equation rule families add no
`unif_rule`, preserve 971/157 warnings, and retain zero/45/27 audit. The
catalog has 1,592 checks across 56 areas; health checks 38 files with an
18,452-line/764-symbol/579-rule/51-unification-rule kernel and 1,430 positive
diagnostics. Quiet owner/signature/inherited-check logs end in
`20260716-104217`/`104520`/`104613`, warning logs end in `104636`, and the
scratch/active reviewer logs end in `104802`/`104928`. The indexed view remains
one-way and does not inhabit `OmegaEquivAlongEvidenceProp_D0`. The full
reviewer sweep passes, and synchronized 38-file CI passes with 201.708s of
measured checking time (212.59s wall time).
The first registered elementary-former action is now completed/promoted.
`sum_map(f,g)` is the eliminator-owned canonical
binary-sum map. `sum_obs_action(f,g,u,v)` delegates equal-tag paths to the two
supplied `ObsAction` registrations, returns the impossible input in mixed
selected-action branches, eliminates it in mixed coherence branches, and
packages pointwise agreement with generic `eq_ap`. Transparent `eq_ap`
unfolded before a direct two-action proof-time equation could fire. The
selected architecture therefore uses one stable reflexive action basis per
tag and two direct `unif_rule`s per basis: normalized component reflexivity and
the exact outer-`ind_eqr` normal form. The arbitrary comparison is derived by
ordinary component J and explicitly composes the two paths, without relying
on unification transitivity. This is trust-classified as a semantically
justified former-specific structural action law. Runtime basis/action
conversion, direct transitive proof-time collapse, open selected/semantic
action equality, and package collapse remain negative. Twenty-one positive/
six negative diagnostics and a thirteen-positive/four-negative reviewer pass;
thirteen symbols and four proof-time equations add no runtime rewrite rule,
preserve 971/157 warnings, and retain zero/45/27 audit. The catalog has 1,619
checks across 57 areas; health checks 39 files with an 18,883-line/777-symbol/
579-rule/55-unification-rule kernel and 1,451 positive diagnostics. Final
feasibility/owner/inherited-check logs end in `20260716-112405`/`114250`/
`113027`, warning logs end in `113036`/`113051`, and the active reviewer log
ends in `113631`. Full examples pass, and synchronized 39-file CI passes with
129.250s of measured checking time. Arbitrary structured J/fibrancy, proof
erasure, no-confusion/canonicity, categorical coproduct structure, and other
former actions remain separate. The next bounded replacement probe targets
OneCat-scoped ordinary-iso univalence; it may not restore or consume a global
`cat_iso_univalence` assumption, and must instead derive the ordinary-iso/
omega-equivalence comparison or record the exact missing owner.
That probe has now promoted a bounded one-sided prerequisite.
`iso_evidence_omega_along_D0(i)` is a stable, source-backed
fixed-arrow evidence generator: both inverse observations are
`iso_evidence_from(i)`, while the ordinary left/right inverse equations encode
with `idtoequiv_cat` as the two recursive cells. Its public Sigma package is
`iso_evidence_omega_equiv(i)`. A proposed runtime reflexive fold added four
unjoinable reports; it was rejected. The selected single `unif_rule` compares
only the backed reflexive evidence head with canonical D0 reflexivity at proof
time, is exercised by typed `eq_refl`, and leaves the package and decoder
runtime-distinct. Generic J proves
`iso_evidence_omega_equiv(idtoiso_cat(p)) = idtoequiv_cat(p)` without relying
on unification transitivity. `one_cat_iso_path(X,i)` then uses the canonical
omega decoder, and `one_cat_iso_path_idtoiso(X,p)` supplies the first
decoder-after-encoder round trip.

The full `CatIsoUnivalence` replacement was not claimed by that one-sided
checkpoint. Its focused reverse probe showed the missing endpoint exactly: an arbitrary public omega-equivalence
has separate `left_inv` and `right_inv`; its right cell decodes at
`f o right_inv`, not at the `f o left_inv` endpoint needed by an ordinary
package choosing the left inverse. The next prerequisite at that checkpoint
was a OneCat-derived
directed comparison between those inverses, conversion to a discrete-hom
path, transport of the right law, and nested-Sigma extensionality. Neither a
rewrite nor an unbacked proof-time identification is selected. The then-active
legacy global `cat_iso_univalence` assumptions remain unused by the new owner
and are retired after the full scoped replacement closes. Twelve positive/six
negative diagnostics and a nine-positive/four-
negative reviewer pass; five symbols, two two-equation rule families, and one
proof-time comparison preserve 971/157 warnings and zero/45/27 audit. The
catalog has 1,637 checks across 58 areas; health checks 40 files with a
19,062-line/782-symbol/581-rule/56-unification-rule kernel and 1,463 positive
diagnostics. Final owner/signature/inherited-check logs end in
`20260716-120633`/`121149`/`120824`; warning logs end in `120226`/`120834`, the
intentional reverse failure ends in `120916`, and the active reviewer log ends
in `121326`. Full examples pass; synchronized 40-file CI closes the one-sided
prerequisite with 281.823s of measured checking time.

The dependency-ready inverse-comparison continuation is completed/promoted
with synchronized 40-file CI. The first intended-owner attempt composed the
two recursive cells
through raw `Hom_func` action and failed at three unresolved comparisons: both
unit presentations and the middle associativity step. This is recorded in the
owner log ending `20260716-123757` and is evidence against relying on
unification transitivity, not against the mathematical construction. The
selected owner instead exposes both recursive cell arrows, uses the existing
stable post- and precomposition functors for whiskering, and inserts an
explicit propositional associator through `path_to_hom`. The resulting
`omega_equiv_along_left_to_right_D0(u) : left_inv(u) -> right_inv(u)` is
generic; `one_cat_omega_inverse_path(X,e)` decodes it through hom discreteness.
Canonical reflexivity computes to the identity 2-cell through generic owners,
while the decoded path remains runtime-distinct from `eq_refl`. Eight symbols,
no rewrite, and no `unif_rule` add nine positive/four negative diagnostics and
six positive/three negative reviewer statements; the reviewer now totals
fifteen positive/seven negative statements. Quiet owner/check logs end in
`20260716-124247`/`125136`, warning logs in `125119`/`125140`, and the reviewer
log in `124544`. The warning inventory remains 971/157 and the strict audit
remains zero/45/27. The catalog has 1,650 checks across 59 areas;
health checks 40 files with a 19,373-line/790-symbol/581-rule/56-unification-
rule kernel and 1,472 positive diagnostics. Full examples and synchronized CI
pass with 139.872s of measured checking time. The remaining
full-capability prerequisite is no longer inverse comparison: it is transport
of the right law along the selected inverse path followed by ordinary
nested-Sigma evidence reconstruction and the reverse round trip.

That final OneCat-scoped continuation is now completed/promoted. The generic
`omega_equiv_left_law` and `omega_equiv_right_law` decode the two recursive
cells. `one_cat_omega_right_law_at_left` transports the latter along
`one_cat_omega_inverse_path`, and `one_cat_omega_iso_evidence` reconstructs
ordinary evidence with exact forward/inverse/law projections. In a OneCat,
the inverse-law proof fields live in discrete endomorphism hom-categories;
`discrete_cat_path_proof` and the existing nested-Sigma path owner therefore
prove `one_cat_omega_iso_lift_retract`. Encoder agreement and the categorical
decoder round trip then give `one_cat_idtoiso_iso_path`, completing the
specified inverse pair with `one_cat_iso_path_idtoiso`.

The first packaging attempt targeted the then-active legacy
`CatIsoUnivalenceByDecoder(C)` and failed because that classifier hardcoded
the frozen `iso_evidence_path`; the log ending `20260716-132624` records the
two unresolved decoder comparisons. The selected
`OneCatIsoUnivalenceByDecoder(X)` instead names the scoped decoder explicitly,
derives `one_cat_iso_univalence(X)` through
`is_equiv_map_by_inverse`, and exposes `one_cat_iso_type_equiv(X,x,y)`.
Its forward map, selected inverse, and selected right path compute, while the
contraction-derived left proof remains runtime-distinct. The unused global
capability and hardcoded classifier are retired in the follow-up slice. Ten
semantic symbols add no rewrite or `unif_rule`.
Owner quiet/warning logs end in `133706`/`133718`, inherited-suite logs in
`133745`/`133751`, and the expanded 32-positive/12-negative reviewer in
`134212`; warnings remain 971/157 and the audit remains zero/45/27. The new
active area contributes thirteen positive/two negative diagnostics, bringing
the catalog to 1,678 checks across 61 areas with zero unclassified checks.
Health passes across 40 files at a 19,883-line/804-symbol/581-rule/56-
unification-rule kernel with 1,495 positive diagnostics, and full examples
pass. Synchronized CI passes with 109.546s measured checking time. The scoped
construction is closed; active inventory selects bounded retirement of the
unused global capability inhabitants/classifier while retaining the consumed
`iso_evidence_path` reflexive/Product owner.

That bounded retirement is now promoted. `cat_iso_univalence`,
`cat_iso_univalence_by_decoder`, and `CatIsoUnivalenceByDecoder` had no active
kernel consumer and only three compatibility diagnostics; they are removed
without replacing the assumption. `CatIsoUnivalence` and `isotoid_cat` remain,
and the latter now computes in a diagnostic through
`one_cat_iso_univalence(X)` to `one_cat_iso_path(X,i)`. The obsolete
scoped-vs-global negative is removed because its global term no longer exists.
The Product decoder rules and their checks still consume `iso_evidence_path`
and are unchanged. Owner/check quiet logs end in `140150`/`140155`, warning
logs in `140205`/`140228`, and the 33-positive/11-negative reviewer in
`140406`. Three symbols are removed with no rewrite or `unif_rule`; warnings
remain 971/157, the audit remains zero/45/27, and the catalog has 1,675 checks
across 61 areas with zero unclassified checks. Health passes across 40 files
at a 19,859-line/801-symbol/581-rule/56-unification-rule kernel with 1,493
positive diagnostics, and full examples pass. Synchronized CI passes with
212.799s measured checking time. The global
ordinary-iso capability retirement is closed.

The next dependency-ready former-action continuation is also completed and
promoted. Recursive Nat equality exposes
`(succ m = succ n)` as `(m = n)`, so `nat_succ_obs_action` selects `p |-> p`.
Generic `eq_refl(n)` and outer `eq_refl(succ n)` retain distinct runtime
provenance. The accepted owner therefore introduces
`nat_succ_ap_basis(n)` and two direct, narrowly typed `unif_rule`s: one
compares that stable basis with each reflexivity presentation at proof time.
`nat_succ_component_basis` and `nat_succ_basis_outer` are internal paths, and
generic `ind_eqr` composes them to prove `nat_succ_eq_ap(p)` for an arbitrary
predecessor path. The registered package reuses that theorem as its semantic
coherence and composes through the generic `obs_action_comp` owner. Direct
runtime basis/reflexivity conversion, proof-time transitivity, selected-map/
generic-`eq_ap` conversion, and package collapse remain negative; no
successor-specific J beta or Nat canonicity claim is added.

Owner/check quiet logs end in `141904`/`142047`, warning logs in
`142057`/`142329`, and the active eleven-positive/five-negative reviewer log in
`142721`. Seven symbols and two proof-time equations add no runtime rewrite
rule. Warnings remain 971/157 and the strict audit remains zero/45/27.
Fourteen positive/five negative diagnostics bring the catalog to 1,694 checks
across 62 areas with zero unclassified checks. Health passes across 41 files
at a 19,988-line/808-symbol/581-rule/58-unification-rule kernel with 1,507
positive diagnostics. Full examples and synchronized CI pass; CI records
220.269s measured checking time.

Candidate D0 introduces the neutral general-category
`OmegaEquivAlong_D0(f)` certificate independently of the old public
`OmegaEquiv`. Its transparent `OmegaEquiv_D0(x,y)` Sigma package exposes exact
forward/evidence projection beta; selected inverse observations and recursive
higher inverse cells are indexed by the fixed arrow. Reflexive evidence
computes in both inverse slots and both cells, and a diagnostic projects the
left cell and observes reflexivity again in the next hom-category. No raw
inverse-composite cancellation, package eta, compatibility bridge, new
`unif_rule`, or property-valuedness claim is added. Eighteen positive and
three negative diagnostics plus an eight-positive/three-negative reviewer
example pass the owner/projection orders. Quiet and warning-enabled full-file
owner probes end in `20260715-193201`/`193222`; warnings remain 991/157 and the
strict audit remains zero with 45 annotated slots across 27 clauses. The
promoted D0b variable-evidence Cat hom action is described next; D1 is the
remaining public migration gate.
Candidate D0b now constructs
`omega_equiv_along_fapp1_D0(u,x,y)` from variable rather than reflexive
fixed-arrow evidence. Its forward map is exactly `fapp1_func(F,x,y)`. The raw
hom action of either selected inverse functor has the wrong endpoints; the
left inverse is `Hom(eta_x,epsilon_y) o L_1`, while the right inverse combines
components from `L o F ~ id_A` and `F o R ~ id_B` to compare `L` and `R`
before conjugating `R_1`. Both recursive cells are transparent D0 packages
with stable cell/evidence observations and remain iterable for one more
observation. The implementation adds no `unif_rule` or raw cancellation.
Twenty-four positive and two endpoint-negative diagnostics plus an
eight-positive/two-negative reviewer example pass. Quiet owner logs end in
`20260715-194634`/`194846`; warning-enabled logs end in `20260715-194900` and
remain exactly 991/157 with the strict audit unchanged.
D1 replaces the public opaque `OmegaEquiv` classifier by
`Sigma f, OmegaEquivAlong(f)`. Public projections and inverse/cell
observations route through the fixed-arrow evidence owner; reflexive,
opposite, and Product closure use evidence generators rather than duplicated
public destructor rules. `omega_equiv_path` is evidence-indexed, and the
decoder capability now supplies both named propositional round trips, the
derived `cat_univalence_from_decoder`, a named `TypeEquiv`, and the
propositional encoder/`path_to_hom` square. The semantic fibre comparison is
only a one-sided retraction, preserving the package-eta/property-valuedness
boundary. Applying D0b to a category path supplies an exact, iterable
next-hom public omega-equivalence without a per-instance `unif_rule`. Forty-one
positive and five negative diagnostics plus a twelve-positive/four-negative
reviewer example cover the migration. Ten new observation-versus-reflexive-
evidence overlap families have explicit both-order checks; replacing the old
public rule family improves the inventory from 991/157 to 990/157, while the
strict audit remains zero with 45 annotated slots across 27 clauses.
Phase 8 replaces the category-indexed first-class adjunction package by the
relation `Adjunction(F,G)`. `left_adj_func` and `right_adj_func` are now
transparent compatibility views, while `unit_adj_transf` and
`counit_adj_transf` remain stable opaque observations and the sole triangle
discriminators. Both triangles, opposite adjunction, the hom-profunctor mate,
and weighted-limit/colimit preservation now thread the functor indices
directly. The active inventory found no concrete preselected unit/counit
declaration, so promotion adds no unification equation or existential
`AdjunctionPackage`; three positive and three negative diagnostics instead
cover the views, opposite involution, absent untrusted operation agreement,
and raw-operation runtime erasure. The expanded reviewer example checks both
triangles, opposite involution, mate cancellation, and the trust negative.
Minimizing the inferred opposite-functor LHS slots removes the superseded
left/right projection overlaps and improves warnings from 990/157 to 978/157;
the `comp_fapp0` family remains 400 and the strict audit remains unchanged.
The first Phase 9 slice makes `IsDiscreteCat(C)` exactly the Product of
`IsSetGrpd(Obj(C))` and fixed-map omega-equivalence evidence for
`Core_incl_func(C)`. Its Product constructor/projections compute and no package
eta or evidence erasure is selected. `core_incl_hom_func(C,x,y)` is the
generic hom action and its object action is exactly `path_to_hom`. Applying
the promoted D0b generator to the projected core evidence yields
`discrete_core_homwise`; the selected left inverse defines `hom_to_path`.
One recursive public cell, the left component, and a general composite through
the selected left/right comparison supply the two coherent round trips. They
remain non-runtime, and set truncation alone is an explicit negative. Thirteen
positive/four negative diagnostics and a six-positive/two-negative reviewer
example add no rule or unification equation, leave warnings at 978/157, and
leave the strict audit at zero with 45 intentional slots across 27 clauses.
The next Phase 9 slice keeps groupoidal truncation and directed dimension
separate. `IsObjTruncCat(n,C)` is exactly `IsTruncGrpd(n,Obj(C))`; native
`CatDim` starts at zero, `IsNCat(cat_zero,C)` computes to the active exact
`IsDiscreteCat(C)`, and the successor recurses over every hom-category.
`NCat(n)` retains a carrier and its evidence, with computing constructor /
projection boundaries and transparent `ZeroCat`/`OneCat` aliases but no
package eta or proof erasure. `one_cat_hom_discrete` projects the successor
evidence, and `one_cat_hom_core_homwise` is the required next-hom consumer of
the promoted discrete theorem. Eighteen positive/five negative diagnostics
and a seven-positive/three-negative reviewer example add four rule
declarations (five equations) and no `unif_rule`; warnings remain 978/157 and
the strict audit remains zero with 45 intentional slots across 27 clauses. The implication from directed
dimension to object truncation and OneCat-scoped ordinary-iso univalence are
not formation rules and remain separately dependent. The synchronized CI gate
passes all 17 files in 78.267s with source TOC, active-reference/header,
strict-LHS, and fresh-catalog checks.
The bounded object-truncation prerequisite now adds
`cat_dim_trunc_level : CatDim -> TruncLevel`. It computes from `cat_zero` to
`trunc_zero` and commutes with successor, so one- and two-dimensional codes
normalize to `trunc_one` and its successor. Five positive/one negative active
diagnostics and four positive/one negative additions to the directed-dimension
reviewer example cover formation, both equations, low-dimensional reductions,
and the crucial absence of an evidence coercion from `IsNCat`. The two map
equations leave warnings at 978/157 and the strict audit at zero with 45
intentional slots across 27 clauses. Categorical equivalence invariance and
recursive equivalence-evidence truncation still block the implication theorem.
The synchronized index-bridge CI gate passes all 19 files in 87.056s with
every repository-integrity check.
The first Phase 10 structural-action slice introduces explicit
`ObsAction(f)` and `ObsDAction(s)` packages. Each stores a selected action and
pointwise next-dimensional agreement with the existing semantic `eq_ap` or
`eq_apd` owner, so specialized computation cannot silently assert an unrelated
path action. Constructor/projection application computes; canonical
registrations use the semantic owners, the registered identity acts by
`p |-> p` on arbitrary paths, and registered nondependent actions compose
pointwise with a J-derived coherence proof. `path_record_action` exposes the
result on the shaped record view, while `path_record_witness_action` transports
the genuinely dependent witness field through `PathOver`. Thirty-one
positive/five negative diagnostics and a ten-positive/three-negative reviewer
example add no rule or `unif_rule`, leave warnings at 978/157, and leave the
strict audit at zero with 45 intentional slots across 27 clauses. Arbitrary
package agreement stays propositional, coherence evidence is retained, and an
arbitrary selected loop still gives no dependent-J beta; fibrancy remains a
separate owner. The synchronized CI gate passes all 18 files in 86.300s with
source TOC, active-reference/header, strict-LHS, fresh-catalog, example, and
repository-integrity checks.
The general binary-sum foundation extension adds a native two-parameter
`SumData(A,B)` carrier, decoded `Sum_grpd(A,B)` classifier, both constructors,
and dependent `sum_elim` through the generated induction principle. Both
constructor betas compute; six positive and one negative active diagnostics
plus an eight-positive/two-negative reviewer example cover decoding,
formation, dependent use, branch computation, a swap consumer, constructor
non-collapse, and the absence of runtime open eta. The failed grouped-binder
candidate exposed that Lambdapi generalized the second classifier in the
generated recursor; separate `(A : Grpd) (B : Grpd)` parameter binders are the
selected owner. The one decoding rule adds no warning family, leaving the
inventory at 978/157 and the strict audit at zero with 45 intentional slots
across 27 clauses. At that foundation gate observational sum identity and
higher action were separate; the visible identity and registered componentwise
action are now promoted in later bounded slices, while no-confusion,
canonicity, and categorical coproduct structure remain separate.
The synchronized binary-sum CI gate passes all 19 files in 88.539s with every
repository-integrity check.
General truncation invariance now maps the operational
`grpd_equiv_path(e)` through `X |-> IsTruncGrpd(n,X)`, decodes the resulting
path with `idtoequiv_grpd`, and exposes a canonical `TypeEquiv` of truncation-
evidence classifiers plus both directional evidence maps. Reflexive path,
package, and map computation is active; arbitrary self-equivalences do not
collapse at runtime. Ten positive/one negative diagnostics and a seven-
positive/two-negative reviewer example add no rule or `unif_rule`, preserve
the 978/157 warning inventory, and leave the strict audit at zero with 45
intentional slots across 27 clauses. The synchronized gate passes all 20 files
in 97.398s.
The fixed-map categorical consumer uses the single
`omega_equiv_along_path_D1` decoder rather than reconstructing inverse object
maps from transformation components. Mapping `Obj` over its category path and
applying `idtoequiv_grpd` gives an ordinary equivalence of object classifiers;
the general theorem then supplies a `TypeEquiv` between
`IsObjTruncCat(n,A)` and `IsObjTruncCat(n,B)` and forward/backward evidence
transport. Twelve positive/three negative diagnostics and an eight-positive/
two-negative reviewer example cover formation, reflexive computation, both
round trips, open evidence, and the deliberate absence of runtime agreement
with `fapp0(F)`. Five semantic definitions add no rule or `unif_rule`; warnings
and the strict audit remain 978/157 and zero/45/27. The synchronized gate
passes all 21 files in 98.423s. At that gate, recursive omega-equivalence
evidence truncation and the corresponding Sigma closure argument still
blocked the `IsNCat -> IsObjTruncCat` theorem; the Sigma theorem described
below is now active, leaving the recursive certificate representation/evidence
theorem as the blocker. Categorical invariance no longer blocks it.
General one-step truncation monotonicity is constructive rather than a
weakening rewrite. `eq_sym_trans_self`, `contractible_path_center`, and
`contractible_path_contract` prove the contractible-to-proposition base;
`is_trunc_grpd_succ` then recurses through the generated `ind_TruncLevel`
eliminator. The owners must be split: the path/base lemmas occur after
`IsGroupoidGrpd`, while the all-classifier `TruncMonotonicity` theorem occurs
after `Grpd_grpd` decoding is available. A fully explicit `@Struct_sigma`
base failed elaboration broadly, whereas retaining inferred Sigma indices
passes the focused signature and full owner-position checks. Twelve positive/
one negative diagnostics and an eight-positive/one-negative reviewer example
add six semantic definitions and no rule or `unif_rule`; warnings remain
978/157 and the strict audit remains zero/45/27. The catalog now has 1,261
checks across 39 areas, and health checks all 22 files. The open-centre
negative preserves the absence of proof erasure. Truncation-evidence
property-valuedness and general dependent-Pi closure were separately owned
and are described next; dependent-Sigma closure and recursive omega-
equivalence evidence truncation remain separate.
The synchronized CI gate passes all 22 files in
127.18s with every repository-integrity check.
Truncation evidence is now proposition-valued at every native level.
`is_contr_evidence_path` compares two contractibility witnesses through the
active dependent Sigma path view: it transports the second contraction
function along the first centre path and uses `PiFunext` pointwise in the
contractible path spaces. `is_contr_pi` and `is_prop_pi` provide exactly the
dependent-Pi bases consumed by the level theorem. A transparent
`ind_TruncLevel` declaration inhabits the result, and its base conversion is
bounded, but both applied and unapplied successor conversion probes exceed
60s after unfolding the reducible Pi/equivalence motive. The selected
`is_trunc_grpd_evidence_is_prop` stable head instead has one disjoint two-
equation rule declaration at classifier consumers; it exposes the base or
named successor helper without a proof-time equation. Sixteen positive/two
negative diagnostics and an eight-positive/two-negative reviewer example add
ten symbols and one rule declaration, keep warnings at 978/157, and keep the
strict audit at zero/45/27. The catalog has 1,279 checks across 40 areas;
health checks 23 files with a 16,557-line/685-symbol/569-rule/51-unification-
rule kernel and 1,207 positive diagnostics. Open evidence remains non-
convertible, so this theorem does not erase proofs. General dependent-Sigma
truncation bounds, package-path control, and recursive omega-equivalence
evidence truncation remain separate. The synchronized CI gate passes all 23
files in 75.41s with every repository-integrity check.
Arbitrary-level dependent-Pi truncation closure is now active.
`PiTruncClosure(n)` states the family theorem; `is_trunc_pi` uses
`is_contr_pi` at `-2`, while `trunc_pi_succ` applies the recursive theorem to
the pointwise path family and transports the result back through
`pi_happly_type_equiv` using general `TypeEquiv` invariance. A stable theorem
head has one disjoint two-equation consumer rule declaration, and the readable
`is_prop_pi` alias now routes through its `-1` specialization instead of
duplicating the pointwise equivalence proof. Ten positive/one negative active
diagnostics and an eight-positive/one-negative reviewer example add three
symbols and one rule declaration, preserve 978/157 warnings, and keep the
strict audit at zero/45/27. The catalog has 1,290 checks across 41 areas;
health checks 24 files with a 16,606-line/688-symbol/570-rule/51-unification-
rule kernel and 1,217 positive diagnostics. Open pointwise evidence remains
non-convertible. The synchronized CI gate passes all 24 files in 131.21s.
At the Pi-closure gate, dependent-Sigma closure and recursive omega-equivalence
evidence truncation remained separate; the Sigma theorem is described next.
Same-level dependent-Sigma truncation closure is now active.
`is_contr_sigma` constructs the contractible-total base from contractible base
and fibres. At a successor, `trunc_sigma_succ` recursively truncates the
`SigmaPathView` of two total points: base-path evidence comes from the base
hypothesis, while reducible `PathOver` exposes an equality after transport to
which the source-fibre hypothesis applies. `is_trunc_sigma` is a stable head
with one disjoint two-equation consumer rule declaration; both hypotheses stay
visible. Ten positive/two negative active diagnostics and an eight-positive/
two-negative reviewer example add four symbols and one rule declaration,
preserve 978/157 warnings, and keep the strict audit at zero/45/27. The
catalog has 1,302 checks across 42 areas; health checks 25 files with a
16,721-line/692-symbol/571-rule/51-unification-rule kernel and 1,227 positive
diagnostics. The synchronized CI gate passes all 25 files in 136.09s.
The remaining recursive omega-equivalence evidence theorem is not proof-ready:
`OmegaEquivAlong_D0` is an opaque constant with no general constructor or
eliminator, and its compatibility fibre has only a one-sided retraction. The
finite observation/path view now exposes all four current observations and a
one-way encoder, but the rejected recursive equality rule shows that it does
not supply a bounded reverse decoder or evidence eta. A certificate-
representation redesign or independently justified recursion-safe evidence-
path capability is still required before property-valuedness can be derived;
it must not be postulated from the observations alone.
Truncated-universe carrier/evidence path control is now active.
`TruncGrpdPathView(n,X,Y)` pairs a carrier path with the dependent `PathOver`
between retained evidence fields. The reviewed native-package eliminator
supports constructor-level decoding; proposition-valued evidence reconstructs
the second field from any carrier path. Carrier projection and reconstruction
have named propositional round trips, reconstruction at reflexivity is proved,
and `trunc_grpd_carrier_path_type_equiv` packages the two path classifiers as
an ordinary `TypeEquiv`. Its forward and selected inverse projections compute,
but the inverse laws and generic encode/decode round trip are deliberately not
runtime cancellation. Fifteen positive/three negative active diagnostics and
an eight-positive/three-negative reviewer example add 22 symbols and no rule
or `unif_rule`, preserve 978/157 warnings, and keep the strict audit at
zero/45/27. The catalog has 1,320 checks across 43 areas; health checks 26
files with a 17,447-line/714-symbol/571-rule/51-unification-rule kernel and
1,242 positive diagnostics. Restricted ambient-univalence agreement and the
expected universe-level truncation theorem remain separate; the latter also
needs a truncation theorem for carrier equivalences. The synchronized CI gate
passes all 26 files in 188.15s.
Restricted truncated-universe univalence is now active. The decoder capability
is packaged once as `grpd_univalence_type_equiv`; composing it in categorical
order with `trunc_grpd_carrier_path_type_equiv` yields
`trunc_grpd_univalence_type_equiv`. Its forward map is exactly ambient
`idtoequiv_grpd` after carrier projection, and its selected inverse is exactly
`grpd_equiv_path` followed by evidence-derived package reconstruction. Two
named propositional round trips and inverse reflexivity preserve the runtime
boundary; only forward reflexivity computes. Twelve positive/three negative
diagnostics and an eight-positive/three-negative reviewer example add seven
semantic symbols and no rule or `unif_rule`, preserve 978/157 warnings, and
keep the strict audit at zero/45/27. The catalog has 1,335 checks across 44
areas; health checks 27 files with a 17,547-line/721-symbol/571-rule/
51-unification-rule kernel and 1,254 positive diagnostics. This is restricted
decoder-mediated compatibility, not direct observational universe identity.
The expected package-universe level theorem remains separate; a focused
explicit-inverse probe establishes its contractible `TypeEquiv` base without
proof erasure. The synchronized CI gate passes all 27 files in 282.49s.
The expected truncated-universe level theorem is now active. At the
contractible base, `contractible_map_by_inverse` gives every map a constant
inverse at the source centre, proposition-valued `IsEquivMap` evidence makes
the evidence fibres contractible, and `contractible_type_equiv` applies the
existing Pi/Sigma closure. At successors, the function space inherits target
truncation and equivalence evidence is raised from proposition-valuedness;
source truncation is intentionally not a branch discriminator because only
the base needs it. The stable `is_trunc_type_equiv` owner has one disjoint
two-equation rule declaration, and `is_trunc_grpd_universe` transports the
result through restricted package univalence to prove
`IsTruncGrpd(trunc_succ n,TruncGrpdU n)`. Seventeen positive/three negative
diagnostics and an eleven-positive/three-negative reviewer example add ten
semantic symbols and one rule declaration, preserve 978/157 warnings, and
keep the strict audit at zero/45/27. The catalog has 1,355 checks across 45
areas; health checks 28 files with a 17,735-line/731-symbol/572-rule/
51-unification-rule kernel and 1,271 positive diagnostics. No same-level
universe theorem, direct universe identity, or proof erasure is installed.
The synchronized CI gate passes all 28 files in 155.30s.
The Product reflexivity-provenance cleanup removes the two competing runtime
collapses from `iso_evidence_product(refl,refl)` and
`omega_equiv_along_product_D1(refl,refl)` to their unrelated generic
reflexive evidence heads. Componentwise Product constructors are now the
selected normal forms at reflexivity. Their forward/inverse and decoder
projections compute; selected inverse-arrow observations still join the
generic Product identity spelling, while recursive cells and full decoder
paths deliberately retain their structured Product heads. No replacement
rewrite or `unif_rule` is installed because no typed consumer requires the
proof-time comparison, and omega-evidence property-valuedness remains
unproved. Eleven explicitly scoped Product diagnostics, the adjacent
ordinary-iso and categorical-decoder controls, and a nine-positive/five-
negative reviewer example pass. Owner-position quiet source/check logs end in
`20260716-025427`/`030307`, warning-enabled logs end in
`20260716-030323`/`030715`, and the focused reviewer log ends in
`20260716-031113`. Removing the collapses lowers unjoinable reports by six,
from 978 to 972, while replaceable advisories remain 157 and the strict audit
remains zero/45/27. The catalog has 1,360 checks across 46 areas; health checks
29 files with a 17,714-line/731-symbol/570-rule/51-unification-rule kernel and
1,271 positive diagnostics. Synchronized 29-file CI passes in 189.90s.
The first elementary observational-equality subgate gives the four visible
Boolean constructor pairs their Unit/Empty classifier matrix. Owner-position
evidence rejects the initially probed `eq_refl -> tt` normalization: that
orientation required Boolean-specific J, PathSym, Core, path-unit, and two
encoder registrations and added exactly 42 unjoinable reports (14 literal-
reflexivity consumer overlaps, 12 PathSym functoriality/action/naturality
overlaps, and 16 Core overlaps including four ill-typed displayed-target
combinations). The promoted minimum adds only the four classifier equations.
Generic `eq_refl` retains its runtime provenance, so every existing literal-
reflexivity consumer continues to compute without a new registry; raw `tt`
proofs receive no second beta and no proof-time equation. Twenty-two positive
and eleven negative diagnostics plus an eleven-positive/six-negative reviewer
example pass. Quiet owner/check logs end in `20260716-034236`/`034410`, the
warning-enabled owner/check logs end in `20260716-034258`/`034311`, and the
reviewer log ends in `20260716-034631`. Warnings remain 972/157, the strict
audit remains zero/45/27, the catalog has 1,393 checks across 47 areas, and
health checks 30 files with a 17,728-line/731-symbol/571-rule/51-unification-
rule kernel and 1,293 positive diagnostics. Synchronized 30-file CI passes in
143.199s.
The matching Unit subgate applies the same provenance policy to the sole
visible constructor. One equation reduces `tt = tt` to `Unit_grpd`; generic
`eq_refl Unit_grpd tt` remains the proof normal form, all existing literal-
reflexivity consumers compute, and raw `tt` receives neither a second beta nor
a proof-time equation. Ten positive/nine negative diagnostics and a seven-
positive/six-negative reviewer example pass. Quiet owner/check logs end in
`20260716-040227`/`040238`, warning-enabled logs end in
`20260716-040248`/`040259`, and the reviewer log ends in
`20260716-040444`. Warnings remain 972/157, the audit remains zero/45/27, the
catalog has 1,412 checks across 48 areas, and health checks 31 files with a
17,737-line/731-symbol/572-rule/51-unification-rule kernel and 1,303 positive
diagnostics. Synchronized 31-file CI passes in 153.385s.
The recursive Nat subgate adds the four zero/successor classifier equations:
zero reflexivity exposes Unit, the two mixed cases expose Empty, and successor
equality recurses to predecessor equality. The first classifier-only candidate
passed quiet and 972/157 warning probes, but invalidated the pre-existing broad
`ind_eqr _ u (eq_refl _)` beta. In the focused proof-dependent
`NatJProbeMotive`, Lambdapi accepted a predecessor-reflexivity J term at the
predecessor-indexed result and normalized it to the outer-reflexivity branch,
while an executable negative confirmed that branch did not inhabit the
declared result type. The same broad rule could already consume foreign Unit
and Boolean reflexivity because their visible equality classifiers reduce to
the same `Unit_grpd`.

The promoted prerequisite therefore makes J's category and repeated endpoint
real LHS subject-reduction discriminators. Outer reflexivity still computes;
raw `tt`, foreign reflexivity, and predecessor reflexivity remain stuck at J,
and no registry or `unif_rule` is added. The guard also removes the old generic-
J/PathRecord shaped-reflexivity critical pair, improving warnings from 972/157
to 971/157. The Nat area has 23 positive/11 negative diagnostics, the separate
J-guard area has four negative diagnostics, and the reviewer example has 11
positive/eight negative statements. Rejected unguarded quiet source/check logs
end in `20260716-041943`/`042647`; its warning logs both end in
`20260716-042708`, and the adversarial subject-reduction log ends in
`20260716-043035`. Selected guarded quiet source/check logs end in
`20260716-043247`/`043414`, warning-enabled logs end in
`20260716-043427`/`043428`, and the reviewer log ends in
`20260716-043749`. The strict audit remains zero/45/27. The catalog has 1,450
checks across 50 areas; health checks 32 files with a 17,753-line/731-symbol/
573-rule/51-unification-rule kernel and 1,326 positive diagnostics. The
synchronized 32-file CI gate passes in 151.336s.
The general binary-sum subgate extends the same guarded provenance contract to
parameterized constructors. Four equations reduce inl/inl and inr/inr paths to
their component equality and the two mixed cases to `Empty_grpd`. Generic
outer sum reflexivity remains the proof normal form; component reflexivity is
separately typed by the reduced classifier but receives no J/path/encoder beta
and no proof-time equation. A proof-dependent injective-motive probe confirms
that generic J remains stuck on component reflexivity and that its outer-
indexed branch does not inhabit the component-indexed result.

The first LHS-minimal candidate was critical-pair neutral but retained six
Lambdapi replaceable-variable advisories on reconstructible constructor
indices. Inferring the unused opposite summand and both indices in mixed-tag
clauses removes all six without changing computation. Final quiet source/check
logs both end in `20260716-050336`; final warning-enabled logs both end in
`20260716-050351`; the proof-dependent guard log ends in
`20260716-050426`; and the reviewer log ends in `20260716-050744`. Twenty-four
positive/eleven negative diagnostics and a twelve-positive/eight-negative
reviewer example pass. Warnings remain 971/157 and the strict audit remains
zero/45/27. The catalog has 1,485 checks across 51 areas; health checks 33
files with a 17,777-line/731-symbol/574-rule/51-unification-rule kernel and
1,350 positive diagnostics. The synchronized 33-file CI gate passes with
161.044s of measured checking time
(167.96s wall time), closing the elementary visible-constructor lane.
The displayed-identity/`tdapp0` follow-up replaced the primitive
`id_transfd` normal form by a transparent generic-`id` view and removed 19
older identity critical-pair reports. The complete typed projection-order
package for Cat-valued component naturality, including both identity-base
degenerations, adds 34 classified reports, for a net increase of 15 over the
previous baseline. Its outer category must remain inferred: a product-valued
target can reduce `Functor_cat(X,A×B)` to a product head before the bridge is
selected. A rigid-head alternative fails that product-target diagnostic.
Displayed vertical-composite components now project pointwise through two
SOP-minimal `tdapp0_fapp0` clauses, mirroring the ordinary `tapp0_fapp0`
projection beta. Their outer inferred slots are `_`; the inner composite's
rigid `Functord_cat` or `Transf_cat` category is the discriminator and retains
the information required for subject reduction. The rules pass the generic
strict-action diamond, both identity units, product-target normalization, and
one further component projection without changing the warning inventory. The
reverse fully capped contraction remains rejected: it chooses the wrong
component-projection normal form and its minimal LHS also fails subject
reduction. A proof-time comparison is not a substitute for the selected
runtime projection beta.

`emdash3_2.lp` contains no executable `assert` commands. Diagnostics live in
`emdash3_2_checks.lp`; reviewer-facing milestones live in `examples/`.

## Current Architecture

### Sections 0–3: kernel foundations

The kernel begins with the groupoid/type universe, equality/path induction,
encoded Sigma/Pi/product object layers, and the core category interface.

Active equality/equivalence staging includes:

- decoded elementary H0 classifiers `Empty_grpd`, `Unit_grpd`, `Bool_grpd`,
  `Nat_grpd`, and `Sum_grpd(A,B)`, with native Empty/Unit/Bool/Nat/sum carriers,
  dependent eliminator facades, constructor beta, and a Bool conversion-level
  anti-collapse diagnostic; visible Unit, Boolean, Nat, and general-sum
  constructor equality additionally compute to Unit, Empty, predecessor, or
  component equality while generic `eq_refl` retains runtime provenance and
  open endpoints retain primitive equality. Generic J repeats its category
  and endpoint as subject-reduction guards, so a foreign/component proof with
  the same reduced classifier cannot trigger reflexive computation. Remaining
  elementary observational identity, broader no-confusion, higher action for
  other formers, canonicity, and categorical universal properties remain
  separate. The kernel retains the eliminator-owned canonical `sum_map`; its
  componentwise `sum_obs_action`, equality comparisons, and four proof-time
  bases are checked in `emdash3_2_sum_observational_action.lp` as library
  surface, with no kernel or univalence consumer. `nat_succ_obs_action` is the
  first recursive-inductive
  registration: its selected action keeps the exposed predecessor path, while
  a stable basis and generic J prove agreement with successor `eq_ap` without
  runtime proof collapse or unification-transitivity. The transparent
  `nat_succ_ind_eqr` facade separately routes successor-indexed motives through
  predecessor J and computes only at component reflexivity; outer reflexivity,
  the action basis, and generic J keep their existing runtime boundaries;
- generic `ObsAction`/`ObsDAction` register selected computation for a raw
  groupoid function or dependent section and prove agreement with
  `eq_ap`/`eq_apd`. They are not the structured groupoidal-J transport owner:
  `PathOut` consumes an already functorial `Catd` motive. Replacing the
  registry would first require a consumer-driven constructor from raw
  function-plus-path-action data to an iterable
  `Path_cat(A) -> Path_cat(B)` functor. Nat and PathRecord remain real
  consumers; the registry is retained library-facing computation, not a
  second univalence or fibrancy foundation;
- the named dependent `PathRecord_grpd(A)` representative, implemented by a
  parametrized one-constructor native carrier with direct source, target, and
  dependent witness projections plus a generated-induction facade; its active
  observational path view, stable shaped reflexivity, projection betas, and
  reflexive specialized J are described below, while runtime record eta,
  arbitrary structural action, and additional arbitrary-constructor J remain
  deliberately absent;
- native `TruncLevel` codes beginning at -2, recursive
  `IsTruncGrpd(n,A)`, and transparent proposition/set/ordinary-groupoid views;
  the successor equation makes equality lowering computational, while the
  decoder-owned ordinary `TypeEquiv` invariance package transports truncation
  evidence in both directions and computes on reflexivity;
- the named one-constructor package `TruncGrpdU(n)`, with computing carrier
  and retained-evidence projections and the aliases `PropU_grpd`,
  `SetU_grpd`, and `GroupoidU_grpd`; carrier/evidence path views, carrier-path
  reconstruction, propositional inverse laws, and the resulting path
  `TypeEquiv` are active; composing with the canonical ambient decoder gives
  restricted equivalence between package equality and carrier `TypeEquiv`,
  while no package eta, proof erasure, or same-level universe theorem is
  selected; `is_trunc_type_equiv` and `is_trunc_grpd_universe` prove the
  expected successor universe level through this restricted equivalence;
- truncation monotonicity, evidence property-valuedness, arbitrary-level
  dependent-Pi closure, and same-level dependent-Sigma closure are active;
  restricted package univalence and the expected universe-level truncation
  theorem are active; truncation reflectors and the representation prerequisite
  for recursive omega-equivalence evidence remain separately statused;
  general `TypeEquiv` invariance and its fixed-map categorical object consumer
  are active;
- `TypeEquiv` with forward/inverse maps and inverse paths, plus identity,
  symmetry, and categorical-order composition with derived `IsEquivMap`
  closure evidence;
- the finite `GrpdPathView(A,B)` universe identity view, with canonical
  reflexivity, decoder-owned encode/decode, propositional inverse laws and
  transport agreement, Product/Pi/Sigma consumers, and no direct public
  universe-equality rule or duplicated univalence body;
- direct categorical-universe identity
  `@=(Obj Cat_cat,A,B) -> CatPathView(A,B) = OmegaEquiv(Cat_cat,A,B)`, with
  retained generic reflexivity provenance, decoder-owned round trips,
  reflexive Product action, and an iterable D0b next-hom package;
- path views for encoded Sigma and Pi types;
- arbitrary propositional Sigma path encode/decode round trips and transparent
  named PathRecord round trips, with constructor-reflexive computation and no
  open runtime eta;
- ordinary `PiHapply`/`PiFunext` over the related-input Pi view, with
  pointwise runtime beta, generic-J propositional eta, an explicitly
  classified proof-time reflexive basis, and contractible-fibre
  `pi_happly_type_equiv`; arbitrary structured-Pi J computation and
  computational fibrancy remain separate;
- the repaired path-category composition boundary: generic `comp_fapp0` owns
  runtime composition, two narrow `eq_refl` unit bridges join both projection
  orders, and `path_comp_eq_trans` proves J-derived propositional agreement;
  `Op_cat(Path_cat(A))` remains a genuine opposite head, while the oriented
  post/pre action heads retain distinct runtime forms and compare with shared
  composition only at proof time; `Path_sym_func(A)` owns path reversal from
  the genuine opposite, generic functoriality owns anti-composition, and
  `path_sym_agrees_eq_sym`, `path_sym_invol`, and
  `path_sym_core_incl_agreement` provide propositional coherence without open
  runtime folds;
- `GrpdUnivalence` and decoder-based groupoid-univalence capabilities, with
  named decoder round trips, a canonical contractible-fibre capability
  selecting `grpd_equiv_path`, a propositional decoder transport square, and
  a Pi-universe action consumer; arbitrary legacy `ua_grpd` agreement and
  direct universe identity remain absent;
- `IsoEvidence` for ordinary categorical isomorphism data;
- the general `CatIsoUnivalence` capability type with no global inhabitant,
  plus
  the derived ordinary-iso-to-omega lift, generic selected-inverse directed
  comparison, transported inverse law, nested-Sigma reconstruction, both
  OneCat-scoped decoder round trips, the derived scoped capability, and its
  path/isomorphism `TypeEquiv`;
- independent Candidate-D0 fixed-arrow `OmegaEquivAlong_D0(f)` evidence and
  its transparent recursive `OmegaEquiv_D0` staging package, plus the
  endpoint-correct variable-evidence Cat hom-action generator and the finite
  one-layer observation/path view with a one-way evidence-path encoder;
- public `OmegaEquivAlong(f)` and Sigma-packaged `OmegaEquiv`, with exact
  evidence-routed observations and reflexive/opposite/Product closure;
- `CatUnivalence` and decoder-based omega-categorical univalence capabilities,
  both named round trips, the named path/equivalence `TypeEquiv`, the
  propositional `path_to_hom` square, one integrated next-hom witness, and the
  induced ordinary `TypeEquiv` of object classifiers for fixed-map evidence.
- exact `IsDiscreteCat` Product data, D0b-derived core homwise evidence,
  `hom_to_path`, both coherent round trips, and a recursive cell consumer.
- independent object truncation, native directed-dimension codes, recursive
  `IsNCat`, evidence-retaining `NCat`/`ZeroCat`/`OneCat` packages, and a
  `OneCat` next-hom core-adequacy consumer; the conditional object-truncation
  D0 compatibility induction remains active with an explicit,
  still-uninhabited global fixed-arrow evidence-property capability. The
  downstream native-EQ1 module independently proves unrestricted fixed-arrow
  evidence property, arbitrary truncation under retractions, and unconditional
  finite-`NCat` object truncation with computing base/successor equations. The
  ordinary-iso lift and first scoped
  decoder round trip, left/right inverse comparison, transported right law,
  nested-Sigma evidence reconstruction, reverse round trip, scoped
  `CatIsoUnivalence`, and named `TypeEquiv` are active. The arbitrary-category
  capability inhabitants/classifier are retired; the legacy
  `iso_evidence_path` Product computation remains separately compatibility-
  owned.
- registered nondependent/dependent observational path actions with semantic
  agreement, computing identity/composition, shaped PathRecord action, and
  dependent witness-field transport; no additional arbitrary-constructor J.

These are explicit kernel interfaces and checked computation skeletons. They
do not claim that every future univalence/coherence theorem is already
internalized.

### Finite dependent-record convention

Ordinary finite named structures use a parametrized one-constructor native
inductive carrier when later fields depend on earlier ones. A decoded
`*_grpd` classifier owns the public type; named projections are manual semantic
symbols with constructor beta rules, and public projection/eliminator
signatures retain the decoded classifier rather than exposing only the raw
carrier. Use the generated dependent induction principle directly or through
a thin reviewed facade when its raw parameter/motive surface is inconvenient.

Projection rules infer non-discriminating inductive parameters as `_` when
subject reduction and the strict LHS audit permit. Do not add runtime record
eta by default. A small map-plus-property existential may remain an encoded
Sigma; a structure with several stable field names or downstream structural
equality uses the record convention. The active `PathRecord_grpd` is the
executable representative: its original formation/elimination owner-position
and nested-Sigma comparison are warning-neutral, while the record supplies
direct named access and a direct three-field eliminator instead of nested
`sigma_Fst`/`sigma_Snd` chains. This decision is about the public API and
equality telescope, not a claim that nested Sigma is computationally invalid.

### Shaped PathRecord equality

`PathRecordPathView(A,r,s)` reads the named record structurally as
`Σ src : A, Σ dst : A, src = dst` and reuses the existing dependent Sigma
path view. The public equality rule for `PathRecord_grpd(A)` exposes that view
directly. `PathRecordPathRefl(A,r)` is the stable runtime reflexivity head;
`path_record_path_src` and `path_record_path_tail` expose its source and
dependent-tail components. Their beta clauses are ordered separately because
the tail result is indexed by the already-reduced source component.

The generic `ind_eqr` owner remains available for every equality. One narrow
former-specific clause restores its literal-reflexivity beta after record
reflexivity has reduced to the stable head. The same closed-registry policy is
used for generic consumers whose literal `eq_refl` pattern would otherwise be
erased: shared path units, `Path_sym_func`, `Core_incl_func`, `idtoiso_cat`,
and `idtoequiv_cat`. Do not extend this registry mechanically. Inventory a
real literal-reflexivity consumer, place the candidate at its owner, and test
both reduction orders and warning families. In particular, the active slice
does not make raw `sigma_path_refl` compute through J or PathSym; those steps
still depend on structural action and the separate fibrancy/dependent-J
architecture.

### Structural Sigma and PathRecord round trips

`sigma_path_decode_encode(p)` and `sigma_path_encode_decode(w)` prove the two
arbitrary path-characterization composites propositionally through generic J.
They are not open runtime eta rules. Constructor-exposed reflexivity computes
through the existing Sigma eliminator. Keep
`sigma_path_encode_decode_eq_refl` as the literal-reflexivity J base rather
than trying to reuse the stable `sigma_path_refl` theorem inside the nested
decode term: current proof-time unification does not propagate that comparison
transitively.

`PathRecord` needs no second Sigma normalization because its public equality
already reduces to `PathRecordPathView`. Its public encode/decode names are
transparent identity views, so both named round trips, shaped reflexivity, and
the dependent-tail observer compute directly and iterate through a nested
record. Preserve this distinction. Do not infer global eta, arbitrary
structural action, fibrancy, or additional structured-J computation from the
round-trip surface.

### Pi happly/funext equivalence

`PiPointwisePath(A,B,f,g)` is the diagonal family `Π x:A, f(x)=g(x)`.
`PiHapply(p)` observes a `PiPathView` path at `(x,x,refl_x)`, and
`PiFunext(h)` reconstructs its arbitrary related-input action by `ind_eqr` on
the base path. Point application of `PiHapply(PiFunext(h))` reduces to `h(x)`;
the whole functions do not receive a second eta-like runtime rule.

`pi_funext_eta(p)` derives `PiFunext(PiHapply(p))=p` with retained generic J.
Its reflexive base uses one two-rigid-head proof-time equation. Classify this
as a generic semantically justified structural law: the transparent lambda
presentation computes to the same reflexive term, whereas typed `eq_refl`
only confirms that the stable-head rule fires. Keep a conversion-negative
check and an arbitrary structured-Pi J negative check whenever this owner is
changed.

`pi_happly_by_inverse` supplies both propositional round trips explicitly.
The transparent theorem `is_equiv_map_by_inverse` converts such data into the
active contractible-fibre `IsEquivMap`. It constructs the contraction through
left-oriented J and half-adjoint coherence, then re-centres it at
`(g(b),right(b))`. This makes `type_equiv_from` and `type_equiv_right` compute
for `pi_happly_type_equiv`, while the contraction path remains propositional
and does not duplicate `pi_funext_eta`. Do not infer a generic runtime eta,
arbitrary structured J, or fibrancy from this package.

### Ordinary TypeEquiv algebra

`type_equiv_refl(A)`, `type_equiv_sym(e)`, and
`type_equiv_comp(eBC,eAB)` form the ordinary identity/inverse/composition
surface. Composition is in categorical order: its forward map is
`eBC.to(eAB.to(a))`. Symmetry and composition construct explicit
`EquivByInverse` values from `type_equiv_left`/`type_equiv_right` and route
their contractible-fibre evidence through `is_equiv_map_by_inverse`.

Keep these public packages transparent. Their forward maps and the generic
theorem's selected fibre centre make the inverse and right-path projections
compute without extra rules. The contraction proof is transparent but remains
propositional structure, so the derived left projection is only typed, not
identified by conversion with the separately constructed inverse law. Unit
and associativity compute on forward maps; do not promote package eta,
double-symmetry cancellation, or univalence-decoder coherence into this owner.

### Groupoid decoder coherence

`grpd_univalence_by_decoder(A,B)` is the proof authority for the two named
round trips `grpd_equiv_path_idtoequiv` and
`idtoequiv_grpd_equiv_path`. `grpd_univalence_from_decoder` converts that
specified-inverse package to the contractible-fibre `GrpdUnivalence` surface.
Its selected inverse, `grpd_univalence_selected_path`, computes to
`grpd_equiv_path`; this is the canonical capability agreement. Do not infer or
postulate the same agreement for an arbitrary legacy `ua_grpd(U,e)`.

`coe_grpd_idtoequiv` is generic-J transport coherence. Compose it with the
decoder right round trip to obtain the propositional
`grpd_equiv_path_coe(e,a)` square; `grpd_equiv_path_pi_action` is its first
pointwise Pi-universe consumer. Keep this square propositional until each
constructor path has a joining transport owner. The measured broad runtime
orientation competes with Product decoding: decoder-first produces
`coe(product_grpd_path(...))`, for which no component transport rule exists.
Do not promote that fold or disguise the missing Product branch with a
proof-time equation.

The category universe satisfies the directed-universe principle:

```text
Obj(Cat_cat) = Cat
Hom_cat Cat_cat A B = Functor_cat A B.
```

`Catd_cat K`, `Functord_cat`, and `Transfd_cat` are stable displayed facades
for the ordinary Cat-valued functor, transfor, and next-hom presentations.
Their category equalities are proof-time comparisons. Runtime computation
crosses the boundary through documented `Obj` and `Hom_cat` projections, so
neither ordinary nor displayed category heads are erased prematurely.

Generic identity, composition, functor action, and naturality are owned by the
global `id`, `comp_fapp0`, `fapp*`, and `tapp*` calculus. Specialized
`id_func`, `id_funcd`, `id_transfd`, `comp_cat_fapp0`, and
`comp_catd_fapp0` spellings are transparent public views or specialization
surfaces, not parallel owners. No separate ordinary `id_transf` constructor
exists.

### Section 4: ordinary internal hom and variance-separated actions

The represented covariant family is:

```text
hom_(F,W)[y] = Hom_A(W,F[y]).
```

Its postcomposition action is owned by the `hom_postcomp_*` hierarchy:

```text
(F[p])_*(g) = F[p] o g.
```

The represented contravariant family is primitive:

```text
hom_con(W,F)[y] = Hom_A(F[y],W).
```

Its precomposition action is owned by `hom_precomp_along_*`:

```text
(F[p])^*(h) = h o F[p].
```

`hom_int(F)` internalizes the represented source object; `hom_con_int(F)` is
the target-internalized mirror. Both expose their off-diagonal actions through
the rigid two-endpoint hom action:

```text
Hom_func(g,f)[h] = Hom_fapp0(g,f,h) = f o h o g.
```

Runtime normalization preserves the postcomposition, precomposition, and
rigid-`Hom` provenance. Opposite/identity presentations, independently
factored pre/post cuts, and one-inactive-endpoint degenerations are related by
narrow two-rigid-head `unif_rule`s. They are not global runtime folds.

`Hom_tele_func`, `Hom_func`, and `Hom_fapp0` retain focused runtime identity
and composition joins because projection can hide the literal generic
functor-action pattern.

`DefIso(C,x,y)` is the computational isomorphism package whose inverse cuts
cancel under the stable hom-action owner. `IsoEvidence` is its ordinary
propositional view.

### Sections 5–7: products, transfors, curry, and adjunctions

The product architecture includes:

- `Product_cat`, componentwise homs, projections, pairing, and symmetry;
- product-valued functor/transfor projection ladders;
- `Product_cat_func` for internalized product formation;
- `Product_map_func` for componentwise endpoint maps;
- `Eval_func`, fixed-object evaluation, semantic curry, and semantic uncurry;
- ordinary weakening, exchange, and contraction packages;
- an indexed `Adjunction(F,G)` relation with transparent left/right
  compatibility views, stable unit/counit observations, both component-level
  triangle cut-elimination laws, opposite-index swapping, and mate consumers.

Cat-valued horizontal action is expressed through the generic
`comp_prod_fapp1_func` / `comp_prod_fapp1_fapp0` owner and its projection
ladder. Remaining `comp_cat_cov_*` / `comp_cat_con_*` names are transparent
readability or Cat-only projection surfaces where they expose transfor
structure; they do not own a duplicate functor law.

### Sections 8–10: directed Cat-valued families, Sigma/Pi, and mixed variance

Active family constructors include fibre notation, pullback/reindexing,
constant/terminal/opposite families, displayed composition, section
categories, and internalized Pi over varying bases.

```text
Pi_cat(E) =proof-time Functord_cat(Terminal_catd K,E)
Pi_cat(Const_catd K A) ≃ Functor_cat K A  (proof-time comparison).
```

`piapp0_func` and `piapp0` remain semantic definitions over terminal-source
component evaluation; they are not parallel primitive heads. Their full hom
action projects through the generic `tdapp0_func` owner and caps through
`tdapp0_fapp0`, so `pi_hom_fapp0` computes without a Pi-specific bridge.
When that capped component has already hidden a literal generic
`fapp1_fapp0`, four documented projection-order joins recover the two
ordinary naturality orientations and their `tapp1(epsilon,id) ->
tapp0(epsilon)` degenerations. They accumulate to the existing
`tapp1_fapp0` normal form; they do not add a second naturality calculus.
These joins can share the inferred outer category with their surviving
ordinary `tapp1`/`tapp0` operand. Vertical composition is handled separately
as evaluator projection beta: a composite displayed transfor under
`tdapp0_fapp0` expands to the pointwise composite of its displayed
components. This is the same orientation as ordinary `tapp0_fapp0`; it joins
the path where generic `fapp1_fapp0(tapp0_func)` strictness accumulates first
with the path where both operands project first. It does not introduce a
second functoriality calculus.
Likewise, `piapp1_func` remains the terminal-source specialization of
`fdapp1_int_presheaf_arrow`; its first next action reaches
`fdapp1_int_hom_fapp0`, preserving the iterated-hom tower. Runtime evaluation
of a constant-family section still computes through `piapp0` to ordinary
`fapp0`. The hom action of the constant-section constructor is owned by
`Const_transfd_func` / `Const_transfd`, rather than by an ordinary transfor
category fold.

Sigma total objects are dependent pairs. A total arrow consists of a base
arrow and a fibre arrow:

```text
(p,alpha) : (x,u) -> (y,v)
alpha : E[p](u) -> v.
```

`sigma_arrow` and `sigma_transport_arrow` are defined through this hom
characterization. `sigma_map_func` uses the displayed internal-hom projection
ladder for its fibre action; `sigma_map_transf` exposes the next generic hom
action as an ordinary transfor between total maps. Arbitrary displayed
functors are lax rather than silently strict/cartesian.

`Functor_catd`, `Hom_catd`, and `Transf_catd` are mixed-variance family
constructors. Pointwise formulas do not replace their required base-arrow
actions.

### Sections 11–17: representables, dependent hom, and displayed action

The dependent-hom architecture is shared by Sigma homs, fibre transport, and
section action. Important owners are:

```text
Rep_catd
Edge_catd_func / HomPresheaf_catd_func
homd_ / homd_int
homd_src_func / homd_src_sec / homd_tgt_func
fib_cov_int / fib_cov_transf
tdapp1_int_func_transfd / fdapp1_int_transfd
fdapp1_int_* / tdapp1_int_*
```

The Sigma-map fibre projection ladder ends at:

```text
fdapp1_int_hom_fapp0(FF,p,u,alpha)
```

with the transported-identity specialization:

```text
fdapp1_int_hom_fapp0(FF,p,u,id) -> fdapp1_int_cell(FF,p,u).
```

This is the component-level displayed laxity normal form. A whole-transfor
laxity interface remains deferred.

Section 17 contains generic Sigma/Pi introduction/evaluation, constant
sections, ordinary structural logic, generic functor hom-action, section
pullback, and internal Pi action. Ordinary weakening `Const_func_func` is a
stable ordinary owner separate from the proof-time-only displayed
`const_section_func` facade.

### Section 18: Cat-valued profunctors and computational comparison

`Prof_cat(A,B)` is the primitive fixed-endpoint category of Cat-valued
profunctors on `A^op × B`; `Prof(A,B)` is its object classifier and `ProfMap`
is its fixed-endpoint vertical hom.

Active infrastructure includes:

- primitive `Unit_prof(A)` with direct rigid `Hom_*` base action;
- `Prof_reindex` through `Product_map_func(Op_func(F),G)`;
- readable representables `Hom_prof_along`, `Hom_prof`, `Companion_prof`, and
  `Conjoint_prof`;
- shaped cells/elements and internalized reindexing;
- primitive profunctor tensor and fixed-endpoint co-Yoneda maps;
- covariant and contravariant profunctor implication;
- fixed-endpoint eval/lambda inverse pairs;
- weighted cone/limit comparison and the dual weighted-colimit presentation;
- adjunction mate comparison and preservation of weighted limits/colimits;
- primitive directed join and its internally natural cross cell.

`ProfComparison(P,Q)` is a transparent compatibility name for
`DefIso(Prof_cat(A,B),P,Q)`. Its push/pull and evidence APIs route through the
generic `DefIso` and hom-action owners; it is not an independent eliminator
theory.

`Prof_tensor` and implication objects are symbolic primitives where the
current kernel lacks a general coend/coinserter quotient. Their checked beta,
reindexing, and closed-core interfaces state the active computational scope.

### Section 19: PathOut, path induction, and Eckmann–Hilton

For fixed `x : Z`:

```text
PathOut_Z(x) = Sigma (y : Z), Hom_Z(x,y).
```

The canonical arrow from `(x,id_x)` to `(y,p)` is the generic Sigma transport
arrow for the representable family. The primary path-induction package is the
telescope theorem `PathInd_transfd(Z)`; `PathInd_funcd(Z)` is derived by
`Sigma_transfd_funcd`.

The transitivity benchmark computes to ordinary composition. Nested telescope
terms stress the mixed-variance surface.

The first Eckmann–Hilton slice defines 2-endomorphisms of an identity 1-cell,
vertical and represented horizontal composition, the common-middle
equalities, and commutativity `EH_comm`.

## Core Ownership Invariants

### Runtime computation versus proof-time comparison

A rewrite rule selects a runtime normal form and participates in critical
pairs. A `unif_rule` helps elaboration/proof construction when neither side is
chosen as the runtime normal form.

Use:

```text
assert t ≡ u
```

for runtime conversion, and a typed reflexive equality:

```text
eq_refl(t) : τ(t = u)
```

to exercise a proof-time unification comparison. Do not infer runtime
joinability from a successful typed `eq_refl` probe.

### Displayed facade tower

The first three displayed heads remain stable:

```text
Catd_cat K
Functord_cat K E D
Transfd_cat K E D FF GG.
```

They compare at proof time with `Functor_cat K Cat_cat`,
`Transf_cat K Cat_cat E D`, and the corresponding ordinary iterated hom.
Their `Obj` projections compute toward the ordinary presentations, while their
`Hom_cat` projections expose the next displayed rung. Add direct comparisons
at every represented rung; do not rely on unification-rule transitivity.

`Pi_cat K E` is the stable section-category facade over the terminal-source
displayed rung. It compares directly at proof time with both
`Functord_cat K (Terminal_catd K) E` and the corresponding ordinary
`Transf_cat`, while its `Obj` and `Hom_cat` projections expose section objects
and the `Transfd_cat` next hom. The constant-family comparison with
`Functor_cat K A` is also direct; do not rely on comparison transitivity.

For sections over `Sigma_proj1_pullback_catd`, the distinct `Pi_cat` and
`Functord_cat` heads now support a direct proof-time uncurrying comparison.
Runtime subject reduction for `path_ind_sec -> fib_cov_transf` crosses the
general Pi/displayed object ladder and one measured join between ordinary
`Obj(Transf_cat)` classifiers. A direct specialized displayed-`Obj` rule is
redundant. The next `Transfd_cat` projection is retained for iterability.

### One generic owner for ordinary laws

The global `fapp*`/`tapp*` calculus is the sole owner of ordinary identity,
composition, functoriality, and naturality. A constructor-specific rule whose
only content is one of those laws indicates a missing internalized
functor/transfor owner or a detached projection.

Do distinguish a duplicate structural law from projection beta. Once a
stable evaluator head such as `tapp0_fapp0` or `tdapp0_fapp0` has erased the
literal generic evaluation-action pattern, a rule exposing the component of a
composite is the next rung of the evaluator ladder:

```text
tapp0(x,eta o epsilon)
  -> tapp0(x,eta) o tapp0(x,epsilon)
tdapp0(x,eta o epsilon)
  -> tdapp0(x,eta) o tdapp0(x,epsilon).
```

This pointwise expansion coexists with the generic strict-functor cut
`F[g] o F[f] -> F[g o f]` because the rules operate at different heads and
must be tested as a joining projection diamond.

A specialized projection-order bridge is exceptional but legitimate when:

1. a stable projection erases the literal generic-owner pattern;
2. an outer generic cut competes with that projection;
3. the two paths do not already join;
4. a focused owner-position probe establishes one canonical orientation.

Never install both orientations or generate such bridges mechanically.

### Hom variance and Došen cuts

When a term is already expressed through a stable hom-action owner, fold
consecutive actions to the one action indexed by the composite arrow:

```text
(F q)_*((F p)_*(g)) -> (F(q o p))_*(g)
(F p)^*((F q)^*(g)) -> (F(q o p))^*(g).
```

The second formula reflects contravariance: `q o p` first traverses `p`, then
`q`, while the induced precomposition actions are encountered in the reverse
endpoint order. These are the current runtime accumulation orientations.

Raw expanded compositions should normally remain `comp_fapp0` terms. Use the
existing proof-time bridges when a theorem compares them with stable hom-action
syntax. Add a raw runtime bridge only for a concrete consumer after testing
owner-first and projection-first reductions.

### Omega-friendly structure

Prefer functor-level folds over capped object rules when later hom action is
needed. A RHS that computes one selected cell can lose the functor object
required for the next dimension.

A formula `E[x] = ...` is only the object part of a directed family. A formula
`eta[x] = ...` is only a transfor component. Identify the base-arrow action and
off-diagonal/naturality action or explicitly record them as deferred.

## Before Editing The Kernel

1. Identify the semantic owner and whether the desired result is runtime or
   proof-time.
2. Search current declarations, rules, checks, examples, and the relevant plan
   with `rg`.
3. Decide whether a missing projection, transparent alias, or canonical
   endpoint fixes the problem before introducing a stable head.
4. Write the mathematical formula and the intended normal form.
5. Probe the candidate in a temporary full-file copy at its owning position.
6. Add a focused conversion assertion or typed `eq_refl` consumer.
7. Run a bounded quiet check; enable warnings when interactions are unclear.
8. Promote the smallest working change and add a durable diagnostic/example.
9. Update the task report when the architecture or a rejected orientation
   matters beyond the local rule.

## Rewrite And LHS Hygiene

### Minimal inferred slots

Keep reconstructible source/target/category/family arguments as `_` on rule
LHSs unless they are:

- the actual constructor discriminator;
- a composition-interface guard;
- required for subject reduction;
- a measured decision-tree/performance guard.

Observational classifier equations can make identity types with distinct
categories or endpoints decode to the same classifier. Whenever such an
equation is added, re-audit every beta whose LHS matches a proof constructor
while leaving those indices inferred. A quiet full check is insufficient:
instantiate a proof-dependent injective motive, compute the candidate term,
and verify that its normal form still inhabits the declared result. The generic
`ind_eqr` beta therefore repeats both its category and reflexive endpoint; this
is a subject-reduction guard, not optional overspecification. A proof-time
`unif_rule` cannot repair an ill-typed runtime beta.

Compound reducible inferred terms such as `fapp0 F x`, `Functor_catd ...`,
`Op_cat(Hom_cat ...)`, or transparent readability aliases can cause brittle
matching and conversion explosions.

Audit candidates with:

```bash
python3 scripts/audit_rule_lhs.py --show-kept
make audit-rules
```

Do not apply the scanner mechanically. Probe each `_` replacement. Mark a
measured exception immediately above the rule:

```text
// lhs-audit: keep SLOT[,SLOT] -- reason
```

The rule applies at rewrite-family scale, not only one slot at a time. Match on
the true stable discriminee and do not copy surrounding presentation wrappers
across sibling rules. For example, when `Op_func(_,_,F)` selects the case,
extra `Op_cat A`, `Op_cat B`, product-functor, or transparent-alias endpoints
should remain inferred unless the theorem genuinely distinguishes those
wrappers. A surface pattern that works for a variable endpoint may otherwise
stop matching when that endpoint normalizes to a product or functor category.

### Explicitness depends on the surface

Do not apply LHS minimality as a blind whole-file formatting rule. The four
main surfaces have different needs:

1. **Rewrite and unification patterns:** keep the stable discriminator
   explicit and reconstructible endpoint/category/family slots implicit.
   Apply this discipline to both sides of a `unif_rule`.
2. **Rule RHSs and defined-symbol bodies:** omit only arguments that are
   syntactically recoverable from the visible data. A fixed parameter that is
   not determined by the remaining arguments must stay visible even if an
   expected type happens to recover it in one probe.
3. **Theorem-style examples:** prefer the compact mathematical formula;
   projectionwise product/Sigma statements are often clearer and more robust
   than raw dependent-constructor equality.
4. **Diagnostic assertions:** keep canonical source/target endpoints explicit
   when the purpose is to expose the full `fapp1_func`, `fapp1_fapp0`, product,
   or displayed-action shape. Compactness must not turn a regression into a
   test of accidental endpoint inference.

This distinction preserves readability without erasing the information needed
for matching, subject reduction, or a stable diagnostic.

### Outer eliminators over active cuts

Treat an LHS such as:

```text
sigma_Fst(comp_fapp0(...))
sigma_Snd(fapp0(specialized_func,...))
```

as a high-risk commuting conversion. The outer projection and inner cut can
reduce in competing orders. Prefer:

1. an existing generic projection ladder;
2. a constructor beta rule;
3. a stable intermediate component;
4. an equation at the functor/transfor owner;
5. propositional evidence when judgmental computation is unnecessary.

A new commuting conversion requires a concrete consumer, focused checks for
both paths, an owner-position full-file probe, and warning classification.

### Canonical types and expected-type probes

Prefer reduced declared types and canonical endpoints:

```text
τ(Functord E D)
Hom_cat Z x y
Functord_cat E D
```

Use unreduced types only when the exact projection route is intentional and
document why.

A bare `assert t ≡ u` lets Lambdapi infer both sides independently. When a real
consumer supplies an expected type, test that typed shape explicitly before
concluding that conversion fails: first check the raw term at the intended
type `T` (or bind it with a temporary helper returning `T`), then test
conversion or typed reflexivity using that term. Keep a bare conversion
assertion only when both sides are expected to elaborate without contextual
type information.

Do not introduce decoded `*_TYPE` or parallel classifier heads merely to make
binders shorter. Such a head needs to join the existing category/classifier
reductions and can create a second semantic layer. Keep ownership at canonical
heads such as `Transf_cat`, `Functord_cat`, and `Product_cat`; use narrow
`Obj(...)` elaboration aids only when a measured consumer requires them.

### Constants and unification limits

A `constant` cannot head a rewrite LHS. Changing it to `injective` is a global
normal-form migration requiring full downstream, subject-reduction, warning,
and decision-tree review.

Unification rules are experimental and not reliably transitive. Prefer two
rigid heads or a stable intermediary. Apply inferred-slot hygiene to both sides
of a `unif_rule`.

### Stable heads and semantic equivalences

Add a stable head only when later rules need a visible constructor or a focused
probe establishes a real discrimination/performance boundary that a smaller
projection or canonical endpoint cannot solve. A surface-readable name alone
is not enough; transparent aliases should normally remain definitions.

Notation-only heads such as `Fibre_cat(E,k) = fapp0(E,k)` should not receive
broad injectivity or inversion rules: equality of two fibres must not generally
recover the entire family and index.

Likewise, familiar equivalences for maps out of the terminal category are not
global runtime computation by default:

```text
Functor_cat(1,A) ≃ A
Transf_cat(const(u),const(v)) ≃ Hom_A(u,v).
```

Prefer a consumer-local projection/fold through the existing section and
component owners. Promote a global terminal-source rewrite only after a
concrete consumer, both reduction orders, and the warning/subject-reduction
effects have been measured.

## Identity Normal Forms

Identity may appear as `@id`, the transparent `id_func`, `id_funcd`, or
`id_transfd` views, or a specialized projected identity. There is no separate
ordinary `id_transf` constructor. A rule for the generic surface does not
automatically match every proof-time-comparable category presentation.

Prefer narrow typed consumer rules or a coherent small specialization package
over broad global identity rewrites. The current middle-constrained generic
composition identity rules keep the shared middle object as the true cut
interface while inferring outer endpoints. Competing runtime identity
spellings are joined through the typed pre/post proof-time bridge; that
proof-time joinability is the selected criterion for this measured overlap.
Across the ordinary/displayed first-hom facade, identity-specialized
`tdapp1_int_*` consumers explicitly accept generic `id` at both
`Functord_cat(E,D)` and `Transf_cat(K,Cat,E,D)`. This is a typed façade package,
not a global rewrite between the two identity terms.

## Comment And Layout SOP

Put a brief comment immediately above most semantic symbols and nontrivial
rule families:

- public constructor: mathematical name/formula and primitive/defined status;
- stable head: projection formula and generic owner;
- transparent alias: explicitly label it an alias/view;
- rewrite: label beta, projection, cut, accumulation, or confluence join;
- unification: state that it is proof-time only;
- evidence symbol: state the proposition witnessed.

One comment may cover a cohesive `rule ... with ...` command.

Use compact horizontal layout for simple stable-head rules. Keep vertical
layout for nested endpoint formulas, deliberate explicit guards, and
diagnostic assertions that expose canonical endpoints.

Do not duplicate a semantic body in a readability helper. Route aliases
through the named semantic constructor.

## Development And Validation Workflow

### Bounded checks

```bash
EMDASH_TYPECHECK_TIMEOUT=60s make check
timeout 20s lambdapi check emdash3_2.lp
make check-warnings
```

If a quiet check times out or hides the interaction, rerun the smallest target
with warnings enabled before changing the architecture.

### Focused probes

```bash
scripts/probe.sh tmp/probes/name.lp
scripts/explain_failure.py logs/probes/name.log
```

Ordinary experiments belong under ignored `tmp/probes/`. Move durable
reviewer-facing computations to `examples/`.

### Warning and decision-tree diagnosis

```bash
make warning-summary
scripts/explain_failure.py --warning logs/warnings/latest.log
scripts/decision_tree.sh SYMBOL
scripts/decision_tree.sh --png /tmp/tree.png SYMBOL
```

Use the smallest Lambdapi debug flag set: `u` unification, `c` conversion, `q`
rewriting, `w` weak-head normalization, `s` subject reduction, `k` local
confluence, `d` decision-tree compilation, and `i` typing. Never use
`--no-sr-check` for promoted code.

### Catalog, examples, CI, and health

```bash
make examples
make catalog
make toc
make ci
make health
```

`make catalog` can be non-strict during exploration; `make ci` requires a fresh
catalog and zero unclassified checks. `make toc` requires the header source map
to match every formal section/subsection heading exactly and is also part of
CI. Run `make health` after meaningful architecture/check changes.

### Type-aware search

Use `rg` for ordinary discovery and:

```bash
scripts/lambdapi_search.sh 'name = hom_int'
scripts/lambdapi_search.sh 'type >= Prof_imply_cov'
```

for normalization/type-aware search.

## Current Deferred Boundaries

The following remain explicit future work rather than hidden assumptions:

- full general dependent adjunctions `Sigma_F ⊣ F^* ⊣ Pi_F`, including the
  planned `Pi_f`/comma-category infrastructure;
- displayed structural logic and remaining product/curry compatibility;
- semantic uncurry action on arbitrary transfors;
- whole-transfor displayed laxity beyond `fdapp1_int_cell`;
- the arrow action of `sigma_intro_tapp0_func`;
- off-diagonal `tapp1_*` projections for `sigma_map_transf` beyond its current
  point-component computation;
- a fully internalized general coend/coinserter semantics for profunctor tensor;
- general tensor associativity/coherence and complete co-Yoneda equivalences;
- dependent elimination and semantic collage construction for primitive join;
- specialized higher `fapp1*` projections of `Hom_tele_func` beyond current
  demand;
- raw unreified-path observer computation, reverse pointwise-to-coherent-core
  assembly, consumer-led core-universe inclusion functors, and full legacy
  decoder API retirement beyond the selected native direct-univalence MVP;
- general higher-inductive categories and pushouts;
- a finalized parser/surface language;
- module splitting of the single kernel file after comment/section boundaries
  stabilize.

Consult `INDEX.md` for the active plan owning a deferred item. Do not copy a
constructor-local law from an older plan without first rechecking the current
generic owner.

## Retirement And Recovery Policy

The v3.1 and v2 baselines are retired from normal checking and design work.
Their surviving lessons are represented in the active source, this SOP,
Foundations, canonical syntax, current plans, and the v2 retirement audit.

Infinity Codex response archives under `tmp/ai-responses/` are recovery
evidence only. Authority remains:

```text
active code/SOP -> active plan and side-task ledger
                -> explicitly linked decision responses -> raw archive.
```

After compaction/interruption, re-read the active authorities and task plan,
inspect staged/unstaged diffs, relocate symbols with `rg`, and run a bounded
baseline check before continuing.
