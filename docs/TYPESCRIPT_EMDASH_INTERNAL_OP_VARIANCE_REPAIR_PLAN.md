# Internal Opposite: Bounded Variance Repair Plan

Date: 2026-09-08

Status: active isolated design/probe tranche; no kernel migration promoted

Parent: [bounded long-exact homology and book](TYPESCRIPT_EMDASH_BOUNDED_LONG_EXACT_HOMOLOGY_AND_BOOK_PLAN.md)

Finding: [confirmed internal-op diagnostic](TYPESCRIPT_EMDASH_INTERNAL_OP_VARIANCE_DIAGNOSTIC.md)

## Objective And Scope

Correct the higher variance of internal opposite while retaining the existing
directed categories, whole functor/transfor action, and legitimate local
`Op_cat`, `Op_func`, and `Op_transf` observations. This is a prerequisite of
the unchanged long-exact goal, not a replacement for its remaining homology,
proof-CAS, and book work. Keep baseline `054b43bd` and all checkpoints.

The preceding clarification turn restated the confirmed diagnostic; it did
not repair the encoding. This tranche must add discriminating implementation
evidence, not merely repeat the soundness notice.

## Small Foundational Candidate

For the current strict working interpretation, first probe a dimension-two
opposite with unchanged objects and 1-arrows:

```text
Obj(Co₂(C)) = Obj(C)
Hom_Co₂(C)(x,y) = Op(Hom_C(x,y))
Co₂(Co₂(C)) = C.
```

The existing generic composition at the opposite Hom then reverses vertical
2-cell composition. Ambient 1-cell composition is unchanged. The corresponding
functor `Co₂(F)` has unchanged object/arrow action and whole Hom action
`Op(F₁(x,y))`. This expresses the dimension shift directly in the existing
iterated-Hom architecture; no new cell grammar is required.

The candidate corrected internal package has type

```text
op : Co₂(Cat) → Cat
op[C] = Op(C)
op[F] = Op(F)
op₁(A,B) : Op(Functor(A,B)) → Functor(Op(A),Op(B)).
```

Its transformation action must project to the existing `Op_transf` with
reversed endpoints. Preserve the whole hom functors at both stages and test
their next action, not just their capped components. Initially use a distinct
probe name so the active kernel is not partially migrated.

This is not a claim that finitely many projection checks establish all
omega/lax coherence. In particular, dualizing a lax transformation may change
its lax/oplax profile. Do not import the parallel strictness migration or hide
this question behind arbitrary invertibility assumptions. The existing
strict branch is the first qualification boundary.

## Omega Depth, Not A Two-Dimensional Truncation

The proposed `Co2_cat` reverses exactly dimension 2. Its Hom rule unfolds to

```text
Hom_(Hom_Co₂(C)(x,y))(f,g) = Hom_(Hom_C(x,y))(g,f),
```

and every further Hom keeps its original orientation. Thus dimension 3 and
all higher dimensions remain present. Both `Op_cat` (dimension 1 only) and
`Co2_cat` (dimension 2 only) are instances of dimension-selected duality.
They are not the odd/even dualities often also called `op`/`co` in the
omega-category literature. Do not change that convention silently.

The scalable mathematical rule for a set S of positive dimensions is

```text
S↓ = { n ≥ 1 | n+1 belongs to S }
Hom_(D_S C)(x,y) = D_(S↓)(Hom_C(y,x))  when 1 belongs to S,
Hom_(D_S C)(x,y) = D_(S↓)(Hom_C(x,y))  otherwise.
```

This follows the existing iterated-Hom architecture. For the strict
cartesian transformation interpretation, an n-transformation contributes an
(n+1)-cell of the category universe, so the internal universe source must
shift the reversed dimensions up by one. In particular `{1}` in the objects
requires `{2}` in the universe, which is exactly the proposed Co₂ source.
This is the mathematical justification to qualify, not a claim that all
universe rules have already been migrated or all higher computations checked.

Primary references reviewed:

- Ara and Guetta, [Lax functorialities of the comma construction for
  omega-categories, sections 2.4 and 2.22](https://arxiv.org/pdf/2503.08832v3):
  strict higher transformations and duality in a set of dimensions.
- Ara and Maltsiniotis, [Un theoreme A de Quillen pour les infinity-categories
  strictes II, sections 4.6–4.8](https://www.i2m.univ-amu.fr/perso/dimitri.ara/files/thmAII.pdf#page=32):
  dimension-selected, odd, even and total dualities, and the exchange of lax
  and oplax internal Homs under the odd/even dualities.

The latter formulas use the authors' odd/even conventions, not emdash's
dimension-1-only `Op_cat`. They warn against identifying all possible
transformation profiles; they are not a ready-made proof of a dimension-1
lax-profile implementation. The goal remains full omega-dimensional action,
with no truncation or collapse of arbitrary higher cells.

## Propagation Is Part Of The Repair

An arbitrary directed family `E : K → Cat` cannot simply retain its base and
be postcomposed with the corrected `op`. The candidate is instead

```text
Eᵒᵖ : Co₂(K) → Cat
Eᵒᵖ = op ∘ Co₂(E).
```

At objects and base 1-arrows this retains the desired familiar fibre formulas;
at base 2-cells it exposes the formerly missing reversal. A same-base interface
needs an explicitly justified base/coherence restriction or comparison.
Do not add an unrestricted `K → Co₂(K)` cast: that would recreate the defect.

For the same strict transformation interpretation, the candidate whole family
operator must also expose the shifted variance of transformations between
displayed maps:

```text
Op_catd_func(K) : Co₂(Catd(K)) → Catd(Co₂(K)).
```

It sends a displayed map `FF : E → D` to a displayed map between the new
opposite families, with component `Op_func(FF[k])`. A transformation between
such displayed maps reverses, because its components are ordinary
transformations of fibre functors. This signature is now implemented by the
separate whole-family prototype below, not yet by the active kernel.
The generic Co₂ action on functor categories should own that construction,
rather than another untyped same-base identification.

Before migration, inventory the actual uses of `op`, `Op_catd`,
`Op_catd_func`, and `Op_funcd`. In particular test whether the old family
declarations can recreate the problematic covariant operation independently
of the literal `op` name. A rename/type change of one symbol is not sufficient
if another unrestricted constructor reinstates the same action.

## Execution Ledger

| Row | Status | Required evidence |
|---|---|---|
| OP-REPAIR-1 | baseline reproduced | original native-empty fixture accepted under the unchanged core; exact source and log retained |
| OP-REPAIR-2 | isolated prototype checked; not promoted | Co₂ category/functor projections, corrected whole op action, correctly directed transformation computation and a rejected wrong-direction application |
| OP-REPAIR-3 | family-only counterexample confirmed; propagation inventory still open | same-base family reconstruction control and source-level dependent-owner inventory |
| OP-REPAIR-3A | whole-family prototype checked; not promoted | derive the correctly based operator, displayed map and reversed displayed-transformation action, with genuine base-2-cell computation and retained next Hom action |
| OP-REPAIR-4 | isolated full-copy migration exposes negative-section and Homd-target boundaries | smallest coherent owner-position migration that removes the bad covariant surfaces and qualifies their legitimate consumers |
| OP-REPAIR-5 | pending | positive opposite regressions, exact variance-negative fixture, warnings/SOP/health qualification and downstream homology consumer |

The append/import probes for row 2 establish local types and observations only:
the imported old kernel still contains the defect. They are not a consistency
proof or evidence that the active signature has been repaired. A final negative
must run against the migrated owner, not an unrelated import, syntax error,
missing symbol, or timed-out check.

## Checked Prototype And Family-Only Control

The durable non-library candidate and reviewer are
[`internal_op_co2_prototype.lp`](../emdash2/audits/internal_op_co2_prototype.lp)
and [`internal_op_co2_prototype_checks.lp`](../emdash2/audits/internal_op_co2_prototype_checks.lp).
They add no rules to the active kernel or positive source registry. The
prototype has twelve runtime rules, no unifier, and no primitive equality
witness. The two whole action views and opposite-family construction are
transparent definitions.

The eleven positive observations cover the second-Hom direction, unchanged
third-Hom direction, involution, whole Co₂ action, correct functor and
transformation projections, retained next whole hom action, and the original
fibre/1-arrow formulas at the corrected family base. The direction-correct
point-functor construction reduces to the original input arrow. Two negative
checks reject the swapped transformation type and the old diagnostic's
wrong-direction application. An initial reviewer typo used `@Transf` without
its category arguments and was rejected as an ill-formed expected type; it
was corrected before the passing run and is not counted as variance evidence.

The minimal Co₂ prototype passed subject reduction in
`hint_internal_op_co2_foundation-20260908-142422.log`. Its final ignored
reviewer passed in `hint_internal_op_co2_checks-20260908-142859.log`.
The strict inferred-LHS-slot audit reports zero unreviewed compound slots.
The tracked reviewer passes in
`internal_op_co2_prototype_checks-20260908-143113.log`; the warning-enabled
run is `internal_op_co2_prototype_checks-20260908-143245.log`. Its imported
core contributes the unchanged 1,125 critical-pair / 157 pattern reports.
The append-only prototype contributes 49 critical pairs and no new pattern
reports: four identity-projection pairs, sixteen composition/self pairs,
ten action/self pairs, eighteen composition/action pairs, and one Co₂-functor
involution pair. ANSI-stripped strict parsing accounts for all 1,174 pairs.
These are interaction families to qualify at the eventual owning position,
not a warning-count veto or a global confluence claim. The initial direct
parse of the colored log failed its location parser; stripping color restored
the expected complete classification without rerunning Lambdapi.

Active-reference and report-lifecycle/header checks pass. Registry inspection
confirms neither prototype file is a registered positive target. No kernel,
CAS, book source, generated catalog, or health snapshot changes in this
audit-only tranche; no unrelated aggregate is run.

A full copied-core control comments out the original `op` declaration and
all six rules that directly refer to it, while retaining the separate
same-base `Op_catd` formation, fibre and capped-action rules. In that core,

```text
reconstructed_covariant_op : Functor(Cat,Cat)
reconstructed_covariant_op = Op_catd(id_Cat)
```

still yields a closed native-empty witness by the original construction.
The copy and consumer are `hint_internal_op_family_only_core.lp` and
`hint_internal_op_family_only_empty.lp`; the bounded successful reproduction
is `hint_internal_op_family_only_empty-20260908-142523.log`. No new axiom,
rewrite or unification rule is needed by that control. The original unchanged
fixture was also rerun in `internal_op_empty_reproducer-20260908-141839.log`.

Therefore the family base change is necessary, not a speculative extension
of the repair. Keeping the old unrestricted same-base interface would undo
the correction even if no source expression mentioned the literal `op`.

## Whole-Family Prototype And Its Higher Action

The preceding goal turn was progress: checkpoint `e4486791` recorded the
dimension-shifted prototype and independent family-only counterexample.
The next scoped baseline passes in
`internal_op_co2_prototype_checks-20260908-143810.log`.

The new durable non-library source and reviewer are
[`internal_op_co2_families_prototype.lp`](../emdash2/audits/internal_op_co2_families_prototype.lp)
and [`internal_op_co2_families_checks.lp`](../emdash2/audits/internal_op_co2_families_checks.lp).
One new fundamental whole owner supplies

```text
Co₂_functor_cat_func(A,B) : Co₂(Functor(A,B)) → Functor(Co₂(A),Co₂(B)).
```

Its object action is `Co2_func`; its transformation view is a transparent
alias of ordinary functor action, with point and whole off-diagonal
projections. The opposite-family operator is a transparent composite of this
functor and ordinary postcomposition by `op_co2`. The family, displayed-map,
Hom-functor, displayed-transformation functor and transformation point views
are derived. There is no new primitive `Op_catd_func`, `Op_funcd` or
`Op_transfd` mirror in this prototype.

The checked computations recover the original opposite fibres, map
components `Op_func(FF[k])`, and off-diagonal components
`Op_func(tapp1(FF,p))`. Displayed-transformation components reduce to
`Op_transf(eta[k])`. A genuine `a : p ⇒ q` in an arbitrary base Hom also
computes: action of the retained whole off-diagonal functor, with endpoints
q,p in the opposite Hom, returns the opposite of the original action on a.
After transformation projection, the next whole Hom action remains typable.
Both the wrong transformation direction and an unrestricted same-base family
type are rejected. No manually stored square or inverse witness is added.

### Endpoint, normal-form and projection decisions

1. The first composite used ordinary functor-category endpoint annotations
   while its public type used the stable Catd facade. The generic composition
   projection repeats its endpoints, so this prevented the displayed-map
   definition from checking. Aligning those annotations resolved the failure
   without adding a rule.
2. The whole operator's object normal form is `hom_postcomp_fapp0`, not raw
   `comp_cat_fapp0`. The prototype `op_co2_catd` now uses that existing owner.
   The raw-composition view has a checked typed-reflexivity path through the
   existing generic usability unifier. No new unifier, primitive equality,
   opacity or global postcomposition-to-composition fold is introduced.
3. Displayed-transformation components required two further projection rules:
   Co₂ acting on modifications, and generic Cat-valued postcomposition of a
   modification. The latter is not op-specific; on eventual migration it
   belongs with component evaluation/whiskering. Its RHS uses the original
   modification component and the postcomposing functor's whole Hom action.
4. An `id _ _` discriminator in that postcomposition probe fails subject
   reduction because its fapp0/fapp1 actions remain unresolved
   (`hint_internal_op_co2_transfd_checks-20260908-144943.log`). The literal
   universe identity is a measured computation/SR guard. With it, the
   component computes in
   `hint_internal_op_co2_transfd_checks-20260908-145018.log`. The actual base
   2-cell test passes in `hint_internal_op_co2_base_two_cell-20260908-145322.log`.

The extension adds one primitive whole functor, six runtime projection rules
and transparent observations. It adds no generic identity/composition laws,
changes no existing accumulation orientation, and has no alias-headed rule.
Its strict LHS audit reports no unreviewed compound inferred slots.

The tracked family reviewer passes eight positive and two negative checks in
`internal_op_co2_families_checks-20260908-145613.log`. All eleven earlier
positive and two negative prototype checks still pass in
`internal_op_co2_prototype_checks-20260908-145615.log`. The scoped ignored
warning run gives 1,194 critical pairs / 157 pattern reports, with complete
strict parser accounting
(`hint_internal_op_co2_transfd_checks-20260908-145323.log`). These are local
append-only tests, not a completed kernel migration or consistency proof.
The final tracked warning run confirms the same counts in
`internal_op_co2_families_checks-20260908-145838.log`. Relative to the first
Co₂ prototype, the family extension adds twenty pairs and no pattern
reports: four component/action groups of three each, four composition/
component pairs, and four component/self pairs. All pair structures parse;
owning-position joining remains a separate migration gate. Active-reference,
report-lifecycle and strict LHS checks pass, and registry inspection confirms
the new audit files are not positive library targets. No unrelated aggregate,
kernel/CAS source change, catalog/health regeneration or book rendering is
performed for this non-library checkpoint.

Next: inventory and migrate the active same-base consumers as a coherent
slice, retaining the corrected base in object and whole-action types. Do not
erase `Co2_cat(K)` through an unrestricted cast to recover old signatures.
Qualify generic identity/composition projection orders at the eventual owner
positions, rerun the empty-type negative against that migrated kernel, and
return to the homology consumer. The active signature still admits the
diagnostic; the full long-exact goal is not complete.

## Migration Experiment: Distinguish Pointwise Opposite From Negative Sections

Checkpoint `7e190956` completes the preceding isolated family prototype, not
the kernel migration. A full copied-core migration is now in
`tmp/probes/hint_internal_op_migrating_core.lp`; the active kernel is unchanged.

The first source failure is the `Hom_catd` fibre projection's old `piapp0 K`
annotation. Its negative section now belongs to a family over Co₂(K).
The adjacent constant-Cat reduction needs a stronger review: it expects that
section to supply an ordinary family over Op(K), not Op(Co₂(K)). Blindly
changing endpoint annotations does not justify that semantic interface.

Before choosing a replacement, test the constant-family requirement directly:
negative sections of const_K(C) should have the ordinary contravariant
functor interpretation Op(K) → C. A total dual reverses all positive
dimensions; its universe shift reverses dimensions 2,3,... . The candidate
uses those two dualities specifically for the negative-section interface,
without changing the meaning of the existing dimension-1 `Op_cat` or the
dimension-2 Co₂ prototype. Reject any candidate that only checks by equating
K with Co₂(K), truncating the base, or adding an arbitrary inverse witness.
This is a next local mathematical/typing experiment, not a selected repair
of `Hom_catd`, `homd_int`, Sigma, or the homology representation.

### Full-copy result and the distinct dualities

The copied kernel accepts the corrected Co₂/universe/family owner declarations
and reaches the mixed-Hom section. Its first failure is the old negative
`piapp0` base (`hint_internal_op_migrating_core-20260908-150939.log`). After
updating that annotation and its adjacent transfor counterpart, it reaches
the constant-Cat mixed-Hom reduction and fails subject reduction with
`K ≡ Co2_cat(K)` unsolved
(`hint_internal_op_migrating_core-20260908-151604.log`). These are concrete
source-position failures, not a timeout or warning-count rejection. This
partial full copy is not a complete migrated kernel and is not promoted.

The durable [total-duality/negative-section prototype](../emdash2/audits/total_duality_negative_sections_prototype.lp)
tests a different role of duality, without renaming the existing Op:

```text
All(C)       reverses dimensions 1,2,3,...
CoAll(C)     reverses dimensions 2,3,4,...
Hom_All(C)(x,y)   = All(Hom_C(y,x))
Hom_CoAll(C)(x,y) = All(Hom_C(x,y))
All(CoAll(C)) = Op(C).
```

The corresponding `all_op : CoAll(Cat) → Cat` and whole `CoAll_func` give a
derived `All_catd(E)` over CoAll(K). For a constant family, an actual section
of that family has the existing Pi-usability view
`X : CoAll(K) → All(C)`. Applying the whole All functor yields precisely
`Op(K) → C`, including its higher-dimensional directions. This restores the
required constant-Cat reduction of a candidate mixed-Hom interface. The
analogous pointwise-1-opposite route instead gives `Op(Co2(K)) → C`; the
comparison with `Op(K) → C` is rejected for arbitrary K.

The prototype checks eight positive observations and one negative, including
actual family fibre/arrow computation, the existing Pi constant-family
interface, the mixed-Hom constant reduction and retained dimension-3
orientation. Log:
`total_duality_negative_sections_prototype-20260908-152845.log`.
Its general mixed-Hom formation is still a primitive candidate, not a derived
proof that this is the correct arbitrary-family replacement. Full coherence,
all higher projection ladders, and the coupled dependent-Hom target remain
unqualified. Do not confuse this local successful constant case with a repair
of the complete foundation.

### The presheaf target is a separate coupled boundary

The [presheaf variance-boundary probe](../emdash2/audits/internal_op_presheaf_variance_boundary.lp)
follows the existing Rep/Edge/Presheaf composition with corrected whole
operators and the commuting dimension-1/dimension-2 dualities. It derives

```text
Edge_corrected : Op(Co2(Z)) → Catd(Co2(Z))
HomPresheaf_corrected : Co2(Z) → Catd(Op(Co2(Z))).
```

Both original point formulas compute: Hom_Z(x,y)ᵒᵖ and its Cat-valued
presheaf category. But the existing `Homd_target_section_catd` body then
expects its other input over Co2(Z), while the supplied E is over Z. The
probe rejects that old input and accepts an explicitly supplied correctly
based E2. The latter is only a positive constructor control; it does not
postulate a canonical E ↦ E2 or authorize new assumptions in the homology
development. Three positive and one negative checks pass in
`internal_op_presheaf_variance_boundary-20260908-152847.log`.

Thus a mechanical base-annotation migration is not enough. The next owner
decision must reconstruct the dependent-Hom target with jointly correct
variances, preserving the original supplied family, rather than invent an
unrestricted same-fibre regrading or erase Co2(Z) with an equality/unifier.
This does not prove that no suitable internal target exists; it identifies
the exact current target expression that cannot simply be reused. Preserve
the total-duality candidate and earlier pointwise Co₂ prototypes as distinct
design evidence. The original long-exact/CAS/book objective remains intact.

### Scoped validation for these migration controls

The tracked total-duality warning run passes at 1,212 critical pairs / 157
pattern reports (`total_duality_negative_sections_prototype-20260908-153210.log`).
Relative to its imported Co₂ prototype, its 38 additional pairs comprise
three All/CoAll interactions, ten action/self interactions, twenty-four
composition/action interactions and one All-functor involution interaction.
The presheaf boundary passes at 1,196/157
(`internal_op_presheaf_variance_boundary-20260908-153211.log`); its two new
pairs concern commuting Co₂ with the ordinary Op. Both inventories parse
completely. These are measured interaction families, not global joining or
consistency claims and not a warning veto.

Both strict LHS audits report zero unreviewed compound inferred slots. Active
reference and report-lifecycle checks pass; registry inspection confirms the
two new files are not positive library targets. No active kernel/CAS source,
book source, catalogue or health snapshot is changed, and no unrelated
aggregate is run. The failed full-copy migration remains ignored, with its
exact source and logs retained as recovery evidence.

## Validation And Handoff

Use ignored probes first and at most 90 seconds per Lambdapi invocation, with
ordinary subject-reduction checking. Put candidate rules at their intended
owning positions before promotion. Keep inferred endpoint slots free of
compound guards except for measured discriminators. Preserve mapped-arrow
composition orientation; no broad new cut or proof-time equality may hide an
ill-typed opposite action.

Documentation/audit checkpoints use exact diff and the owning link/lifecycle
checks, not repository aggregates. Kernel promotion requires its scoped
warning comparison, LHS audits and affected consumer checks under the parent
SOP. Local validated checkpoints are authorized; no push, merge, publication,
history rewriting, or worktree cleanup is authorized.
