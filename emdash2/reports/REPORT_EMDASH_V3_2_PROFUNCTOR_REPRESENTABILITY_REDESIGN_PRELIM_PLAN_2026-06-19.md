# EMDASH v3.2 Profunctor Representability Redesign Preliminary Plan

Date: 2026-06-19
Last reviewed: 2026-06-22

Status: active incremental redesign. The coherent Phase 1 foundation
(`ProfMap` and ordinary `IsoEvidence`) and the first Phase 2 propositional
evidence/representability algebra are active. Covariant implication is now
internalized as a complete unary functor and as a direct mixed-variance
bifunctor in its varying profunctor and contravariant weight. The ordinary
ambient adjunction mate and the propositional right-adjoint preservation
theorem are also active. A dedicated computational `ProfComparison` algebra
now owns the established weighted-limit API. It makes inverse
universal-property operations compute on dedicated eliminator heads and
forgets to ordinary `IsoEvidence`. The initially proposed generic
judgmentally cancelling `StrictIso` layer and a later profunctor-specialized
variant based on cancellation under `Prof_comp_transf` both failed active
critical-pair audits and were not promoted. The old primitive weighted-limit
witness and theorem-specific preservation calculus have now been replaced by
transparent public aliases of the comparison implementation. The remainder of
this report is still provisional.

The recommendations below are not a commitment to reproduce the obsolete
`cartierSolution13.lp` presentation. They are reassessed from the traditional
enriched-category and profunctor-equipment semantics, the current v3.2 kernel,
and focused Lambdapi feasibility evidence. Every proposed interface remains
subject to adjustment, replacement, or a prerequisite kernel side task as
implementation probes expose better normal forms.

## Correction: Generic Functor Ownership, 2026-06-22

The earlier implication checkpoints below recorded dedicated
`Prof_imply_cov_func*_transf` action heads with local identity/composition
rules. That architecture is superseded.

Ordinary functoriality and naturality must be owned exclusively by the global
`fapp*`/`tapp*` calculus. A local rule that merely states preservation of an
identity or composite is evidence that the operation or one of its variables
has not been internalized far enough.

The active correction is:

```text
Prof_imply_cov_func2
  : Prof(A,X) x Prof(B,X)^op -> Prof(A,B);

Prof_imply_cov_fixed_weight_func(Q)(O) = (O,Q);

Prof_imply_cov_func(Q)
  := Prof_imply_cov_func2 o Prof_imply_cov_fixed_weight_func(Q).
```

The unary semantic composition is opaque, as with `Hom_prof_func`, so its
generic identity/composition cuts remain visible. Its object projection still
computes. The fixed-endpoint equipment-cell action folds directly to the
generic capped action of `Prof_imply_cov_func2`; the four dedicated action
heads and all their local functor laws were removed.

This correction also exposed a general kernel omission: `id_funcd` is the
canonical identity normal form in `Catd_cat`, so the global strict-functor
identity law needs one Catd-specialized bridge, parallel to the already-active
global Catd composition bridge. The bridge is generic for every functor out of
`Catd_cat`; it is not an implication-specific law.

## Deferred Internalization Side-Task Ledger

The generic-owner audit also found older clusters whose local identity or
composition rules look like ordinary functoriality stated at a specialized
head. They are audit and possible-migration candidates, not current blockers.
This classification does not presume that every existing rule is redundant or
should be removed. A rule may instead be a necessary projection bridge, a
chosen semantic normal-form conversion, or a genuine Došen-style cut. Do not
refactor all of them preemptively. Resume one cluster when the named consumer
first needs to extend it, or earlier only when a focused probe shows that its
present ownership blocks the active slice.

| ID | Existing cluster | Expected ownership direction | Resume trigger |
| --- | --- | --- | --- |
| `INT-COMP` | `comp_cat_cov_transf`, `comp_cat_con_transf`, and their local identity laws | Keep Cat-specialized component/off-diagonal heads when they expose genuine transfor structure, but obtain ordinary identity/composition from the existing composition functors and generic `fapp*`/`tapp*` projections. | Direct tensor-implication eval/lambda naturality, or any broader ordinary full-naturality extension, needs a new law on these heads. |
| `INT-OP` | `Op_func`, `Op_transf`, `Op_funcd` | Reassess `Op_func` as the arrow projection of `op`, `Op_transf` as the next hom-action of that owner, and `Op_funcd` as action owned by `Op_catd_func`. Retain readable projection heads and local normal-form bridges when focused reduction-order evidence shows they are computationally intentional. | New duality or univalence work would otherwise add another local identity/composition/naturality rule. |
| `INT-PROF-FUNC` | `Prof_func_transf` and its direct identity/composition rules | Seek an internalized representable-equipment action in the varying functor, potentially displayed or total because both endpoint legs vary. `Prof_func_transf` may remain its readable projection. | General co-Yoneda or join/collage work must compute functor-induced cells beyond the currently checked cases. |
| `INT-OP-PROF` | `Op_prof_transf` and its direct involution/identity/composition rules | Internalize base-swap duality on an appropriate category or displayed/total category of profunctor cells; project the current stable head from that owner. | Extended profunctor-cell duality, semantic pullback comparison, or colimit duality needs additional cell laws. |
| `INT-EQUIP-COMP` | Local identity/composition laws for `Prof_comp_transf` and related equipment operations | Make ordinary laws consequences of an internalized category/functor of equipment cells once its varying bases and endpoints have a coherent owner. Preserve only genuine equipment beta/eta or cut-elimination laws. | A bicategory/equipment coherence layer, tensor associativity, or generalized cell composition requires laws beyond the current bounded API. |

For each resumed side task:

1. Recover the mathematical operation independently of its current stable
   head and identify all variables that must vary internally.
2. Classify each questioned rule as a redundant generic law, a projection or
   normal-form bridge, a genuine beta/eta or cut law, or an unresolved overlap.
   Do not infer the classification from its syntax alone.
3. Probe the smallest `Functor`, `Transf`, displayed, or total-category owner;
   do not begin by copying the local law to a new name. Test both the generic
   and specialized reduction paths on the actual downstream consumer.
4. Route readable heads through generic projections where that produces the
   intended normal form. Remove only laws that the generic calculus
   demonstrably subsumes; explicitly retain and document rules whose
   projection or cut behavior is needed.
5. Add object, full hom-action, capped action, identity, and composition
   diagnostics appropriate to the owner. Compare warning-enabled checks before
   and after the migration.
6. Promote the slice only when `make check`, the LHS audit, catalog/health
   refreshes, and `make ci` pass. Record any deliberately retained stable head
   and why its behavior is more than generic functoriality.

For example, the active rule

```text
Op_func(F o G) -> Op_func(F) o Op_func(G)
```

does not state the ordinary functoriality of `Op_func(F) : A^op -> B^op` on
arrows inside `A^op`; that behavior belongs to generic `fapp*`. It states that
the opposite operation sends a composite functor to the composite of the
opposite functors. Equivalently, it exposes the composition behavior of the
arrow projection of the higher functor `op : Cat -> Cat`. Its implementation
orientation expands that projection to the chosen ordinary-functor
composition normal form, rather than performing the generic inward
functoriality cut. It is therefore presumptively an intentional projection and
normal-form bridge. `INT-OP` must not perturb it without a concrete conflict.
Any later audit must distinguish these categorical levels and compare both
reduction orientations, the duality consumers that need the expanded form,
and critical-pair behavior. A side task may conclude that an existing rule
should be retained with better ownership documentation rather than changed.

The active next slice remains direct Došen-style naturality for the primitive
tensor-implication eval/lambda bijection. `INT-COMP` becomes a prerequisite
only if that focused probe genuinely requires extending the composition
transformation cluster; otherwise it remains deferred. The other four tasks
are tied to the later triggers in the table.

## Implementation Checkpoint: 2026-06-21

The first bounded implementation slice started from clean baseline commit:

```text
422c0df8b76921eb00d41ef141a3b6d02bb3dcbc
```

The following coherent infrastructure is active:

```text
ProfMap(P,Q) := Obj(Hom_cat(Prof_cat(A,B),P,Q));

IsoEvidence(C,x,y);
iso_evidence_to;
iso_evidence_from;
iso_evidence_left;
iso_evidence_right;
iso_evidence_refl;
iso_evidence_sym;
eq_sym;
eq_ap;
comp_assoc;
iso_evidence_comp;
iso_evidence_fmap;
Companion_prof;
Conjoint_prof;
IsRepresentedBy_iso;
Representation_iso.
Hom_prof_func(J,B);
Prof_imply_cov_func2;
Prof_imply_cov_fixed_weight_func(Q);
Prof_imply_cov_func(Q);
WeightedCone_prof(F,W);
IsWeightedLimit_cov_iso(F,W,L).
```

`ProfMap` is transparent, so its identity and composition remain the existing
`id_funcd` and `comp_catd_fapp0`. `IsoEvidence` is nested Sigma data with
propositional inverse equations; reflexivity has identity-arrow projections,
symmetry swaps both arrows and inverse proofs, composition exposes ordinary
arrow composition, and strict functors transport evidence through their arrow
action. `comp_assoc` is propositional category-law evidence. It is
transparent `eq_refl` evidence under the active ordinary-composition
associativity unification equation. Associativity remains absent from runtime
arrow rewriting; see the corrected feasibility audit below.

`Companion_prof` and `Conjoint_prof` are transparent views of
`Hom_prof_along`; they introduce no competing rewrite head.
`IsRepresentedBy_iso` is ordinary representability by a conjoint, and
`Representation_iso` is its Sigma of chosen representing functors. This layer
does not claim the stronger computational beta/eta interface still needed by
weighted-limit preservation.

Two candidate computational `StrictIso` implementations were rejected after
ordinary typechecking had initially passed:

1. Generic or `Catd_cat`-owned cancellation plus projection-expanding
   `strict_iso_comp`/`strict_iso_fmap` produced unjoinable projection-first
   versus cancellation-first critical pairs. Contextual cancellation rules
   also overlapped Catd identity and component projection.
2. Orienting ordinary composition toward a stable composite-isomorphism
   witness removed the composite expansion problem, but still produced
   unjoinable overlaps with reflexivity, symmetry, Catd identities, and
   `tapp0_fapp0` projection.

The successful ordinary-evidence probe is:

```text
logs/probes/profunctor_representability_phase1_iso_evidence_probe-20260620-191023.log
```

Useful negative evidence is retained in:

```text
logs/probes/profunctor_representability_phase1_strict_iso_probe-20260620-185745.log
logs/probes/profunctor_representability_phase1_strict_iso_fold_probe-20260620-190859.log
```

The first log shows that assertions alone can pass for a non-confluent rewrite
system. The later decision-tree audit, not ordinary typechecking, invalidated
the design. Therefore no active `StrictIso`, generic judgmental-cancellation,
or Catd-specific cancellation rule should be inferred from this checkpoint.

A third experiment attempted to encode inverse cancellation and ordinary
composition associativity as unification rules. Its results must be separated:

1. The inverse-cancellation hints did not make conversion assertions compute
   and did not let `eq_refl(id)` inhabit the required inverse equations.
   Projected composite witnesses also escaped the generic cancellation
   pattern.
2. The historical associativity hint was malformed: the inner composite used
   endpoints `C y x z` where the typed composite of `h : y -> z` and
   `g : x -> y` requires `C x y z`.
3. The corrected arrow-level rule is:

   ```lambdapi
   unif_rule @comp_fapp0 $C $w $y $z $h
       (@comp_fapp0 $C $w $x $y $g $f)
     ≡ @comp_fapp0 $C $w $x $z
         (@comp_fapp0 $C $x $y $z $h $g)
         $f
     ↪ [ tt ≡ tt ];
   ```

   This successfully elaborates `comp_assoc` as `eq_refl` from either
   bracketing.
4. The initial attempt to promote the corrected rule timed out, but that was
   not an inherent cost of associativity. A warning-enabled run localized the
   interaction to the generic strict-functor composition rule, whose three
   inferred target-object slots were explicit reducible terms:

   ```lambdapi
   @comp_fapp0
     B
     (fapp0 F X)
     (fapp0 F Y)
     (fapp0 F Z)
     (fapp1_fapp0 F g)
     (fapp1_fapp0 F f)
   ```

   Those endpoint slots are reconstructible from the two action terms and are
   not discriminators. Replacing them by `_` removes the unification
   explosion while preserving the strict-functor cut:

   ```lambdapi
   @comp_fapp0 B _ _ _
     (fapp1_fapp0 F g)
     (fapp1_fapp0 F f)
   ```
5. With that LHS correction, warning-enabled and quiet checks of the full
   active `emdash3_2.lp` both complete quickly. The associativity unification
   rule is active and `comp_assoc` is defined by `eq_refl`.

The focused isolated evidence remains:

```text
logs/probes/comp_assoc_unif_review_probe-20260621-134559.log
logs/probes/profunctor_representability_phase2_iso_comp_step_probe-20260620-204039.log
```

The initial `Hom_prof_func` probe was architecturally wrong even though its
focused assertions passed. It introduced constructor-specific identity and
composition rules for `Hom_prof_func_transf`, plus broad
`hom_postcomp_func` identity/composition rules. Those duplicated strict
functoriality already owned globally by `fapp1_fapp0` and
`comp_fapp0`. Against an earlier active diagnostic baseline of about 1140
unjoinable-pair warnings, the full package reported about 1444; removing the
two broad postcomposition rules lowered it to about 1156.

After remapping the existing kernel, `Hom_prof_func` was reimplemented
semantically:

```text
Functor(J,B)
  -> Functor(Functor(B,Cat),Functor(J,Cat))
  -> Functor(B^op,Functor(J,Cat))
  -> Prof(B,J).
```

The three steps are existing precomposition-in-a-functor,
precomposition by `hom_int(id_B)`, and semantic uncurry. The composite is made
opaque only to preserve a stable public head; its object projection computes
to `Hom_prof(G)`. Its `fapp1_func` and `fapp1_fapp0` are the ordinary generic
actions of that functor. No `Hom_prof_func`-specific identity or composition
rule exists. The fibre component of its capped action is expressed through
existing `comp_cat_cov_transf`; this reduces locally through
`hom_postcomp_tele_func`.

One general kernel bridge was missing because a target
`comp_fapp0` in `Catd_cat(K)` canonicalizes to `comp_catd_fapp0` before the
global strict-functor composition cut can match. The active bridge is the
generic `Catd_cat` specialization of that same cut, with inferred family
endpoints. It is not a representable-specific law.

The corrected focused probe is:

```text
logs/probes/profunctor_representability_hom_prof_func_semantic_probe-20260621-025230.log
```

Active checks cover object action, the whole hom-action type, capped arrow
action, its fibre component, inherited identity, and inherited composition.
The comparative decision-tree count moved from about 1144 to about 1147. The
three additional warnings require impossible type equations, such as treating
`Hom_prof_func(J,B)` as an object of its own source category or as a map
between unrelated constant families. This remains comparative bounded
evidence, not a global confluence proof.

The fixed-weight implication functor is now active:

```text
Prof_imply_cov_func(Q)
  : Functor(Prof_cat(A,X),Prof_cat(A,B)).
```

Its object projection computes. Its full and capped arrow actions are the
generic actions of the declared functor, so strict identity/composition are
inherited globally. The dedicated action heads and their reindex rule described
by the original checkpoint were removed by the generic-owner correction above.
This remains a symbolic closed-structure interface while end semantics are
absent.

The focused passing probe is:

```text
logs/probes/profunctor_representability_phase2_imply_cov_func_probe-20260621-020628.log
```

The historical warning analysis for the removed action heads no longer
describes the active architecture. Current validation is recorded by the
generic-owner correction and generated health report.

The next bounded slice selected domain-specific adjunction-mate ownership
instead of a new global computational-isomorphism classifier. The active
ordinary layer is:

```text
Adjunction_hom_prof_iso_evidence(adj)
  : IsoEvidence(
      Prof_cat(A,B),
      Hom_prof_along(left(adj),id_B),
      Hom_prof_along(id_A,right(adj)));

Adjunction_hom_prof_iso_evidence_along(adj,M,F)
  := iso_evidence_fmap(
       Prof_reindex_func(M,F),
       Adjunction_hom_prof_iso_evidence(adj)).
```

The existing `Adjunction_prof_transpose` and
`Adjunction_prof_untranspose` now cancel directly under vertical
`comp_catd_fapp0`, in addition to their existing equipment-cell cancellation.
These are narrow rules discriminating on the adjunction mate heads; they do
not assert generic judgmental cancellation for arbitrary `IsoEvidence`.
Reindexing the ambient forward and inverse maps simultaneously along `(M,F)`
computes to the existing shaped mate operations.

The focused quiet and warning-enabled probes both passed. The active
warning inventory remained exactly 1,139 recognized warnings, including 986
unjoinable critical-pair warnings and 153 replaceable-pattern warnings. Thus
the new vertical cancellation and reindex rules added no newly detected
critical pair. The strict rewrite-LHS audit also remains at zero unreviewed
compound slots.

This ambient evidence makes the ordinary preservation theorem a genuine
definition:

```text
right_adjoint_preserves_weighted_limit_cov_iso(isl,adj)
  : IsWeightedLimit_cov_iso(
      right(adj) o F,
      W,
      right(adj) o L).
```

Its three transparent steps are:

```text
1. map the inverse adjunction mate through Prof_imply_cov_func(W);
2. map isl through Prof_reindex_func(left(adj),id);
3. compose with the adjunction mate at L.
```

The forward projection computes to the expected vertical composite of
implication-untranspose, the reindexed weighted-limit comparison, and
transpose. This proves ordinary isomorphism-level preservation without an
axiomatic theorem symbol. It deliberately does not redefine the unsuffixed
`right_adjoint_preserves_weighted_limit_cov`, because that API still promises
the stronger judgmentally cancelling `WeightedLimit_cov` interface.

The immediate motivation is the current implementation of:

```text
right_adjoint_preserves_weighted_limit_cov
right_adjoint_preserves_weighted_limit_cov_univ_transf
```

but the review treats those symbols as symptoms of broader architectural
issues rather than as an isolated rewrite cleanup.

## Implementation Checkpoint: 2026-06-22

The comparison-owner question has now been resolved provisionally in favor of
a Došen/Yoneda-style eliminator rather than cancellation on ordinary
composition.

Three focused experiments were compared.

First, a generic comparison acting by inverse operations on incoming homs
passed:

```text
Comparison(C,x,y);
comparison_push(i) : Hom(z,x) -> Hom(z,y);
comparison_pull(i) : Hom(z,y) -> Hom(z,x);

comparison_pull(i,comparison_push(i,f)) -> f;
comparison_push(i,comparison_pull(i,g)) -> g.
```

Reflexivity, symmetry, and composition compute structurally on the dedicated
heads. A strict-functor image can be a certified stable comparison, but its
action cannot generally be exposed by invoking the source comparison at an
arbitrary target test object. The coherent form keeps mapped eliminators
stable and exposes their ordinary mathematical evidence separately.

Passing focused log:

```text
logs/probes/profunctor_representability_comparison_eliminator_probe-20260622-012438.log
```

Second, a profunctor-specialized comparison whose selected forward and inverse
arrows cancelled directly under `Prof_comp_transf` passed isolated assertions.
It could express the full preservation theorem as a composition of three
comparisons and forget exactly to
`right_adjoint_preserves_weighted_limit_cov_iso`.

That result did not survive active integration. The two new cancellation rules
created exactly two new critical pairs with the existing rule distributing
`Op_prof_transf` over `Prof_comp_transf`: cancellation-first produced a dual
identity, while duality-first produced a composite of dualized comparison
arrows. Adding an `Op_prof_comparison` closure and involution rule increased,
rather than removed, the overlap set. The active warning inventory moved from
1,139 to 1,141 and then 1,151. The raw-composition presentation was therefore
backed out.

This is an important SOP result: a probe module that imports the active kernel
and adds rules afterward may not expose every rule-order interaction that
appears when those rules are inserted into the owning module. Active
warning-enabled integration remains a required promotion gate.

Focused semantic construction log:

```text
logs/probes/profunctor_representability_prof_comparison_probe-20260622-013039.log
```

Third, the successful architecture specializes the generic eliminator idea to
profunctor categories:

```text
ProfComparison(P,Q);

prof_comparison_push(i) : ProfMap(R,P) -> ProfMap(R,Q);
prof_comparison_pull(i) : ProfMap(R,Q) -> ProfMap(R,P);
prof_comparison_evidence(i) : IsoEvidence(Prof_cat(A,B),P,Q).
```

The two eliminators are judgmental inverses on dedicated heads. The initial
promotion used primitive propositional semantic fields to relate them to
ordinary postcomposition. A follow-up refinement removed that unnecessary
opacity.

Selected arrows are now identity applications:

```text
prof_comparison_to(i)   := prof_comparison_push(i,id);
prof_comparison_from(i) := prof_comparison_pull(i,id).
```

Incoming-map naturality is the inward cut-elimination rule:

```text
prof_comparison_push(i,r) o h
  -> prof_comparison_push(i,r o h);

prof_comparison_pull(i,s) o h
  -> prof_comparison_pull(i,s o h).
```

The reverse expansion orientation was rejected: it produced twelve
probe-owned critical pairs with identity cuts, the semantic equipment fold,
and reductions of opposite/product bases. The inward orientation added no
critical pair in either the imported probe or a full owning-module copy.

Proof-time unification equations identify the selected identity applications
with the normalized Sigma projections of `prof_comparison_evidence`. Because
`iso_evidence_to/from` are transparent aliases, rules written with those alias
heads do not fire; the active equations deliberately use
`sigma_Fst(evidence)` and `sigma_Fst(sigma_Snd(evidence))`.

Consequently:

```text
prof_comparison_to_evidence(i);
prof_comparison_from_evidence(i);
```

are definitions by `eq_refl`. Unification does not recursively rewrite an
evidence projection inside arbitrary composition, so the general
`prof_comparison_push/pull_semantics` proofs are transparent
`eq_trans`/`eq_ap` derivations from:

```text
the reflexive selected-arrow bridge;
inward accumulation.
```

They are no longer primitive evidence fields.

Functorial action is owned by the existing generic infrastructure:

```text
prof_comparison_push_func(i,R)
  := hom_postcomp_func(id_Prof,R,P,Q,prof_comparison_to(i));

prof_comparison_pull_func(i,R)
  := hom_postcomp_func(id_Prof,R,Q,P,prof_comparison_from(i)).
```

Their object actions reduce to the dedicated push/pull eliminators through
ordinary postcomposition plus accumulation, while higher-arrow behavior is
inherited from `hom_postcomp_*`. Thus `ProfComparison` owns computational
invertibility, not a duplicate functor calculus.

The active algebra includes:

```text
prof_comparison_refl;
prof_comparison_sym;
prof_comparison_comp;
prof_comparison_fmap.
```

Reflexivity, symmetry, and composition compute structurally on push/pull.
Functorial image remains a certified stable comparison; its evidence
projection computes through `iso_evidence_fmap`.

Weighted limits now have a parallel computational representation:

```text
IsWeightedLimit_cov_comp(F,W,L)
  := ProfComparison(WeightedCone_prof(F,W),Hom_prof(L));

weighted_limit_cov_push;
weighted_limit_cov_pull;
weighted_limit_cov_comp_univ_transf;
weighted_limit_cov_comp_cone_transf.
```

One ambient comparison is reindexed along every shaped probe `M : I -> B`.
The resulting push/pull operations quantify over every incoming
`R : Prof(I,J')` and are judgmental inverses. The old selected universal and
cone maps are recovered by applying push and pull to identity maps. This is
both more internalized and closer to the standard representability universal
property than storing only two selected inverse arrows for every external
probe.

The adjunction mate is an atomic certified comparison:

```text
Adjunction_hom_prof_comparison(adj);
Adjunction_hom_prof_comparison_along(adj,M,F).
```

Its evidence projection is the existing unit/counit-based
`Adjunction_hom_prof_iso_evidence`; its ambient form internalizes both hom
variables, and shaped forms are obtained by `prof_comparison_fmap` along
`Prof_reindex_func(M,F)`.

The computational preservation theorem is now a genuine definition:

```text
right_adjoint_preserves_weighted_limit_cov_comp
```

It composes:

```text
the inverse adjunction comparison through Prof_imply_cov_func(W);
the given weighted-limit comparison reindexed along the left adjoint;
the adjunction comparison at the candidate limit.
```

Its push/pull beta/eta laws follow from generic comparison computation, and
its evidence projection reduces exactly to
`right_adjoint_preserves_weighted_limit_cov_iso`. It introduces no
theorem-specific fold.

Passing focused log:

```text
logs/probes/profunctor_representability_weighted_eliminator_probe-20260622-014137.log
logs/probes/profunctor_comparison_accumulation_probe-20260622-022308.log
logs/probes/profunctor_comparison_unif_bridge_probe-20260622-023828.log
```

After initial active promotion:

```text
make check: passed;
warning inventory: unchanged at 1,139
  (986 unjoinable critical pairs, 153 replaceable variables).
```

Therefore the currently selected computational owner is:

```text
dedicated inverse application/elimination;
ordinary IsoEvidence for semantic arrows and equations;
selected arrows related to evidence projections by proof-time unification;
transparent postcomposition semantics derived by accumulation and equality
congruence;
generic hom_postcomp_func ownership of functorial/higher action;
no generic inverse cancellation on shared category/equipment composition.
```

This does not settle global `StrictIso`, `OmegaEquiv`, or univalence. Those
remain parallel foundational work. Univalence may eventually explain or
generate certified comparisons, but it does not by itself justify judgmental
cancellation on ordinary composition.

The public cutover was completed on 2026-06-22:

```text
WeightedLimit_cov := IsWeightedLimit_cov_comp;
weighted_limit_cov_univ_transf := weighted_limit_cov_comp_univ_transf;
weighted_limit_cov_cone_transf := weighted_limit_cov_comp_cone_transf;
right_adjoint_preserves_weighted_limit_cov
  := right_adjoint_preserves_weighted_limit_cov_comp.
```

The primitive witness, giant exact-syntax fold, implication helper,
theorem-specific universal-map head, and constructor-local equipment
cancellation joins are retired. Diagnostics now test arbitrary-map push/pull,
selected projections, and transparent theorem equality. Weighted colimits and
left-adjoint preservation continue definitionally through duality.

The cutover reduced warning-enabled diagnostics from:

```text
1,139 total = 986 unjoinable + 153 replaceable
```

to:

```text
1,043 total = 890 unjoinable + 153 replaceable.
```

The next bounded closed-structure slice was completed later on 2026-06-22.
The direct product-domain proposal:

```text
Prof_cat(A,X) x Op_cat(Prof_cat(B,X)) -> Prof_cat(A,B)
```

initially failed the stronger arbitrary-object identity audit. The failure was
not intrinsic to the product presentation: product objects are encoded Sigma
data, but the kernel only decomposed a whole product identity when a
`Struct_sigma` constructor was visible.

A broad whole-arrow rule rebuilding every opaque product identity as a
`Struct_sigma` was rejected. It introduced genuine nonjoinable interactions
with hom precomposition and postcomposition consumers. The coherent repair is
projection-owned:

```text
sigma_Fst(id_(A x B)(xu)) -> id_A(sigma_Fst(xu));
sigma_Snd(id_(A x B)(xu)) -> id_B(sigma_Snd(xu)).
```

The whole identity stays opaque unless its object is an explicit pair, while
component consumers obtain exactly the identities they need. With those rules
the selected owner is the direct bifunctor:

```text
Prof_imply_cov_func2 :
  Product_cat(Prof_cat(A,X),Op_cat(Prof_cat(B,X)))
    -> Prof_cat(A,B).
```

Its object action accepts an arbitrary opaque `(O,Q)`, and its full/capped
arrow actions accept an arbitrary opaque `(o,q)` through the ordinary generic
functor action. The fixed-endpoint form of `Prof_imply_cov_transf` folds to
that generic action. The former dedicated mixed and unary action heads were
removed; fixed-weight implication is now a semantic specialization of this
mixed owner. The temporary curried owner and outer contravariant
transformation head remain removed.

A separate `Hom_prof_func` endpoint audit established a narrower boundary.
Right-endpoint restriction preserves representability definitionally on
objects, and both transformation routes have the expected type. A direct
runtime fold between those arrow routes added two nonjoinable overlaps with
identity reindexing and identity transformations; a proof-time unification
equation did not make the conversion reflexive in the required position.
No bridge was promoted. If a downstream theorem needs that square as data, it
should be expressed as a natural comparison rather than imposed as another
runtime normal form.

Active validation after the direct implication promotion reports:

```text
1,052 total = 899 unjoinable + 153 replaceable.
```

The nine new critical-pair reports are sort-impossible generic decision-tree
artifacts, analogous to the bounded artifacts already documented for unary
internalized functors. Their terms require the new functor or transformation
head itself to inhabit unrelated source-object positions. The well-typed
identity and composition paths join and have direct regression checks.

The same review scanned every active `Struct_sigma` occurrence on a rewrite
LHS in `emdash3_2.lp`. Constructor discrimination remains justified for:

```text
the sigma_Fst/sigma_Snd eliminators;
explicitly paired product-valued functors and product composition;
evaluation and fixed-factor product maps;
Sigma homs, Sigma arrows, and Sigma-map arrow action;
displayed-total uncurrying and the measured path-induction guard.
```

The audit distinguished whole-output rules from projection-owned rules:

```text
product composition:
  sigma_Fst(g o f) -> sigma_Fst(g) o sigma_Fst(f)
  sigma_Snd(g o f) -> sigma_Snd(g) o sigma_Snd(f)

Sigma-map object action:
  sigma_Fst(Sigma(eta)[ku]) -> sigma_Fst(ku)
  sigma_Snd(Sigma(eta)[ku]) -> eta[sigma_Fst(ku)](sigma_Snd(ku)).
```

Both projection-only packages typechecked and proved their opaque-object
assertions when installed at their owning declaration positions. They were
still not warning-neutral. Product-composition projections added six
critical-pair reports, principally against generic strict-functor composition
and left/right identity cuts. Sigma-map projections added two reports against
the generic projection of product-valued functor application in the
constant-family case where a Sigma total reduces to a product. Resolving those
would require a broader product hom-action/projection ownership side task, not
just weakening a constructor pattern.

The common failure is architectural: both proposed packages put an outer
Sigma eliminator directly over another independently rewrite-active cut:

```text
sigma_Fst(comp_fapp0(...))
sigma_Snd(fapp0(sigma_map_func(...),...)).
```

These are commuting conversions. Composition/application may first normalize
through identity, strict functoriality, naturality, or the generic
product-valued projection ladder; alternatively, the new outer projection may
fire first. Constructor beta rules such as
`sigma_Fst(Struct_sigma(x,u))` do not have this problem because the inner head
is data, not a competing cut.

The redesign therefore adopts the general SOP that an
outer-eliminator/inner-cut LHS is presumptively rejected. It is acceptable only
as a designated projection ladder with one canonical semantic owner, or as a
narrow measured commuting conversion required by a concrete consumer whose
outer-first and inner-first paths join in a warning-enabled full-file probe at
the owning declaration position. For these product/Sigma-map formulas, the
preferred future work is a coherent general product hom-action/projection
owner or a stable component head, not additional raw nested-cut rules.

Evaluation and the tested total-family consumers generally return an arbitrary
category object or a category, not Sigma data, so an output-headed
`sigma_Fst`/`sigma_Snd` replacement is not available for their general rule.
Product-valued constructors such as product swap and the fixed-right product
map already obtain opaque-input component computation through the generic
`sigma_Fst(fapp0 H i)`/`sigma_Snd(fapp0 H i)` ladder plus projections of `H`.

The earlier combined broad product/evaluation experiment added twenty active
critical pairs, and broad whole `sigma_map_func` object reconstruction added
another real overlap. Opaque object fallbacks for `Sigma_proj1_func`,
`Sigma_proj1_pullback_catd`, and `Sigma_catd_functord_catd` passed when appended
to an imported probe but added two pairs when placed at their owning
declaration point because later rules also interact with them. None were
promoted. This establishes an important SOP point: a focused probe is
necessary but not sufficient for a broad rule; warning-enabled validation in
the owning module at the intended declaration position is the promotion gate.

## Assessment

The concern about the current preservation implementation is correct. It is
computationally useful, but it is not a satisfactory theorem architecture.

In the current implementation,
`right_adjoint_preserves_weighted_limit_cov` is a symbol without a definition.
Formally, it introduces an inhabitant rather than constructing one from `isl`
and `adj`. Its projection rules characterize some behavior, but do not turn it
into a derived lemma.

The large rewrite folding an explicit preservation composite to
`right_adjoint_preserves_weighted_limit_cov_univ_transf`, together with the
constructor-local cancellation rules for the resulting witness, compensates
for missing general infrastructure.

The preferred redesign is therefore not a theorem-local rewrite cleanup. It is
a strict closed-profunctor-equipment and representability layer whose immediate
algebra lives in fixed profunctor hom-categories. Endpoint-changing equipment
cells remain useful, but they should not be the default language for vertical
universal properties.

### Cartier Retrospective: Invertible Does Not Mean Identity

The obsolete `cartierSolution13.lp` did not avoid isomorphisms. It encoded
several isomorphisms as unnamed pairs of operations with direct beta/eta
rewrite rules:

```text
Eval_cov_transf / Lambda_cov_transf;
limit_cov_univ_transf / limit_cov_cone_transf;
Adj_cov_hom / Adj_con_hom.
```

For example, the two weighted-limit comparison maps compose to
`Id_transf`, but neither map is generally an identity transformation. The old
preservation symbol:

```text
righ_adjoint_preserves_limit_cov
```

was a transparent composite constructing the forward universal
transformation. It did not construct a complete new `limit_cov` witness with
both inverse maps and cancellation laws. Its apparent simplicity therefore
does not establish that right-adjoint preservation can generally be represented
by an identity-arrow isomorphism.

The old file did use genuine identity-arrow strictification in narrower
contexts:

```text
type_intro_hom(eq_refl) -> identity;
classification followed by decoding in the strict universe -> original data;
identity functors/transformations used as unchanged legs of larger composites.
```

This supports a bounded optimization principle:

```text
when a comparison path is reflexivity, its induced equivalence arrow computes
to identity;
```

but not the stronger and generally false principle:

```text
every representability, adjunction, or preservation comparison is itself an
identity arrow.
```

## Root Causes

### 1. Destructor-Only Weighted-Limit Witness

`WeightedLimit_cov` is a primitive classifier with projection/destructor
operations:

```text
weighted_limit_cov_univ_transf
weighted_limit_cov_cone_transf
```

There is no reusable constructor/combinator algebra that composes or maps
weighted-limit witnesses. Consequently, a theorem that should construct a new
weighted-limit witness cannot assemble one from generic identity, symmetry,
composition, and functorial-image operations.

A completely general constructor from arbitrary maps plus propositional inverse
proofs is not automatically the solution. If its projections reduce to the
supplied maps while generic cancellation also reduces judgmentally, the same
term may have non-joinable projection-first and cancellation-first reduction
paths. The immediate requirement is a reusable computational isomorphism
algebra; arbitrary proof-to-computation strictification is a separate problem.

### 2. Over-Externalized Universal Property

The current universal property quantifies externally over every:

```text
I : Cat
M : Functor I B.
```

Instead, one profunctor isomorphism at `M = id_B` should contain the fully
internalized universal property. Every shaped instance should then be derived
by profunctor reindexing.

The current witness therefore stores a family of maps for every `M` without
expressing naturality between those maps. An internalized profunctor
isomorphism would make this naturality part of the construction itself.

### 3. Missing Generic Invertibility Infrastructure

Invertible pairs are repeatedly implemented independently:

```text
weighted-limit universal/cone maps
adjunction transpose/untranspose
implication eval/lambda
opposite involutions
```

There is no generic computational strict-isomorphism or equivalence layer that
owns:

```text
forward and inverse projections
inverse cancellation
identity isomorphisms
symmetry
composition
functorial image of an isomorphism
```

This forces each subsystem to install its own cancellation rules.

The missing layer must not prematurely identify three different strengths:

```text
identity-arrow comparison;
strict isomorphism with on-the-nose inverse equations;
weak/recursive equivalence with higher cancellation data.
```

The present weighted-limit calculus uses strict inverse cancellation. A
globally univalent omega-categorical foundation is now the intended
architecture, but it is not yet active and should not be silently conflated
with this immediate strict interface.

### 4. General Equipment Composition Used For Vertical Maps

Weighted-limit calculations use the general six-endpoint
`Prof_comp_transf`, even when every relevant map is vertical inside one fixed
`Prof_cat(A,B)`.

This produces large endpoint-explicit terms and makes ordinary composition of
universal maps harder to reuse. The architecture does not clearly separate:

```text
vertical profunctor maps in one Prof_cat
general endpoint-changing equipment cells.
```

### 5. Closed Operations Need Complete Functorial Ownership

The first fixed-weight owner is now active:

```text
Prof_imply_cov_func(W).
```

It has the complete current unary object/whole-hom/capped interface and strict
vertical identity/composition laws. The direct mixed-variance owner is now
active as `Prof_imply_cov_func2`; what remains missing is the hom-action's
separate higher-arrow projections and any demanded tensor/implication
adjunction package.
`prof_comparison_fmap` now supplies certified comparison transport through
this functor. The computational preservation theorem uses that transport, and
the established unsuffixed theorem is now its transparent public name.

### 6. The Adjunction Hom Bridge Is Also Over-Externalized

`Adjunction_prof_transpose` and `Adjunction_prof_untranspose` are parameterized
by two external probes:

```text
M : I -> A.
F : K -> B.
```

They should instead arise from one ambient hom-profunctor isomorphism in
`Prof_cat(A,B)`, with the component at arbitrary `(M,F)` obtained by one
profunctor reindexing. The earlier fixed-`F` proposal was still unnecessarily
externalized.

### 7. No Generic Representability Abstraction

Weighted limits are representability statements, but the implementation has no
generic `RepresentedBy` layer. The weighted-limit subsystem directly encodes
the expanded universal-property components instead of reusing a general
representability concept.

## Recommended Architecture

### Semantic Strength: Distinct Equivalence Interfaces

Do not overload one `Equiv` name across distinct domains and computational
strengths. The proposal has three semantic strata, with the ordinary strict
categorical stratum exposed through both `IsoEvidence` and its computational
`StrictIso` refinement.

First, HoTT equivalence between groupoid/type classifiers:

```text
TypeEquiv(A,B)
```

should eventually be based on a map whose homotopy fibres are contractible, or
on an equivalent half-adjoint formulation. A pair of potentially different
left and right inverses is a useful bi-invertible presentation, but plain
quasi-inverse data should not silently be treated as the final
proof-irrelevant `IsEquivMap` predicate.

Second, distinguish propositional isomorphism evidence:

```text
IsoEvidence(C,x,y)
```

from computational strict isomorphisms:

```text
StrictIso(C,x,y)
strict_iso_to
strict_iso_from
strict_iso_refl
strict_iso_sym
strict_iso_comp
strict_iso_fmap(F,i)
```

`IsoEvidence(C,x,y)` may be nested Sigma data consisting of arrows
`to : x -> y` and `from : y -> x` with equality paths showing that both
composites are identities.

`StrictIso(C,x,y)` is the computational algebra needed by the active
cut-elimination interface. Its public arrows must cancel judgmentally:

```text
strict_iso_from(i) o strict_iso_to(i) -> id;
strict_iso_to(i) o strict_iso_from(i) -> id.
```

The immediate computational interface should provide:

```text
stable strict_iso_to / strict_iso_from projections;
generic projection-cancellation rules;
strict_iso_refl;
strict_iso_sym;
strict_iso_comp;
strict_iso_fmap.
```

This remains a semantic desideratum, not a validated rewrite presentation.
The 2026-06-20 probes refute the earlier assumption that attaching generic
cancellation to ordinary composition and then adding projection equations for
these combinators is a coherent implementation. The next design must choose a
different computational owner, for example:

```text
domain-specific inverse-operation calculi with generic propositional
IsoEvidence as the common forgetful layer;

a dedicated cut/eliminator syntax whose computation does not overlap ordinary
category composition and component projection;

or path/equivalence ownership followed by a separately justified strict
specialization.
```

No option is selected yet. In particular, do not add category-by-category
cancellation rules merely to make a finite assertion suite pass.

Preservation constructs its result using these combinators; it does not require
an unrestricted `strict_iso_intro`.

This interface is not an ordinary freely constructible record. Its
nontrivial atomic inhabitants must come from semantically justified
computational generators whose projected arrows already have joining inverse
computations. Examples may include an adjunction hom comparison exposed by a
computational adjunction presentation, or a closed-structure comparison exposed
by eval/lambda. Each such generator requires:

```text
stable forward and inverse projections;
projection-first inverse composites that reduce or unify with identities;
agreement with the selected computational comparison's cancellation;
focused critical-pair and timeout checks.
```

Identity, symmetry, composition, and functorial image then propagate these
certified generators. They cannot create a nontrivial strict isomorphism from
arbitrary propositional inverse evidence.

The name `StrictIso` is provisional terminology for this computational
classifier. Its intended extra strength is judgmental inverse cancellation,
not merely the usual mathematical assertion that inverse equations are
inhabited. Consequently, `StrictIso` is a refinement of ordinary categorical
isomorphism evidence and is not assumed to classify every mathematical
isomorphism.

The first usable computational implementation should also provide a forgetful
map:

```text
strict_iso_evidence : StrictIso(C,x,y) -> IsoEvidence(C,x,y).
```

The reverse direction:

```text
strictify_iso : IsoEvidence(C,x,y) -> StrictIso(C,x,y)
```

is not generic infrastructure unless a focused probe provides a coherent
strictification principle.

In particular, do not simultaneously install all three of:

```text
strict_iso_intro(f,g,p,q);
strict_iso_to(strict_iso_intro(...)) -> f;
strict_iso_from(strict_iso_intro(...)) -> g;
```

together with generic judgmental cancellation, without proving the resulting
critical pairs join. Cancellation-first yields an identity, while
projection-first exposes `g o f`; the proof `p` has disappeared from that
reduct. Ordinary typechecking alone is not evidence of confluence for this
overlap.

Third, weak omega-categorical equivalence arrows:

```text
OmegaEquiv(C,x,y)
omega_equiv_to
omega_equiv_left_inv
omega_equiv_right_inv
omega_equiv_left_cancel
omega_equiv_right_cancel
```

may use distinct left and right inverse arrows. Their cancellation data should
be equivalences recursively in the next hom-categories rather than necessarily
groupoid equality proofs. A feasible Lambdapi presentation may declare the
`OmegaEquiv` classifier first and expose the recursive structure through
separate destructor/constructor symbols.

There are canonical bridges:

```text
StrictIso(C,x,y) -> OmegaEquiv(C,x,y);
path x y         -> OmegaEquiv(C,x,y).
```

The path bridge should compute by equality induction:

```text
idtoequiv_cat(refl_x) -> omega_equiv_refl(x);
omega_equiv_to(omega_equiv_refl(x)) -> id_x.
```

Thus identity-arrow computation is the reflexivity specialization of the
general equivalence story. It must not replace nonidentity representability or
adjunction comparisons.

For the immediate weighted-limit redesign, two implementation routes remain
mathematically legitimate:

```text
computational-first:
  implement the StrictIso refinement, forget it to IsoEvidence, and later map
  it into OmegaEquiv and paths;

path/equivalence-first:
  implement enough global univalence that representability is stored as a path,
  then recover the comparison maps needed by the current API.
```

The first attempted implementation was `computational-first`. It successfully
landed `IsoEvidence`, but the proposed generic `StrictIso` rewrite
presentation failed the 2026-06-20 critical-pair audit. The choice of
computational owner is therefore reopened. The existing weighted-limit API
still requires judgmentally cancelling inverse comparison maps, while path
ownership additionally requires computational laws for `idtoequiv_cat` over
path composition and functorial path action.

The path/equivalence route should proceed in parallel and may become the deeper
owner after focused probes show that its projections reproduce the strict
comparison calculus without theorem-specific folds.

General `OmegaEquiv` is the largest foundational feasibility risk in this
layer. Recursive cancellation data is coinductive in character: a naive
ordinary inductive encoding risks describing only finite-height invertibility.
Initial probes should compare:

```text
primitive classifier plus recursive destructor/constructor heads;
finite-height OmegaEquiv_n approximations;
path-first equivalence under the global univalence bridge;
strict isomorphisms embedded into a deferred weak-equivalence interface.
```

No general `OmegaEquiv` encoding should block the computational weighted-limit
migration.

Broad raw composition-associativity rewrites should not be introduced merely
to support this layer.

Following the project's cut-elimination/Dosen discipline, associativity should
normally remain a metatheorem rather than a reduction rule. A carefully
oriented unification rule may identify:

```text
f o (g o h)  =?=  (f o g) o h
```

during elaboration or proof checking without making associativity part of
runtime normalization. The corrected ordinary rule is now active after
removing reducible, non-discriminating endpoint terms from the generic
strict-functor composition LHS. The same possibility may be explored
separately for `comp_catd_fapp0`, but it must not be inferred from the
ordinary result. Constructor projection computation should remain the primary
mechanism.

### Foundational Decision: `Cat` Classifies Univalent Categories

The intended foundational contract is now:

```text
every C : Cat is an internally univalent omega-category;
Cat_cat is itself univalent.
```

This replaces the previously safer proposal to introduce a separate `UCat`
subuniverse. The implementation must distinguish the global availability of
univalence from full computation for every category constructor.

A schematic interface is:

```text
idtoequiv_cat [C] [x y] :
  (x = y) -> OmegaEquiv(C,x,y)

equivtoid_cat [C] [x y] :
  OmegaEquiv(C,x,y) -> (x = y)

idtoequiv_cat(equivtoid_cat(e)) -> e
equivtoid_cat(idtoequiv_cat(p)) -> p.
```

Making both directions judgmental is stronger than the usual computation
available from ordinary intensional HoTT presentations of univalence. Here it
is a proposed operational/computational contract, not a claim that both rules
follow automatically from Voevodsky's univalence axiom. The focused design
must weaken either direction to propositional coherence if the two-rule
presentation is not confluent or modelable in the intended universe
interpretation.

The exact ownership may instead use:

```text
CatUnivalence(C)
cat_univalence(C) : CatUnivalence(C)
```

with the two conversions as projections. The latter makes the foundational
assumption explicit and gives constructor-specific closure rules a stable
owner. Focused probes should compare both formulations.

Because `Cat_cat` is itself a `Cat`, the same interface specializes to:

```text
(A = B) ~= OmegaEquiv(Cat_cat,A,B).
```

The right side is an omega-categorical equivalence whose underlying arrow is a
functor `A -> B`. This is the category-universe analogue of Voevodsky
univalence.

This is a strong universe-level contract because:

```text
Cat_cat : Cat;
Obj(Cat_cat) = Cat;
Cat_cat is univalent.
```

Before making consistency or model-existence claims, the development must state
which interpretation is intended:

```text
an operational specification axiom;
a universe-stratified family Cat_i with Cat_i : Cat_(i+1);
or a deliberate impredicative/self-universe model.
```

This question does not block focused Lambdapi experiments, but it must remain
explicit rather than being hidden by the single current `Cat` classifier.

The groupoid/type universe requires a parallel but distinct interface:

```text
idtoequiv_grpd : (A = B) -> TypeEquiv(A,B)
ua_grpd        : TypeEquiv(A,B) -> (A = B).
```

It should not be defined by identifying `TypeEquiv` with
`OmegaEquiv(Grpd_cat,A,B)` until the truncation and higher-cell semantics of
`Grpd_cat` are settled.

The global categorical bridge also supplies the previously deferred
path-to-arrow inclusion:

```text
path_to_hom_fapp0(C,p)
  := omega_equiv_to(idtoequiv_cat(C,p));

Core_incl_func(C) : Core_cat(C) -> C.
```

Its object action is identity and its arrow action is the formula above. This
keeps the safe `path -> arrow` direction computational while univalence owns
the reverse `equivalence arrow -> path` direction.

### Incremental Univalence Closure

Global univalence can be available before every constructor has specialized
computation. Generic `idtoequiv_cat` and `equivtoid_cat` terms may remain stuck
for a constructor whose closure laws are deferred.

The development should add univalence closure in parallel with the existing
directed `Obj`/`Hom_cat` computation:

| Category constructor | Directed computation already owned by | Undirected/univalence closure |
| --- | --- | --- |
| `Path_cat(A)` | equality paths and `eq_trans` | path equivalences reduce to path algebra |
| `Op_cat(C)` | reversed homs/composition | equivalences reverse coherently |
| `Product_cat(A,B)` | projections and component homs | paths/equivalences compute componentwise |
| `Functor_cat(A,B)` | `fapp0`, `fapp1_func`, transformations | functor paths correspond to natural equivalences |
| `Catd_cat(K)` | natural family morphisms | family paths correspond to natural fibre equivalences |
| `Sigma_cat(E)` | total objects and directed dependent homs | total paths/equivalences decompose into base and fibre data |
| `Pi_cat(E)` | sections and section action | section paths/equivalences compute pointwise and naturally |
| `Prof_cat(A,B)` | Cat-valued families on `A^op x B` | profunctor paths correspond to natural pointwise equivalences |
| `Cat_cat` | functor categories | category paths correspond to omega-equivalences of categories |

Closure should follow existing semantic ownership. In particular:

```text
Catd_cat(K) = Functor_cat(K,Cat_cat);
Prof_cat(A,B) = Catd_cat(Op_cat(A) x B).
```

Their first univalence behavior should therefore be inherited from
`Functor_cat`, `Cat_cat`, `Op_cat`, and `Product_cat`, rather than duplicated by
new primitive closure heads. A specialized `Catd_cat` or `Prof_cat` head is
justified only when a focused projection or normalization test demonstrates
that the inherited route is too reducible, stuck, or expensive.

There is a concrete implementation caveat: `Functor_cat K Cat_cat` reduces to
the canonical `Catd_cat K` head. Therefore the semantic owner may be
`Functor_cat` while the visible normal form needed by later rules is
`Catd_cat`. A Catd-specialized univalence projection may be necessary for the
same reason other Cat-specialized projection ladders are retained in v3.2.
Such a head should document `Functor_cat` as its generic owner and include the
required overlap/join checks.

The initial implementation should target only the obvious/high-value cases:

```text
reflexivity/identity equivalence;
Path_cat;
Op_cat;
Product_cat;
Cat_cat at least at the generic univalence interface;
Prof_cat only as far as representability immediately consumes it.
```

Functor, family, Sigma/Pi, and full profunctor closure can remain stuck but
must be listed explicitly. This mirrors the existing kernel strategy: a
constructor may exist globally before its entire projection ladder computes.

### Univalence Rewrite Discipline

Global univalence must not be implemented by directly rewriting category
objects or arbitrary arrows:

```text
do not rewrite A to B merely because e : OmegaEquiv(Cat_cat,A,B);
do not identify every arrow with an equality path;
do not install evidence-irrelevance for equivalence witnesses by default.
```

Keep explicit stable heads:

```text
idtoequiv_cat;
equivtoid_cat;
omega_equiv_to;
omega_equiv_*_inv;
strict_iso_to_omega.
```

The principal generic computation should be cancellation of adjacent
conversion heads:

```text
idtoequiv_cat(equivtoid_cat(e)) -> e;
equivtoid_cat(idtoequiv_cat(p)) -> p;
idtoequiv_cat(refl) -> omega_equiv_refl;
omega_equiv_to(omega_equiv_refl) -> id.
```

Path-owned representability additionally requires explicit compatibility laws:

```text
idtoequiv_cat(eq_trans p q)
  -> omega_equiv_comp(idtoequiv_cat p,idtoequiv_cat q);

idtoequiv_cat(ap F p)
  -> omega_equiv_fmap(F,idtoequiv_cat p).
```

Equality induction alone computes only the reflexivity case. Without these
laws, composing representability paths gives concise syntax but leaves the
universal comparison arrow stuck.

Constructor-specific closure rules should be keyed on visible constructors
such as `Path_cat`, `Op_cat`, or `Product_cat`. Unification rules may help
compare path/equivalence normal forms during proof checking, but they must not
turn univalence into an unrestricted bidirectional conversion procedure.

### Separate Vertical Maps From Equipment Cells

Use fixed profunctor hom-categories as the default semantic layer:

```text
ProfMap(P,Q) := Hom_(Prof_cat A B)(P,Q)

ProfCell(R',F,R,G)
  := ProfMap(R', Prof_reindex(R,F,G)).
```

`ProfMap` should initially be a transparent notation/alias for the existing
hom-category:

```text
ProfMap(P,Q) := Hom_(Prof_cat A B)(P,Q).
```

Its identities and composition should remain the existing:

```text
id_funcd;
comp_catd_fapp0.
```

Do not add primitive `ProfMap_id` or `ProfMap_comp` heads merely for naming.
Introduce a stable vertical-map head only after a focused probe demonstrates a
real discrimination, projection, or performance requirement.

Universal properties and profunctor isomorphisms should use vertical
`ProfMap`s. Endpoint-changing constructions should use `ProfCell`s.

This is not an additional nonstandard notion: the right-hand side is exactly
the traditional restriction/base-change reading of an equipment cell. The
existing `Prof_transf_cat` is already definitionally close to this formula and
may remain the implementation of `ProfCell`.

The redesign should nevertheless avoid `ProfCell` whenever all endpoints are
fixed. In particular, strict isomorphisms, representability, implication
functoriality, and weighted-limit preservation should be composed using the
ordinary identity and composition operations of one `Prof_cat`. The
six-endpoint `Prof_comp_transf` should be a derived equipment facade used only
when endpoint change is semantically present.

This vertical-core architecture is preferable to retaining the generalized
Cartier-style shaped-cell calculus merely because it was previously successful.
If the standard `ProfMap` semantics suffices, it is both smaller and more
reusable.

### Companions, Conjoints, And Representables

Organize representables using the standard equipment interpretation. For a
functor `F : A -> B`, distinguish:

```text
Companion_prof(F) := Hom_prof_along(F,id_B)  : Prof(A,B)
Conjoint_prof(F)  := Hom_prof(F)             : Prof(B,A)
Unit_prof(A)      := Companion_prof(id_A)
                  := Conjoint_prof(id_A)
```

The existing symmetric form:

```text
Hom_prof_along(F,G)
```

is then the restriction of the unit/hom profunctor along the pair `(F,G)`.
This explains its legitimate role without making every downstream theorem use
two external shaped functors.

`Hom_prof`, `Unit_prof`, and `Hom_prof_along` may retain their current stable
normal forms. The conceptual companion/conjoint names can initially be
transparent aliases unless focused rewrite discrimination requires stable
heads.

### Functorial Representables And Closed Operations

Introduce or expose:

```text
Hom_prof_func(J,B)
  : Functor(Functor_cat J B, Prof_cat B J)

Prof_imply_cov_func(W)
  : Functor(Prof_cat A J, Prof_cat A J')

Prof_reindex_func(F,G)
  : Functor(Prof_cat A B, Prof_cat A' B')
```

`Prof_reindex_func`, `Hom_prof_func`, the fixed-weight
`Prof_imply_cov_func(W)`, and the direct mixed-variance
`Prof_imply_cov_func2` are active. The remaining closed-structure work is
limited to higher projections and adjunction/naturality packages demanded
downstream.

For every such internalized functor, implementation is not complete at object
action alone. The required checks are:

```text
object action;
whole arrow action in the relevant Prof_cat;
capped arrow projections where consumed;
identity preservation;
composition preservation;
compatibility with Prof_reindex_func.
```

For `Hom_prof_func`, the first five checks now pass. The endpoint-reindex audit
described in the 2026-06-22 checkpoint confirms strict object compatibility
but rejects a direct runtime arrow fold because it adds two identity overlaps.
Its local component delegates to the existing postcomposition telescope rather
than installing duplicate identity/composition rules.

For `Prof_imply_cov_func(W)`, object and generic full/capped action checks pass.
It is the opaque semantic composition of the mixed implication functor with
the fixed-weight insertion. There is no stable unary action head and no local
identity/composition law.

The mixed-variance owner is now active in direct product form:

```text
Prof_imply_cov_func2 :
  Product_cat(Prof_cat(A,X),Op_cat(Prof_cat(B,X)))
    -> Prof_cat(A,B).
```

Its fixed-weight specialization is the unary `Prof_imply_cov_func(W)`, and its
arrow action is the generic action of the mixed functor. Product-object eta is
still absent and unnecessary. Tensor/implication eval and lambda remain the
primitive closed-structure bijection; an ordinary fixed-weight adjunction is
only a possible derived view and must not own that calculus.

## Weighted Limits As Representability

Define the weighted-cone profunctor:

```text
WeightedCone_prof(F,W)
  := Prof_imply_cov(Hom_prof(F),W).
```

Separate the traditional representability property from its computational
refinement:

```text
IsRepresentedBy_iso(P,L)
  := IsoEvidence(Prof_cat B J', P, Conjoint_prof(L)).

IsRepresentedBy_comp(P,L)
  := StrictIso(Prof_cat B J', P, Conjoint_prof(L)).

Representation_iso(P)
  := Sigma L, IsRepresentedBy_iso(P,L).

Representation_comp(P)
  := Sigma L, IsRepresentedBy_comp(P,L).
```

Under global univalence there is also a path-oriented formulation:

```text
IsRepresentedBy_path(P,L)
  := P = Conjoint_prof(L).

Representation_path(P)
  := Sigma L, IsRepresentedBy_path(P,L).
```

The two are connected by:

```text
idtoequiv_cat :
  IsRepresentedBy_path(P,L)
    -> OmegaEquiv(Prof_cat B J',P,Conjoint_prof(L));

equivtoid_cat :
  OmegaEquiv(Prof_cat B J',P,Conjoint_prof(L))
    -> IsRepresentedBy_path(P,L).
```

A strict isomorphism maps to the same `OmegaEquiv`. Recovering a
`StrictIso` from an arbitrary omega-equivalence is not automatic; it is valid
only for the strict fragment or with an additional strictification result.

Consequently, three interfaces must be distinguished:

```text
IsWeightedLimit_cov_iso(F,W,L)
  := IsRepresentedBy_iso(WeightedCone_prof(F,W),L);

IsWeightedLimit_cov_comp(F,W,L)
  := IsRepresentedBy_comp(WeightedCone_prof(F,W),L);

IsBiWeightedLimit_cov(F,W,L)
  := IsRepresentedBy_path(WeightedCone_prof(F,W),L).
```

`IsWeightedLimit_cov_iso` is the ordinary strict categorical isomorphism
property.
`IsWeightedLimit_cov_comp` selects the stronger computational witness needed
by the current cut-elimination API. The existing public
`WeightedLimit_cov(F,W,L)` should remain computational during the migration,
initially as a compatibility name for `IsWeightedLimit_cov_comp`.
Path/omega-equivalence representability must use an explicitly weak name such
as `IsBiWeightedLimit_cov` or `IsWeakWeightedLimit_cov`; it must not silently
change the meaning of the existing API.

The forgetful map:

```text
IsWeightedLimit_cov_comp(F,W,L)
  -> IsWeightedLimit_cov_iso(F,W,L)
```

is induced by `strict_iso_evidence`. The reverse implication is not assumed.

A globally selected weighted-limit operation is a separate later layer:

```text
WeightedLimit_cov_chosen(F,W)
  := Sigma L, IsWeightedLimit_cov_comp(F,W,L).
```

The preservation theorem currently needs only the property at an explicit
candidate `L`; it does not require globally chosen limits.

The two candidate owners remain:

```text
computational owner:
  compose strict isomorphisms directly;

path owner:
  compose paths by eq_trans/ap and derive comparison arrows through
  idtoequiv_cat.
```

The 2026-06-20 result rejects one generic strict-isomorphism presentation; it
does not yet select the path owner. The path owner is architecturally
attractive because path composition,
symmetry, and functorial action can replace a separate strict-isomorphism
algebra. It is feasible only when `Prof_cat` univalence exposes comparison maps
with the required strict beta/eta behavior and with computation over
`eq_trans` and `ap`. Until those focused probes succeed, path
representability remains the weak/biweighted parallel layer rather than the
owner of the computational theorem.

The computational formulation removes the need for a primitive
destructor-only weighted-limit witness immediately and forgets to the
traditional isomorphism property. The path formulation may later provide a
deeper owner after a proven strictification/computation bridge.

For a shaped probe `M : I -> B`, derive:

```text
weighted_limit_cov_comparison_at(isl,M)
  := strict_iso_fmap(Prof_reindex_func(M,id_J'),isl)

weighted_limit_cov_univ_transf(isl,M)
  := strict_iso_to(weighted_limit_cov_comparison_at(isl,M))

weighted_limit_cov_cone_transf(isl,M)
  := strict_iso_from(weighted_limit_cov_comparison_at(isl,M)).
```

For a path-owned witness, replace `strict_iso_fmap` by path action:

```text
weighted_limit_cov_path_at(isl,M)
  := ap(Prof_reindex_func(M,id_J'),isl);

weighted_limit_cov_equiv_at(isl,M)
  := idtoequiv_cat(weighted_limit_cov_path_at(isl,M)).
```

The universal and cone maps are then projections of
`weighted_limit_cov_equiv_at`. They compute to identities when the
representability path is reflexivity, but are not generally identity arrows.

Thus the current shaped API can remain as a compatibility or presentation
layer, while its implementation is derived from one internalized
computational representability isomorphism.

## Computational Adjunction Presentations And The Mate Bridge

### The Active Presentation Is Already Computational

The active v3.2 package:

```text
adj : Adjunction(A,B)
L   := left_adj_func(adj)  : A -> B
R   := right_adj_func(adj) : B -> A
eta := unit_adj_transf(adj)
eps := counit_adj_transf(adj)
```

is a valid computational presentation of an adjunction. Its essential content
is not merely the existence of unit/counit transformations or propositional
triangle equations. The kernel has generalized component-level
cut-elimination rules:

```text
eps[f] o L(eta[g]) -> f o L(g);
R(eps[g]) o eta[f] -> R(g) o f.
```

Here the off-diagonal `tapp1_fapp0` components fuse transformation naturality
with the surrounding arrow cut. These rules are the computational triangle
laws from which the ordinary transpose/untranspose beta laws are expected to
follow.

The redesign must therefore not describe unit and counit as the uniquely
foundational definition of adjunction. In the Došen cut-elimination discipline,
several presentations can carry equivalent computational content:

```text
unit + counit + triangle cut rules;
transpose + untranspose + beta/eta and naturality;
mixed triangular presentations using one unit/counit direction and one mate
operation.
```

For example, from a hom-mate presentation:

```text
transpose    : Hom_B(L a,b) -> Hom_A(a,R b);
untranspose  : Hom_A(a,R b) -> Hom_B(L a,b),
```

one recovers:

```text
eta_a := transpose(id_(L a));
eps_b := untranspose(id_(R b)).
```

Conversely, the familiar object-level formulas are:

```text
transpose(f)   = R(f) o eta_a;
untranspose(g) = eps_b o L(g).
```

The operational normal forms should be chosen to expose the active
`tapp1_fapp0` triangle redexes; the implementation should not blindly expand
these formulas into a bracketing that the cut rules cannot recognize.

The current unit/counit `Adjunction` package should remain the active owner
unless a focused migration establishes computational translations in both
directions to a better presentation. The representability redesign only needs
a presentation-independent consumer boundary: an adjunction supplies its
fully internal hom-mate isomorphism.

### Fully Internal Ambient Mate Isomorphism

The canonical comparison has no external shaped functor:

```text
Adjunction_hom_prof_iso(adj) :
  StrictIso(
    Prof_cat A B,
    Hom_prof_along(L,id_B),
    Hom_prof_along(id_A,R)).
```

Its fibre at `(a,b)` is the traditional hom isomorphism:

```text
Hom_B(L a,b) <-> Hom_A(a,R b).
```

Both shaped variables are derived simultaneously. For:

```text
M : I -> A;
F : K -> B,
```

define:

```text
Adjunction_hom_prof_iso_along(adj,M,F)
  := strict_iso_fmap(
       Prof_reindex_func(M,F),
       Adjunction_hom_prof_iso(adj)).
```

The two sides compute to:

```text
Hom_prof_along(L o M,F);
Hom_prof_along(M,R o F).
```

The previous fixed-`F` comparison is only the specialization along
`(id_A,F)`. The current `Adjunction_prof_transpose(adj,M,F)` and
`Adjunction_prof_untranspose(adj,M,F)` should become the forward and inverse
projections of `Adjunction_hom_prof_iso_along`.

This formulation is both more traditional and more internalized than the
earlier report proposal. It makes naturality in `M` and `F` inherited from
`Prof_reindex_func`, rather than a later collection of theorem-specific rules.

### Computational Ownership

For the current unit/counit presentation, the intended observational behavior
of the ambient generator is:

```text
forward fibre action  -> R(f) o eta;
inverse fibre action  -> eps o L(g);
forward-after-inverse -> identity by the right triangle cut;
inverse-after-forward -> identity by the left triangle cut.
```

At higher dimensions, the corresponding whole and capped projections must be
compatible with representable hom action and the natural-transformation
projection ladder.

Because the current kernel has no general constructor assembling a
`Functord` from these fibre formulas, the ambient mate operations may need
stable primitive heads. Such heads are acceptable as a computational
presentation or definitional extension when all observable structure is tied
to the existing adjunction calculus:

```text
their fibre/arrow projections compute to the mate formulas;
their reindexing computes through Prof_reindex_transf;
their projection-first composites reduce by the existing triangle cuts;
those reductions join the cancellation law of the selected computational
comparison owner;
identity/composition/naturality checks pass without theorem-specific folds.
```

This is different from a bare opaque inhabitant whose only behavior is an
unrelated generic cancellation rule. If a whole-transformation constructor is
later added, the stable mate heads may become transparent definitions without
changing their public normal forms.

The implementation should be staged so that failures identify the missing
layer precisely:

```text
1. fibre mate functors
   Adjunction_transpose_func(adj,a,b)
   Adjunction_untranspose_func(adj,a,b);

2. object and higher-arrow actions of those functors, with beta/eta joins
   against the off-diagonal triangle rules;

3. natural assembly over A^op x B as vertical ProfMaps;

4. packaging as Adjunction_hom_prof_iso(adj);

5. reindexing along arbitrary (M,F) and comparison with the current shaped
   API.
```

The names in the first step are provisional. A direct internalized constructor
is preferable if it exposes the same intermediate checks without duplicating
semantic bodies.

Because the immediate `StrictIso` interface deliberately has no unrestricted
constructor from propositional inverse proofs, the ambient mate is a
semantically justified atomic computational generator. Its justification is
the chosen computational presentation of `Adjunction`, not specifically the
fact that this presentation happens to expose both unit and counit as
primitives.

Under `Prof_cat` univalence, the same comparison induces:

```text
Adjunction_hom_prof_path(adj) :
  Hom_prof_along(L,id_B)
    = Hom_prof_along(id_A,R)
  := equivtoid_cat(
       strict_iso_to_omega(Adjunction_hom_prof_iso(adj))).
```

If the path-oriented route proves computationally cleaner, this path may become
the semantic owner and the mate maps may be recovered by `idtoequiv_cat`. Both
conversion directions and their compatibility with the adjunction cut rules
must be checked before changing ownership.

## Derived Right-Adjoint Preservation

The preservation theorem can be the composition of three generic strict
isomorphisms:

```text
right_adjoint_preserves_weighted_limit_cov(isl,adj)
  :=
  Adjunction_hom_prof_iso_along(adj,id_A,L)
  o
  strict_iso_fmap(Prof_reindex_func(left(adj),id),isl)
  o
  strict_iso_fmap(
    Prof_imply_cov_func(W),
    strict_iso_sym(
      Adjunction_hom_prof_iso_along(adj,id_A,F))).
```

Semantically:

```text
Imply(Hom_A(-,right(F)),W)
  ~= Imply(Hom_B(left(-),F),W)
  ~= Hom_B(left(-),L)
  ~= Hom_A(-,right(L)).
```

This would be an actual definition. Its universal and cone projections would
follow from generic:

```text
strict_iso_to
strict_iso_from
strict_iso_comp
strict_iso_fmap
```

computations.

The theorem-specific large fold and constructor-local preservation rules would
then be unnecessary.

The globally univalent weak/biweighted alternative composes the corresponding
three paths:

```text
right_adjoint_preserves_biweighted_limit_cov_path(isl_path,adj)
  :=
  ap(
    Prof_reindex_func(id_A,L),
    Adjunction_hom_prof_path(adj))
  · ap(Prof_reindex_func(left(adj),id),isl_path)
  · ap(
      Prof_imply_cov_func(W),
      inverse(
        ap(
          Prof_reindex_func(id_A,F),
          Adjunction_hom_prof_path(adj)))).
```

Here `·`, `inverse`, and `ap` are path composition, path reversal, and
functorial action on equality. The public universal and cone transformations
are obtained by applying `idtoequiv_cat` to this composite path.

This path formula should become the owner of the weak/biweighted theorem once
focused probes show that:

```text
idtoequiv_cat(path composite)
```

projects to the expected composite of universal maps without theorem-specific
folds. The strict-isomorphism composite remains the selected owner of the
computational theorem. It may also be converted to ordinary isomorphism
evidence and, through univalence, to a path. Those conversions do not identify
arbitrary weak equivalence or ordinary isomorphism evidence with a
judgmentally cancelling `StrictIso`.

## Duality And Weighted Colimits After The Redesign

The active base-swap-only definition of `Op_prof` remains correct for the
kernel's established opposite convention:

```text
Hom_cat(Op_cat X,b,a) -> Hom_cat(X,a,b).
```

Adding a pointwise `Op_catd` here would introduce an extra fibre opposite and
would break the checked representable behavior. The redesign does not reopen
that decision unless the underlying `Op_cat` semantics itself changes.

The three representability interfaces should dualize definitionally:

```text
IsWeightedColimit_con_iso(F,W,L)
  := IsWeightedLimit_cov_iso(Op_func(F),Op_prof(W),Op_func(L));

IsWeightedColimit_con_comp(F,W,L)
  := IsWeightedLimit_cov_comp(Op_func(F),Op_prof(W),Op_func(L));

IsBiWeightedColimit_con(F,W,L)
  := IsBiWeightedLimit_cov(Op_func(F),Op_prof(W),Op_func(L)).
```

The existing `WeightedColimit_con` remains a compatibility name for the
computational interface. Therefore:

```text
left_adjoint_preserves_weighted_colimit_con(isc,adj)
  := right_adjoint_preserves_weighted_limit_cov(
       isc,
       Op_adjunction(adj))
```

should remain a transparent dual of the genuinely defined right-adjoint
theorem.

Generic transport of profunctor isomorphisms through duality eventually
deserves:

```text
Op_prof_func(A,B) :
  Functor(Prof_cat A B,Prof_cat (Op_cat B) (Op_cat A)).
```

Its object action is `Op_prof` and its arrow action is the vertical
specialization of `Op_prof_transf`. It should have involution, identity,
composition, representable, and `strict_iso_fmap` checks. This functor is
useful for the reusable duality library, but the transparent colimit
definition above means it is not a prerequisite for replacing the
right-adjoint preservation theorem.

## Focused Feasibility Evidence

Two focused probes already support the central internalization claim.

### Internalized Weighted-Limit Universal Cell

One ambient universal cell at the identity probe:

```text
Prof_imply_cov(Hom_prof(F),W)
  ->
Hom_prof(L)
```

was successfully reindexed along arbitrary:

```text
M : I -> B
```

to exactly the current shaped universal-map type.

Successful probe log:

```text
logs/probes/profunctor_weighted_limit_internalized_probe-20260619-135634.log
```

### Internalized Adjunction Hom Bridge

The earlier probe established that a fixed-`F` ambient adjunction
hom-profunctor cell can be reindexed along arbitrary:

```text
M : I -> A
```

to exactly the current shaped transpose type.

Successful probe log:

```text
logs/probes/profunctor_weighted_limit_internalized_probe-20260619-135825.log
```

The stronger fully internal formulation has now also passed. One ambient map:

```text
Hom_prof_along(L,id_B)
  ->
Hom_prof_along(id_A,R)
```

over `A^op x B`, reindexed simultaneously along:

```text
M : I -> A;
F : K -> B,
```

has exactly the current shaped transpose type. The inverse direction passes
the same check.

Successful probe log:

```text
logs/probes/profunctor_adjunction_fully_internal_probe-20260620-162419.log
logs/probes/profunctor_adjunction_fully_internal_surface_probe-20260620-162800.log
```

The second probe checks the current `Prof_transf_cat` surface directly rather
than only its unfolded `Functord` normal form.

These probes establish that the proposed internalization does not require a
new base-reindexing mechanism. The missing work is the generic
isomorphism/representability and functorial-closed-operation infrastructure.

### Basic Equality And Propositional Isomorphism Data

A final-review probe established that the current kernel can already express:

```text
eq_sym by equality induction;
nondependent ap by equality induction;
Sigma-encoded propositional IsoEvidence data;
the reflexivity evidence package.
```

Successful probe log:

```text
logs/probes/profunctor_representability_final_review_probe-20260619-184248.log
```

This establishes that propositional isomorphism data is easy to represent. It
does not establish a computational `StrictIso` interface. The remaining
difficulty is selecting a coherent owner for judgmental cancellation,
composition, functorial image, and the desired projection normal forms.

They also support a selective internalization policy:

```text
internalize both hom variables of the adjunction mate immediately;
derive every shaped (M,F) mate by Prof_reindex_func(M,F);
internalize the weighted-limit probe M immediately;
keep the diagram F, weight W, and candidate L as weighted-limit theorem
parameters until their simultaneous variation has a concrete consumer.
```

Internalization should remove duplicated external quantification and expose
actual functorial action. It should not be pursued solely to maximize the
number of variables hidden inside one primitive.

## Feasibility Risks And Required Probes

### Strict Isomorphism Composition

The current kernel has equality induction and transitivity, generic identity
cuts, and specialized composition normal forms. It does not yet expose a
generic proof-level associativity theorem for arbitrary `comp_fapp0` or
`comp_catd_fapp0`.

The following proposed interface was probed:

```text
strict_iso_to
strict_iso_from
strict_iso_refl
strict_iso_sym
strict_iso_comp
strict_iso_fmap
strict_iso_evidence
```

The probes distinguished:

```text
IsoEvidence as nested Sigma data with explicit equality evidence;
a dedicated computational StrictIso classifier;
identity-arrow specializations for judgmentally equal endpoints.
```

The Sigma evidence representation passed and is active. Arbitrary-witness
cancellation with `strict_iso_refl`, `strict_iso_sym`, `strict_iso_comp`, and
`strict_iso_fmap` did not pass the critical-pair audit and is not active.

A temporary probe of the rejected unrestricted constructor/projection design
did pass ordinary typechecking:

```text
logs/probes/strict_iso_intro_overlap_probe-20260620-155202.log
```

That result is deliberately negative evidence only: ordinary typechecking did
not inspect or establish joinability of the nested projection/cancellation
overlap.

An unrestricted `strictify_iso : IsoEvidence -> StrictIso` remains outside the
plan. If explored later, it must test the constructor-projection versus
generic-cancellation overlap explicitly.

It must also test the critical overlaps between:

```text
projection and cancellation of strict_iso_refl;
projection and cancellation of strict_iso_sym(i);
generic cancellation of strict_iso_comp(i,j);
projection of strict_iso_comp(i,j) to composites of component arrows;
projection and cancellation of strict_iso_fmap(F,i);
identity cuts;
generic functor identity/composition action;
any associativity unification rule.
```

The required join would make both:

```text
strict_iso_from(strict_iso_comp(i,j))
  o strict_iso_to(strict_iso_comp(i,j))
```

and its projected/reassociated component form reduce or unify with the same
identity. The tested projection-expanding strategy failed this requirement.
The tested strategy in which a stable composite head accumulated ordinary
composition also failed because it overlapped reflexivity, symmetry, identity,
and component projection. Neither strategy is safe.

If composition of equality evidence is blocked only by bracketing, the active
ordinary associativity unification equation may solve the proof-time
constraint. If it exposes a performance problem, rerun with warnings and
audit existing interacting LHSs for reducible non-discriminator arguments
before rejecting the equation itself. Do not turn arbitrary arrow
associativity into a global reduction rule.

### Global Equivalence And Univalence Infrastructure

Equivalence and univalence are no longer treated only as an optional
subuniverse side quest. They are part of the intended meaning of `Grpd`,
`Cat`, and `Cat_cat`. Their implementation must still be staged.

The groupoid/HoTT layer first needs focused designs for:

```text
eq_sym;
ap and dependent ap;
dependent groupoid-level Pi or an adequate classifier;
IsContr(A);
homotopy fibre of a map;
IsEquivMap(f);
TypeEquiv(A,B);
idtoequiv_grpd / ua_grpd.
```

Some initial probes may use bi-invertible map data before `IsContr` and
dependent Pi are available. That temporary representation must be documented
and connected to the final `IsEquivMap` interface rather than silently
becoming the definition.

The categorical layer must determine:

```text
whether OmegaEquiv is inductive, coinductive, or encoded by destructors;
how separate left and right inverse data are represented;
how cancellation recurses through higher hom-categories;
how StrictIso maps into OmegaEquiv;
how OmegaEquiv relates to the existing groupoid equality;
which computation is definitional and which is propositional;
whether CatUnivalence(C) is an explicit structure or direct global operations;
how constructor-specific univalence closure is registered incrementally.
```

The foundational commitment that every `C : Cat` is univalent may initially be
implemented by a generic primitive bridge with only reflexivity computation.
That is an explicit kernel assumption, not a derived closure theorem.
Constructor-specific computation should then progressively reduce the generic
bridge for `Path_cat`, `Op_cat`, products, functor categories, family
categories, Sigma/Pi, profunctors, and `Cat_cat`.

For weighted limits, the implementation should probe both:

```text
StrictIso representability;
path representability via univalence.
```

Computational representability is the selected first active implementation.
It immediately yields ordinary isomorphism representability by forgetting
judgmental computation. Path representability remains a parallel
weak/biweighted experiment and may become a deeper owner only after
`idtoequiv_cat` computes over path composition and functorial action. General
`OmegaEquiv` and full univalence closure are not prerequisites for replacing
the current computational preservation theorem.

### Completeness Boundary

This redesign addresses:

```text
the global univalence contract for Cat and Cat_cat;
the initial TypeEquiv/OmegaEquiv distinction and path bridges;
vertical profunctor maps and endpoint restriction;
representables and their functoriality;
closed implication functoriality;
ordinary isomorphism representability and its computational refinement;
right-adjoint preservation;
left-adjoint preservation by duality.
```

It does not by itself provide:

```text
coend/end semantics for tensor and implication;
general tensor associators and unitors;
weak/pseudo weighted limits;
full computation of univalence for every category constructor;
all HoTT laws for Sigma, Pi, identity, and universe types;
the complete computational equivalence of every standard adjunction
presentation;
generic directed-inductive types or a semantic collage construction.
```

The first two univalence interfaces are part of the foundational architecture;
their complete constructor-specific computation remains incremental rather than
a prerequisite for the first representability migration.

## File And Migration Management

This redesign changes a substantial connected region of `emdash3_2.lp`, but it
should not be implemented by first deleting that region and reconstructing it
from a copied backup.

### Git Is The Baseline Owner

Do not add tracked files such as:

```text
emdash3_2_backup.lp;
emdash3_2_before_representability.lp;
emdash3_2_checks_backup.lp.
```

They would create stale parallel specifications, duplicate module surfaces,
confuse searches and reference lint, and eventually diverge from the active
file. They are weaker baselines than an immutable Git commit.

At the time of this file-management review, the active Lambdapi implementation
and checks are at:

```text
8cdf0e3c074a18496ae5e9cf53931bfd0f5fa583
```

Before the first implementation slice:

```text
commit the finalized plan or otherwise start from a deliberately recorded
worktree state;
run git status --short;
record git rev-parse HEAD in the implementation log;
run make ci.
```

That commit is the migration baseline. The old files remain available without
copying:

```text
git show BASELINE:emdash2/emdash3_2.lp;
git show BASELINE:emdash2/emdash3_2_checks.lp;
git diff BASELINE -- emdash2/emdash3_2.lp emdash2/emdash3_2_checks.lp.
```

An optional tag or dedicated branch may be created by the maintainer for
workflow convenience, but neither is technically required once the baseline
commit has been recorded. The implementation should not create branches,
tags, or commits implicitly.

### Three Distinct Working Surfaces

Use three surfaces for different purposes.

#### 1. Focused Probe Files

Use:

```text
tmp/probes/<slice>_probe.lp
```

for isolated declarations, rules, and assertions. Prefer importing
`emdash.emdash3_2` and using `Probe_*` names when the experiment is additive.
Run the probe with `scripts/probe.sh`.

When an experiment must remove, reorder, or replace an existing declaration or
rule, an imported additive probe is insufficient. In that narrow case, create
a temporary full-file copy under `tmp/probes/`, patch only the relevant region,
and append focused assertions. This is a disposable cutover simulation, not a
backup or an implementation target.

Successful declarations and checks must be promoted to the active files.
Temporary probe files must then be deleted. Probe logs may be cited in this
report when they provide architecture evidence.

#### 2. Active Additive Integration

Promote stable results directly into:

```text
emdash3_2.lp;
emdash3_2_checks.lp.
```

Do this incrementally while the current profunctor and weighted-limit API
remains active. In particular:

```text
add IsoEvidence and computational StrictIso infrastructure;
add functorial representable/implication infrastructure;
add the fully ambient adjunction mate;
add computational representability;
add a derived preservation implementation under a bounded provisional name
when the existing public name prevents parallel definition.
```

Each promoted slice must include focused diagnostics in
`emdash3_2_checks.lp` and pass a timeout-bounded `make check`. Refresh the
catalog after adding or reorganizing assertions. Run `make health` and
`make ci` at architectural checkpoints.

Do not use a backup copy as the place where successful probes accumulate. That
would postpone integration conflicts and test only a fork rather than the
active kernel.

#### 3. Legacy Compatibility Surface

Keep the current:

```text
WeightedLimit_cov;
weighted_limit_cov_univ_transf;
weighted_limit_cov_cone_transf;
Adjunction_prof_transpose / Adjunction_prof_untranspose;
right_adjoint_preserves_weighted_limit_cov;
WeightedColimit_con and left-adjoint preservation facade
```

active while their generic replacements are being built. New generic
infrastructure should coexist with these symbols until the replacement:

```text
has the required object, whole-arrow, and capped projections;
passes identity/composition/cancellation checks;
reproduces the current shaped endpoint types;
passes a behavior-parity check against the old public API.
```

This is an additive migration, not a second permanent architecture. Provisional
parallel names must be few, scoped to the cutover, and listed in the
implementation log.

Keeping the legacy rules active can mask missing generic computation. In
particular, the existing explicit preservation-composite fold may recognize a
term produced by the provisional implementation and reduce it through the old
theorem-specific path.

Therefore every replacement slice that overlaps a legacy rule needs two
results:

```text
compatibility result:
  the new construction coexists with the active public API;

independence result:
  the new construction still passes its focused assertions in a temporary
  full-file probe with the overlapping legacy fold/rules disabled.
```

Use static search and `scripts/decision_tree.sh` to identify candidate masking
rules before the temporary-removal probe. Record every disabled legacy rule
and the first downstream failure, if any, in the implementation log.

### Cutover Procedure

Do not delete the old weighted-limit/preservation block at the beginning of
the work. Perform the public-name cutover only after the replacement is green
under provisional names.

The cutover should be one bounded slice:

```text
1. record a pre-cutover Git checkpoint;
2. use a temporary full-file cutover probe if removing the old declarations is
   necessary to test the final public names;
3. verify the replacement's independence with every overlapping
   theorem-specific legacy fold disabled;
4. deactivate only the exact legacy declarations/rules being replaced;
5. install the derived implementations under the established public names;
6. redirect compatibility projections to the new generic owner;
7. migrate existing diagnostics without weakening their behavioral coverage;
8. run bounded make check, make catalog, make health, and make ci.
```

If active-file debugging temporarily requires disabling legacy code, comment
that exact block with a dated migration marker rather than deleting it
immediately, as required by the repository SOP. Once the replacement passes
all gates and the baseline/pre-cutover commits preserve the old text, remove
the commented block in a dedicated cleanup slice. Long-lived commented copies
are not an acceptable backup strategy.

Never use destructive Git restoration to perform this process. Inspect old
text with `git show` and edit the active files deliberately. Existing unrelated
worktree changes must be preserved.

### Check Migration And Regression Discovery

`emdash3_2_checks.lp` is not to be replaced wholesale. Add new checks beside
the old checks first. Maintain a small parity inventory covering:

```text
old public computation;
new generic computation;
old shaped endpoint;
new reindexed ambient endpoint;
forward/inverse cancellation;
duality and left-adjoint preservation;
the same new computations with overlapping legacy rules disabled;
timeout/performance behavior.
```

At cutover, rewrite only checks whose owning symbol changes. Preserve tests of
observable behavior even when their implementation-specific term changes. A
check may be removed only when the report records which stronger check
subsumes it.

### Module Splitting

Do not combine this semantic migration with a broad physical split of
`emdash3_2.lp`. A new extension module that merely imports the old monolith
cannot replace declarations already owned by it, while extracting prerequisites
would add a second large dependency migration.

After the new architecture and public cutover stabilize, a separate
reorganization plan may extract generic equivalence, profunctor, or
representability modules. Until then, use comments and local section placement
to keep ownership clear.

## Migration Strategy

The work should proceed on two tracks. Global univalence remains a foundational
commitment, but it is not on the critical path for repairing computational
weighted limits.

### Critical Path: Computational Representability

1. Completed: introduce transparent `ProfMap` notation over
   `Hom_(Prof_cat A B)` and verify that identity/composition are already owned
   by `id_funcd` and `comp_catd_fapp0`. Treat endpoint-changing `ProfCell` as
   restriction into a fixed target.
2. Completed: introduce Sigma-encoded `IsoEvidence` with forward/inverse
   projections, both propositional inverse proofs, reflexivity, symmetry,
   transparent composition, and strict-functor image. Ordinary associativity
   is proof-time unification with transparent `eq_refl` evidence, not runtime
   arrow rewriting.
3. Rejected: the proposed generic computational
   `StrictIso` classifier with ordinary-composition cancellation,
   reflexivity/symmetry/composition projections, and functorial image. Both
   projection-expanding and composition-folding presentations failed the
   decision-tree critical-pair audit.
4. Completed after redesign: select `ProfComparison`, whose inverse
   `prof_comparison_push/pull` operations compute on dedicated heads.
   Selected arrows are identity applications; inward accumulation derives
   ordinary postcomposition behavior; `hom_postcomp_func` owns functorial and
   higher action. Proof-time unification makes selected-arrow/evidence
   agreement reflexive, and general semantic proofs are transparent.
   Direct cancellation under `Prof_comp_transf` was rejected after active
   duality overlaps increased the warning inventory.
5. Completed: add transparent companion/conjoint presentation names and
   ordinary `IsRepresentedBy_iso`/`Representation_iso`.
6. Completed after redesign: `Hom_prof_func` is the stable opaque view of a
   semantic composition/precomposition/uncurry pipeline. Object, whole
   hom-action, capped action, fibre component, identity, and composition are
   checked. Strict functoriality is inherited globally; no constructor-specific
   identity/composition rule was promoted. A generic `Catd_cat` composition
   cut bridges canonical `comp_catd_fapp0` normalization.
7. Completed after correction: add fixed-weight `Prof_imply_cov_func` as the
   opaque semantic composition of the mixed functor with
   `Prof_imply_cov_fixed_weight_func(Q)`. Object action computes; full/capped
   action, identity, and composition are inherited from the global functor
   calculus.
7a. Completed after kernel correction: add the direct mixed-variance
    `Prof_imply_cov_func2`. Its object action computes, its full/capped actions
    remain generic, and fixed-endpoint `Prof_imply_cov_transf` folds to that
    generic action. Dedicated unary/mixed action heads and their local
    identity/composition rules were removed. Componentwise product identity
    projections and the global Catd identity-action bridge make arbitrary
    opaque product identities compute. The temporary curried workaround was
    removed.
8. Completed for the selected comparison owner:
   `prof_comparison_fmap` transports certified comparisons through
   `Prof_reindex_func` and `Prof_imply_cov_func(W)`. Its ordinary evidence
   computes through `iso_evidence_fmap`; its target eliminators remain stable
   because an arbitrary target probe cannot invoke the source eliminator.
9. Completed: `IsRepresentedBy_iso`,
   `Representation_iso`, `WeightedCone_prof`, and
   `IsWeightedLimit_cov_iso` over `IsoEvidence`. The generic
   `iso_evidence_fmap` now maps ordinary comparisons through
   `Prof_imply_cov_func(W)`. The parallel computational classifier
   `IsWeightedLimit_cov_comp` is active over `ProfComparison`, with shaped
   push/pull operations and selected identity applications.
10. Completed for ordinary and computational evidence:
   `Adjunction_hom_prof_iso_evidence(adj)` packages the active mate operations
   in `IsoEvidence`, and
   `Adjunction_hom_prof_iso_evidence_along(adj,M,F)` is its simultaneous
   reindexing along both hom variables. Its forward/inverse projections compute
   to the existing shaped transpose/untranspose heads.
   `Adjunction_hom_prof_comparison(adj)` is the atomic certified computational
   mate, and its shaped form is obtained by comparison functoriality.
11. Completed in both parallel APIs:
   `right_adjoint_preserves_weighted_limit_cov_iso` is a transparent
   composition of implication functoriality, reindexed weighted-limit
   evidence, and ambient adjunction-mate evidence.
   `right_adjoint_preserves_weighted_limit_cov_comp` composes the same three
   certified comparisons and forgets exactly to the ordinary theorem.
12. Completed: one ambient weighted-limit comparison is reindexed to every
   shaped probe, and its inverse operations act on every incoming profunctor
   map. The selected universal and cone maps are identity applications.
13. Completed: migrate selected-arrow checks and public consumers to the
   eliminator API. Preserve selected projection checks while replacing
   duplicate `Prof_comp_transf` cancellation checks with arbitrary-map
   push/pull beta/eta.
14. Completed: replace the primitive preservation theorem and remove its
   theorem-specific rewrite behavior from the active calculus. After the
   cutover passed all validation gates, the dated commented implementation
   and diagnostic copies were removed; Git history remains the baseline
   reference.
15. Completed and retained: left-adjoint preservation is a transparent dual
    of the genuinely defined right-adjoint theorem.

### Parallel Track: Equivalence And Computational Univalence

1. Record the foundational contract that `Cat` classifies univalent
   omega-categories and that `Cat_cat` is univalent, including the unresolved
   universe-stratification/impredicativity interpretation.
2. Add the minimum equality infrastructure: `eq_sym`, `ap`, dependent `ap`,
   and the groupoid-level classifiers needed for `TypeEquiv`.
3. Design `TypeEquiv` using `IsEquivMap`, with temporary bi-invertible data only
   as an explicitly bridged prototype.
4. Probe `OmegaEquiv` using primitive recursive destructors, finite-height
   approximations, or path-first ownership. Do not require a final solution for
   the computational profunctor migration.
5. Add `idtoequiv_cat`, `equivtoid_cat`, reflexivity computation, and the
   `Core_cat(C) -> C` path-to-arrow bridge.
6. Add compatibility computation for path composition and functorial `ap`
   before using paths as computational owners.
7. Add univalence closure by semantic ownership: first `Path_cat`, `Op_cat`,
   `Product_cat`, `Functor_cat`, and `Cat_cat`; inherit `Catd_cat` and
   `Prof_cat` behavior through their definitions whenever feasible.
8. Introduce `IsBiWeightedLimit_cov` or `IsWeakWeightedLimit_cov` as the
   path/omega-equivalence representability property.
9. Define the path-based right-adjoint-preservation theorem and compare its
   projected maps against the computational theorem.
10. Promote path ownership only if those projections compute without
    theorem-specific folds and a strictification theorem justifies any claimed
    computational result.

### Later Consolidation

After the two tracks stabilize:

1. Refactor eval/lambda and other inverse-pair APIs onto the reusable strict or
   weak equivalence infrastructure according to their actual semantic strength.
2. Refactor weighted colimits through duality without duplicating the proof
   calculus.
3. Expose `Op_prof_func` when generic transport of maps or isomorphisms through
   duality has a concrete consumer.
4. Add chosen representation/limit operations only when a downstream consumer
   needs:

```text
Representation_iso(P);
Representation_comp(P);
WeightedLimit_cov_chosen(F,W).
```

5. Extend constructor-specific univalence closure and document every remaining
   stuck projection.

## Acceptance Criteria

The selected computational owner is now `ProfComparison`, not generic
`StrictIso`. Any later global strict-isomorphism interface is independent and
must satisfy its own confluence audit.

The computational migration is complete only when all of the following hold:

```text
right_adjoint_preserves_weighted_limit_cov has a defining body;
its universal operations are projections of constructed ProfComparison data;
their beta/eta laws follow from dedicated push/pull elimination;
ProfComparison forgets to coherent propositional IsoEvidence;
the computational weighted-limit witness forgets to the ordinary
isomorphism-representability property;
every nontrivial atomic ProfComparison exposes ordinary evidence and
reflexive selected-arrow bridges;
general postcomposition semantics is derived transparently from accumulation;
the ambient weighted-limit witness reindexes to every shaped probe M;
the ambient adjunction mate reindexes simultaneously to every shaped pair
(M,F);
the mate evidence computes to the chosen adjunction presentation;
the old theorem-specific exact-syntax fold is unnecessary;
the preserved push and pull operations are equally explicit and computational;
left-adjoint colimit preservation remains a transparent dual;
all existing diagnostics pass without hidden primitive replacement axioms.
```

Additionally:

```text
ProfMap remains transparent unless a focused probe justifies a stable head;
prof_comparison_refl/sym/comp push/pull paths join;
prof_comparison_fmap evidence computes without exposing an invalid target
action formula;
prof_comparison_push/pull_func use generic hom_postcomp infrastructure and
compute to the eliminators on objects;
Hom_prof_func and Prof_imply_cov_func pass identity/composition checks;
any Catd_cat-specialized univalence head documents Functor_cat as owner;
the adjunction mate bridge has no behavior independent of the chosen
computational Adjunction presentation;
any temporary whole-transformation head records the constructor that prevents
it from being a transparent definition.
```

The implementation must document every new stable computational head,
including:

```text
ProfComparison and prof_comparison_push/pull/evidence;
prof_comparison_refl/sym/comp/fmap;
Hom_prof_func;
Prof_imply_cov_func;
Adjunction_hom_prof_comparison and its evidence projection;
closed implication arrow action.
```

These heads are not automatically architectural debt: stable constructors may
be the intended computational presentation. An adjunction mate head is
acceptable when its projections, naturality, and cancellation are
computationally fixed by the active `Adjunction` interface. A bare opaque
`Adjunction_hom_prof_iso` without those bridges remains unacceptable.

The internalization target is:

```text
one ambient weighted-limit comparison internalizes the probe M;
one ambient adjunction mate internalizes both hom variables and derives every
shaped pair (M,F) by reindexing;
the weighted diagram F, weight W, and candidate L remain theorem parameters
until their simultaneous variation has a concrete downstream use.
```

The weak/path track is computationally ready only when:

```text
idtoequiv_cat computes on reflexivity, path composition, and ap;
path-owned representability projects to the expected nonidentity maps;
ordinary-isomorphism, computational, and weak weighted-limit names remain
semantically distinct;
constructor-inherited Prof_cat univalence does not require duplicate broad
rewrite rules.
```

Every migration slice should use focused probes, then `make check`; substantial
handoffs should refresh `make health` and pass `make ci`.

## Current Provisional Conclusion

The object-level `Prof_tensor` and `Prof_imply_cov` may remain primitive while
coend/end semantics are absent. Their primitivity is not the main problem.

The missing architectural pieces are:

```text
global but incrementally computational univalence for Cat and Cat_cat;
separate TypeEquiv, IsoEvidence, StrictIso, and OmegaEquiv layers;
functorial ownership of representables and closed operations;
vertical ProfMap ownership beneath endpoint-changing ProfCell;
the active dedicated ProfComparison algebra and its future generalization;
generic representability;
internalized rather than externally repeated universal properties;
companion/conjoint organization of representables;
an explicit boundary among ordinary-isomorphism, computational, and weak
weighted-limit semantics.
```

The implementation confirms vertical `ProfMap` ownership, ordinary
isomorphism representability, and dedicated inverse eliminators as coherent
foundations. It rejects a single generic judgmentally cancelling `StrictIso`
classifier as the immediate computational owner. Computational univalence
remains a parallel foundational track and may later generate or classify
certified comparisons.

The redesign should still be evaluated globally against tensor, co-Yoneda,
implication, weighted limits, duality, and join usage. It must not be
implemented as a theorem-local cleanup.

The computational representability migration and first mixed-variance
internalization are complete. The next work is bounded to independent
extensions:

```text
retain ProfComparison as the computational representability owner;
retain the direct mixed implication bifunctor and projection-owned product
identity computation;
retain eval/lambda as the primitive tensor-implication bijection and add its
direct Došen-style naturality cuts;
derive any later fixed-weight ordinary adjunction view from that closed
calculus rather than making it the owner;
develop TypeEquiv/OmegaEquiv/univalence as the parallel foundational track;
require warning-enabled owning-module validation for every promoted rule.
```

`OmegaEquiv`, full univalence, higher implication projections, and a
tensor/implication adjunction should still not all be mixed into one migration
slice. Neither should an unrestricted `IsoEvidence -> StrictIso`
strictification constructor be added. The failed probes establish that passing
beta/eta assertions is weaker than establishing a coherent computational
algebra; active warning and confluence audits remain promotion criteria.
