# Homology Internalization: Variance Owner Audit

Date: 2026-09-08

Status: reviewed inventory; dependent contravariant implementation remains experimental

Parent: [strict internal homology pilot](TYPESCRIPT_EMDASH_STRICT_INTERNAL_HOMOLOGY_PILOT_PLAN.md)

Implementation baseline: `febf287d`; planning checkpoint: `b3144f40`.

## Purpose And Scope

The user's proposed `fdapp1_con_int_hom_func` is a reason to audit the whole
dependent hom-action and laxity-extraction ladder, not just a leaf name.
This inventory covers the active nucleus's Hom, composition, ordinary and
displayed action, represented transport, opposite, Sigma/Pi and path-category
families, together with the directly relevant cubical extension owners. It
does not claim that every mathematically imaginable dual needs a new symbol,
or inventory all applied algebraic-geometry constructions.

Source declarations, their actual projection rules and typed probes are the
authority. A missing name, a missing semantic operation and a missing runtime
projection are different findings. In particular, a defined `con` alias can
be a useful whole interface without becoming a discriminating rewrite head.

## Findings By Foundational Family

| Family | Present owner or dual route | Finding and action |
|---|---|---|
| ordinary represented Hom | `hom_` / `hom_con` | Both are stable owners; no missing mirror. |
| internalized ordinary Hom | `hom_int` / `hom_con_int` | Both exist, with whole projection ladders and proof-time opposite comparison. |
| ordinary post/precomposition | `hom_postcomp_*` / `hom_precomp_along_*`, including telescope, whole Hom action, transfor and capped projections | Both polarities exist. Do not infer a gap from the different naming conventions. |
| varying represented source/target | `hom_int_precomp_*` / `hom_con_int_postcomp_*` | Both are implemented; these are the relevant internal endpoint owners. |
| composition in Cat | `comp_cat_cov_*` / `comp_cat_con_*` | Both delegate to the preceding generic owners and expose their transfor projections. |
| ordinary internal functor/transfor action | `fapp1_int_transf`, `tapp1_int_*`; defined `fapp1_con_int_transf`, `tapp1_con_int_fapp0_transf`, `fapp1_con_at_transf`, `tapp1_con_at_transf` | The target-internalized mirror already exists through ordinary Op. It is not a missing independent theory. |
| higher variation of the ordinary mirrored transfor | no named `tapp1_con_int_func_transf` or `tapp1_con_int_fapp1_func_transf` | Explicitly consumer-gated in the source header. The returned mirror transfor retains its source-variable action; a whole functor in epsilon is a distinct further interface. |
| dependent endpoint Hom and its internal package | `homd_`, `homd_int`, `homd_src_func`, `homd_src_sec`, `homd_tgt_func` | No named dependent `homd_con_` / `homd_con_int` ladder in active source. A native reversed-Hom endpoint-family probe now passes; the full target family and internalization must still be designed. |
| displayed functor internal action | `fdapp1_int_transfd`, section/target/presheaf/whole-Hom/capped/cell projections | No active `fdapp1_con_int_*` owners. The current concrete consumer reaches the existing ladder at `Op_funcd(FF)`. A fixed-base-arrow native-typed alias is checked, but it has no new runtime discriminator. |
| displayed transfor internal action | `tdapp1_int_func_transfd`, `tdapp1_int_fapp0_transfd`, `tdapp1_int_fapp1_func_transfd`, and their projection ladder | No active `tdapp1_con_int_*` mirror. Audit this together with the functor identity specialization; duplicating only the final cell would leave the whole higher-action story unspecified. |
| whole displayed laxity extraction | `fdapp1_project_*`, `fdapp1_comma_projection_func/transf`, `functord_laxity_transf` | No named dependent contravariant extraction ladder. This is a candidate companion of the preceding internal action, not permission to postulate new laxity cells independently. |
| ordinary post/left and pre/right laxity | `tapp1_post_laxity_transf/cell` and `tapp1_pre_laxity_transf/cell` | Both already exist and reuse the shared displayed extractor. The pre/right route uses `hom_con` and `tapp1_con_at_transf` over `Op_cat A`. |
| pointwise opposite of families and displayed maps | `Op_catd`, `Op_catd_func`, `Op_funcd` | Categories, components and involutions exist, but the whole `Op_catd_func` first action is not currently identified computationally or by the tested unifier with `Op_funcd`. This is a separate owner-link gap, confirmed by a focused probe. |
| opposite of displayed transfors | ordinary `Op_transf` exists; no named `Op_transfd` | Do not equate ordinary base reversal, pointwise fibre opposite and reversal of a higher transfor. Audit source/target directions before proposing a higher mirror. Generic higher action of an existing functor remains available, but its identification with a desired opposite operation is not automatic. |
| fibre transport | `fib_cov_tapp0_func`, `fib_cov_int`, `fib_cov_transf`, `catd_transport_func` | No separately named `fib_con_*` family. A contravariant family is already represented over `Op_cat K`; this is not evidence that its basic transport is absent. Add a stable mirror only for a measured whole-variable or projection consumer. |
| mixed family classifiers | `Functor_catd`, `Hom_catd`, `Transf_catd`, `Catd_catd_con` | Variance is already in the input families. A second classifier named `*_con` is not justified merely by symmetry. The currently probed constant-domain displayed evaluation uses these existing owners. |
| Sigma/Pi, sections and total maps | `Sigma_cat`, `sigma_map_func`, `Pi_cat`, `piapp*`, `section_total_func`, their Op-derived uses | Sigma and Pi are different universal constructions, not missing `con` variants of one another. No blanket duplicated totalization calculus is proposed. Projection-order joins may be needed where an Op wrapper hides an existing computational owner. |
| source/target total projections | generic Sigma projection; `sigma_proj1_family_funcd` with ordinary and `Op_funcd` projection instances | The cubical extension already demonstrates justified duplication of a narrow opposite projection without a new primitive theory. This is a design reference for the current consumer. |
| outgoing/incoming path categories | `PathOut_cat`, `PathOut_cat_func`, `PathOut_transport_func`; no `PathIn_cat` family | An incoming category is a candidate Op-derived alias, not a missing mathematical construction established by this audit. It is not required by the current outgoing-path triangle prototype. |
| cubical internal Hom and arrow category | `homdc_`, `homdc_int`, `homdc_total_cat`, `LaxArrow_cat` | Already derived through nested Sigma/opposite and `homd_int`; do not add an independent square grammar. The separate `CubicalArrow_func(F,P)` lifts a supplied pseudofunctor, not a ready-made whole endofunctor of Cat. |
| profunctor implication and weighted duality | covariant/contravariant implication and evaluation owners; `Op_prof`, weighted-limit/colimit comparison owners | Both polarities are already represented. No new missing `con` family is inferred for these unrelated consumers. |

The relevant active declarations are in
[the nucleus](../emdash2/emdash3_2.lp), especially sections 4, 7e–7f,
8–16 and 18zz–19, and in
[cubical total projections](../emdash2/emdash3_2_cubical_square_total.lp),
[cubical internalization](../emdash2/emdash3_2_cubical_internalization.lp) and
[cubical functor lifting](../emdash2/emdash3_2_cubical_arrow_functor.lp).
The ordinary pre/right extraction is exercised by
[the dependent-Hom laxity reviewer](../emdash2/examples/dependent_hom_laxity.lp).

## The Existing Laxity Ladder And Its Prospective Mirror

The current extraction is genuinely internal:

```text
homd_int
  → fdapp1_int_transfd
  → section / target / presheaf / Hom projections
  → self-comma transported-identity section
  → fdapp1_comma_projection_transf
  → functord_laxity_transf
  → component and further Hom action.
```

The ordinary pre/right route does not independently supply a square. It feeds
`tapp1_con_at_transf(epsilon,Y)` between the corresponding `hom_con` families
into that same extractor over `Op_cat A`. Its component reads

```text
epsilon[q] ∘ F[h] ⇒ epsilon[q ∘ h].
```

Thus the user's suggested architecture is already present in the ordinary
case. The outstanding question is the analogous fully dependent mirror,
including its internal target family, arbitrary-transfor action, identity
specialization and identity-section extraction. A standalone
`fdapp1_con_int_hom_func` would be only one rung of that story.

## Two Checked Interfaces, With Different Variance Roles

For FF:D⇒E, the existing dependent endpoint family has the reading

```text
homd_(FF,x,u,y,v)[p] = Hom(E[y], E[p]u, FF[y]v)
```

and is contravariant in p:Hom_K(x,y). Reversing the fibre Hom changes this
base-Hom variance:

```text
homd_con_(FF,x,u,y,v)[p] = Hom(E[y], FF[y]v, E[p]u),
homd_con_(...) : Hom_K(x,y) → Cat.
```

The ignored `hint_homd_con_fibre.lp` defines this whole family directly from
existing `hom_` and `fib_cov_tapp0_func`. Its point computation and further
whole Hom action both pass
(`hint_homd_con_fibre-20260908-114236.log`). This is useful evidence for a
native dependent mirror. It is not yet a declaration of `homd_con_int` or
its whole varying-endpoint target family.

Separately, at a fixed p:x→y, with FF:E⇒D, a native-typed interface for the
existing opposite displayed action reads

```text
fdapp1_con_int_hom_func(FF,p,u,v) :
  Hom(E[y], v, E[p]u)
    → Hom(D[y], FF[y]v, D[p](FF[x]u)).
```

`hint_fdapp1_con_interface.lp` defines that functor transparently as the
existing `fdapp1_int_hom_func` applied to `Op_funcd(FF)`, with the opposite
families. A point alias applies the whole functor. Both declarations pass
(`hint_fdapp1_con_interface-20260908-113637.log`). No new stable symbol,
rewrite, unifier or equality assumption has been installed in active code.
This fixed-p test does not settle all variance in p or the varying endpoint
families; that is why the full ladder must be reviewed before promotion.

In particular, these probes reuse the current kernel's `Op_funcd` semantics.
They do not prove that an arbitrary directed laxity witness is invertible.
Reversing a fibre Hom, reversing the base, and constructing an inverse
comparison are distinct operations. The strict working profile permits the
intended structural normalization experiments, not arbitrary higher-cell
collapse. Any eventual lax-profile comparison must make its reverse/coherent
data explicit rather than infer them from a matching point type.

## A Separate Opposite-Owner Link

The active `Op_catd_func(K)` projects at E to `Op_catd(E)`, while `Op_funcd`
has its own component and involution rules. A rule search did not find a
first-action fold connecting them; the following focused probe confirms the
current behavior rather than relying only on that search:

```text
Op_catd_func(K)[FF]    does not currently convert to Op_funcd(FF),
its component at k    does not convert to Op_func(FF[k]),
the corresponding typed eq_refl comparison also fails to elaborate.
```

All three negative checks pass in
`hint_op_catd_action_owner_audit-20260908-113930.log`. These are absence-of-
conversion/unification tests, not a proof of semantic inequality. This
missing link may matter for a whole higher mirror and should be audited
alongside it. It is not a reason to add an indiscriminate `Op_transfd` fold
with guessed direction.

## The Current Triangle Consumer And What Actually Failed

The hybrid prototype uses an existing mixed family

```text
D[A] = Functor([1], PathOut_C(A)),
TriangleDiagram(C) = Op(Σ A:Cᵒᵖ, Op(D[A])).
```

Native triangles introduce the inner arrow through the existing walking-
arrow recursor. A map retains a:A₀→A₁ and an actual natural transformation
T₀⇒PathOut(a)∘T₁. Its coherence is not a newly supplied list of squares.
Displayed evaluation and totalization give whole vertex and edge
observations. The nine checks for vertices, source/long edges, native
generator, initial-vertex nonidentity action and retained map data pass in
`hint_triangle_diagram_family_checks-20260908-112410.log`.

The nonidentity edge observation currently normalizes to the schematic term

```text
(a, fdapp1_int_hom_fapp0(Op_funcd(eval_i), a, T₁, eta)),
```

not yet `(a, eta[i])`. The retained head is confirmed by
`hint_triangle_diagram_edge_action_normal_forms-20260908-112627.log`.
The first comparison also had an inferred Hom(Σ)/Hom(Op Σ) type-presentation
issue. A native-typed expected-arrow alias resolves that issue, after which
the conversion assertion still fails
(`hint_triangle_diagram_edge_action_typed-20260908-112545.log`).

The attempted direct rewrite expanded the transparent eval_i body into
Eval_funcd composed with a displayed pair of identity and the fixed i.
The all-wildcard version fails subject reduction, not merely warnings.
Tying the base K and then adding the measured Catd composition-category
guards removes some obligations, but the source evaluation family and
identity/constant component endpoints are still not reconstructed. Last
guarded log: `hint_diagram_fibre_eval_projection_rules-20260908-113146.log`.
Those candidates remain ignored probes; no broad rule or opacity workaround
has entered active source. A `con` head may simplify the projection route,
but by itself it does not prove these separate typing obligations solved.

## Continuation Decision

The user's subsequent historical pointer resolves an immediate reuse option:
commit `20c6dd2e8a7d939bf7f2b25a6578e5c072c6ccb3` on the parallel branch
stabilizes the four existing ordinary con aliases. Its nucleus-only change
adds whole/fixed-target projection and identity computation plus proof-time
Op comparisons. Its separate gray-profile/classifier changes are outside
this branch's current scope. The next bounded tranche will selectively port
and validate the nucleus owner change and its relevant reviewers before
designing an independent dependent mirror. The inventory above records the
pre-port baseline; it does not claim those stable heads are already active.

1. Design the dependent mirror as a coherent family of owners, starting with
   the native reversed-Hom family and its full varying-endpoint type.
2. Relate the new whole action to the existing internal action/Op route;
   audit the `Op_catd_func`/`Op_funcd` link and higher-transfor directions.
3. Derive the contravariant laxity observation from that action and the
   appropriate identity section. Do not postulate another laxity cell.
4. Select stable heads only where needed to retain a runtime discriminator.
   Keep non-discriminating inferred slots wildcarded, preserve whole action,
   and justify any guard with a subject-reduction/consumer probe. Warnings
   remain diagnostics, not vetoes.
5. Return to the actual nonidentity triangle edge action and zero-complex
   restriction before qualifying the whole complex/homology interface.

This is a bounded architectural audit inside the original long-exact goal,
not a replacement goal to complete every possible variance mirror. The
original generic window exactness, bounded assembly, retained proof–CAS
choices, formal-boundary audit and final book obligations remain open.
