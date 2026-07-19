# EMDASH v3.2 Walking Endomorphism Directed-HIT And Nat Normal-Form Plan

Date: 2026-07-17
Last reviewed: 2026-07-19
Plan-ID: EMDASH-V3-2-WALKING-ENDOMORPHISM-DIRECTED-HIT-2026-07-17
Depends-On: REPORT_EMDASH_V3_2_EQUALITY_VALUED_OMEGA_EQUIVALENCE_REREDESIGN_PLAN_2026-07-17; REPORT_EMDASH_V3_2_OBSERVATIONAL_EQUALITY_TRUNCATION_UNIVALENCE_REDESIGN_PLAN_2026-07-13; REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26; EMDASH_FOUNDATIONS; emdash3_2.lp; emdash3_2_nat_arithmetic.lp; emdash3_2_eq1_hom_action.lp; emdash3_2_eq1_evidence_property.lp; emdash3_2_checks.lp
Supersedes: none
Side-Task-Ledger: #current-implementation-ledger
Infinity-Codex-Origin: current-session-walking-endomorphism-review-and-user-clarification-2026-07-17
Infinity-Codex-Decision-Responses: infinity-codex:019f6bd3-8405-7d31-8ced-8a6b127c1499:e08b19e4-e4ef-41f3-bee3-87086450d411; infinity-codex:019f6bd3-8405-7d31-8ced-8a6b127c1499:019f7269-46dc-7942-8438-6110fb05cfdb
Status: **REOPENED / G3 OPAQUE OWNER COMPLETE AND G4 ACTIVE — `WalkingEnd_cat`, `walking_base`, and `walking_loop` are opaque constants; the generated-word Hom datatype and every WalkingEnd-specific object/Hom/identity/composition rule are removed; explicit one-dimensional evidence, its homwise specializations, and the contextual `Functord` eliminator are active; the contextual base/loop betas are the only HIT-specific runtime rules; derived sections compute at `piapp0`/`piapp1`, while the ordinary recursor base is propositionally joined across the retained terminal-component critical pair and its ordinary loop observer remains proof-time compared with the canonical section observer; the separate `BNat` category is consistency evidence rather than definitional Hom; the active kernel remains `984/159`, the rebuilt walking module measures `989/159`, both strict LHS audits are zero, and bounded kernel/diagnostic/reviewer checks pass; G4 concrete `Code`, representable decoder data, powers, and directed spiral are next**
Review baseline: `394cf3bc369ddcdb4da74aaf5fdc0557de515532`
Implementation baseline: `8fd9bdfac53b018b77f20ecec24f85efe44febc9`
HIT-computation correction baseline: `b5037078dfaafc665adb2d996bec38596e6914c9`
Corrective-review baseline: `9858a420fd6f94e920415a8728ffd9d6bf8d18a5`
Implementation-goal starting baseline: `92daacc5a90ec9b7b457cfa310c0bb51e1531237`
Current implementation-goal baseline and review provenance: `82d0e27fd75573309a9c7e26e621706c66d24e64`
Parent plan: `REPORT_EMDASH_V3_2_EQUALITY_VALUED_OMEGA_EQUIVALENCE_REREDESIGN_PLAN_2026-07-17.md`, especially deferred task `EVOGJ-H2-READINESS`
Current implementation owners: reusable Nat prerequisites in
`emdash3_2_nat_arithmetic.lp`; walking HIT/model/comparison in
`emdash3_2_walking_end_hit.lp`

## Status And Authority

This report is the reopened bounded sub-plan of the completed selected-MVP
equality-valued omega-equivalence overlay. The 2026-07-18 corrective review
invalidates the earlier claim that the committed `walking_end_hom` word
carrier is the intended HIT's “intrinsic Hom.” It does not reopen or
supersede the completed equality, univalence, groupoidality, structured-J,
evidence-property, or finite-truncation work.

The authority order remains the repository order in `AGENTS.md`. In
particular:

1. `emdash3_2.lp` remains the active computational kernel;
2. the native EQ1 extension modules retain their current one-way dependency
   direction;
3. this report is only the living design and decision ledger for the walking
   endomorphism experiment;
4. the parent July 17 report remains the completed equality/groupoidality
   overlay and the July 13 report remains the retained ledger for unaffected
   H0, truncation, dimension, directed, former-action, and long-term H2 work.

The original review and implementation baselines were clean and
`EMDASH_TYPECHECK_TIMEOUT=60s make check` passed on 2026-07-17 before semantic
probes. The corrective baseline `9858a42...` was also clean and
`EMDASH_TYPECHECK_TIMEOUT=60s make check` passed on 2026-07-18. The commits are
historical provenance only and never authorize a reset or rollback. The
authoritative correction plan is recorded next; the former completion record
is retained afterward only as rejected-decision evidence.

## 2026-07-19 Active G1–G3 Promotion Record — Current Override

This section is the current implementation ledger for the first promoted
slice. It supersedes later checkpoint sentences saying that the active kernel
is unchanged or that owner-position/warning work remains wholly deferred.

The goal resumed from clean commit
`82d0e27fd75573309a9c7e26e621706c66d24e64`. Bounded `make check` and
`make examples` passed before edits. The initial kernel warning inventory was
`971/157`; the legacy walking module was `977/157`; the strict LHS audit had
zero unreviewed clauses with 45 annotated slots across 27 clauses.

### G1 promoted and atomic remainder

The generic terminal-source runtime rule is now the proof-time equation

```text
fdapp1_int_cell(s,p,*) ≡ fapp1_fapp0(s,p).
```

`terminal_fdapp1_int_cell_eq` exercises that equation by typed reflexivity,
and `piapp1_const_fapp0_eq` supplies the derived constant-section ordinary
view. Permanent diagnostics retain negative conversion controls: neither
comparison is described as runtime beta. With only this demotion active, the
kernel inventory was `969/157` and the legacy walking module was `975/157`.

The exact selected hybrid, including generic contextual base and loop betas,
passed a fresh full owner-position copy quietly at
`logs/probes/wehit_g1_selected_hybrid_owner_full-20260719-131300.log` and with
warnings at
`logs/probes/wehit_g1_selected_hybrid_owner_full-20260719-131320.log`; that
complete probe measured `972/157` and the strict audit remained zero. The
contextual betas are not yet active. Promoting them beside the legacy walking
module fails subject reduction because its current `walking_loop` unfolds to
the generated-word constructor. They must therefore land atomically with the
opaque `WalkingEnd_cat`/`walking_loop` owner migration in G3. This is a
dependency ordering result, not a rejection of the contextual interface and
not permission to add a word-specific bridge.

### G2 generic Path/Core slice promoted

The following permanent owners are active:

```text
Path_cat_func                 : Grpd_cat -> Cat_cat
path_map_func(f)              : Path_cat(A) -> Path_cat(B)
path_map_transf(h)            : path_map_func(f) => path_map_func(g)
core_incl_naturality(F)       : F o CoreIncl_C => CoreIncl_D o PathMap(F_0)
core_incl_naturality_whiskered(F,G)
path_lift_func                : Path(Function(A,Obj(C))) -> (Path(A) -> C)
NatSucc_func                  : Path_cat(Nat) -> Path_cat(Nat).
```

The named projection ladder supplies object action, equality action through
`eq_ap`, point components through `PiHapply`, capped off-diagonal cells, and
the full iterable next-hom action. `path_lift_func` remains the transparent
semantic composite of the first Path action with postcomposition by
`Core_incl_func`; no primitive PathLift head was introduced. Permanent
check-local power/spiral definitions exercise exact endpoints, identity
components, and the next iterable `tapp1_func` rung without adding a public
parallel recursion interface.

The final full owner-position probe passes quietly at
`logs/probes/wehit_g2_path_internal_owner_full-20260719-133310.log` and with
warnings at
`logs/probes/wehit_g2_path_internal_owner_full-20260719-133312.log`. The
active kernel reproduces its `984/159` inventory and has no new unification
rule. Relative to the post-G1 `969/157` kernel, the selected runtime owners add
15 unjoinable reports: one from capped application of groupoid-function
composition, two from the generic Cat-valued postcomposition object
projection, and twelve from the stable strict Core-inclusion consumer. The
rigid `Path_cat` object-action endpoints exchange two avoidable Sigma
projection critical pairs for two measured replaceable-variable advisories;
they are annotated as actual overlap guards. The strict audit remains at zero
unreviewed clauses.

The legacy walking module currently measures `992/159`: its six old
constructor-composition reports remain, and the strict Core consumer adds one
temporary overlap at each legacy `Obj(WalkingEnd_cat)` and `Obj(BNat_cat)`
reduction. Those two cross-module reports are tied to the rejected concrete
object presentations and must be remeasured after G3/G6 migration; they do not
justify a walking-specific join.

Two alternatives were rejected by owner evidence. Removing the stable Core
consumer and expressing whiskering through generic precomposition reaches two
separate stable post/precomposition endpoint comparisons that the existing
unification rules do not compose; the failure is recorded at
`logs/probes/wehit_g2_path_internal_no_stable-20260719-133934.log`. Making the
outer path-category source a rigid LHS guard changes neither warning family
nor count, so that slot remains inferred. A primitive PathLift or a new local
unifier is therefore not selected.

The capped rule `comp_Grpd(g,f)[x] -> g(f(x))` does not install the rejected
broad whole-term fold to `grpd_comp_function`. With the repository's
`eta_equality` flag, however, conversion can observe the same lambda at the
whole-function type. The pre-existing negative conversion assertion exposed
this consequence during active integration and has been changed to a positive
eta-observation diagnostic. Any statement that the whole categorical
composition is conversion-distinct from its lambda is superseded; the
syntactic runtime owner remains categorical composition.

The remaining G2 formation probe is
`tmp/probes/wehit_g2_rep_dimension_formation.lp`. It passes quietly at
`logs/probes/wehit_g2_rep_dimension_formation-20260719-140025.log` and is
warning-neutral at the active `984/159` inventory in
`logs/probes/wehit_g2_rep_dimension_formation-20260719-140034.log`. With only
opaque stand-in constructors, it verifies all of the following exact shapes:

```text
Rep_catd(base)[x] = Hom_cat(WalkingEnd,base,x)

fdapp1_int_cell(decode,p,n) :
  p o decode[base](n) -> decode[x](Code[p](n))

walking_end_is_one_cat(x,y)
  : IsDiscreteCat(Hom_cat(WalkingEnd,x,y))

hom_to_path(walking_end_is_one_cat(base,x),alpha) : p = q.
```

The negative formation control confirms that the same evidence does not
inhabit `IsDiscreteCat(WalkingEnd)`. The probe declares no object, hom,
identity, composition, word-carrier, or decoder computation and therefore
does not pre-implement G3/G4.

The completed level-by-level internalization audit is:

| Surface | Active strength | Deliberate boundary |
| --- | --- | --- |
| `Function_grpd(A,B)` | transparent constant-family `Pi_grpd`; Pi path infrastructure supplies equality | not a directed transformation classifier |
| `Path_cat(A)` | injective category former; object, hom, and identity compute; generic composition remains owner and hom iteration is recursive | no separate path-composition calculus |
| `Path_sym_func(A)` | fixed-`A` functor with object/reflexivity projections; generic functoriality supplies reversal composition and all typed higher actions | no collapse of `Path_cat(A)^op` with `Path_cat(A)` |
| `Core_cat(C)` | valid transparent object-level alias `Path_cat(Obj(C))` | no `Core : Cat_cat -> Cat_cat` and no `Core_catd` |
| `Core_incl_func(C)` | fixed-category functor with object, reflexivity, shaped-reflexivity, generic composition, and exposed hom action | arrow-to-path inverse requires explicit `IsDiscreteCat(C)` evidence |
| `Path_cat_func` | complete positive internal functor through object, function, function-equality point/capped/full action, and iterable next hom | does not reflect directed cells into equality |
| fixed functor `F : C -> D` | object function `F_0`, `path_map_func(F_0)`, strict Core-inclusion naturality, and stable whiskering | no action on an arbitrary directed transfor between `F` and `G` as object equality |

This completed the G2 exit gate and licensed the atomic G3 opaque-owner and
contextual-beta migration recorded next. No further generic Core
internalization was a prerequisite.

### G3 opaque owner and contextual eliminator promoted

`emdash3_2_walking_end_hit.lp` has been atomically rebuilt around opaque
constants for `WalkingEnd_cat`, `walking_base`, and `walking_loop`, together
with the explicit signature datum

```text
walking_end_is_one_cat : IsNCat(1,WalkingEnd_cat).
```

The generated `walking_end_hom` datatype, `WalkingEndHom_grpd`, Hom induction,
and all WalkingEnd-specific `Obj`, `Hom`, identity, and composition rules are
gone. Permanent diagnostics separately reject the former object and Hom
normal forms and reject identity/loop and loop-composition collapses. The
transparent `walking_end_hom_discrete`,
`walking_end_based_hom_discrete`, and
`walking_end_based_cell_to_path` interfaces expose truncation only through the
explicit dimension witness; a negative control still rejects
`IsDiscreteCat(WalkingEnd_cat)`.

The selected contextual interface is now active:

```text
walking_end_ind_funcd(R,D,u,sigma) : Functord(R,D)

Fibre_func(walking_end_ind_funcd(...),base)          ↪ u
fdapp1_int_cell(walking_end_ind_funcd(...),loop,r)  ↪ sigma[r].
```

These are the only two HIT-specific runtime rules. The terminal section
specialization and constant recursor are transparent definitions. Section
base and loop observations compute at `piapp0` and `piapp1`. At the ordinary
constant-recursion object observer, the retained generic terminal-component
rule produces the bounded nonconfluent branch forecast by G1, so
`fapp0(rec,base)` is deliberately **not** a new runtime beta. Two typed branch
theorems separately exercise the contextual and generic projections;
`walking_end_rec_beta_base` composes them propositionally after terminal
evaluation. The canonical recursor loop theorem stays at the section observer,
and `walking_end_rec_loop_ordinary_comparison` exposes the existing proof-time
`piapp1`/`fapp1` comparison. No specialized recursor rule or new unification
rule was added. The inferred declaration type of the transparent
`walking_end_rec_beta_loop` alias preserves the canonical section classifier
across this measured terminal boundary; its exact readable formula is checked
in the reviewer surface.

The retained `BNat_cat` is now explicitly a separate semantic consistency
model. Its Nat-monoid operations and one-dimensionality evidence remain
concrete, while `walking_bnat_model_func` interprets the opaque base and loop
through the derived recursor. No `BNat` carrier is used to define
`Hom(WalkingEnd_cat,base,base)`.

The full G3 prototype passes quietly at
`logs/probes/wehit_g3_opaque_module-20260719-141741.log`. The promoted walking
module passes warning-enabled checking at
`logs/probes/emdash3_2_walking_end_hit-20260719-142226.log` with `989/159`:
one expected terminal/contextual base overlap, one retained `BNat`/strict-Core
object overlap, and the three retained `BNat` composition/action overlaps.
This is three fewer critical pairs than the rejected `992/159` legacy module.
The module and kernel strict LHS audits both report zero unreviewed clauses.
Bounded `make check`, complete diagnostics, the rewritten
`examples/walking_endomorphism_hit.lp`, and full `make examples` pass. The
refreshed catalog has 1,996 checks across 73 areas with zero unclassified
checks. Health and CI are deferred to the next synchronized gate after the
current G4 inner slice.

## 2026-07-18 Contextual `Functord` And Directed-First Decision — Current Override

This section supersedes the later passages that select a special
`walking_end_ind_cell`/`cell_ind` primitive or leave a primitive-versus-derived
1-cell-eliminator decision open. Those passages remain historical probe
evidence only. The selected practical route is now the parameterized
whole-HIT eliminator already expressible by the existing `Catd`, `Functord`,
fibre-functor, and displayed-arrow infrastructure:

```text
R,D : WalkingEnd → Cat
u   : R(base) → D(base)
σ   : D(loop) ∘ u ⇒ u ∘ R(loop)

indᵈ(R,D,u,σ) : Functord(R,D).
```

Its selected constructor observations are both runtime computation:

```text
Fibre_func(indᵈ(R,D,u,σ),base)          ↪ u
fdapp1_int_cell(indᵈ(R,D,u,σ),loop,r)  ↪ σ[r].
```

This is not elimination on a separately exposed Hom carrier. It returns one
structured functor between arbitrary directed families over the opaque HIT;
therefore its ordinary `fdapp1` action is available at every opaque arrow
`p : Hom(WalkingEnd,base,x)`. The selected directed specialization is:

```text
R ≔ Code
D ≔ Rep_catd(base)
u ≔ power
σ ≔ spiral
decodeᵈ ≔ indᵈ(Code,Rep_catd(base),power,spiral).
```

Evaluating the generic displayed arrow action at the inner datum `0` gives
the required arbitrary-arrow directed normalization cell:

```text
fdapp1_int_cell(decodeᵈ,p,0) :
  p ∘ decodeᵈ[base](0) ⇒ decodeᵈ[x](Code[p](0)).
```

After base beta, `power(0)`, and the right-unit law, this yields

```text
νₚ : p ⇒ power(encodeₓ(p)).
```

This is the primary directed/categorical computation. It is fully functorial
because `Rep_catd(base)` already owns postcomposition on 1-arrows and
whiskering on higher directed cells. No fibrewise `Core_cat`, generic
`Core_catd`, or equality-reflecting higher action is needed to construct it.

The selected walking HIT is explicitly one-dimensional in the kernel's
native directed-dimension sense:

```text
constant symbol walking_end_is_one_cat
  : τ (IsNCat (cat_succ cat_zero) WalkingEnd);
```

This computes to `Π x y, IsDiscreteCat(Hom_cat(WalkingEnd,x,y))`; it does
**not** assert `IsDiscreteCat(WalkingEnd)` and does not make `loop` invertible.
Its base-hom specialization converts the directed normalization cell only
after that cell has been constructed:

```text
walking_end_hom_discrete(x)
  ≔ walking_end_is_one_cat(base,x)

hom_to_path(walking_end_hom_discrete(x),νₚ)
  : p = power(encodeₓ(p)).
```

Thus the implementation order is directed decoder first, explicit
one-dimensional truncation second, equality round trip third. The
one-dimensionality witness is part of the selected truncated-HIT signature,
not a theorem secretly inferred from the Hom–Nat carrier comparison. A later
derivability audit may replace it by a theorem if a stronger general HIT
induction/initiality interface proves the same fact without circularity; that
audit is not a prerequisite for this practical MVP.

No `WalkingWord`, Hom induction, special ad hoc 1-cell eliminator,
equality-valued decoder motive, or functor-category initiality metatheorem is
selected. The minimal probe establishes the contextual `Functord` type shape;
it does not yet implement the concrete `Code`, directed decoder, truncation
specialization, or round trips.

The initial focused feasibility probe is
`tmp/probes/wehit_opaque_functord_ind_minimal.lp`. It checks the generic
formation/base/loop rules and the decoder-shaped inner application
`Code[p](0)`. An append-only version exposed exactly two interactions with
pre-existing broad terminal-source rules. Those interactions were warning
diagnostics, not a typechecking timeout: the quiet probe passed.

The selected owner design is the following hybrid. Preserve the established
full terminal-component runtime rule exactly at its current owner:

```text
rule tapp0_fapp0(K,Cat,Const(Terminal),Const(A),k,F)
  ↪ Obj_func(A,F[k]).
```

Do **not** add a symmetric general `tapp0_fapp0 ≡ Const_func(1,A,F[k])`
unification rule. Its right side contains the open reducible component
`F[k]`, it is unnecessary while the runtime owner remains, and it broadens
proof search without resolving the underlying runtime diamond. Contextual
base beta remains a runtime rule. At the terminal/constant specialization the
two runtime rules have the measured nonconfluent boundary

```text
Fibre_func(indᵈ(Const(1),Const(A),u,σ),base)
  ↪ u

Fibre_func(indᵈ(Const(1),Const(A),u,σ),base)
  ↪ Obj_func(A,indᵈ(...)[base]).
```

This is not a blocker for the hard decoder, whose motive is `R ≔ Code` and
`D ≔ H`. It is nevertheless a real runtime nonconfluence diagnostic, not
cosmetic warning lint. The selected MVP accepts and records that bounded
terminal-motive debt rather than replacing a long-established kernel normal
form during the HIT migration. Do not add a WalkingEnd-specific point-consumer
join merely to erase the warning; derived constant-family observations must be
staged transparently through the generic projection and contextual beta.

Demote only the broad terminal-source arrow rule

```text
fdapp1_int_cell(s,p,*) ↪ fapp1_fapp0(s,p)
```

to the corresponding typed proof-time comparison between the same two rigid
heads. Contextual loop beta remains the runtime owner:

```text
fdapp1_int_cell(indᵈ(R,D,u,σ),loop,r) ↪ σ[r].
```

Do not add a WalkingEnd- or HIT-specific bridge from ordinary
`fapp1_fapp0(indᵈ(...),loop)` directly to `σ[*]`. The canonical derived-section
observer is `piapp1_fapp0`; after demoting the broad terminal arrow rewrite,
its projection path remains at `fdapp1_int_cell` and the generic contextual
loop beta owns the runtime computation. When an ordinary-functor view is
needed, expose a transparent theorem assembled from the generic terminal
`fdapp1_int_cell ≡ fapp1_fapp0` comparison and the generic contextual beta;
do not install a constructor-specific unification rule merely to make that
composed theorem reflexivity in one step.

The owner migration must add no other HIT-specific rewrite or unification
bridge. In particular, do not preselect terminal point-consumer joins or
base-beta/vertical-composition unification rules. Exercise the surviving
runtime critical-pair boundaries with typed transparent theorems built from
the generic category/functor laws. A further kernel rule requires a new,
specific failing consumer and a revised recorded decision; it is not part of
this selected design.

The pre-stale demote-both owner experiment passes quietly and at `964/157` in
`logs/probes/wehit_functord_terminal_owner_full-20260718-185544.log` and
`logs/probes/wehit_functord_terminal_owner_full-20260718-185555.log`. It
establishes that the terminal `fdapp1_int_cell` demotion and generic contextual
betas are viable, but it is not the exact selected hybrid because it also
demoted `tapp0_fapp0`. Later edits to the ignored owner probe by another agent
are stale and non-authoritative; neither that file's current contents nor its
later logs may select architecture or be promoted verbatim.

G1 must reconstruct the selected retain-`tapp0`/demote-`fdapp1` hybrid from the
rules enumerated here at the actual current owner positions. Exact owner
accounting forecasts approximately `972/157` against the active `971/157`,
but that number is not validation evidence. Record fresh quiet, warning,
typed-consumer, and strict-audit results before promotion. The existing
experiments establish computational feasibility of the contextual interface;
they do not claim that the active kernel or walking implementation has already
migrated.

## 2026-07-19 Internal Path Action And Spiral Checkpoint — Current Override

This checkpoint refines G2 and G4. It supersedes any earlier wording that
treated a bodyless spiral as the remaining option, that called the current
`PathLift` probe promotion-ready, or that selected a primitive `PathLift`
before inspecting the normal form of its semantic body.

The internal computational core is now demonstrated. The focused probe
`tmp/probes/wehit_path_int_internal_action.lp`, copied verbatim at the
verified checkpoint to
`tmp/wehit_path_int_internal_action_success_2026-07-18-4.lp`, constructs:

```text
PathInt    : Functor(Grpd_cat,Cat_cat)
PathMap(f) : Functor(Path_cat(A),Path_cat(B))
PathLift(h): Transf(PathLift(f),PathLift(g)).
```

Its permanent checks show that:

```text
tapp₁(PathLift(h),x,y)
  ↪ CoreIncl₁ ∘ PathMap(cell_h)

tapp₁(PathLift(h),p)
  ↪ path_to_hom(cell_h(p)),
```

and the exact Nat spiral component reduces to the identity in that
experimental environment. The complete off-diagonal action remains a functor
and is iterable; no opaque spiral, external component family, handwritten
naturality square, or WalkingEnd-specific Hom eliminator supplies that data.

This earlier copied checkpoint is not a promotable solution. It contains five
direct `unif_rule` endpoint shortcuts. Two contain a reducible
`comp_fapp0(Grpd_cat,...)`; the others directly register composite
`PathInt`, `CoreIncl`, and `PathLift` presentation chains because
unification rules do not compose transitively. They do not construct the
spiral, but they are currently what lets Lambdapi regard the internally
constructed transformation as having the exact contextual-eliminator
endpoints. The strict inferred-slot audit being clean does not validate their
semantic ownership or reducibility. None of these five rules is selected for
promotion.

The full owner-position experiment is
`tmp/probes/wehit_path_int_internal_action_owner_full.lp`. It passes quietly
at
`logs/probes/wehit_path_int_internal_action_owner_full-20260719-003917.log`;
its warning-enabled run
`logs/probes/wehit_path_int_internal_action_owner_full-20260719-003933.log`
has 993 unjoinable critical pairs against the fresh active-kernel baseline
971. Isolating the candidates gives:

```text
runtime comp_Grpd ↪ grpd_comp_function       +20
generic Cat-valued postcomposition projection +2
PathInt/PathLift/spiral rules themselves       +0.
```

Warnings are not an automatic veto, but the broad `Grpd` migration is not
selected merely because this feasibility probe passes. It overlaps arbitrary
Grpd-valued identities, functoriality, transfors, represented actions, and
definitional isomorphisms. The two postcomposition warnings are exactly the
existing Sigma first/second projection commuting cuts.

Normal-form probes now localize the smaller issue:

- `tmp/probes/wehit_pathlift_semantic_compute.lp`, with log
  `logs/probes/wehit_pathlift_semantic_compute-20260719-011539.log`;
- `tmp/probes/wehit_pathlift_semantic_compute_no_grpd_runtime.lp`, with log
  `logs/probes/wehit_pathlift_semantic_compute_no_grpd_runtime-20260719-011652.log`.

For the transparent semantic construction

```text
PathLift_sem(f) ≔ hom_postcomp(CoreIncl_C,PathMap(f)),
```

they establish:

```text
PathLift_sem(f) ∘ PathMap(g)
  ↪ hom_postcomp(CoreIncl_C,PathMap(comp_Grpd(f,g)))
  ≡ PathLift_sem(comp_Grpd(f,g)),
```

without the experimental `Grpd` runtime fold. Thus precomposition already
accumulates through the semantic body. In contrast:

```text
F ∘ PathLift_sem(f)
  ↪ F ∘ hom_postcomp(CoreIncl_C,PathMap(f))
```

stops at the existing stable `hom_postcomp_fapp0` head, while the intended
normal form is:

```text
hom_postcomp(
  CoreIncl_D,
  PathMap(F₀) ∘ PathMap(f)).
```

This normal form identifies the missing mathematical comparison, but it does
not by itself justify making the two functors judgmentally equal by a runtime
rewrite. The first owner to probe is the structured fixed-functor comparison

```text
κ_F :
  F ∘ CoreIncl_C
    ⇒
  CoreIncl_D ∘ PathMap(F₀),
```

for each `F : Functor(C,D)`. Its component at `x` is `id_(F(x))`; its action
on `p : x = y` is the equality-induction comparison between
`F(path_to_hom(p))` and `path_to_hom(eq_ap(F₀,p))`. It must be packaged as
one ordinary transfor with its full `tapp*` ladder, not as an external family
of naturality equations. Whiskering it by `G : Functor(A,Core_cat(C))` gives
the exact reusable endpoint cell

```text
κ_F ⋆ G :
  F ∘ hom_postcomp(CoreIncl_C,G)
    ⇒
  hom_postcomp(CoreIncl_D,PathMap(F₀) ∘ G).
```

This is already the form needed in the spiral: the contextual eliminator asks
for a structured cell, not for an unrecorded claim that its endpoint functors
are definitionally identical.

The mathematical cell is canonical, but at this checkpoint its kernel
construction had not yet been demonstrated. The active kernel has no general
transparent constructor that
turns pointwise components plus a naturality proof into an arbitrary
`Transf`. The 2026-07-19 user decision selected the strict representation as
the first focused probe strategy for this same generic Core-inclusion owner.
After that probe passed, the strict representation became the active design
to implement first; this does not assert that strictness is mathematically
necessary or optimal forever:

1. select a strict
   Core-inclusion fusion computation making the two endpoint functors share a
   canonical normal form, so that the corresponding structured cell is the
   ordinary identity transfor; then
2. retain a bodyful `κ_F`, preferably as the `tapp₁` projection of the
   restricted `CoreInclTransf` package described below, as an explicitly
   deferred possible redesign rather than a prerequisite for this MVP.

Do not introduce a bodyless `κ_F` constant. The smaller strict owner is

```text
F ∘ CoreIncl_C
  ↪ CoreIncl_D ∘ PathMap(F₀).
```

Its stable postcomposition consumer is

```text
F ∘ hom_postcomp(CoreIncl_C,G)
  ↪ hom_postcomp(CoreIncl_D,PathMap(F₀) ∘ G).
```

The stable `hom_postcomp` form is a consumer projection, not an independent
HIT rule. The focused experiment below establishes this representation's
feasibility and selects it as the active first implementation route, but does
not itself promote either rule to the kernel.
Give `PathInt`, `PathMap`, `κ_F` (if the fallback becomes necessary), and
their transformation/higher-action projections a proper named
`fapp*`/`tapp*` ladder so permanent rules match stable intermediate heads
rather than nested reducible presentations.

### Strict Core-Inclusion Feasibility Result — 2026-07-19

The selected strict experiment passes. The final append-only work probe is
`tmp/probes/wehit_path_int_internal_action.lp`; its immutable verbatim
snapshot is
`tmp/wehit_path_int_strict_core_incl_success_2026-07-19.lp`, with SHA-256
`b81998eecb1154ef3bfc114ea542d48587a5d0cb7c0ae95cb6b1636dd036d16d`.
The quiet successful run is recorded in
`logs/probes/wehit_path_int_internal_action-20260719-115841.log`.

This result supersedes the earlier feasibility checkpoint only with respect
to the five rejected endpoint shortcuts. The passing snapshot has zero local
`unif_rule` declarations and does not install the broad whole-term
`comp_Grpd ↪ grpd_comp_function` fold. Instead it uses:

1. capped evaluation
   `comp_Grpd(g,f)[x] ↪ g(f(x))`, retaining categorical `comp_Grpd(g,f)` as
   the whole-function normal form;
2. a transparent object-function `F₀(x) ≔ F[x]`;
3. the smaller strict Core-inclusion owner
   `F ∘ CoreIncl_C ↪ CoreIncl_D ∘ PathMap(F₀)`;
4. the stable `hom_postcomp` consumer of that owner; and
5. the generic Cat-valued postcomposition object projection needed to
   evaluate the resulting functors.

In that environment, typed reflexivity validates both PathLift accumulation
directions, the exact Nat spiral has the contextual eliminator's required
endpoints, every spiral component computes to the categorical identity, and
the full off-diagonal `tapp1_func` remains a functor that can be iterated.
The general Path-transformation component and capped/full PathLift actions
also compute to `PiHapply`, `CoreIncl₁ ∘ PathMap(cell_h)`, and
`path_to_hom(cell_h(p))` at their respective projection levels. Thus the
structured-spiral issue is computationally feasible without an opaque
spiral, bodyless `κ_F`, special Hom eliminator, or endpoint unification
shortcut. Under the selected strict normal form, `κ_F` is represented by the
ordinary identity transfor because its two endpoint functors are
definitionally the same.

This is deliberately a feasibility result, not a promotion record or a proof
that a non-strict structured `κ_F` is inferior. It is nevertheless the
selected implementation starting point. At the
user's 2026-07-19 direction, no fresh owner-position splice, warning delta,
or strict rule audit was performed for this snapshot. Those checks, naming
cleanup, projection-ladder ownership, and the decision whether each generic
candidate belongs in `emdash3_2.lp` remain early G2 work when the complete
plan is implemented. The ignored work probe and log are evidence; the active
kernel is unchanged.

In the active calculus the transparent lift remains

```text
PathLift_sem
  ≔ comp_cat_cov_func(CoreIncl_C) ∘ PathInt₁(A,Obj(C)).
```

It would be literally a `tapp1_func(CoreIncl_)` projection only after a full
`CoreIncl_ : Core ⇒ Id_Cat` had been constructed. The fixed-functor
`κ_F`/strict-fusion owner supplies exactly the postcomposition naturality
needed by `PathLift_sem` without assuming that unavailable stronger package.

There is a promising more-internal reading: `κ_F` is the functor-indexed
naturality structure one expects from the components
`CoreIncl_C : Core_cat(C) → C`. It must, however, be formulated at the
strongest level actually available. The current declaration

```text
Core_cat(C) ≔ Path_cat(Obj(C)) : Cat
```

is deliberately a transparent object-level assignment. Whether it is a
defined alias or a primitive stable head is not what determines higher
functoriality: neither form supplies action on functors, transformations, and
all iterated cells. A full transformation

```text
CoreIncl_ : Core ⇒ Id_Cat
```

would first require a genuine endofunctor `Core : Cat_cat → Cat_cat`.
Although its action on a functor `F : C → D` can be defined as
`PathMap(F₀)`, its action on an arbitrary directed transformation
`η : F ⇒ G` would require object equalities `F(x)=G(x)`; the components
`ηₓ : F(x)→G(x)` do not supply those equalities in a general directed
category. Thus `Core_cat` is functorial on the ordinary one-dimensional
category of categories and functors, but not automatically an omega-functor
on the full directed `Cat_cat`. This is the same directed obstruction that
rejected a generic `Core_catd`. Do not postulate that missing higher action.

### Deferred Possible Redesign — Restricted `CoreInclTransf`

A restricted equality-local or path 1-skeleton does solve the semantic
obstruction in the naive global `Core : Cat_cat → Cat_cat`. The clearer
reusable architecture is a `CatDim`-recursive equality-skeleton, with the
existing `Core_cat` as its zero case:

```text
Sk⁼(cat_zero,A) ≔ Core_cat(A)

Obj(Sk⁼(cat_succ(n),A)) ≔ Obj(A)

Hom_cat(Sk⁼(cat_succ(n),A),x,y)
  ≔ Sk⁼(n,Hom_cat(A,x,y)).
```

At each successor, identities and composition at the retained dimension are
inherited from `A`; the recursive hom action replaces all higher directed
cells by equality action. The corresponding action on a functor must be
defined simultaneously:

```text
Sk⁼₀(F) ≔ PathMap(F₀)

Sk⁼ₙ₊₁(F)[x] ≔ F[x]

Sk⁼ₙ₊₁(F)₁[x,y]
  ≔ Sk⁼ₙ(F₁[x,y]).
```

This simultaneous category/functor recursion is the reusable foundation;
identity, composition, product-composition, and capped/full higher-action
projections must be included in its permanent ladder rather than inferred
from the object and hom formulas alone. The specialized source needed here is

```text
Cat₁⁼ ≔ Sk⁼(cat_succ(cat_zero),Cat_cat).
```

Its objects are categories and its hom-category is

```text
Hom_cat(Cat₁⁼,C,D) ≔ Path_cat(Functor(C,D)).
```

This is the precise construction intended by the informal `τ≤1(Cat_cat)`
notation in this deferred design. It removes arbitrary directed
transformations but can retain higher equality paths between functors. It is
therefore not automatically a witness of the kernel predicate
`IsNCat(cat_succ cat_zero,Cat₁⁼)`: that stronger claim would require each
`Functor(C,D)` classifier to be set-truncated. The active kernel deliberately
has truncation predicates and evidence-retaining packages, not a truncation
reflector, so a genuine universal finite 1-truncation would be a separate HIT
or quotient prerequisite. That stronger truncation is unnecessary for the
restricted `Core` construction.

It retains ordinary functors as 1-arrows but replaces arbitrary directed
transformations by equality paths between functors. Consequently there is no
arbitrary `η : F ⇒ G` from which `Core` would have to manufacture object
equalities: every higher source cell is already equality-valued. Notice that
this is not `Core_cat(Cat_cat)`, whose 1-arrows would be equalities between
categories and which would discard ordinary functors.

The equality-skeleton has a recursive canonical inclusion:

```text
Sk⁼Incl(n,A) : Sk⁼(n,A) → A

Sk⁼Incl(cat_zero,A) ≔ Core_incl_func(A)

Sk⁼Incl(cat_succ(n),A)[x] ≔ x

Sk⁼Incl(cat_succ(n),A)₁[x,y]
  ≔ Sk⁼Incl(n,Hom_cat(A,x,y)).
```

Thus `J ≔ Sk⁼Incl(cat_succ(cat_zero),Cat_cat)`. Its hom action is already the
existing semantic owner

```text
J₁(C,D) ≔ Core_incl_func(Functor_cat(C,D)),
```

which fixes a functor `F` and sends `h : F = G` to the equality-induced
transfor `path_to_hom(h)`.

After the reusable `PathInt` action is available, the intended fully typed
sequence is

```text
Core₁ : Cat₁⁼ → Cat_cat      Core₁(C) ≔ Core_cat(C)
                              Core₁(F) ≔ PathMap(F₀)

J     : Cat₁⁼ → Cat_cat      J(C) ≔ C
                              J(F) ≔ F

CoreInclTransf : Core₁ ⇒ J.
```

The complete hom action of `Core₁` should be factored through named internal
owners rather than specified only pointwise:

```text
ObjMap_C,D(F)(x) ≔ F[x]

(Core₁)₁(C,D)
  ≔ PathInt₁(Obj(C),Obj(D))
       ∘ PathMap(ObjMap_C,D).
```

It therefore sends `F` to `PathMap(F₀)` and sends `h : F = G` to
`PathTransf(eq_ap(ObjMap_C,D,h))`, with the remaining higher action supplied
by the same iterable `PathInt` ladder.

At the current kernel boundary, `Sk⁼` would be a named primitive recursive
category family with the displayed projection rules, because `Cat` is not a
record assembled transparently from object, hom, identity, and composition
fields. Formation of `Sk⁼` and its recursive inclusion is high-feasibility;
the simultaneous functor action is high-feasibility after `PathInt` is
promoted; the complete primitive `CoreInclTransf` ladder is the medium-sized
part because every `tapp*` observation must be supplied and checked. No
mathematical obstruction is known for any of these equality-local pieces.

Here `J` is the canonical inclusion, equivalently the restriction of
`Id_Cat` to `Cat₁⁼`; writing `CoreIncl_ : Core ⇒ Id_Cat` is harmless shorthand
when that domain restriction is implicit. This sequence genuinely removes
the obstruction to the naive full-`Cat_cat` declaration and internalizes the
family `Core_incl_func(C)` as the object components of one transformation.

For this deferred redesign, `CoreInclTransf` is selected as a primitive
stable transfor head: it is the more-internalized natural family whose object
components are the existing primitive `Core_incl_func(C)`. Do not make a
generic pointwise-transfor assembler a prerequisite merely to avoid this
semantic primitive. Primitive here means a kernel constructor with a complete
computational projection ladder, not a bodyless axiom whose observations
remain opaque. Its initial computations are

```text
tapp₀(CoreInclTransf,C) ↪ Core_incl_func(C)

tapp₁(CoreInclTransf,F) ↪ κ_F,
```

followed by component, capped-arrow, full-hom, and iterated equality-action
computations for `κ_F`. In particular its first transfor projection at
`F : C → D` has type

```text
tapp₁(CoreInclTransf,F) = κ_F : F ∘ CoreIncl_C ⇒ CoreIncl_D ∘ PathMap(F₀).
```

This `κ_F` is not a second semantic obstruction: it is simply the ordinary
`tapp₁` computation that must accompany the definition of
`CoreInclTransf`. The strict Core-inclusion rule demonstrated above makes its
source and target definitionally identical, so this projection is the
identity transfor; equality induction/`PathInt` supplies its action on the
remaining equality-valued higher cells. Thus the proposed one-skeleton
package is mathematically coherent and computationally feasible in the
current architecture. Building the complete `Sk⁼` category/functor/inclusion
recursion, the specialized `Cat₁⁼`, and the transformation projection ladder
has not itself been probed and remains optional library
packaging rather than a prerequisite for the WalkingEnd MVP. This design is
fully natural and may ultimately be architecturally preferable because the
Core-inclusion naturality cell is owned by one internal transformation and is
consumed explicitly by the spiral. It is intentionally deferred until after
the already-probed strict WalkingEnd design has been implemented and
validated; do not expand the current MVP by constructing `Cat₁⁼`, `Core₁`, or
`CoreInclTransf`.

Strictness is not required to construct the spiral. Let

```text
p : Nat → Obj(C)
s : Nat → Nat
h : S₀ ∘ p = p ∘ s
P ≔ PathLift(p).
```

Using the endpoint-comparison names fixed earlier, define

```text
κₗ(S,p) : S ∘ PathLift(p) ⇒ PathLift(S₀ ∘ p)
κₗ(S,p) ≔ tapp₁(CoreInclTransf,S) ⋆ PathMap(p)

κᵣ(p,s) : PathLift(p ∘ s) ⇒ PathLift(p) ∘ PathMap(s).
```

The right comparison `κᵣ` is already the identity after conversion because
ordinary `PathInt` functoriality computes
`PathLift(p) ∘ PathMap(s)` to `PathLift(p ∘ s)`. The left comparison `κₗ` is
the whiskered Core-inclusion naturality cell; it need not be an identity.
Consequently the non-strict structured spiral is

```text
spiral ≔ κᵣ(p,s) ∘ᵥ PathLift(h) ∘ᵥ κₗ(S,p)
  : S ∘ P ⇒ P ∘ PathMap(s).
```

Under the active strict representation already probed, `κₗ` also becomes the
identity and the same composite reduces to `PathLift(h)` up to endpoint
conversion. Under the restricted-transformation representation, the genuine
`κₗ` is retained in the spiral. Both are mathematically correct and preserve
the structured higher action. The current G2 implements and audits the strict
version first. A future redesign may compare the non-strict package on
genericity, compositionality, computation, and warning evidence; it must not
silently replace the selected MVP during the present implementation goal.

The intended arrow-to-path collapse is already represented at its proper
strength by groupoidality evidence: the Foundations define
`IsGroupoidalCat(C)` through `Core_incl_func(C)` being an omega-equivalence,
whose selected inverse sends directed arrows back to paths. Such a collapse
can be internalized over a structured/restricted universe carrying that
evidence. It is not valid uniformly over unrestricted `Cat_cat`, and it is
not wanted for `WalkingEnd` itself: the selected HIT is locally discrete
above dimension one but its generating 1-arrow remains noninvertible.

G2 must instead audit, in order:

1. a fully internal `PathInt : Grpd_cat → Cat_cat`, which is feasible because
   higher arrows in `Grpd_cat` are equalities;
2. reproduce, promote, or revise the now-feasible strict fixed-functor
   Core-inclusion owner and its whiskered stable-postcomposition projection
   after the required projection, owner-position, and warning audits; the
   bodyful restricted-one-skeleton alternative is deferred;
3. preserve the demonstrated exact spiral endpoints without any endpoint
   unification shortcut or broad whole-term `Grpd` runtime fold;
4. only if a concrete consumer remains stuck, whether the generic
   Core-inclusion/postcomposition accumulation is a justified runtime owner;
5. only if that stable body still loses a required discriminator, a primitive
   `PathLift` owner with projectionwise agreement to the semantic
   construction, never a broad runtime fold of the semantic body into the
   primitive; and
6. restricted alternatives such as naturality over
   `Core_cat(Cat_cat)` or over explicitly locally discrete categories,
   labelled at their true weaker strength rather than presented as a global
   directed `Core` functor.

The broader groupoidal internalization audit must classify each proposed
owner by level rather than by suggestive name:

| Surface | Expected status | Required interpretation |
| --- | --- | --- |
| `PathInt : Grpd_cat → Cat_cat` | positive | full internal functor; source higher cells are equality |
| `PathMap(f)` and equality action | positive | projections of `PathInt`, with a named iterable ladder |
| `Core_cat(C)` | retain | transparent object-level assignment |
| `CoreOnFunctor(F) ≔ PathMap(F₀)` | positive | action on a fixed ordinary functor, not evidence of a full `Cat_cat` endofunctor |
| `core_incl_naturality(F)` | active strict feasibility demonstrated | implement first as identity after strict endpoint normalization; retain the non-strict `tapp₁(CoreInclTransf,F)` interpretation only in the deferred redesign |
| recursive equality-skeleton `Sk⁼`, `Cat₁⁼`, `Core₁`, and primitive `CoreInclTransf` | semantically positive, potentially preferable, explicitly deferred | use `Core_cat` as the zero skeleton, recurse through homs and functor action, and give the primitive transformation a complete `tapp*` ladder; this removes the arbitrary-directed-`η` obstruction and packages genuine `κₗ`, but is not a general `IsNCat(1)` truncation and must not be constructed during the selected strict MVP |
| `Core : Functor(Cat_cat,Cat_cat)` | negative in general | would require arbitrary directed transformation components to yield paths |
| arrow-to-path collapse | restricted positive | selected inverse supplied by explicit `IsGroupoidalCat`/local-discreteness evidence |
| `Path_sym_func` natural package | plausible | internalize over equality-valued `Grpd_cat`, not by assuming directed `Core` action |
| `Function_grpd` composition/evaluation packages | plausible | promote only with complete identity, composition, and higher equality action |

The G2 exit gate is an exact structured spiral with component and iterable
higher-action computation, zero new probe-specific unification rules, no
bodyless naturality or spiral constant, and an explicit negative check that no
unsupported global directed `Core : Cat_cat → Cat_cat` has been introduced.

## Implementation Goal — Authoritative Work Plan

The report status, the contextual-`Functord` decision above, and this section
are the complete current implementation authority. Everything after the
heading **Superseded Corrective Decisions And Former Implementation —
Historical Evidence** is retained only for provenance and must not be used to
select an architecture, a primitive Hom eliminator, or a completion claim.

### Goal objective

Replace every walking-endomorphism construction that depends on the committed
generated-word Hom presentation by an opaque directed-HIT presentation whose
practical Hom–Nat correspondence is derived from:

1. the contextual whole-HIT eliminator
   `walking_end_ind_funcd(R,D,u,spiral) : Functord(R,D)`;
2. whole-HIT-defined `Code` and its ordinary action on arbitrary walking
   arrows;
3. Nat-recursive powers packaged as a functor into the ordinary directed
   representable hom-category;
4. the directed decoder `Functord(Code,Rep_catd(base))` and its generic
   `fdapp1_int_cell` at zero, producing `p ⇒ power(encode(p))`;
5. an explicit one-dimensionality/truncation witness
   `IsNCat(cat_succ cat_zero,WalkingEnd)` in the selected HIT signature,
   used afterward to turn that directed cell into equality;
6. Nat induction for the other inverse; and
7. only afterward, `BNat`, carrier and hom-category equivalence packaging,
   sethood, and negative directed consequences.

The migration includes the kernel terminal-owner correction, the walking
module, permanent checks, reviewer examples, current documentation, catalog,
health report, and all proportional CI gates. It does not require full
functor-category initiality.

### Explanatory design inputs

Read `tmp/tmp-hit-solution.md`, `tmp/tmp-hit-solution-2.md`,
`tmp/tmp-hit-solution-2-1.md`, `tmp/tmp-hit-solution-2-1-1.md`,
`tmp/tmp-hit-solution-2-1-1-1.md`,
`tmp/tmp-hit-solution-2-1-1-1-1.md`,
`tmp/tmp-hit-solution-2-1-1-1-1-1.md`, and
`tmp/tmp-hit-solution-2-1-1-1-1-1-1.md` before beginning G1–G5. They are tracked
explanatory notes, not implementation authorities. The first records the
Circle-style Code, encode/power, spiral, and decoder idea. The second selects
the parameterized contextual `Functord(R,D)` interface. The third makes the
decisive directed-first correction: use `Rep_catd(base)` for the primary
decoder and postpone equality until the explicit one-dimensionality evidence
is applied. The fourth records the pre-spiral feasibility review; the fifth
records the 2026-07-19 semantic normal-form computation and the remaining
Core-inclusion accumulation problem; the sixth isolates the valid
fixed-functor naturality strength and selects strict Core-inclusion naturality
as the first probe strategy; the seventh records why restricting the source
removes the arbitrary-transfor obstruction and how a genuine non-strict
`κₗ` enters the spiral; and the eighth records the equality-local skeleton's
kernel-feasibility outline and the distinction from a genuine truncation
reflector. Where any note conflicts with the active kernel or this current
override, this report and the active kernel win. Preserve all eight files
unless the user explicitly requests their removal.

### Evidence boundary at goal start

Already demonstrated:

- opaque category/base/loop formation and generic contextual-`Functord`
  typing;
- runtime base and loop constructor beta at `Fibre_func` and
  `fdapp1_int_cell`;
- internal expression of `Code[p](0)` and the exact type of the arbitrary-arrow
  decoder cell;
- an existing transparent directed representable family
  `Rep_catd(base) : Catd(WalkingEnd)` with the required postcomposition and
  higher directed action;
- the native finite-dimension predicate
  `IsNCat(cat_succ cat_zero,W)`, its reduction to homwise `IsDiscreteCat`, and
  the existing `hom_to_path` consumer needed for the equality upgrade;
- an internally generated `PathInt`/function-equality action whose
  transformation components and full higher action compute, plus a concrete
  Nat spiral in the experimental endpoint-comparison environment;
- semantic normal-form evidence that
  `PathLift_sem(f) ∘ PathMap(g)` already accumulates through the existing
  owners and that only the outer `F ∘ CoreIncl`/postcomposition cut remains
  stuck;
- the append-only strict Core-inclusion resolution of that final cut, with
  zero local unification rules, exact spiral endpoints, identity component
  computation, iterable higher action, and a byte-for-byte snapshot at
  `tmp/wehit_path_int_strict_core_incl_success_2026-07-19.lp`;
- viability of demoting the generic terminal `fdapp1_int_cell` owner and of
  retaining generic contextual runtime beta, in the earlier demote-both owner
  experiment;
- the demote-both experiment's `964/157` inventory against active `971/157`,
  as bracketing evidence rather than the selected hybrid's inventory; and
- zero strict-LHS findings.

Not yet demonstrated by the selected contextual probe:

- a concrete, non-bodyless `Code` family and successor functor;
- an owner-position, warning-audited, promotion-quality `PathInt` projection
  ladder and strict fixed-functor Core-inclusion owner in the active kernel;
- a concrete `power_func` integrated into the ordinary directed based-hom
  category and the clean exact spiral;
- a signature-level `walking_end_is_one_cat` witness for the new opaque HIT
  and its transparent based-hom specialization;
- a fresh exact owner-position run of the selected retain-`tapp0`/
  demote-`fdapp1` hybrid;
- the directed decoder, its arbitrary-arrow normalization cell, or either
  equality inverse theorem in the contextual design;
- integration with the active walking module, checks, examples, or downstream
  consequence packages.

The constants named `Code`, `H`, `power`, and `spiral` in
`wehit_opaque_functord_ind_minimal.lp` are type-shape sentinels. They are not
implementations of those objects, and its opaque equality-valued `H` is no
longer the selected decoder target. The implementation agent must not cite
that probe as evidence that the concrete directed decoder or hard equality is
already finished.

### Phase G0 — Recovery, inventory, and baselines

1. Follow `AGENTS.md` recovery and starting-task procedure; read this current
   authority before the historical remainder.
2. Inspect staged and unstaged changes independently. Read and preserve the
   eight listed `tmp/tmp-hit-solution*.md` explanatory files unless the user
   has changed their status.
3. Relocate all owners and consumers with `rg`; do not use the line numbers in
   this report as edit coordinates.
4. Run bounded `make check`, `make examples`, kernel and walking warning
   summaries, and strict LHS audits.
5. Record the exact active symbol/check/example inventory before removal so no
   public consequence is silently lost.

Exit criterion: a clean baseline and an explicit migration map for every
walking/BNat symbol, diagnostic, and example.

### Phase G1 — Terminal and contextual-beta owner migration

Reconstruct the selected design at the real owning positions; do not copy the
current ignored `tmp/probes/wehit_functord_terminal_owner_full.lp`, whose later
contents are stale. The complete terminal-owner change is:

```text
retain runtime unchanged:
  tapp0_fapp0(F,k) ↪ Obj_func(F[k])

demote runtime to proof time:
  fdapp1_int_cell(s,p,*) ≡ fapp1_fapp0(s,p)

add contextual HIT computation:
  Fibre_func(indᵈ(R,D,u,σ),base) ↪ u
  fdapp1_int_cell(indᵈ(R,D,u,σ),loop,r) ↪ σ[r].
```

Do not add either proposed `tapp0_fapp0` eta unification rule, a direct
`Const_func` specialization, a WalkingEnd-specific terminal point join, a
WalkingEnd-specific ordinary-loop bridge, or preselected vertical-composition
bridges. Validate the one generic terminal arrow comparison with typed
`eq_refl`, and validate the generic contextual base and loop betas by direct
runtime assertions. State derived section/ordinary-functor views as
transparent theorems composed from those generic owners when they do not
reduce in one step.

Exit criterion: full owner copy and active owners pass quiet checking,
warning comparison, the typed generic terminal-arrow consumer, direct generic
HIT-beta assertions, strict LHS audit, and runtime negative controls. Record
the retained terminal base-beta and generic vertical-composition warnings as
measured boundaries; do not misdescribe proof-time theorems as runtime joins.

### Phase G2 — Path action and the one-dimensional truncated-HIT contract

Construct and validate the ordinary equality action genuinely available from
a function:

```text
Path_map(f) : Functor(Path_cat(A),Path_cat(B))
NatSucc_func : Functor(Path_cat(Nat),Path_cat(Nat))
NatSucc_func(n) ↪ succ(n).
```

Require object action, equality action via `eq_ap`, identity, composition, and
iterable next-hom behavior. Build a named intermediate `fapp*`/`tapp*`
projection ladder for `PathInt`, `PathMap`, function-equality action,
components, and full off-diagonal action; do not retain the nested
probe-local patterns as the permanent interface. A reusable
`Path_cat_func` may act on an ordinary function or functor's object map.

Audit the broader groupoidal constructor surface level by level:
`Path_cat`, `Core_cat`, `Core_incl_func`, `Path_sym_func`,
`Function_grpd`, and their existing object/arrow/higher projections. Add an
internalized version only when all required higher actions are supplied.
`PathInt : Grpd_cat → Cat_cat` is the positive reference case. Do not declare
a generic directed `Core : Cat_cat → Cat_cat` or `Core_catd`, because an
arbitrary directed transfor does not supply equality between its component
objects. Retain `Core_cat(C)` as the valid object-level alias and distinguish
the fixed ordinary-functor action `PathMap(F₀)` from a nonexistent full
higher action. Treat arrow-to-path collapse as inverse data carried by an
explicit groupoidality/local-discreteness structure. Reproduce the successful
strict fixed-functor `core_incl_naturality(F)` and whiskering probe at their
candidate owner positions before promotion; use a primitive `PathLift` only
if the stable semantic construction fails a concrete permanent consumer.

Select the ordinary directed representable as the decoder target:

```text
Hᵈⁱʳ ≔ Rep_catd(base) : Catd(WalkingEnd)
Hᵈⁱʳ(x) ≔ Hom_cat(WalkingEnd,base,x).
```

Its complete higher action already exists internally:

```text
Hᵈⁱʳ[p](r) ≔ p ∘ r
Hᵈⁱʳ[α]ᵣ ≔ α ▷ r.
```

Probe the exact open `fdapp1_int_cell` endpoints for
`Functord(Code,Hᵈⁱʳ)` at arbitrary `p` and `n`; no bodyless target family
or equality-reflecting action is permitted. This directed construction is the
selected primary milestone, not a fallback.

The selected WalkingEnd is a **one-dimensional directed HIT**. Record that
dimension explicitly in its signature:

```text
constant symbol walking_end_is_one_cat
  : τ (IsNCat (cat_succ cat_zero) WalkingEnd);
```

By the active kernel definition, this is exactly:

```text
Π x y : Obj(WalkingEnd),
  IsDiscreteCat(Hom_cat(WalkingEnd,x,y)).
```

It is not `IsDiscreteCat(WalkingEnd)`: the generator remains a directed,
potentially noninvertible 1-cell. The signature-level evidence states only
that no independent higher directed cells occur above the freely generated
1-category. Prefer this global, reusable dimension contract over an ad hoc
constant mentioning only `Hom_cat(WalkingEnd,base,base)`.

Define transparent specializations rather than duplicate assumptions:

```text
walking_end_hom_discrete(x,y)
  ≔ walking_end_is_one_cat(x,y)

walking_end_based_hom_discrete(x)
  ≔ walking_end_is_one_cat(base,x).
```

Run a focused formation probe in which an arbitrary directed cell in a based
hom-category is converted by the latter witness through the existing
`hom_to_path`. The witness itself has no Hom–Nat, word-carrier, decoder, or
normal-form field, so applying it after the directed decoder is not circular.
Document it honestly as a truncation constructor/evidence of the selected HIT,
not as a theorem derived by the current eliminator.

Also record a nonblocking derivability audit: a future stronger general HIT
induction/initiality interface may prove the same `IsNCat` witness from the
absence of higher generators, at which point the primitive signature evidence
can be retired. Do not delay the practical MVP for that metatheorem, and do
not claim in the meantime that one-dimensionality was derived.

Exit criterion: `Path_map` and `NatSucc_func` are concrete through a named
projection ladder; fixed-functor Core-inclusion naturality, its whiskering, and
the exact spiral compute without new probe-local `unif_rule` declarations or
an unneeded runtime fusion rule; the
open directed representable target and its higher action typecheck without
sentinels; the one-dimensional signature contract and `hom_to_path`
specialization pass a focused probe; and negative controls confirm that
neither `IsDiscreteCat(WalkingEnd)` nor an unsupported generic directed
`Core`/`Core_catd` has been added.

### Phase G3 — Opaque walking HIT and eliminator family

Rebuild `emdash3_2_walking_end_hit.lp` around only:

```text
WalkingEnd_cat : Cat
walking_base   : Obj(WalkingEnd_cat)
walking_loop   : Hom(WalkingEnd_cat,walking_base,walking_base)

constant symbol walking_end_is_one_cat
  : τ (IsNCat (cat_succ cat_zero) WalkingEnd_cat);
```

Delete the `walking_end_hom` datatype, `WalkingEndHom_grpd`, its induction,
and every WalkingEnd-specific `Obj`, `Hom`, identity, or composition rewrite.
Retain opacity checks for all four forbidden reductions. The last declaration
is the standard one-dimensional truncation evidence of this selected HIT, not
a carrier presentation or computation rule. It must not add a rewrite for
WalkingEnd `Obj`, `Hom`, identity, or composition.

Install the contextual eliminator and data classifiers:

```text
walking_end_loop_lhs_func(R,D,u) ≔ D[loop] ∘ u
walking_end_loop_rhs_func(R,D,u) ≔ u ∘ R[loop]
walking_end_loop_coherence(R,D,u) ≔
  Transf(D[loop] ∘ u, u ∘ R[loop])

walking_end_ind_funcd(R,D,u,σ) : Functord(R,D).
```

Promote runtime constructor beta only at the stable existing owners:

```text
Fibre_func(walking_end_ind_funcd(R,D,u,σ),base) ↪ u
fdapp1_int_cell(walking_end_ind_funcd(R,D,u,σ),loop,r) ↪ σ[r].
```

Derive, rather than duplicate, the ordinary section eliminator by setting
`R ≔ Const_catd(WalkingEnd,Terminal_cat)`, and derive the nondependent
recursor by also taking a constant target family. Their readable base/loop
theorems must route transparently through `walking_end_ind_funcd`, the generic
terminal projection comparison, and the contextual betas. Do not add
specialized recursor beta rules merely to force one-step reflexivity. Label
which observations are runtime reductions and which are transparent equality
theorems assembled from generic comparisons.

Derive the based-hom discreteness witnesses transparently by applying
`walking_end_is_one_cat`; do not postulate a second base-specific `d`. Check
that a `BNat`/free-monoid model satisfies the constructors, contextual
eliminator equations, and one-dimensionality contract as semantic consistency
evidence, without using that model as the definitional Hom of `WalkingEnd`.

Exit criterion: the opaque one-dimensional HIT, contextual eliminator,
terminal section specialization, and constant recursor all compute at
base/loop while arbitrary Hom remains opaque; homwise discreteness is exposed
only through the explicit dimension witness.

### Phase G4 — Concrete `Code`, directed representable, powers, and spiral

After G2 passes, construct the previously opaque sentinels transparently,
replacing the sentinel `H` by the existing representable:

1. `Code : Catd(WalkingEnd)` by the derived recursor into `Cat_cat`, with
   a runtime/transparent base observation and a transparent loop-action
   theorem comparing `Code[loop]` with `NatSucc_func`; claim a raw
   `Code[loop] ↪ NatSucc_func` reduction only if a direct runtime assertion
   demonstrates it without a specialized bridge;
2. `encodeₓ(p) ≔ Code[p](zero)` using ordinary `catd_transport_func` and
   `fapp0`;
3. a readable transparent alias, if useful, for
   `Hᵈⁱʳ ≔ Rep_catd(base)`, retaining the generic representable as the
   semantic owner; verify its open postcomposition and whiskering actions
   rather than duplicating them in WalkingEnd-specific rules;
4. the Nat-recursive object function
   `power(0) ↪ id` and `power(succ n) ↪ loop ∘ power(n)`, lifted through
   the reusable path action and core inclusion to
   `power_func : Functor(Path_cat(Nat),Hom_cat(WalkingEnd,base,base))`; and
5. a transparent **directed** spiral transfor
   `Hᵈⁱʳ[loop] ∘ power_func ⇒ power_func ∘ Code[loop]`, whose
   component has type
   `loop ∘ power(n) ⇒ power(succ n)` and reduces to the appropriate
   identity 2-cell after the power equation. Do not declare a bodyless
   equality-valued spiral.

Check composition orientation on open variables. The one-generator example
must not use commutativity of Nat addition to conceal a variance error.

Exit criterion: concrete formation and accurately classified base/loop
computations for `Code`, `encode`, the generic directed representable,
`power_func`, and the directed spiral, including open higher-action checks and
negative controls against direct Hom–Nat conversion or a generic `Core_catd`.

### Phase G5 — Decoder and both inverse proofs

Define only through the contextual eliminator:

```text
walking_directed_decode_funcd ≔
  walking_end_ind_funcd(Code,Rep_catd(base),power_func,spiral)
  : Functord(Code,Rep_catd(base)).
```

For arbitrary `p : Hom(WalkingEnd,base,x)`, evaluate its generic displayed
action at zero. After base beta, `power(0)`, generic representable
postcomposition, and the right-unit comparison, first retain the result in
its native directed form:

```text
νₚ : p ⇒ decodeᵈ[x](encodeₓ(p)).
```

This directed normalization theorem is an independently named public
milestone. Its proof must materially contain the generic `fdapp1_int_cell` of
`walking_directed_decode_funcd`; do not immediately hide it inside an equality
wrapper.

Next specialize the signature's one-dimensionality evidence:

```text
dₓ : IsDiscreteCat(Hom_cat(WalkingEnd,base,x))
dₓ ≔ walking_end_is_one_cat(base,x).
```

Convert the already-constructed directed cell through the existing selected
core inverse:

```text
hom_to_path(dₓ,νₚ)
  : p = decodeᵈ[x](encodeₓ(p)).
```

Use explicit equality symmetry to export the intended orientation:

```text
decodeᵈ[x](encodeₓ(p)) = p.
```

At `x ≔ base`, contextual base beta identifies `decodeᵈ[base]` with
`power_func`, giving the hard endomorphism inverse:

```text
power(encode(p)) = p.
```

Prove the other inverse by native Nat induction:

```text
encode(power(n)) = n.
```

Its successor case must visibly use generic Code functoriality, Code's loop
beta, the power recursion equation, and the induction hypothesis. Inspect
theorem bodies and normalized projections: neither inverse may be bodyless or
route through word induction, an equality-valued decoder sentinel, a hidden
normal-form axiom, or a pre-existing Hom–Nat equivalence.

Exit criterion: the directed arbitrary-arrow normalization cell and both
transparent equality inverse proofs pass. The hard equality visibly factors
as contextual `fdapp1_int_cell` → right-unit endpoint comparison →
`hom_to_path` using the explicit one-dimensional signature evidence →
orientation-changing `eq_sym`; none of those stages is hidden in a bodyless
constant.

### Phase G6 — Nat/`BNat` packaging and directed consequences

Retain `emdash3_2_nat_arithmetic.lp` as reusable independent infrastructure.
`BNat_cat` may remain as a separate explicit one-object Nat model, but it is
downstream packaging, never the definition of WalkingEnd Hom. Rebuild its
walking encoder/decoder functors only from the corrected recursor, `encode`,
and `power` after both inverse proofs pass.

Then rebuild:

- `EquivByInverse`, `TypeEquiv`, and native EQ1 Hom–Nat packages;
- the packaged `walking_end_one_cat : OneCat` directly from the explicit
  signature evidence, and its transparent homwise-discreteness projections;
- sethood of the **object carrier** `Hom(WalkingEnd,base,base)`, with the
  signature evidence and corrected carrier equivalence recorded as distinct
  available proofs rather than conflated;
- where supported by the existing EQ1 layer, the structured comparison of
  `Hom_cat(WalkingEnd,base,base)` with `Path_cat(Nat)` using its core
  equivalence and the corrected carrier maps;
- loop nonidentity, noninvertibility, and nongroupoidality from encoding and
  Nat no-confusion, never word constructors; and
- any useful composition-to-addition theorem with the existing generic
  composition owner and measured warning policy.

Do not infer local discreteness or `IsNCat(cat_succ cat_zero,WalkingEnd)` from
the carrier-level Hom–Nat equivalence. They are available because
one-dimensionality is explicit data in the selected HIT signature. Conversely,
do not describe that truncation witness alone as a proof that the 1-arrow
carrier is Nat; the directed decoder and both inverse proofs still do the
normal-form work. `BNat_cat` retains its own separately proved `OneCat`
evidence.

If a former theorem cannot be derived without the rejected representation,
mark it honestly deferred rather than replacing it by a constant.

Exit criterion: every retained public mathematical consequence depends on
the corrected semantic maps/inverses and contains no rejected symbol; carrier
sethood, Hom-category discreteness, carrier equivalence, and structured
Hom-category equivalence are stated at their actual distinct strengths; the
`WalkingEnd` `OneCat` claim points to the explicit HIT truncation evidence.

### Phase G7 — Complete consumer and documentation migration

Rewrite the complete catalog area in `emdash3_2_checks.lp`; remove every
assertion mentioning `walking_end_hom`, `WalkingEndHom_grpd`, word identity,
word step, or transparent WalkingEnd Hom. Add permanent checks for:

- opaque `Obj`/`Hom` and no WalkingEnd-specific identity/composition fold;
- explicit `IsNCat(cat_succ cat_zero,WalkingEnd)` signature evidence,
  transparent homwise-discreteness specialization, and negative control
  against `IsDiscreteCat(WalkingEnd)`;
- contextual formation and both runtime constructor betas;
- terminal-section and constant-recursion specializations;
- the retained runtime terminal `tapp0_fapp0`, the proof-time generic terminal
  `fdapp1_int_cell ≡ fapp1_fapp0` comparison, contextual runtime betas, and
  explicit positive/negative checks at the accepted terminal base-beta
  warning boundary;
- `Code`, the generic directed representable, power, directed spiral,
  directed decoder, arbitrary-arrow directed normalization, its explicit
  `hom_to_path` equality upgrade, the hard inverse, and the Nat easy inverse;
- both positive equivalence projections and negative open conversion controls;
- downstream `BNat`, carrier-sethood, signature-owned WalkingEnd
  one-dimensionality, and directed negative results that survive.

Rewrite `examples/walking_endomorphism_hit.lp` as the reviewer-facing story of
the opaque constructors, explicit one-dimensional truncation evidence,
contextual elimination, Code/encode, directed representable power/spiral, the
directed normalization cell, its equality upgrade, both inverse proofs, and
downstream consequences. Retain
`examples/walking_endomorphism_nat_prerequisites.lp` only for genuinely
walking-independent Nat infrastructure.

After implementation facts pass, synchronize `reports/INDEX.md`,
`reports/EMDASH_FOUNDATIONS.md`,
`reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`, the parent
H2 row, this plan's status/ledger, generated catalog, and health report. Search
the complete repository for rejected symbols and stale word-carrier prose.

Exit criterion: no active code, check, example, or current-status document
describes words as the HIT Hom or a special 1-cell eliminator as selected.

### Phase G8 — Final gates and completion policy

Run, at minimum:

```text
make check
make examples
make check-warnings
make warning-summary
make audit-rules
make catalog
make toc
make health
make ci
```

Also run focused quiet/warning probes for every new nontrivial owner and typed
`eq_refl` consumers for every unification rule. Compare kernel and walking
warning inventories by exact owner, not only total count. Record and justify
every new unjoinable pair; do not call a runtime pair solved merely because a
proof-time comparison exists.

The goal is complete only when all rejected word/Hom symbols and consumers are
gone; the opaque HIT, contextual eliminator, and explicit one-dimensional
signature evidence are active; the concrete `Code`, directed representable
decoder, and arbitrary-arrow normalization cell are transparent; both genuine
equality inverses visibly use the selected truncation evidence where required;
all retained consequences state carrier equality, directed cells, and
hom-category discreteness at their actual strengths; current documentation is
synchronized; and full CI passes. A directed decoder cell is a valid completed
intermediate milestone but not by itself the final Hom–Nat equality result. A
difficult prerequisite or warning is not a blocker until the `AGENTS.md`
repeated-blocker policy is met.

### Current implementation ledger

| Task | Status at goal start | Required result |
| --- | --- | --- |
| `WEHIT-G1-TERMINAL-OWNER` | terminal `fdapp1` demotion and typed derived views active at the generic owner; exact hybrid full-copy probe passes; contextual betas held for atomic G3 because the reducible legacy loop causes subject-reduction failure | land the already-probed contextual base/loop betas with opaque WalkingEnd and retain no HIT-specific bridge |
| `WEHIT-G2-PATH-DIMENSION` | complete: named Path/Core/NatSucc/spiral owners active at `984/159`; warning-neutral formation probe validates the exact directed `Rep_catd(base)` cell, global OneCat signature shape, `hom_to_path` specialization, and non-discreteness control | land the already-validated opaque signature declarations atomically in G3 |
| `WEHIT-G2-GROUPOID-INTERNALIZATION-AUDIT` | complete: all requested surfaces classified level by level; capped composition eta consequence recorded; fixed-functor Core action retained; no global directed Core/Core_catd or directed-cell reflection added | retain these boundaries during G3–G7 |
| `WEHIT-FUTURE-COREINCL-TRANSF` | explicitly deferred possible redesign; mathematically natural and potentially architecturally preferable | after the strict MVP is complete, optionally probe recursive `Sk⁼(n,A)` with `Core_cat` at zero, simultaneous `Sk⁼` functor action and recursive inclusion, `Cat₁⁼ ≔ Sk⁼(cat_succ(cat_zero),Cat_cat)`, `Core₁`, primitive computational `CoreInclTransf`, genuine `κₗ`, and the non-strict spiral `κᵣ ∘ᵥ PathLift(h) ∘ᵥ κₗ`; do not conflate it with an unavailable universal `IsNCat(1)` truncation or make it a current-goal prerequisite |
| `WEHIT-G2-DIMENSION-DERIVABILITY` | nonblocking future audit | determine whether stronger general HIT induction derives OneCat evidence and can retire the explicit truncation constructor; never claim this during the MVP without a proof |
| `WEHIT-G3-OPAQUE-OWNER` | complete: generated-word Hom and all WalkingEnd category-operation rules removed; opaque constructors, explicit dimension evidence, contextual eliminator, derived section/recursor views, four opacity controls, and separate BNat model active; module `989/159`, zero unreviewed LHS clauses | preserve the two-rule HIT runtime boundary during G4–G7 |
| `WEHIT-G4-CODE-REP-POWER` | active: generic exact spiral mechanism and directed representable formation already demonstrated without endpoint shortcuts; opaque WalkingEnd integration now unblocked | concrete transparent Code, generic directed representable, power functor, and exact directed spiral through the selected G2 internal owners |
| `WEHIT-G5-DIRECTED-AND-EQUALITY-ROUNDTRIPS` | open in selected design | directed normalization from decoder `fdapp1`; hard equality via explicit hom discreteness; easy inverse from Nat induction |
| `WEHIT-G6-PACKAGING` | old implementation rejected | rebuild BNat, carrier/structured Hom comparisons, sethood, OneCat package, and negative consequences at their distinct strengths |
| `WEHIT-G7-MIGRATION` | open | checks, examples, docs, catalog, health contain no rejected architecture |
| `WEHIT-G8-GATES` | open | proportional probes, warnings/audits, and full local CI pass |

## Superseded Corrective Decisions And Former Implementation — Historical Evidence

The remainder of this report is chronological evidence from rejected or
superseded branches. It may be consulted to avoid repeating failed probes,
but it is not an instruction source for the implementation goal above.

### Review verdict

The active `emdash3_2_walking_end_hit.lp` does not presently implement the HIT
meant by this plan. It declares an inductive word carrier and then installs:

```text
Obj(WalkingEnd)       ↪ Unit
Hom(WalkingEnd,_,_)   ↪ Path(WalkingEndHom)
id                    ↪ word-id
composition           ↪ word recursion.
```

Consequently `walking_end_hom_ind` is induction on a datatype that has
already been made definitionally equal to the Hom classifier. Renaming that
datatype “intrinsic” does not change the architecture. It makes the desired
free-word result true by the selected representation and is not elimination
from an opaque HIT generated only by `base` and `loop`.

The corrected presentation must instead begin with exactly the opaque
formation and introductions:

```text
WalkingEnd : Cat
base       : Obj(WalkingEnd)
loop       : Hom(WalkingEnd,base,base).
```

There must be no rewrite for `Obj(WalkingEnd)`, no rewrite for
`Hom(WalkingEnd,_,_)`, and no WalkingEnd-specific identity or composition
normalizer. In particular there is no `WalkingWord`, `walking_end_hom`, or
other generated-arrow datatype in the public or definitional presentation of
the HIT. A separate concrete model such as `BNat` may expose Nat-valued Hom;
the HIT itself may not.

### Correct eliminator and constructor computation

For a structured motive `D : Catd(WalkingEnd)`, base datum

```text
u : Obj(D[base])
```

and displayed loop datum

```text
ℓᴰ : Hom(D[base], D[loop](u), u),
```

the primitive eliminator is:

```text
ind(D,u,ℓᴰ) : Obj(Π D).
```

Both constructor computations are selected as judgmental computation:

```text
ind(D,u,ℓᴰ)[base] ↪ u
ind(D,u,ℓᴰ)[loop] ↪ ℓᴰ.
```

In the current projection tower the stable owners are terminal component
evaluation for the point rule and `fdapp1_int_cell` for the loop rule. The
loop equation is therefore a rewrite, not a bodyless equality constant and
not merely a proposition whose proof is postulated. A readable theorem may be
exported, but its body must be `eq_refl` after the rewrite.

The focused probe confirms that both rewrites typecheck while the category,
object, and arrow constructors remain opaque. The constant-family section
action should be observed through `piapp1_fapp0`; this route sees the same
dependent loop beta without installing a second ordinary-`fapp1_fapp0`
constructor rule.

### Why the former loop-square objection does not justify weakening beta

The raw term

```text
ind(Const(C),x,f)[loop] ∘ ind(Const(C),x,f)[loop]
```

still has two runtime reduction orders: loop beta exposes `f ∘ f`, while the
ambient strict-functor cut first exposes action on `loop ∘ loop`. The focused
probe retains this as a negative conversion control. That is a real
normal-form boundary, but it is not a blocker to judgmental constructor beta
or to practical proofs.

The coherent solution is to state the ambient strict-functor law once at a
generic constant-section variable, where its proof is reflexivity, and only
then specialize it to the HIT recursor. The specialized proof retains the
functoriality provenance even after loop beta computes. Combining that generic
law with the constructor rewrite derives the loop-prefix and loop-square
equations propositionally, without a word datatype, a recursive action
normalizer, or a family of composite-specific rules.

Thus the selected boundary is now:

```text
point constructor beta     runtime rewrite
loop constructor beta      runtime rewrite
generic composition law    one ambient strict owner
specialized composite law  transparent theorem from the two items above
```

An attempted bare-term `unif_rule` from the loop action to an arbitrary
supplied `ℓᴰ` was also rejected in the corrective probes: the variable-headed
side is too broad for reliable elaboration. A rigid intermediary did not make
the actual supplied datum judgmentally visible. The direct stable-owner
rewrite is both simpler and stronger.

### Circle inspiration and the exact directed boundary

The HoTT/Coq and Cubical Agda Circle encode–decode constructions determine
the correct abstraction boundary and the Code half of the proof. They do not,
however, supply a directed `J` for a noninvertible category arrow.

| Circle construction | Directed walking construction and status |
| --- | --- |
| `Circle`, `base`, `loop` | opaque `WalkingEnd`, `base`, directed `loop` |
| `helix` / `Circle_code` over the whole Circle | `Code : WalkingEnd ⊢ Cat` from the whole-HIT recursor |
| code at the base is `ℤ` | `Code(base) ≡ Path(ℕ)` |
| loop transports by integer successor equivalence | `Code(loop) ≡ succ`, a noninvertible directed successor functor |
| `encode(p)` transports zero along `p` | `encode(p) ≔ Code[p](0)` |
| `intLoop` / loop exponentiation | `power(0) ≔ id`; `power(n+1) ≔ loop ∘ power(n)` |
| `decodeSquare` / spiral | useful guidance for a structured decoder, but not by itself equality of directed arrows |
| ordinary `J` on `p : base = x` | unavailable for `p : Hom(WalkingEnd,base,x)`; the practical replacement is the HIT's 1-cell elimination component |

The Code family is formed by eliminating the whole HIT into `Cat`:

```text
Code        ≔ rec(Cat, Path(ℕ), succ)
encodeₓ(p) ≔ Code[p](0).
```

This is the important typing point: there is no eliminator
`Hom(WalkingEnd,base,base) → ℕ`. The map on endomorphisms is the action of the
whole-HIT-defined Code family. A one-object `BNat` functor is an optional
packaging of the same observation, not its foundation.

The reverse map on the based endomorphism fibre is ordinary Nat recursion:

```text
power : ℕ → Hom(WalkingEnd,base,base)
power(0)     ↪ id
power(n + 1) ↪ loop ∘ power(n).
```

The easy inverse is then:

```text
encode(power(n)) = n,
```

proved by Nat induction. Its successor step uses the generic
constant-section composition theorem and judgmental loop beta. The focused
probe contains this transparent proof for the actual Code action.

### Why `PathOut` does not supply the Circle's final `J`

The earlier corrective draft overstated the `PathOut` route. An arrow in the
enriched outgoing-path category from `(y,p)` to `(z,q)` consists of a base
arrow and a directed 2-cell, schematically:

```text
(f,α) : (y,p) → (z,q),       α : f ∘ p → q.
```

To make

```text
Roundtrip(y,p) ≔ Path(power(encode(p)),p)
```

a `Catd(PathOut(WalkingEnd,base))`, its action would have to turn equality at
`p` into equality at `q`. The directed cell `α` is not an equality and need
not be invertible. Therefore that action does not follow from Code, a decoder,
or the existing `path_ind_sec`. Declaring a bodyless `Roundtrip` family makes
the final theorem typecheck, but simply assumes the missing freeness result.

This is exactly where the Circle analogy stops: the Circle's `p` is itself an
identity path, so ordinary equality `J` applies. A walking endomorphism's `p`
is deliberately a noninvertible directed arrow. The existing `path_ind_sec`
is generic enriched-slice transport for every category; it is not induction
on the arrows generated by this particular HIT.

The old probe's `opaque_roundtrip_motive` was only such a bodyless type-shape
sentinel. It has now been removed. It was never evidence that the hard inverse
had been constructed.

### Minimal directed solution: the HIT's 1-cell elimination component

A categorical HIT is multi-sorted: it generates objects, 1-cells, and their
higher categorical structure. Keeping its Hom classifier opaque does not mean
omitting the elimination principle for generated 1-cells. The minimal
practical interface extends the section eliminator with the following
based-endomorphism component of the *same* HIT:

```text
cell_ind
  (P : Hom(WalkingEnd,base,base) → Grpd)
  (z : P(id))
  (s : Π p, P(p) → P(loop ∘ p))
  (p : Hom(WalkingEnd,base,base))
  : P(p).
```

This declaration quantifies over opaque Hom. It does not define Hom as a word
or Nat datatype, does not introduce arrow normal forms, and adds no
WalkingEnd-specific identity or composition rule. Its computations are:

```text
cell_ind(P,z,s,id)             ↪ z
cell_ind(P,z,s,loop ∘ p)       ≡ s(p,cell_ind(P,z,s,p)).
```

The probe selects runtime rewrites for identity and generator prefix. The
literal-loop specialization joins the global right-unit reduction at
`loop ∘ id`. One probe-local warning remains where the prefix rule meets the
generic precomposition normalizer. This does not affect the typed hard proof,
but it is a real owner/coherence gate: promotion must either construct the
missing join, select a sound proof-time presentation that passes a typed
`eq_refl` test, or explicitly accept the measured interaction after the full
owner-position audit. An earlier rigid-intermediary unifier passed only while
unused and failed once typed reflexivity actually exercised it; it is rejected.

The hard inverse is then elementary and transparent. Instantiate:

```text
P(p) ≔ Path(power(encode(p)),p).
```

The identity case is reflexivity. For the generator-prefix step, whole-HIT
Code functoriality and loop beta give:

```text
encode(loop ∘ p) = succ(encode(p)).
```

Nat computation and congruence then give:

```text
power(encode(loop ∘ p))
  = power(succ(encode(p)))
  = loop ∘ power(encode(p))
  = loop ∘ p.
```

Applying `cell_ind` yields:

```text
power(encode(p)) = p
```

for arbitrary opaque `p`. Thus the forward classifier still comes from
whole-HIT Code elimination, the easy inverse still uses Nat induction, and
the hard inverse now uses the 1-cell component of the opaque HIT eliminator.
No concrete Hom carrier, decoder axiom, round-trip axiom, or full
functor-category initiality metatheorem is used.

There is one explicit architecture decision before promotion. Either:

1. accept `cell_ind` as the primitive 1-cell component of this first concrete
   categorical HIT; or
2. first implement a reusable general displayed-category/free-category
   eliminator from which this exact `cell_ind` is transparently derived.

If “elimination only on the whole `WalkingEnd`” is interpreted as forbidding
even this opaque 1-cell component, branch 2 is required. Coq/Agda Circle code
does not remove that prerequisite, because its final `J` relies on the
invertibility and identity-type status of the Circle loop. A decoder spiral
may still be valuable later for a directed 2-cell/naturality comparison, but
without prior local discreteness it does not prove equality of arbitrary
walking arrows and is no longer the selected hard-roundtrip route.

### Focused probe evidence

The current decisive probe is:

```text
tmp/probes/wehit_opaque_rewrite_loop_beta.lp
```

It checks all of the following without any `Obj`/`Hom` rule for the probe HIT:

1. opaque formation of the category, point, and directed loop;
2. runtime point and loop beta at the stable section owners;
3. whole-HIT `Code` with Nat successor action;
4. `encode(p) ≔ Code[p](0)`;
5. Nat-recursive `power`;
6. the transparent Nat-inductive proof `encode(power(n)) = n`;
7. the negative raw loop-square conversion control;
8. the opaque 1-cell eliminator with runtime identity and generator-prefix
   computation;
9. the transparent generator-prefix closure proof; and
10. the transparent hard inverse `power(encode(p)) = p` for arbitrary opaque
    `p`.

The final quiet and warning-enabled logs are:

```text
logs/probes/wehit_opaque_rewrite_loop_beta-20260718-150610.log
logs/probes/wehit_opaque_rewrite_loop_beta-20260718-150731.log
```

The warning run reports one probe-local unjoinable interaction between cell
prefix beta and generic precomposition after the literal-loop/right-unit join
is installed. This is bounded operational feasibility evidence and an open
promotion gate, not a semantic model, normalization proof, or derivation of
`cell_ind` from more general infrastructure.

Two rejected unification experiments are retained only as negative evidence:

```text
tmp/probes/wehit_opaque_unif_loop_beta.lp
tmp/probes/wehit_opaque_rigid_unif_loop_beta.lp.
```

### Status of the committed implementation

Until the correction phases below pass, the committed walking module has this
status:

| Component | Corrective status |
| --- | --- |
| reusable Nat addition, associativity, Unit/Empty proposition evidence, Nat sethood | retain |
| separate `BNat` model | potentially retain after dependency and warning recheck |
| `walking_end_hom` / `WalkingEndHom_grpd` | reject and remove from the HIT presentation |
| WalkingEnd `Obj`, `Hom`, identity, and constructor-composition rewrites | reject and remove |
| current `walking_end_hom_ind` round trip | invalid as evidence for the requested HIT freeness |
| opaque-Hom `walking_end_ind_cell` | missing from active code; final probe validates the minimal interface and hard proof |
| current point beta | reusable shape, re-probe after opaque migration |
| current propositional loop-beta constant | replace with judgmental stable-owner rewrite |
| current recursor-derived encoder idea | retain, but rebuild through opaque Code/section action |
| current primitive structured decoder | not accepted as the foundation of either inverse; retain only if later justified as useful packaging |
| current Hom–Nat equivalence packages | rederive only after both corrected round trips |
| current sethood, OneCat, nonidentity, noninvertibility, nongroupoidality | mathematically plausible but must be rederived; their present proofs depend on the rejected Hom representation |

The primitive `Join_cat` remains a useful comparison: its category is opaque
and its recursor computes on inclusions and the natural cross cell, so it does
not commit the same Hom-rewrite error. It is nevertheless only a primitive
nondependent directed-inductive staging point; it lacks a dependent
eliminator and uniqueness theorem and therefore should not be advertised as a
complete general HIT implementation.

### Reopened correction phases

#### Phase R0 — authority and negative controls — completed in this review

1. Reopen this report and invalidate the word-carrier completion claim.
2. Record the exact opaque formation and judgmental beta requirements.
3. Retain negative controls against `Hom(WalkingEnd,base,base) ≡ Nat`, loop
   identity, and hidden object/Hom computation.
4. Preserve unrelated committed work and make no active implementation change
   during the review.

Exit result: this report and the ignored focused probe state the corrected
acceptance boundary.

#### Phase R1 — reusable Nat successor functor

1. Construct an iterable functor `Path(ℕ) ⊢ Path(ℕ)` with object action
   `succ`.
2. Route its first path action through the existing `nat_succ_obs_action` and
   `nat_succ_eq_ap` evidence; do not add an unrelated opaque higher action.
3. Use `nat_is_set` to close higher discreteness where appropriate.
4. Check identity/composition in both reduction orders and validate any
   proof-time comparison with typed `eq_refl`.

Exit criterion: Code's loop image is a reusable structured successor functor,
not the probe's interface-only primitive.

#### Phase R2 — opaque HIT owner and judgmental beta

1. Build an intended-owner-position copy of the walking module with only
   opaque `WalkingEnd`, `base`, and `loop` introductions.
2. Remove the word carrier and every WalkingEnd `Obj`/`Hom`/identity/
   composition rewrite.
3. Install point and loop beta at the two stable section owners.
4. Add the generic constant-section composition theorem before specializing
   it to the recursor.
5. Check the dependent section observer, constant-motive facade, direct loop
   computation, and the negative raw composite conversion boundary.

Exit criterion: constructor beta computes, arbitrary Hom remains opaque, and
composite theorems use the generic owner without a recursive word/action head.

#### Phase R3 — Code, encode, powers, and the easy inverse

1. Define `Code` by whole-HIT elimination into `Cat`.
2. Define `encodeₓ(p) ≔ Code[p](0)` and expose the based endomorphism map.
3. Define `power` by Nat recursion into opaque Hom.
4. Prove identity, loop, loop-prefix, and composition observations from beta
   plus generic functoriality.
5. Prove `encode(power(n)) = n` by Nat induction.
6. Only then decide whether `BNat` packaging adds useful iterability without
   becoming a second foundation.

Exit criterion: the passing probe's transparent Code/easy-roundtrip result is
reproduced at the real owner with no Hom representation or datatype induction.

#### Phase R4 — directed 1-cell elimination and the hard inverse

1. Record the architecture decision explicitly: accept
   `walking_end_ind_cell` as the primitive 1-cell component of this concrete
   categorical HIT, or first derive it from a reusable general
   displayed-category/free-category eliminator. Do not misdescribe
   `path_ind_sec` as supplying this principle.
2. Give `walking_end_ind_cell` exactly the opaque-Hom identity/generator-prefix
   interface probed above. It must not mention `walking_end_hom`, Nat, `BNat`,
   a word constructor, or a hidden decoder.
3. Keep identity beta as a runtime rule. Re-probe the runtime
   generator-prefix/literal-loop pair at the intended owner, resolve its one
   measured precomposition interaction if possible, and reject any proof-time
   alternative that does not pass a typed `eq_refl` exercise.
4. Instantiate the motive with
   `P(p) ≔ Path(power(encode(p)),p)`.
5. Prove the prefix case transparently from whole-HIT Code functoriality,
   judgmental loop beta, Nat successor beta, and congruence.
6. Apply `walking_end_ind_cell` to prove `power(encode(p)) = p` for arbitrary
   opaque `p`.
7. Inspect the theorem body and normalized projections to verify material use
   of Code's whole-HIT recursor and the 1-cell HIT eliminator.
8. Retain the rejected PathOut sentinel as historical negative evidence only;
   no bodyless motive, decoder, or round-trip declaration may survive.

Exit criterion: the hard inverse is transparent through the accepted 1-cell
HIT elimination principle; no Hom datatype, Hom rewrite, bodyless motive,
bodyless decoder, or round-trip axiom is present. If derivation rather than a
primitive 1-cell component is required, the reusable general eliminator is an
explicit prerequisite and R4 remains open until that derivation checks.

#### Phase R5 — comparison packages and directed consequences

1. Package `encode` and `power` as `EquivByInverse`, `TypeEquiv`, and native
   EQ1 only after both inverse proofs pass.
2. Rebuild any useful `BNat` functors from the same maps and prove their laws.
3. Derive Hom sethood/local discreteness through the corrected equivalence.
4. Rederive loop nonidentity, noninvertibility, nongroupoidality, and OneCat
   evidence without referring to word constructors.
5. Retain full functor-category initiality as an optional later theorem; it is
   not required for this practical computation milestone.

#### Phase R6 — migration, examples, and gates

1. Replace the active walking owner only after the intended-owner probe passes.
2. Rewrite permanent diagnostics and the reviewer example to remove every
   word-constructor assertion.
3. Synchronize Foundations, current status, report index, parent H2 row,
   catalog, and health report.
4. Run bounded quiet/warning probes, strict LHS audit, `make check`,
   `make examples`, catalog/TOC/reference checks, health, and `make ci`.

### Feasibility after the corrective probes

| Deliverable | Evidence | Feasibility status |
| --- | --- | --- |
| opaque HIT formation | passing focused probe; no object/Hom rules | demonstrated |
| judgmental point and loop beta | both stable-owner runtime assertions pass | demonstrated |
| generic composite theorem with raw beta | generic constant-section reflexivity theorem specializes successfully | demonstrated |
| whole-HIT Code and `encode(p) = Code[p](0)` | passing focused probe | demonstrated |
| Nat powers and easy inverse | transparent Nat-recursive/inductive proof passes | demonstrated |
| iterable Nat successor functor | object computation probed; existing first-path action available | high feasibility; full higher-action packaging remains |
| `PathOut` equality-motive route | enriched-slice action requires equality from an arbitrary directed 2-cell | rejected as circular without prior local discreteness |
| opaque 1-cell elimination interface | runtime identity/prefix betas and the hard theorem pass with no Hom representation; one precomposition warning remains | operationally demonstrated, with ownership and one rewrite-coherence gate open |
| hard inverse | transparent `cell_ind` proof over actual Code and power passes | demonstrated for the primitive-interface branch |
| Hom–Nat equivalence | both inverse terms pass in the focused opaque probe | high feasibility after owner migration; not active or accepted yet |
| full initiality | not needed | explicitly outside this correction |

The honest status is therefore neither “completed” nor “blocked.” The wrong
representation has been identified; the corrected formation, beta,
Code/encode, powers, and both inverse proof terms are executable in the
focused opaque probe. The remaining design choice is foundational ownership:
whether the based 1-cell eliminator is accepted as a primitive computation
component of this concrete categorical HIT or must first be obtained from a
more general displayed-category/free-category eliminator. The former is a
small, measured implementation; the latter is broader reusable
infrastructure. Neither choice licenses the old word carrier or the rejected
bodyless PathOut motive.

### Corrected acceptance criteria

The reopened plan is complete only when all of the following hold:

1. `WalkingEnd`, `base`, and `loop` are opaque constructors and no rule exposes
   the HIT's object or Hom classifier.
2. Both point and loop constructor betas compute by rewrite; the loop theorem
   is reflexivity after computation.
3. No word/Nat datatype is definitionally identified with Hom, and no
   datatype induction supplies the hard inverse.
4. Code and encode are obtained from whole-HIT elimination.
5. The primitive-versus-derived ownership of the opaque 1-cell eliminator is
   explicitly selected and justified; its identity and generator-prefix betas
   are computational rewrite/unification facts.
6. `encode(power(n)) = n` is a transparent Nat-induction proof.
7. `power(encode(p)) = p` is a transparent application of that accepted
   1-cell HIT eliminator, with a prefix case built from Code beta,
   functoriality, Nat beta, and congruence.
8. No bodyless decoder, PathOut motive, inverse theorem, or hidden Hom
   classifier occurs in either proof.
9. Hom–Nat packages and all negative/dimension consequences are downstream of
   those two proofs.
10. Permanent negative controls show no direct Hom-to-Nat conversion and no
   accidental loop identity/inverse.
11. All proportional warning, audit, example, catalog, health, and CI gates
    pass.

## Superseded Implementation Checkpoint (Historical Evidence Only)

Everything from this heading onward records the former word-carrier/
propositional-loop-beta decision and its validation history. It remains useful
for locating rejected probes and retained Nat/BNat work, but every statement
that calls that architecture the completed or selected HIT is superseded by
the reopened corrective decision above.

The earlier composition-owner blocker remains resolved without adding a family
of constructor-specific runtime bridges. A later independent peer review found
one material completeness defect in the first packaging: the exported Hom-Nat
equivalence used parallel carrier functions even though the encoder itself was
HIT-recursive. The corrected active `emdash3_2_walking_end_hit.lp` now
implements:

- the native inductive `walking_end_hom` carrier exposed as
  `WalkingEndHom_grpd`, explicitly owned as the intrinsic hom component of the
  walking HIT rather than as a second model;
- `walking_end_hom_ind`, the hom-level HIT eliminator with judgmental identity
  and step beta laws;
- `WalkingEnd_cat`, with one object, intrinsic generated-arrow hom, identity,
  and constructor-directed composition;
- a primitive directed-HIT eliminator
  `walking_end_ind_sec(D,u,ell) : Obj(Pi_cat D)`;
- judgmental point beta and a primitive **propositional** generator beta;
- the nondependent recursor as the constant-`Catd` specialization of that
  eliminator;
- `walking_end_rec_step_view`, a target-generic theorem computing recursor
  action on every generated step from strict functoriality and the HIT loop
  beta;
- a derived loop-square equality using the loop beta twice and the global
  Kosta-Došen strict cut, with no second composite-action runtime owner;
- the separate one-object Nat model `BNat_cat`;
- a transparent open theorem `bnat_comp_nat_add`, while runtime composition
  retains its semantic head on an open left operand;
- a recursor-derived structured encoder and a structured decoder whose
  zero/successor laws derive from their generator betas and generic strict
  functoriality;
- `walking_decode_encode_roundtrip`, proved for the actual semantic actions by
  `walking_end_hom_ind`, with every step consuming the HIT-derived encoder
  successor law and the decoder successor law;
- `walking_encode_decode_roundtrip`, proved for the actual semantic actions by
  Nat induction;
- `TypeEquiv` and native `OmegaEquiv_EQ1` packages for
  `Hom(WalkingEnd,base,base) ~= Nat`, whose forward projection is
  `walking_encode_action` rather than a helper length function;
- internal local-discreteness/`OneCat` evidence; and
- derived loop nonidentity and noninvertibility, with downstream diagnostics
  showing that alleged internal groupoidality yields `Empty_grpd`.

The crucial revised decision is:

```text
point beta       runtime/judgmental
generator beta   equality evidence
composite action global strict functoriality only
arbitrary arrow  intrinsic walking_end_hom_ind
hom equivalence  actual encoder/decoder actions
```

This is the requested practical computation/freeness result. It does not
require or claim an initiality theorem for the entire functor category.
Generic `path_ind_sec` is also not part of this proof: it consumes an already
functorial `Catd` motive on `PathOut` and cannot by itself manufacture the raw
arrow-indexed round-trip motive or its higher action. A future generic
PathOut/transfor presentation remains possible after such a motive constructor
exists; it is not a prerequisite for the concrete theorem.

This is the directed analogue of the ordinary intensional Circle boundary.
The [HoTT/Coq Circle implementation](https://github.com/HoTT/HoTT/blob/master/theories/Spaces/Circle.v)
exposes its loop computation as an equality theorem
(`Circle_ind_beta_loop`), while the
[Cubical Agda Circle presentation](https://github.com/agda/cubical/blob/master/Cubical/HITs/S1/Base.agda)
can make the loop clause compute because its path-composition environment does
not also install Emdash's oppositely oriented strict-functor cut as a
competing rewrite. Those systems are inspiration and comparison evidence
only; neither is an implementation template for this Lambdapi calculus.

The decisive owner-position probe is
`tmp/probes/wehit_circle_style_owner.lp`.  Its quiet run passes in
`logs/probes/wehit_circle_style_owner-20260718-010514.log`; its warning run is
`logs/probes/wehit_circle_style_owner-20260718-010608.log`; and the promoted
owner check is `logs/probes/emdash3_2_walking_end_hit-20260718-014905.log`.
The latter has `977` unjoinable critical pairs and `157` replaceable pattern
variables: exactly six more critical pairs than the kernel baseline, three
from the constructor-directed `WalkingEnd` composition and the same three
from `BNat`.  There is no eliminator/action critical-pair family.  Strict LHS
audit of the promoted module has zero unreviewed clauses.

For the later HIT-elimination correction, the standalone semantic proof is
`tmp/probes/wehit_semantic_roundtrip.lp` (quiet log
`logs/probes/wehit_semantic_roundtrip-20260718-121324.log`). The intended-owner
copy is `tmp/probes/wehit_intrinsic_hom_owner.lp` (quiet/warning logs
`logs/probes/wehit_intrinsic_hom_owner-20260718-121613.log` and
`logs/probes/wehit_intrinsic_hom_owner-20260718-121624.log`). It passes with
the same `977/157` warning inventory and zero unreviewed LHS clauses. The
promoted owner then passes in
`logs/probes/emdash3_2_walking_end_hit-20260718-122532.log`. The correction
adds no rewrite or unification rule.

The target-generic recursor-step theorem was isolated in
`tmp/probes/wehit_generic_rec_step.lp`; its final focused log is
`logs/probes/wehit_generic_rec_step-20260718-123719.log`. The final promoted
owner quiet/warning logs are
`logs/probes/emdash3_2_walking_end_hit-20260718-123823.log` and
`logs/probes/emdash3_2_walking_end_hit-20260718-123953.log`; the latter remains
exactly `977/157`.

Despite its chronological proximity to older `wehit_mvp_owner` experiments,
`wehit_circle_style_owner.lp` is the **post-Coq/Agda theorem-first** probe: its
`cs_*` prefix means "Circle style." The older raw-beta/recursive-action
candidates are `wehit_mvp_owner.lp`, `wehit_word_stable_action.lp`, and
`wehit_word_stable_precomp_action.lp`. The Circle-style file is ignored
owner-position evidence, not a second implementation authority; active names
and current behavior are owned only by `emdash3_2_walking_end_hit.lp`.

The six warnings were also tested as typed consumers rather than accepted by
count alone. Identity/pre/postcomposition boundary cases compare directly.
The successor/precomposition case is the associativity square
`k o (g o F[h]) = (k o g) o F[h]`; it is not a desired runtime join. The new
generic theorem `hom_precomp_along_postcomp_assoc` stages the existing stable-
head comparison around `comp_assoc`, avoiding reliance on unification-rule
transitivity. All six WalkingEnd/BNat consumers pass in
`logs/probes/walking_comp_hom_action_consumers-20260718-013636.log`. No
category-specific action theorem or rewrite was needed.

Selected-MVP consolidation on 2026-07-18 passes the complete reviewer-example suite,
strict LHS audits for both the base kernel and the WalkingEnd owner, catalog,
TOC/reference/header/diff checks, refreshed health, and `make ci`. The catalog
contains 1,977 classified diagnostics (1,739 positive and 238 negative) with
zero unclassified entries. Health passes 54 tracked modules/examples; the
WalkingEnd reviewer example contains 20 executable statements. The final CI
metrics phase passes all 54 targets in 140.465 seconds. The warning inventory
remains `971/157` for the base kernel and the measured `977/157` for the
WalkingEnd owner; the six additional pairs are exactly the typed-consumer-
checked constructor-composition pairs described above.

The active diagnostics deliberately contain both sides of the boundary:

- a typed inhabitant of the generator beta;
- a typed derived loop-square equality;
- a negative conversion check showing that raw generator action does not
  reduce to the supplied arrow; and
- both hom-induction constructor beta checks;
- arbitrary transparent semantic-action round-trip proofs, together with
  negative conversion checks showing that open round trips are propositional
  rather than proof-erased runtime equations; and
- a check that the `TypeEquiv` forward projection is the recursor-derived
  `walking_encode_action`.

The 2026-07-18 post-completion consolidation is also closed. The reusable Nat
slice is a 116-line/6-symbol/1-rule module; the walking owner is now
803 lines/48 symbols/13 rules/2 unifiers and contains no inline assertions.
The permanent suite has 1,978 classified diagnostics across 72 areas (1,739
positive and 239 negative), including both open round-trip conversion
controls. All 55 modules/examples pass. Warning inventories remain `971/157`
for the kernel and Nat module and `977/157` for the walking owner; strict LHS
audits have zero unreviewed clauses. The refreshed health report is current,
and synchronized local CI passes with 128.448 seconds of measured checking
time.

The subsequent HIT-elimination correction is now also closed. The walking
owner is 818 lines/44 symbols/13 rules/2 unifiers; the removal of parallel
helper functions more than offsets the generic recursor-step and semantic
round-trip theorems. The permanent suite has 1,980 classified diagnostics
across 72 areas (1,741 positive and 239 negative), the focused reviewer example
has 22 statements, and all 55 targets pass. Warning inventories remain kernel
`971/157` and walking `977/157`; both strict audits have zero unreviewed
clauses. Checked health passes in 121.390 seconds and synchronized local CI
passes in 171.313 seconds.

Both one-object sources expose the same reusable proof-time identity pattern:
`walking_functor_id_view` and `bnat_functor_zero_view` compare action on the
respective normalized source identity with target identity. The concrete
encoder and decoder identity/zero proofs route through those generic source
views; no encoder-specific or decoder-specific unification rule remains.

### Why the formerly blocked runtime requirement was rejected

The former plan required both point and generator beta as raw runtime
projection rewrites.  Combined with the existing strict rule

```text
F[g] o F[f]  ->  F[g o f],
```

this gave the loop square two normal-form paths: generator beta first exposed
`f o f`, while strictness first exposed the section action on
`loop o loop`.  Requiring those raw terms to join was stronger than the
ordinary intensional Circle interface and created a second authority for
composite action.

An explicit generated-hom "spiral" plus the narrow proof-time comparison
`D[zero](u) == u` repaired closed base/loop/loop-square examples; see
`logs/probes/wehit_mvp_owner-20260718-003850.log`.  It still could not make the
open provenance equation `F[g] o f == F[g o loop]` judgmental after generator
beta erased the fact that `f` came from `F[loop]`.  This was useful evidence:
the missing endpoint variable was not the fundamental issue once arbitrary
directed arrows had their own generated-hom induction.

A stable precomposition/action head also made selected equations pass, but it
overlapped every target-specialized generic action owner and added 88
critical pairs; the warning evidence is
`logs/probes/wehit_word_stable_precomp_action-20260718-004346.log`.  It was
rejected rather than promoted.  The earlier recursive-action candidate and
direct composition-to-addition candidate remain useful historical evidence
below, but neither is part of the selected architecture.

### Trust and completeness boundary

`walking_end_ind_sec` and its generator beta are the primitive structured HIT
interface, in the same sense that a higher-inductive eliminator and its beta
law belong to a foundational presentation. `walking_end_hom_ind` is the
transparent eliminator generated by the HIT's native inductive hom carrier.
They are not standalone round-trip or Hom-classification axioms. The section
eliminator returns a structured section for every `Catd` motive, the ordinary
recursor is definitionally routed through it, and the encoder materially uses
that recursor. Hom induction provides the directed freeness principle needed
for arbitrary composite arrows; unlike groupoidal J, directed arrow induction
cannot reduce every arrow to identity.

The decoder is a primitive structured functor head because Emdash functors
are semantic objects rather than record literals.  Its only special law is
propositional generator beta. Its zero and successor action theorems are
derived, not assumed. The complete decoder-after-encoder law is proved by HIT
hom induction, and the reverse is proved by Nat induction. The hom equivalence
is packaged from those actual semantic actions only after both transparent
inverse proofs.

This operational MVP does **not** prove an external model, global confluence,
normalization, canonicity, a general directed-HIT schema, or categorical
initiality at all higher transfors.  It does prove the requested internal
dependent-elimination interface, the concrete Hom-to-Nat correspondence, and
the selected computational observations without declaring Hom to be Nat.

## Historical Blocked Checkpoint (Superseded Decision Evidence)

At the earlier 2026-07-17 checkpoint, only one independent prerequisite slice
was promoted in `emdash3_2_walking_end_hit.lp` (and was later relocated
verbatim to `emdash3_2_nat_arithmetic.lp` during post-completion
consolidation):

- `nat_add` with zero, successor, and open right-unit computation;
- transparent `nat_add_assoc` by native Nat induction;
- internal `unit_is_contr`, `unit_is_prop`, and `empty_is_prop` terms;
- `nat_is_set : IsSetGrpd Nat_grpd` by nested Nat induction over the active
  observational equality classifiers.

The retained slice has permanent diagnostics and the reviewer example
`examples/walking_endomorphism_nat_prerequisites.lp`. Its full owner-position
warning probe retains the baseline `971` unjoinable critical pairs and `157`
replaceable pattern variables, and the strict LHS audit retains zero
unreviewed clauses. The decisive log is
`logs/probes/wehit_nat_owner_full-20260717-214902.log`.

The synchronized blocked checkpoint passes `make check`, all reviewer
examples, catalog/TOC/reference/header checks, health generation, and full
local CI. The generated catalog contains 1,931 classified diagnostics (1,697
positive and 234 negative), health covers 53 files/examples, and the final CI
typecheck phase reports 368.847 seconds total. These gates validate the
retained slice and the consistency of the documentation; they do not convert
the downstream hard blocker into an implemented HIT.

At that superseded checkpoint, the selected directed-HIT MVP was **not**
complete. Two early computational gates appeared to expose the same missing
composition-owner architecture.

### Blocker A: constructor beta versus generic strict functoriality

The exact dependent eliminator shape typechecks. Because `piapp0` and
`piapp1_fapp0` are transparent definitions, the stable constructor owners are
terminal component evaluation and `fdapp1_int_cell`, respectively. Both
individual runtime betas pass and are warning-neutral in the full owner copy;
see `logs/probes/wehit_ind_shape_owner_full-20260717-211309.log` and the
warning run
`logs/probes/wehit_ind_shape_owner_full-20260717-211320.log`.

That local success is insufficient. In a constant motive, the expression

```text
comp(section[loop], section[loop])
```

has two operational paths. Constructor beta first leaves `comp(f,f)`, while
the generic strict-functor cut first leaves `section[loop o loop]`. The latter
has no arrow-induction computation, so the two terms have no common runtime
normal form. The smallest failing assertion is retained in
`logs/probes/wehit_dependent_composition_boundary-20260717-213738.log`; the
two distinct normal forms are printed in
`logs/probes/wehit_dependent_composition_compute-20260717-213839.log`.

The same failure appears through the ordinary constant-motive recursor. A
narrow base/loop observer adapter computes at each constructor, but its
generator-square composition assertion fails. A stable recursive action head
made that one assertion pass in
`logs/probes/wehit_ind_shape_owner_full-20260717-212712.log`, but its general
composition rule overlaps the existing semantic composition owners and raises
the warning inventory from `971/157` to `999/158`; see
`logs/probes/wehit_ind_shape_owner_full-20260717-212723.log`. Adding the
resulting family of constructor-specific bridges would be exactly the ad hoc
design this plan is intended to avoid. A narrowly typed proof-time composition
equation also failed to discharge the closed generator square after
constructor reduction; the final attempt is
`logs/probes/wehit_rec_unif_owner_full-20260717-214215.log`.

This is a normalization/representation blocker, not a mathematical
inconsistency and not a failure to type the eliminator. It invalidates the
earlier computational assumption that the returned section's ambient
functoriality alone supplies generated-composite computation once a generator
beta is installed.

### Blocker B: a transparent `BNat_cat` composition owner

The proposed object, hom, identity, and direct composition-to-addition rules
all typecheck and the Nat/unit/associativity assertions pass in
`logs/probes/wehit_nat_bnat_owner_full-20260717-214725.log`. With warnings
enabled, however, the general rule

```text
comp_fapp0(BNat_cat,g,f) -> nat_add(f,g)
```

creates 18 new unjoinable critical pairs, raising `971/157` to `989/157`; see
`logs/probes/wehit_nat_bnat_owner_full-20260717-214757.log`. The first is the
generic strict-functor cut into `BNat_cat`; the remainder include existing
postcomposition, precomposition, transfor, displayed, and definitional-
isomorphism composition owners. Reducing the target composition to addition
erases the generic semantic head before those paths can join. A stable
`bnat_comp` followed by an unconditional fold to addition has the same final
problem; leaving it opaque would not meet the computational model criterion.

### Required prerequisite and retained alternatives

The smallest credible prerequisite is a reusable free-arrow/composition
interface that does all of the following:

1. gives generated arrows an inductive or otherwise canonical presentation;
2. defines dependent and nondependent action on that presentation;
3. rejoins generator beta with identity, composition, and the existing
   higher hom-action owners at one semantic owner;
4. supplies an eta/arrow-induction principle for arbitrary generated arrows;
5. does not identify the HIT hom with Nat before the comparison proof.

At that checkpoint an explicit internal generated-hom syntax distinct from
`Nat_grpd` was only a candidate. It was subsequently selected after the owner
probes, but the later review corrected its ownership: `walking_end_hom` is the
carrier of the HIT's own Hom classifier and `walking_end_hom_ind` is its
hom-level eliminator, not an additional model beside `WalkingEnd_cat`.
`BNat_cat` alone is the external normal-form model. The broader kernel-level
composition-registration alternative remains rejected.

That checkpoint's conclusion is retained as rejected-decision evidence.  The
selected theorem-first architecture above implements `WalkingEnd_cat`,
`BNat_cat`, encode/decode, and both round trips without the proposed generic
composition-registration layer.  No Hom-to-Nat rewrite, bodyless round trip,
or 18-rule patch family has been installed.

## Executive Decision

The first representative categorical higher-inductive experiment should be
the **walking endomorphism**, also called the free one-object category on one
directed generator. Write it provisionally as:

```text
WalkingEnd_cat : Cat
walking_base   : Obj(WalkingEnd_cat)
walking_loop   : Hom(WalkingEnd_cat, walking_base, walking_base).
```

The generator is directed and is not assumed invertible. Its freely generated
endomorphisms are the powers

```text
id, walking_loop, walking_loop^2, ...,
```

and their expected normal-form monoid is `(Nat,+,zero)`.

The endpoint of this plan is **not** obtained by declaring

```text
Hom_cat(WalkingEnd_cat,walking_base,walking_base)
  -> Path_cat(Nat_grpd).
```

That rewrite would be a useful implementation of a known model, but it would
make the desired correspondence true by declaration. The required endpoint
is instead:

1. an actual primitive or otherwise justified directed-HIT presentation with
   object and arrow constructors;
2. a dependent eliminator into structured `Catd` motives;
3. judgmental point computation, propositional generator computation, and
   derived composite-action laws through the one generic strict owner;
4. a separate transparent Nat normal-form model `BNat_cat`;
5. encode/decode operations derived from the eliminator, Nat recursion, and
   the ordinary functor/section calculus;
6. derived round trips showing that the endomorphism classifier of the HIT is
   equivalent to `Nat_grpd`;
7. computational observations sending identity to zero, the generating loop
   to one, and composition to addition.

This makes the example a real test of elimination and practical
arbitrary-arrow computation rather than an abbreviation for a preselected
hom-category. Full functor-category initiality is a separate optional theorem.

## Why This Is The Right First Representative HIT

The walking endomorphism is the directed analogue of the free monoid on one
generator. It is simpler than the groupoidal Circle because it needs:

- no inverse-loop constructor;
- no word cancellation or group completion;
- no integer normal form;
- no proof that positive and negative powers cancel;
- no prior identification of all directed arrows with paths or equivalences.

Finite words in one generator have canonical length, hence the expected
normal form is Nat. A later groupoid completion should send

```text
BNat -> BInt
```

and provides a natural bridge toward the free groupoid on one loop and the
usual Circle loop-space comparison. That later construction is explicitly
outside this plan.

The example also complements the active primitive `Join_cat(A,B)`. The join
contains a directed cross cell from a left region to a right region and has a
nondependent recursor. The walking endomorphism instead tests cyclic
iteration and dependent elimination. `Join_cat(Unit,Unit)` is a walking arrow
with two distinguished endpoints, not the walking endomorphism; identifying
those endpoints would require a directed coequalizer/quotient or attachment
construction not presently active.

## Current Foundations Relevant To The Plan

The active implementation already supplies most of the ambient language:

- `Nat_grpd`, native `zero`/`succ`, `nat_elim`, recursive observational
  equality, and a retained registered successor action;
- `Cat`, `Obj`, `Hom_cat`, `id`, and generic `comp_fapp0`;
- ordinary functors with iterable `fapp0`, `fapp1_func`, and
  `fapp1_fapp0` action;
- Cat-valued directed families `D : Catd K`, fibre categories, base-arrow
  transport, section categories `Pi_cat D`, section evaluation, and section
  action `piapp1_fapp0`;
- Sigma total categories and dependent homs;
- `Path_cat`, `Core_incl_func`, equality-valued omega-equivalence, and
  internal groupoidality;
- `PathOut` and its structured path-induction section;
- the primitive directed Join and its nondependent recursor.

The active kernel still does **not** provide the following generic facilities.
The one-way walking-plan extension now supplies the concrete walking
endomorphism, Nat model, Nat arithmetic/sethood, and the specialized
comparison without moving them into the kernel:

- a general functor constructor
  `Path_cat(A) -> Path_cat(B)` from a raw function and its higher action;
- a dependent eliminator or semantic initiality theorem for `Join_cat`;
- a generic directed-HIT schema;
- a general free-category or directed-HIT universal-property schema.

These absences are prerequisites or investigation gates, not permission to
replace the desired construction by unrelated axioms.

## Mathematical Specification

### 1. The HIT presentation

The intended object is the free strict directed category generated by:

```text
base : Obj(WalkingEnd_cat)
loop : Hom(WalkingEnd_cat,base,base),
```

with no equation identifying `loop` with `id`, no inverse generator, and no
nonidentity higher generator. Identities, composites, and their strict
functorial higher structure come from the ambient Emdash category kernel.

The phrase "no nonidentity higher generator" does not by itself prove local
discreteness. The implementation must eventually derive or transport the
appropriate `IsDiscreteCat`/`IsNCat(cat_one,...)` evidence from the Nat
normal-form result rather than assume that all higher cells disappear.

### 2. The dependent eliminator

The native Emdash formulation should use a structured motive, not a raw
meta-level family. For

```text
D : Catd(WalkingEnd_cat)
```

the constructor data are:

```text
u : Obj(Fibre_cat(D,base))

ell_D : Hom_(Fibre_cat(D,base))(
          D[loop](u),
          u).
```

Here `D[loop]` is the existing `catd_transport_func` action. The eliminator
should return a section:

```text
walking_end_ind_sec(D,u,ell_D)
  : Obj(Pi_cat(D)).
```

In current kernel notation, the loop datum can use the exact source endpoint
already exposed by `piapp1_src_obj` or the equivalent application of
`catd_transport_func`. Do not introduce a second displayed-arrow
classification merely for this HIT.

The selected constructor computations are:

```text
walking_end_ind_sec(D,u,ell_D)[base]
  -> u

walking_end_ind_sec(D,u,ell_D)[loop]
  = ell_D.
```

The first observation is judgmental through the stable terminal-component
projection. The second is an inhabitant of the displayed generator equality
classifier comparing `piapp1_fapp0(ind,loop)` with `ell_D`. This revised
acceptance decision is deliberate and permanent for the selected intensional
MVP: raw generator action must remain stuck so that generic strict
functoriality is the sole runtime composite-action owner.

Mathematically there is no extra relation on the generator, so no independent
algebra law is requested from the user. Computationally,
`walking_end_hom_ind` is the intrinsic hom component of this HIT interface and
supplies induction over arbitrary generated directed arrows. Composite action
is then proved from generator beta plus strict functoriality; it is not
installed as another normalization family.

### 3. Derived nondependent recursor

For a target category `C`, object `x : Obj(C)`, and endomorphism
`f : Hom(C,x,x)`, specialize the dependent eliminator to the constant motive:

```text
Const_catd(WalkingEnd_cat,C).
```

The existing proof-time comparison

```text
Pi_cat(Const_catd(K,C)) == Functor_cat(K,C)
```

should make the resulting section readable as:

```text
walking_end_rec_func(C,x,f)
  : Functor(WalkingEnd_cat,C).
```

Type acceptance through the `Pi_cat(Const_catd)`/`Functor_cat` comparison
does not by itself guarantee that an ordinary `fapp0` or `fapp1_fapp0`
projection computes on the section term. Probe the two ordinary-functor
observers separately. If an explicit named adapter/wrapper is needed, its
body must route through `walking_end_ind_sec`, and its projection bridges must
join with the `piapp0`/`piapp1_fapp0` route. Do not infer observer computation
merely from successful proof-time type comparison.

Required computations are:

```text
walking_end_rec_func(C,x,f)[base] -> x
walking_end_rec_func(C,x,f)[loop] = f.
```

The readable recursor routes definitionally through the dependent eliminator;
it is not an independent primitive with duplicate semantic authority.  The
loop equation is `walking_end_rec_beta_loop` and raw action remains stuck.

### 4. Initiality and uniqueness

At object level, functors out of the HIT should be determined by an object and
an endomorphism. The full categorical universal property is more accurately
an equivalence between `Functor_cat(WalkingEnd_cat,C)` and a category of
endomorphism objects whose arrows are intertwiners, not merely the informal
classifier `Sigma x, Hom_C(x,x)`.

The initial operational milestone does not construct that entire category
equivalence.  The selected concrete free presentation instead exposes
`walking_end_hom_ind`, the induction principle for every generated directed
arrow. It proves `decode_action(encode_action(w)) = w` transparently for the
actual functor actions. Full uniqueness of functors at all transfor levels
remains a separate and currently unnecessary strengthening.

This is not a standalone round-trip capability: the proof body is intrinsic
hom induction; its successor case consumes the encoder theorem derived from
the structured HIT loop beta and the structured decoder theorem derived from
its generator beta. The encoder itself is produced by the dependent
eliminator's constant-motive specialization. A future abstract HIT interface
lacking an explicit generated-hom presentation would still need a
corresponding arrow-eta or extensionality principle.

Three more abstract proof presentations remain candidates for that future
strengthening:

1. a displayed logical-relation motive over `WalkingEnd_cat`, discharged by
   `walking_end_ind_sec`;
2. a transfor between the endofunctors
   `walking_decode_func o walking_encode_func` and `id_func`, generated from
   their agreement on the base and loop;
3. a structured motive over `PathOut_cat(WalkingEnd_cat,base)` whose objects
   are arbitrary outgoing arrows and whose target property is the desired
   arrow round trip.

These are potential generic presentations of the same practical result, but
none is currently available for free: in particular `path_ind_sec` requires
the `PathOut` motive and its action to have already been constructed. They are
not required for this explicit one-generator intrinsic-hom MVP.

## The Separate Nat Normal-Form Model

### 1. `BNat_cat`

Construct a separate transparent one-object category, provisionally:

```text
BNat_cat : Cat
bnat_obj : Obj(BNat_cat).
```

Its intended computation is:

```text
Obj(BNat_cat)                  -> Unit_grpd
bnat_obj                       -> tt
Hom_cat(BNat_cat,_,_)          -> Path_cat(Nat_grpd)
id_(BNat_cat)                  -> zero
comp_(BNat_cat)(n,m)           -> nat_add(n,m)
bnat_generator                 -> succ(zero).
```

The exact addition order must follow the convention that
`comp_fapp0(g,f)` means `g o f`. Choose and document one recursion orientation
before promotion. Since powers of one generator commute mathematically, this
example alone can conceal a variance error; diagnostics must inspect open
normal forms and not appeal only to commutativity of addition.

This category is the explicit semantic/computational model. It is legitimate
for its hom classifier to reduce to Nat because it is not the HIT whose
freeness is being tested.

The object/identity/composition rules initially make the model transparent at
objects and 1-arrows. Its higher composition action is still the generic
`comp_prod_func`/`comp_prod_fapp1*` action of the ambient kernel. Before the
comparison is called fully computational, Phase 4 must either relate that
action to the selected path action of `nat_add` or explain why Nat
discreteness makes the generic owner sufficient. Do not describe an opaque
BNat-specific higher action as if addition functoriality had been derived.

### 2. Nat arithmetic and truncation

Add or derive, in a suitable library owner:

```text
nat_add zero n       -> n
nat_add (succ m) n   -> succ(nat_add m n)
```

or the deliberately selected opposite recursion orientation. Prove or expose
the unit and associativity facts required by the selected category
presentation without adding a second global category-law calculus.

Separately prove:

```text
nat_is_set : IsSetGrpd(Nat_grpd)
```

from Nat induction, constructor equality, and the active Empty/Unit
truncation facts. Constructor-level equality computation is strong evidence
but is not itself an inhabitant of `IsSetGrpd Nat_grpd`.

The sethood theorem supports the precise statement that
`Path_cat(Nat_grpd)` is discrete and that `BNat_cat` is locally discrete. Do
not call the hom a set internally before this evidence exists.

## Encode, Decode, And The Required Nat Correspondence

### 1. Encoding generated arrows

Use the derived recursor with target `BNat_cat`, sending:

```text
base |-> bnat_obj
loop |-> succ(zero),
```

to obtain:

```text
walking_encode_func : Functor(WalkingEnd_cat,BNat_cat).
```

Its endomorphism action is:

```text
walking_encode(p)
  := walking_encode_func[p]
  : Nat.
```

The selected observations are:

```text
walking_encode(id)          =  zero
walking_encode(loop)        =  succ(zero)
walking_encode(g o f)       =  nat_add(walking_encode(g),walking_encode(f))
```

`walking_functor_id_view`, `walking_end_rec_beta_loop`, and
`walking_encode_comp_view` derive these equations from generic strict
functoriality plus the selected `BNat_cat` normal form. There is no duplicated
encode-specific preservation rewrite.

### 2. Decoding Nat normal forms

The reverse direction is the semantic functor
`walking_decode_func : Functor(BNat_cat,WalkingEnd_cat)`, and its named capped
action is `walking_decode_action`. Its derived observations are:

```text
walking_decode_action(zero)   = id
walking_decode_action(succ n) = loop o walking_decode_action(n)
```

The zero theorem uses the reusable functor-on-source-identity view; the
successor theorem uses the decoder generator beta and generic strict
functoriality. No parallel Nat-recursive raw function is retained. A capped raw
function would be insufficient because the decoder must remain iterable at
higher homs.

### 3. Round trips

The easy round trip should be derived by Nat induction:

```text
walking_encode_action(walking_decode_action(n)) = n.
```

The decisive HIT round trip is:

```text
walking_decode_action(walking_encode_action(p)) = p
```

for arbitrary

```text
p : Hom(WalkingEnd_cat,base,base).
```

This proof materially uses `walking_end_hom_ind`, the intrinsic hom component
of the HIT elimination interface. Its step explicitly uses both semantic
successor theorems, including the encoder theorem derived from
`walking_end_ind_beta_loop`. Together with the recursor-derived encoder, this
satisfies the concrete practical freeness gate. A direct global axiom, an
opaque round-trip theorem with no body, a helper-syntax equivalence, or a
hom-to-Nat rewrite inserted before the proof would not satisfy the plan.

After both round trips, package the actual `walking_encode_action` and
`walking_decode_action` through `EquivByInverse` and `TypeEquiv`, then derive
the native `OmegaEquiv_EQ1` comparison. Do not introduce another decoder or a
parallel carrier-level forward map.

### 4. Stronger comparison

A category-level equivalence between `WalkingEnd_cat` and `BNat_cat` is a
desirable strengthening after the hom equivalence is active. It is not a
substitute for the explicit hom encode/decode computations, and it should be
derived from the same functors rather than asserted independently.

## `PathMap`, `ObsAction`, And Higher Functoriality

### Current distinction

`ObsAction(f)` starts from a raw function `f : τ A -> τ B` and stores one
selected action on paths plus a pointwise comparison with `eq_ap(f)`.
Structured groupoidal J starts from an already functorial `Catd` motive. One
does not replace the other.

A reusable constructor of the schematic form

```text
path_map_func(f) : Functor(Path_cat(A),Path_cat(B))
```

would be useful for the transparent `walking_decode_func`, for other
path-category-valued models, and eventually for presenting raw-function
action through ordinary functor machinery. It is not currently active.

### Why it is not a trivial wrapper

An iterable functor needs a full hom-action functor at every dimension. A
single `ObsAction(f)` supplies only the selected first path operation and its
agreement with semantic `eq_ap`; it does not automatically supply an
`ObsAction` tower for the action map itself.

A naive rule

```text
path_map_func(f)[p] -> eq_ap(f,p)
```

must also join with generic strict functor identity and composition. In
particular, the two reductions of

```text
path_map_func(f)[q] o path_map_func(f)[p]
```

must agree when generic functoriality folds first and when both actions expose
their selected path terms first. Since `Path_cat` deliberately retains
generic `comp_fapp0` rather than reducing all path composition to `eq_trans`,
this is a real owner/normal-form question.

### Selected specialized boundary

The implementation assessed the intended fork:

1. a general raw-function-to-`Path_cat` functor remained disproportionate and
   retained the known recursive higher-action/composition questions;
2. broad stable action/precomposition heads were rejected after the measured
   88-critical-pair increase;
3. the MVP selected a semantic structured functor
   `walking_decode_func : Functor(BNat_cat,WalkingEnd_cat)` with object beta,
   propositional generator beta, and a Nat-inductive theorem identifying its
   complete capped action with `walking_decode_action`.

Selection criteria are:

- full `fapp1_func` iterability, not merely capped action;
- identity and composition joining at the first two hom levels;
- no opaque higher-action capability;
- no assumption that proof-time comparison is transitively propagated;
- no forced replacement of the real Nat/PathRecord `ObsAction` consumers;
- a public API reusable by later standard-library constructions.

The selected term remains iterable because its public type is an ordinary
Emdash functor; generic `fapp1_func` supplies its higher semantic action. The
plan does not claim that a raw function automatically generates that functor,
or that `ObsAction` is subsumed. A reusable `path_map_func` remains deferred
standard-library/kernel research, not an MVP prerequisite.

### Relationship to Join

`PathMap` is not a prerequisite for the existing Join recursor: Join already
consumes ordinary functors and an internally natural cross cell. It may help
future path-category-valued Join models or motives, but it does not supply the
missing dependent Join eliminator.

The genuinely reusable contribution to Join is the dependent-HIT pattern:

```text
structured Catd motive
  + displayed constructor data
  -> Pi_cat section
  + constructor computation.
```

After the walking endomorphism succeeds, a separate Join follow-up can ask
for sections over the two inclusions plus a displayed lift of the internally
natural cross cell. Do not expand this plan into that larger task.

## Composition Ownership And The Hom Actions

`comp_fapp0` is the semantic operation for ordinary categorical composition.
The walking endomorphism and `BNat_cat` must expose their selected
category-specific computation through that owner.

The families

```text
hom_postcomp_*
hom_precomp_along_*
hom_int
hom_con
```

are iterable functorial presentations of postcomposition, precomposition,
and represented hom variation. They are not alternative definitions of the
underlying category composition. Consequently:

1. first establish the selected `comp_fapp0(BNat_cat,...)`/Nat computation;
2. let generic `hom_postcomp*` and `hom_precomp*` expose the resulting action;
3. test their visible projections as consumers;
4. add no `BNat_cat`- or walking-specific hom-action rule whose only content
   is ordinary composition/functoriality;
5. add a specialized bridge only if a stable projection erases the generic
   owner and both reduction orders have been measured.

### Selected constructor-directed composition

The direct open rule `comp(BNat,g,f) -> nat_add(g,f)` was rejected because it
erased the semantic composition head too early. The selected presentation
recurses only when a constructor is visible:

```text
comp(BNat,zero,f)    -> f
comp(BNat,g,zero)    -> g
comp(BNat,succ(g),f) -> succ(comp(BNat,g,f)).
```

`WalkingEnd` uses the same constructor-directed shape on its intrinsic
`WalkingEndHom_grpd` carrier.
`nat_add` recurses on its left input in the same orientation, and
`walking_encode_comp_view` proves that intrinsic-hom composition maps to
`nat_add(encode_action(g),encode_action(f))`. Open composition retains
`comp_fapp0`; it is not silently normalized to an arithmetic head.

The owner probe tested both reduction orders for:

- `g o id` and `id o f` against the generic unit rewrites;
- triple composition against the generic proof-time associativity equation;
- opposite composition;
- the action of an arbitrary functor out of `BNat_cat`;
- visible `hom_postcomp_fapp0` and `hom_precomp_along_fapp0` consumers;
- open Nat terms, not only closed numerals.

The selected rules use `_` for recoverable endpoints and add only the six
documented constructor/generic-owner critical pairs. The two narrowly typed
zero-action `unif_rule`s are validated by typed `eq_refl` views and are never
described as runtime Nat normalization.

## Auxiliary Univalence And Groupoidality Tests

These are useful sub-tasks because they test that the completed parent design
preserves the distinction between arrows, paths, and equivalences.

### Nonidentity

After the Nat equivalence is derived, prove computationally:

```text
walking_loop != id.
```

Under encoding this is `succ(zero) = zero`, whose classifier reduces to
`Empty_grpd`. Do not install nonidentity as a primitive axiom.

### Noninvertibility

Derive that `walking_loop` has no native equality-valued omega-equivalence
evidence. An alleged inverse encodes to a Nat whose composite with one would
equal zero; the relevant Nat successor/zero equality is empty.

The exact theorem may be exposed as a function from

```text
OmegaEquivAlong_EQ1(WalkingEnd_cat,base,base,walking_loop)
```

to `Empty_grpd`, using the active inverse/law projections. It must not rely on
legacy D0 decoders.

### Nongroupoidality

Derive a negative groupoidality theorem by applying alleged
`IsGroupoidalCat_EQ1(WalkingEnd_cat)` evidence to the generating loop and then
using noninvertibility. This is a stronger architecture test than merely
omitting a groupoidality constructor.

### Object-level univalence sanity

The category can still be object-univalent: it has one object, and the Nat
model should show that its only invertible endomorphism is zero. The test must
confirm that object univalence does not turn every endomorphism into an
equivalence. In particular, the path/core inclusion reaches the identity
arrow but not `walking_loop`.

### Directed dimension

After Nat sethood and the hom equivalence are active, attempt to derive that
the model and then the HIT are ordinary one-categories in the active
`IsNCat(cat_one,...)` sense. If truncation transport across the derived
category/hom equivalence is missing, record that theorem as a separate
reusable prerequisite rather than adding one-off evidence to the HIT.

## Module And Ownership Strategy

Begin in a one-way extension module, provisionally:

```text
emdash3_2_walking_end_hit.lp
```

which imports the active kernel and, only when needed, the native EQ1
extensions. The active kernel must never import this experimental module.
Keep the HIT presentation, Nat model, and comparison in one module during the
architecture phase; split them only after the dependency boundary is stable.
Do not combine a file split with a rewrite-normal-form migration.

Post-completion consolidation applies that boundary literally: reusable Nat
addition, associativity, Unit/Empty proposition evidence, and Nat sethood now
live in `emdash3_2_nat_arithmetic.lp`. The walking module imports them while
retaining the intrinsic `WalkingEndHom_grpd` carrier, both one-object
categories, the eliminators,
encode/decode, equivalence packages, and directed negative results. The usual
unqualified arithmetic spellings remain transitively available to clients of
the walking module; their module-qualified owner intentionally moves. No
rule, unifier, theorem body, or runtime normal form changed in that split. The
later HIT-elimination correction removed the parallel carrier functions and
changed the equivalence theorem bodies, while still adding no rule or unifier.

The selected public surface is:

```text
WalkingEndHom_grpd
walking_end_hom_id
walking_end_hom_step
walking_end_hom_ind
WalkingEnd_cat
walking_base
walking_loop
walking_end_ind_sec
walking_end_ind_beta_loop
walking_end_rec_func
walking_end_rec_beta_loop
walking_end_rec_step_view

BNat_cat
bnat_obj
bnat_generator
nat_add
bnat_comp_nat_add
walking_encode_action
walking_encode_func
walking_encode_succ_view
walking_encode_comp_view
walking_decode_func
walking_decode_action
walking_decode_succ_view
walking_decode_comp_view
walking_decode_encode_roundtrip
walking_encode_decode_roundtrip
walking_hom_nat_by_inverse
walking_hom_nat_type_equiv
walking_hom_nat_omega_equiv_EQ1.
```

The API uses "walking endomorphism" or `BNat` rather than "directed Circle",
because the latter suggests an invertible topological loop.

Permanent executable diagnostics belong in `emdash3_2_checks.lp` only after
the module is adopted into the ordinary check graph. Reviewer-facing
mathematical statements should live in a focused example such as:

```text
examples/walking_endomorphism_hit.lp
```

## Phased Implementation Plan

### Phase 0: adoption and exact interface probes — completed

1. Explicitly adopt or revise this proposal before editing active semantic
   owners.
2. Re-read current authorities and inspect staged/unstaged work.
3. Remeasure bounded check, warning, audit, catalog, and example baselines.
4. Probe the exact `Catd` loop-lift type and both `Pi_cat` projection betas in
   an owner-position full-file copy.
5. Probe constant-motive specialization through the existing direct
   `Pi_cat(Const_catd)`/`Functor_cat` comparison.
6. Separately probe ordinary `fapp0`/`fapp1_fapp0` observations of the
   constant-motive result; type acceptance is not observer computation.
7. Record the owner-position distinction between judgmental point beta and
   propositional generator beta.

Exit criterion: the dependent eliminator signature typechecks in isolation,
both proposed projection owners are identified, and the generator equality is
an explicit HIT beta rather than an opaque composite-action theorem.

### Phase 1: Nat monoid and discreteness prerequisites — completed

1. Define selected Nat addition transparently.
2. Add computation diagnostics for both constructors and open terms.
3. Derive unit and associativity statements needed by the category model.
4. Prove `IsSetGrpd Nat_grpd`.
5. Expose only the minimal reusable arithmetic/truncation API required by the
   comparison.

Exit criterion: Nat addition computes, its laws are derived without global
proof erasure, and Nat sethood is an internal term.

### Phase 2: transparent `BNat_cat` model — completed

1. Add the one-object category and object/hom projections.
2. Select constructor-directed native composition from focused probes.
3. Add identity, generator, and composition computation.
4. Test both generic-unit orders, associativity, opposite, functor action,
   postcomposition, and precomposition consumers.
5. Derive local discreteness/one-category evidence where current closure
   theorems suffice.

Exit result: `BNat_cat` is a coherent computational category model with Nat
arrow normal forms, generic higher composition still owned by the ambient
calculus, internal local-discreteness evidence, and no category-specific
post/precomposition rules. The three constructor-owner overlaps are measured
and recorded rather than multiplied into an action bridge family.

### Phase 3: HIT constructors and dependent eliminator — completed at the revised beta boundary

1. Add `WalkingEnd_cat`, `walking_base`, and `walking_loop` without a Hom-to-
   Nat rule.
2. Add the single dependent eliminator owner returning a `Pi_cat` section.
3. Promote judgmental base beta and propositional loop beta after
   owner-position critical-pair checks.
4. Add negative controls showing that no object eta, loop identity, inverse,
   or Nat hom classification is silently available.
5. Derive the constant-motive recursor through the eliminator.

Exit result: the actual HIT constructors, structured dependent eliminator,
judgmental point beta, explicit loop-beta witness, derived recursor, and
derived loop-square law are executable. The raw loop action remains a
negative conversion control.

### Phase 4: path-map/higher-action fork — completed at specialized boundary

1. Probe the generic `Path_cat` functor constructor and its first two hom
   actions.
2. Test identity and composition in both reduction orders.
3. Determine the precise relationship with semantic `eq_ap` and retained
   `ObsAction`; do not claim full registry subsumption from one projection.
4. If the generic route is unstable or disproportionate, implement the
   smallest honest specialized higher-action owner needed for
   `walking_decode_func` and record the generalization gate.

Exit result: the documented specialized `walking_decode_func` is an iterable
semantic functor. Its generator beta is explicit and its arbitrary capped
action is proved by Nat induction. Generic `PathMap` and `ObsAction`
subsumption remain explicitly deferred.

### Phase 5: encode, powers, and decode — completed

1. Derive `walking_encode_func` from the HIT recursor.
2. Define `walking_power` by Nat recursion.
3. Package powers as `walking_decode_func` through the selected Phase-4
   architecture.
4. Check identity, generator, successor/power, and composition formulas.
5. Preserve generic functoriality as the owner of encode/decode preservation.

Exit criterion: both comparison directions are iterable functors or otherwise
have an explicitly equivalent structured presentation; capped functions alone
are not the final boundary.

### Phase 6: round trips and hom equivalence — completed

1. Prove encode-after-power by Nat induction.
2. Derive power-after-encode for arbitrary generated arrows from native
   `walking_end_hom_ind`, using the successor laws of the actual semantic
   encoder and decoder actions.
3. Retain displayed-logical-relation, endofunctor-transfor, and structured
   `PathOut` presentations as future generic strengthenings that first require
   a reusable structured motive/transfor constructor.
4. Keep full functor/transfor extensionality outside the concrete Hom
   equivalence boundary.
5. Package the hom equivalence in native EQ1 form and derive the optional
   `TypeEquiv` view.
6. Add closed and open computational examples.

Exit criterion: both arbitrary round trips have transparent bodies, the hom
equivalence is active, and no prior Hom-to-Nat rewrite made either theorem
tautological.

### Phase 7: selected univalence and dimension consumers — completed; full initiality deferred

1. Record full functor/transfor uniqueness as an optional strengthening beyond
   the practical intrinsic-hom computation result, not as this milestone's
   acceptance condition.
2. Defer category-level equivalence with `BNat_cat` and the category of
   endomorphism algebras.
3. Prove loop nonidentity, loop noninvertibility, and category
   nongroupoidality.
4. Check object-level univalence/core behavior.
5. Derive OneCat/local-discreteness evidence or record the exact missing
   equivalence-invariance theorem.

Exit result: the example consumes native EQ1 packaging, proves the loop
nonidentity/noninvertibility/nongroupoidality tests, and derives OneCat
evidence without collapsing directed arrows into paths.

### Phase 8: consolidation and next-scope decision — completed

1. Synchronize active code, checks, reviewer example, Foundations, current
   status, this ledger, report index, catalog, and health report.
2. Run warning summary, strict LHS audit, examples, catalog, health, and CI.
3. Decide whether the next bounded objective is dependent Join elimination,
   a generic directed-HIT schema, groupoid completion toward `BInt`, or
   continued deferral.
4. Do not begin the next objective in the same semantic migration.

Exit criterion: all promoted claims have executable evidence and every
remaining gap has an exact owner/prerequisite.

## Implemented First Slice And Revised Decision

The original slice exposed the raw loop-beta/composite-action conflict. A
later generated-hom probe showed that arbitrary directed arrows have the
required induction structure, while comparison with standard Circle
interfaces showed that raw loop beta was an unnecessarily strong acceptance
condition. The theorem-first revision was promoted, and the later peer-review
correction rerouted the exported equivalence through the actual semantic
actions.

The realized first slice is:

1. owner-position probe of the exact dependent eliminator type;
2. native non-Nat intrinsic `WalkingEndHom_grpd` carrier,
   `walking_end_hom_ind`, and `WalkingEnd_cat` composition;
3. `walking_end_ind_sec` returning `Pi_cat D`;
4. base projection beta through `piapp0`;
5. a propositional loop beta at `piapp1_fapp0`;
6. constant-motive recursor, point computation, loop theorem, and derived
   loop-square theorem;
7. negative assertions that the hom does not reduce to Nat and the loop does
   not reduce to identity;
8. semantic encode/decode round trips whose decisive source proof is headed by
   `walking_end_hom_ind` and consumes the HIT-derived successor law;
9. warning/LHS comparison, BNat comparison, and bounded active checks.

This slice answers the central feasibility question positively: the current
`Catd`/section/action kernel can host a structured dependent eliminator for a
genuine directed arrow constructor when the generator beta is propositional
and composite runtime action remains globally owned. Its intrinsic hom
eliminator can then prove practical arbitrary-arrow computation for the
recursor's actual action. Generic `PathMap` or `PathOut` was not used to
conceal or implement that boundary.

## Probe And Diagnostic Matrix

| Area | Positive requirement | Negative/control requirement |
| --- | --- | --- |
| HIT formation | base and loop typecheck | no Hom-to-Nat conversion |
| HIT hom induction | identity/step beta compute and motives range over the intrinsic Hom carrier | no second external word model or opaque arrow-induction axiom |
| dependent motive | loop lift has exact `D[loop](u) -> u` endpoint | raw family is not silently accepted as `Catd` |
| base beta | `piapp0(ind,base)` computes to `u` | unrelated section projection does not fold |
| loop beta | `walking_end_ind_beta_loop` inhabits the exact displayed equality | raw generator/arbitrary action does not fold to the lift |
| recursor | constant motive yields `Functor(W,C)` and target-generic generated-step computation | no independent primitive recursor body or target-specific action rule |
| Nat model | id/loop/comp expose 0/1/addition | open terms do not collapse by commutativity |
| category units | both generic/category-specific orders join | no duplicate global unit rule |
| associativity | typed generic associativity survives Nat exposure | no claim that proof-time firing is runtime normalization |
| path map | specialized decoder remains an iterable Functor | capped `eq_ap` alone is not called a functor package |
| encode | point computes; loop/comp laws are derived | no encode-specific duplicate functor laws |
| decode | zero/successor action laws are derived | no claim that a raw function generated the semantic functor |
| round trips | actual semantic actions are inverse; source proof uses hom induction and HIT-derived successor beta | no helper-syntax equivalence, prior Hom rewrite, or bodyless theorem |
| nonidentity | encoded loop/identity equality reaches Empty | loop is not declared unequal axiomatically |
| nongroupoidality | alleged evidence yields Empty | absence of constructor alone is not a proof |
| Join relation | dependency remains one-way/conceptual | no claim `Join(Unit,Unit)=WalkingEnd` |

## Feasibility Assessment

| Deliverable | Mathematical feasibility | Current computational feasibility | Assessment |
| --- | --- | --- | --- |
| Nat addition and powers | standard | `nat_add`, associativity, and semantic decoder successor theorem promoted | complete |
| `Nat_grpd` sethood | standard | nested native Nat induction now supplies an internal term | complete |
| transparent `BNat_cat` | standard one-object monoid category | constructor-directed composition preserves the generic head on open arrows | complete; three measured owner overlaps |
| dependent eliminator formation | standard induction principle for the free category | exact `Catd`/`Pi_cat` signature active | complete at MVP interface |
| base constructor beta | standard | stable terminal-component runtime owner | complete |
| loop constructor beta | standard intensional HIT equality | primitive exact equality evidence; no raw action rewrite | complete at selected boundary |
| derived constant recursor | standard | definitionally routes through the dependent eliminator; target-generic step theorem and loop square derived | complete |
| generic `PathMap` | standard functorial action of functions on paths | recursive higher action and generic composition diamonds remain unresolved | deferred; not an MVP blocker |
| specialized power functor | standard monoid functor | semantic Functor head plus derived zero/successor action laws | complete at specialized boundary |
| encode-after-decode | Nat induction | transparent proof over actual semantic actions | complete |
| decode-after-encode | intrinsic HIT hom induction | transparent proof over actual semantic actions; step consumes recursor loop beta | complete |
| native hom equivalence | follows from semantic round trips | `TypeEquiv` and native EQ1 packages expose `walking_encode_action` as forward map | complete |
| loop noninvertibility | elementary intrinsic-hom argument | native inverse-law projections reach Empty | complete |
| nongroupoidality | follows immediately | active `IsGroupoidalCat_EQ1` consumer exposes loop evidence | complete in diagnostics |
| full functor-category initiality | classical | requires an endomorphism-algebra category and coherent extensionality | feasible later but unnecessary strengthening |
| generic directed-HIT schema | mathematically plausible | beyond one constructor and current Join staging | deferred research/architecture |

Overall, the mathematical target is sound and the selected small extension is
computationally feasible. What was infeasible was the stronger demand for a
raw generator-action rewrite alongside the existing strict-functor cut, and
the direct open collapse of semantic BNat composition to addition. Explicit
an intrinsic generated-hom carrier/eliminator, propositional generator beta,
constructor-directed composition, and semantic-action theorems form a
coherent alternative.
Remaining work concerns generic abstraction and external metatheory, not the
selected concrete Hom-to-Nat MVP.

## Risks And Mitigations

### Risk 1: the Nat model is mistaken for the HIT

Mitigation: keep `WalkingEnd_cat` and `BNat_cat` distinct until encode/decode
and both round trips are derived. Retain a negative Hom-conversion assertion.

### Risk 2: a primitive recursor is presented as dependent induction

Mitigation: the primary owner returns a section for arbitrary structured
`Catd` motives and consumes a displayed loop lift. The nondependent recursor
must be a constant-motive specialization.

### Risk 3: beta is only stated propositionally

Mitigation: the point beta remains runtime; the exact generator beta is a
public equality witness, and loop-square/composite laws are derived. Retain a
negative raw-action conversion test so documentation cannot silently turn
the theorem into a computation claim.

### Risk 4: functor uniqueness is assumed

Mitigation: make the semantic decoder-after-encoder round trip an acceptance
gate. The concrete MVP discharges it by native HIT hom induction, whose step
uses the recursor's loop beta. Full functor/transfor uniqueness is not needed
for practical computation and remains explicitly separate rather than inferred
from the Hom round trip.

### Risk 5: one `ObsAction` is mistaken for an omega-functor

Mitigation: retain `ObsAction` unchanged. The specialized decoder is declared
as an ordinary semantic functor and its zero/successor action laws and inverse
theorems are derived; no raw-function-to-functor constructor is claimed.

### Risk 6: category-specific composition duplicates hom-action owners

Mitigation: use constructor-directed `comp_fapp0` computation, keep open
composition at the semantic head, and treat post/precomposition as consumers
of generic actions. The six resulting owner overlaps are measured; no
duplicate action bridges are installed.

### Risk 7: Nat commutativity hides variance

Mitigation: inspect open normal forms, document the `g o f` addition order,
and retain a later two-generator free-category test if variance needs a
noncommutative witness.

### Risk 8: univalence accidentally groupoidalizes the category

Mitigation: derive explicit loop noninvertibility and nongroupoidality while
checking that object-level univalence/core behavior remains coherent.

### Risk 9: an implementation extension is promoted directly into the kernel

Mitigation: start in a one-way module, validate the public consumer, and move
an owner only when its dependency and normal-form role are stable.

### Risk 10: operational success is overstated as metatheory

Mitigation: this plan claims a checked Lambdapi presentation and derived
computations, not an external consistency, normalization, canonicity, or
semantic-model proof. Those remain the parent's deferred metatheory track.

## Side-Task Ledger

| Task ID | Initial status | Purpose | Dependency | Status-changing result |
| --- | --- | --- | --- | --- |
| `WEHIT-ARCH-REVIEW` | **completed 2026-07-17** | select representative HIT and honest acceptance boundary | completed parent MVP | walking endomorphism selected; explicit Nat model separated from HIT; dependent elimination and derived round trips required |
| `WEHIT-ADOPT` | **completed 2026-07-17** | explicitly adopt/revise this plan for implementation | architecture review | user handoff fixed baseline `8fd9bdf...`; active state and all proportional baselines remeasured |
| `WEHIT-IND-SHAPE` | **completed/revised 2026-07-18** | type exact `Catd` motive, loop lift, section result, and beta interface | adoption | exact signature and point beta active; loop beta selected as equality evidence after Circle-interface comparison; loop square derived |
| `WEHIT-NAT-ADD` | **completed/promoted 2026-07-17** | transparent Nat monoid operations and laws | adoption | constructor/open unit computation and transparent associativity active with no warning/audit delta |
| `WEHIT-NAT-SET` | **completed/promoted 2026-07-17** | internal `IsSetGrpd Nat_grpd` proof | Nat equality/truncation kernel | nested Nat-induction proof, permanent diagnostics, and reviewer example pass |
| `WEHIT-COMP-OWNER` | **resolved by revised boundary 2026-07-18** | preserve the single generic composite-action owner | measured HIT and BNat failures | intrinsic `walking_end_hom_ind` selected; raw loop beta/direct open addition rejected; constructor composition adds only six measured owner pairs |
| `WEHIT-BNAT-MODEL` | **completed/promoted 2026-07-18** | separate transparent one-object Nat category | Nat addition/sethood and revised composition owner | constructor-directed identity/composition, generator, local discreteness, and OneCat evidence active |
| `WEHIT-HIT-INTRO` | **completed/promoted 2026-07-18** | add HIT category, base, and directed loop without Hom-to-Nat conversion | intrinsic generated-hom syntax | native Hom carrier and nonidentity directed generator active |
| `WEHIT-HIT-IND` | **completed at propositional-loop-beta boundary 2026-07-18** | dependent eliminator, runtime point beta, equality generator beta | HIT introductions | structured `Catd` section interface active; raw loop action retained as negative conversion control |
| `WEHIT-REC` | **completed/promoted 2026-07-18** | derive nondependent recursor from constant motive | dependent eliminator | body routes through `walking_end_ind_sec`; loop beta and loop-square equality have explicit terms |
| `WEHIT-PATH-MAP` | **completed at specialized boundary; generic constructor deferred 2026-07-18** | honest structured reverse comparison | Nat model and comparison consumer | `walking_decode_func` is iterable; generator beta and derived zero/successor laws active; `ObsAction` unchanged |
| `WEHIT-ENCODE` | **completed/promoted 2026-07-18** | recursor-derived functor from HIT to Nat model | recursor and `BNat_cat` | point computation, generator beta, and successor/composition theorems active |
| `WEHIT-DECODE` | **completed/promoted 2026-07-18** | Nat-power functor from model to HIT | Nat model and specialized path-map fork | object beta, generator beta, and zero/successor/composition theorems active |
| `WEHIT-ROUNDTRIP-NAT` | **completed/corrected 2026-07-18** | encode after decode | semantic encoder/decoder actions | native Nat-induction proof over actual actions |
| `WEHIT-ROUNDTRIP-HIT` | **completed/corrected 2026-07-18** | decode after encode for arbitrary generated arrow | intrinsic hom induction and HIT loop beta | `walking_end_hom_ind` proof over actual actions; each step uses both derived successor laws; open conversion remains negative |
| `WEHIT-HOM-EQUIV` | **completed/corrected 2026-07-18** | native EQ1 hom equivalence and TypeEquiv view | semantic round trips | transparent inverse package exposes `walking_encode_action`/`walking_decode_action`, not helper carrier functions |
| `WEHIT-HIT-COMPUTE-CORRECTION` | **completed/promoted/validated 2026-07-18** | ensure practical freeness materially uses HIT elimination | independent peer-review defect | parallel word-datatype framing and helper-map equivalence removed; intrinsic hom ownership and target-generic recursor step made explicit; semantic-action round trips active; 1,980 checks/72 areas, 22-statement example, 55 targets, warning inventories `971/157` and `977/157`, zero audit findings, 121.390s health, and 171.313s CI pass |
| `WEHIT-INITIALITY` | **deferred strengthening** | functor uniqueness/category-of-algebras comparison | Hom round trip and transfor extensionality | concrete free-arrow result does not overclaim full higher functor-category initiality |
| `WEHIT-NONIDENTITY` | **completed/promoted 2026-07-18** | prove loop differs from identity | intrinsic hom no-confusion | alleged equality is an Empty inhabitant |
| `WEHIT-NONINVERTIBLE` | **completed/promoted 2026-07-18** | prove loop has no equivalence evidence | constructor composition and EQ1 projections | alleged left inverse law reaches Empty |
| `WEHIT-NONGROUPOIDAL` | **completed diagnostic 2026-07-18** | prove category is not groupoidal | noninvertibility and active groupoidality API | alleged global evidence yields loop evidence then Empty |
| `WEHIT-ONECAT` | **completed/promoted 2026-07-18** | derive ordinary one-category dimension | Nat/intrinsic-hom sethood | both path homs have `IsDiscreteCat`; both one-object categories have `IsNCat(cat_one,...)` |
| `WEHIT-JOIN-FOLLOWUP` | deferred separate plan | use dependent-HIT pattern to reassess Join elimination | completed walking HIT | new bounded plan; no implementation in this task |
| `WEHIT-GROUPOID-COMPLETION` | deferred separate plan | compare `BNat` with free invertible loop/`BInt` | completed walking HIT | separately reviewed architecture |
| `WEHIT-CONSOLIDATE` | **completed 2026-07-18** | synchronize code, examples, reports, and gates | implemented selected MVP | 1,977-check catalog, 54-target health, warnings/audits, all examples, and full local CI pass |
| `WEHIT-POST-CONSOLIDATE` | **completed 2026-07-18** | stabilize the post-MVP module and report boundary | completed selected MVP | reusable Nat prerequisites extracted; inline assertions centralized with the missing second round-trip negative; 1,978 checks/72 areas and all 55 targets pass; warnings remain kernel/Nat `971/157` and walking `977/157`; audits, health, examples, and 128.448s CI pass |

## Validation And Synchronization Protocol

Implementation follows `AGENTS.md` and the current SOP. In particular:

- inspect staged and unstaged changes separately on every continuation;
- relocate all symbols with `rg` and never rely on report line numbers;
- run a bounded baseline before semantic edits;
- probe every rewrite/unification candidate in an intended-owner-position
  temporary full-file copy;
- use `_` for recoverable inferred LHS slots unless a measured guard is
  documented;
- test both reduction orders for every constructor/projection bridge;
- validate proof-time rules with typed `eq_refl` and retain runtime negative
  controls;
- keep generic `fapp*`, `tapp*`, `piapp*`, and hom-action owners authoritative
  for ordinary functoriality/naturality;
- add one focused sanity assertion for every new rule;
- run `make check` in the inner loop, `make examples` for public milestones,
  and warning/audit/catalog/health/CI gates before substantive handoff;
- synchronize this ledger, the parent H2 row, report index, current status,
  Foundations, examples, catalog, and health report when implementation facts
  change;
- never use `--no-sr-check` for a promoted candidate.

## Completion And Blocker Policy

This report began as a proposed design document. The selected concrete MVP is
now implemented and meets the completion conditions below; that completion
does not include the explicitly deferred generic schema, categorical
initiality, Join follow-up, or groupoid completion.

The directed-HIT implementation is complete only when:

1. the intrinsic HIT hom carrier and external Nat model remain independently
   presented, without misdescribing the former as a second model;
2. the dependent eliminator, judgmental point beta, and propositional
   generator beta are active;
3. the nondependent recursor is derived from that eliminator;
4. encode and decode retain iterable higher structure;
5. both arbitrary round trips concern the actual semantic encoder/decoder
   actions, and the source-side proof uses intrinsic hom induction plus the
   HIT-derived successor theorem, without an earlier Hom-to-Nat rule;
6. the native hom equivalence is packaged with `walking_encode_action` as its
   forward projection;
7. required positive/negative examples and all proportional gates pass;
8. claims about nonidentity, noninvertibility, nongroupoidality, or dimension
   are made only when their corresponding rows are discharged; full
   functor-category initiality is explicitly not required for practical
   computation.

All eight conditions pass at the selected theorem-first boundary. The plan is
therefore complete for the concrete walking-endomorphism/BNat MVP. Further
work must begin from one of the deferred rows as a new bounded objective
rather than silently strengthening the generator beta or composition normal
forms in this completed slice.

A hard blocker must record:

- the exact desired term, rule, or theorem;
- the smallest failing owner-position probe and retained log;
- whether the failure is typing, subject reduction, normalization,
  nontermination, overlap, performance, representation, extensionality, or
  missing mathematics;
- the precise prerequisite expected to change the result;
- independent dependency-ready work that remains.

The 2026-07-17 checkpoint met this policy for the then-apparent
`WEHIT-COMP-OWNER` blocker. Subsequent probes resolved it by revising the raw
beta requirement and selecting explicit generated-hom induction. The rejected
logs remain decision evidence; they are no longer a terminal blocker.

The generic `PathMap` candidate is not a blocker because the specialized
structured decoder has derived zero/successor/composition laws and the actual
semantic actions satisfy both inverse laws. The decisive HIT round trip is
discharged by intrinsic `walking_end_hom_ind`, using the HIT-derived encoder
successor law. Generic `path_ind_sec` does not replace this proof because it
requires an already structured motive. A future abstract HIT without native
generated-hom syntax would again need a reusable motive,
extensionality/arrow-induction, or transfor theorem.

## Future Handoff Requirement

After consolidation, a future handoff should treat this selected concrete MVP
as retained work, not resume the superseded `WEHIT-COMP-OWNER` blocker. A new
bounded plan may select dependent Join elimination, generic directed-HIT
abstraction, generic `PathMap`, categorical initiality, or groupoid completion
toward `BInt`. Categorical initiality is optional future scope, not missing
from the practical computation milestone. Any follow-up must preserve the
theorem-first beta boundary and must not replace the semantic-action Hom
comparison by a direct Hom-to-Nat rewrite or parallel carrier equivalence.
