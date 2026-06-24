# EMDASH v3.2 Groupoid And Computational Univalence Implementation Plan

Date: 2026-06-23
Last reviewed: 2026-06-24

Plan-ID: EMDASH-V3-2-GROUPOID-COMPUTATIONAL-UNIVALENCE-2026-06-23
Depends-On: none
Supersedes: EMDASH-V3-2-PROFUNCTOR-REPRESENTABILITY-2026-06-19 (univalence track only)
Side-Task-Ledger: #side-task-ledger
Infinity-Codex-Origin: infinity-codex:019ef47a-919d-77b3-93f9-7af7a7848c73:019ef4a2-2e56-7513-9c26-878b2df22426
Infinity-Codex-Decision-Responses: infinity-codex:019ef47a-919d-77b3-93f9-7af7a7848c73:019ef4a2-2e56-7513-9c26-878b2df22426

Status: active implementation plan. Phase 1 and the first Program A slices are
promoted in `emdash3_2.lp`: transparent `PathOver`, `pathover_refl`,
primitive reflexive `eq_apd`, functor-owned `Core_incl_func`, public
`path_to_hom`, decoded `Pi_grpd`, contractible-fibre `TypeEquiv`, reflexive
`type_equiv_refl`, reflexive `coe_grpd`, canonical `idtoequiv_grpd`,
`GrpdUnivalence`, stable operational `ua_grpd`, and the computational law
`coe_grpd(ua_grpd(U,e),a) -> type_equiv_to(e,a)`. The first Sigma path-view
slice is also promoted: `SigmaPathView`, `sigma_path_base`,
`sigma_path_fibre`, `sigma_path_refl`, reflexive `sigma_path_encode`,
`sigma_path_intro`, and constructor-reflexive `sigma_path_decode`. The first
Pi/function path-view slice is promoted as well: `PiPathView`,
`pi_path_apply`, `pi_path_refl`, and reflexive `pi_path_encode`. The first
constructor-specific computational-univalence skeleton is now promoted:
`Product_grpd`, `Product_pair_grpd`, `product_type_equiv`,
`sigma_type_equiv_same_base`, and `pi_type_equiv_same_domain`, each with
forward `type_equiv_to` computation and corresponding `coe_grpd(ua_grpd(...))`
regression checks. Their `IsEquivMap` witnesses are intentionally isolated
proof capabilities pending fuller Sigma/Pi path algebra. The first
categorical-univalence skeleton is also promoted: 1-categorical staging via
`idtoiso_cat`, `CatIsoUnivalence`, `isotoid_cat`, and global
`cat_iso_univalence`; omega-categorical equivalence via primitive
`OmegaEquiv` destructors, reflexive `omega_equiv_refl`, canonical
`path_cat_omega_path`, `path_cat_iso_path`, opposite closure
`omega_equiv_op` with destructor computation, explicit product closure
`omega_equiv_product` with componentwise forward/inverse/cell computation,
`idtoequiv_cat`, explicit `CatUnivalence`, inverse selection `equivtoid_cat`,
and global `cat_univalence`. The `Cat_cat` univalence interface is available
immediately through the global instance; broader constructor-specific
computation and universe-specific computation remain deferred. No generic
`HomComparison` symbol from this report has yet been promoted. The existing
equality, `Path_cat`, `IsoEvidence`, and `ProfComparison` implementations
remain active. Focused probes have confirmed derivability of the covariant
Yoneda embedding from `hom_int` over the opposite category.

## Scope And Authority

This report is the active owner of the non-directed/groupoidal equality,
computational univalence, categorical object-equivalence, and generic
comparison design. It replaces the provisional univalence track in the
profunctor representability redesign report. That older report remains the
authority for the completed `ProfComparison` and weighted-limit migration.

The goals are:

- preserve Lambdapi's strict conversion and rewrite/unification discipline;
- add observational computation for internal paths incrementally by type
  former;
- distinguish groupoid/type equivalence from categorical equivalence and from
  computational comparison;
- express categorical univalence without identifying arbitrary directed
  arrows with paths;
- reuse the existing internal hom/Yoneda infrastructure;
- permit constructors whose path or univalence projections remain stuck;
- avoid requiring a general omega-equivalence corecursor, complete constructor
  closure, or universe-specific computation before useful lower layers land.

This plan does not modify the active kernel in one large migration. Each phase
must be probed independently and promoted only after warning-enabled
owning-position validation.

## Post-Copy Review Corrections

This report began by copying the architecture proposed in the linked Infinity
Codex decision response. A second review against the active kernel and current
rewrite SOP made the following decisions more precise:

1. Keep the existing `=` classifier and expose constructor computation through
   stable path views. A migration of `=` is not an initial prerequisite.
2. Define `TypeEquiv` from contractible fibres of decoded functions, not from
   the currently incomplete `Grpd_cat` categorical calculus.
3. Treat both `idtoequiv_grpd` and `idtoequiv_cat` as canonical maps derived by
   equality induction.
4. Define univalence capabilities by `IsEquivMap` of those canonical maps.
   Only the inverse selections require the capabilities.
5. Keep `path_to_hom` independent of categorical univalence.
6. Give generic `HomComparison` whole `Functord` maps between Yoneda families;
   dedicated pointwise beta/eta belongs below those maps.
7. Treat general `OmegaEquiv` corecursion/productivity and `Cat_cat`-specific
   computation as separate deferred tasks, not prerequisites for
   observational paths or groupoid type equivalence.
8. Let `Core_incl_func` and generic `fapp1` functoriality own computational
   path-to-arrow composition. Do not add either orientation of a specialized
   composition rule when the generic owner remains visible.
9. Classify the primitive recursive `OmegaEquiv` destructor interface as
   feasible. Keep general corecursion/productivity semantics and closure
   operations as later validation tasks rather than blockers to the
   classifier.
10. If `Cat` is operationally defined to classify only univalent categories,
    a global `cat_univalence(C)` immediately includes `Cat_cat`. Separate that
    interface assumption from deferred constructor-specific computation and
    from model-theoretic justification of the self-universe.
11. Computational equality can be promoted from "external path views" to
    direct constructor rules for `=`, provided `=` is migrated from `constant`
    to `injective`. The path-view classifiers remain useful as the right-hand
    normal forms of equality computation, for example
    `u = v` at a Sigma type can reduce to `SigmaPathView(u,v)`.
12. Do not rewrite `eq_refl` wholesale to the corresponding constructor path
    view. A 2026-06-25 probe showed that `eq_refl(Σ,u) ↪ sigma_path_refl(u)`
    makes the reflexive `ind_eq`/`ind_eqr` computation stop seeing the
    `eq_refl` head. The safer pattern is: rewrite the equality classifier
    itself, keep `eq_refl` eliminator-visible, and add consumer/projection
    rules such as `sigma_path_base(eq_refl u) ↪ refl(fst u)` and
    `sigma_path_fibre(eq_refl u) ↪ pathover_refl(snd u)`.
13. Because the project globally assumes active categories are univalent, the
    operational inverse direction for categorical univalence should not depend
    on passing an explicit `U : CatUnivalence(C)` argument at every use. Add a
    stable operational decoder head such as `omega_equiv_path`, with
    constructor-specific computation, and relate it later to the generic
    `equivtoid_cat` inverse selection.

These corrections are architectural, not merely notational. In particular,
they prevent a chosen pair of conversion functions from competing with the
canonical equality eliminator and prevent ordinary isomorphism evidence from
becoming the accidental definition of homotopy equivalence.

### 2026-06-25 Equality Computation Review

The intended observational direction is now:

```text
= (constructor-shaped groupoid, x, y)
  ↪ constructor-specific path normal form.
```

For Sigma/Product, the owner should be Sigma, since `Product_grpd(A,B)` is a
transparent constant-family Sigma:

```text
@= (@Σ_ A P) u v
  ↪ SigmaPathView(A,P,u,v).
```

This makes the earlier "path-view detour" an implementation staging device,
not a separate semantic layer. The view type is the desired normal form of the
equality classifier once direct equality computation is enabled.

A focused probe confirmed:

```text
injective symbol = ...
rule @= (@Σ_ A P) u v ↪ SigmaPathView(A,P,u,v)
```

typechecks, and Product equality then computes through the transparent
Product-as-Sigma presentation.

The same probe showed that rewriting `eq_refl` itself is the wrong first
orientation:

```text
eq_refl(Σ,u) ↪ sigma_path_refl(u)
```

breaks ordinary reflexive `ind_eq` computation because the eliminator no
longer sees an `eq_refl` head. The viable first orientation keeps `eq_refl`
primitive/inert and exposes constructor reflexivity only through consumers:

```text
sigma_path_base(eq_refl u)  ↪ eq_refl(sigma_Fst u)
sigma_path_fibre(eq_refl u) ↪ pathover_refl(sigma_Snd u)
```

This preserves both:

```text
ind_eq(eq_refl u, M, m) ↪ m
```

and componentwise observation of reflexive constructor paths.

Pi/function equality remains different. A direct decode
`PiPathView(f,g) -> f = g` is functional extensionality in the current
equality discipline. It should remain capability-driven/deferred unless the
project deliberately adds cubical interval machinery or commits to full
observational function equality as a definitional layer.

The corresponding univalence inverse-computation layer should be operational,
not selected through the generic `IsEquivMap` inverse at runtime:

```text
grpd_equiv_path  : TypeEquiv A B -> A = B
iso_evidence_path : IsoEvidence C x y -> x = y
omega_equiv_path  : OmegaEquiv C x y -> x = y
```

The active `ua_grpd`, `isotoid_cat`, and `equivtoid_cat` can remain semantic
interfaces or compatibility wrappers. Constructor-specific computation should
belong first to these stable decoder heads, with later propositional or narrow
unification agreement back to the generic inverse selections.

## Executive Architecture

The implementation should preserve the following distinct layers:

```text
Lambdapi conversion       t ≡ u
internal path             p : x = y
groupoid/type equivalence TypeEquiv(A,B)
categorical equivalence   OmegaEquiv(C,x,y)
isomorphism evidence      IsoEvidence(C,x,y)
computational comparison  HomComparison(C,x,y)
arbitrary directed arrow  f : Hom_C(x,y)
```

These notions have bridges, but they are not interchangeable:

```text
conversion
  -> reflexive internal path;

internal path in Grpd
  -> TypeEquiv;

internal object path in C
  -> directed arrow in C;

internal object path in C
  -> OmegaEquiv(C,x,y);          // by equality induction

HomComparison(C,x,y)
  -> IsoEvidence(C,x,y);

HomComparison(C,x,y)
  -> OmegaEquiv(C,x,y);          // later

OmegaEquiv(C,x,y)
  -> internal object path;       // only through CatUnivalence(C)

TypeEquiv(A,B)
  -> universe path A = B;        // only through groupoid univalence
```

There is no planned generic bridge:

```text
IsoEvidence(C,x,y) -> HomComparison(C,x,y);
OmegaEquiv(C,x,y)  -> HomComparison(C,x,y).
```

Either bridge would be a computational strictification principle. The failed
generic `StrictIso` experiments already show that arbitrary propositional or
weak inverse data cannot safely be given judgmental cancellation on shared
ordinary-composition heads.

## Current Kernel Baseline

The active kernel already separates the relevant concepts:

```text
Grpd;
τ : Grpd -> TYPE;

(=)       : x -> x -> Grpd;
eq_refl;
ind_eq;
eq_trans;
eq_sym;
eq_ap;

Path_cat(A);
Core_cat(C) := Path_cat(Obj C);

Hom_cat(C,x,y);
id;
comp_fapp0;

Grpd_cat;
Cat_cat;

IsoEvidence(C,x,y);

ProfComparison(P,Q).
```

Important existing facts:

1. `=` is a `constant` classifier. It has equality induction but cannot itself
   head a rewrite rule.
2. `Path_cat(A)` turns internal equality into a category with reflexivity and
   path transitivity as identity and composition.
3. `Hom_cat` is directed and independent of internal equality.
4. `IsoEvidence` is Sigma-encoded propositional inverse data and deliberately
   has no judgmental cancellation on ordinary composition.
5. `ProfComparison` obtains computation from dedicated push/pull eliminators,
   not from generic cancellation under `comp_fapp0` or `Prof_comp_transf`.
6. `Grpd_cat` currently decodes hom objects as ordinary functions, but it does
   not yet expose a complete computational identity/composition calculus for
   those functions.
7. The groupoid universe has encoded Sigma, but no general groupoid-level
   dependent-product classifier. This blocks an internal definition of
   contractibility and contractible homotopy fibres.

The bounded baseline check on 2026-06-23 passed:

```text
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

The following isolated feasibility probes also passed on 2026-06-23:

```text
tmp/probes/univalence_path_utilities_design_probe.lp
tmp/probes/univalence_type_equiv_design_probe.lp
tmp/probes/univalence_yoneda_design_probe.lp
```

The first two were repeated with warnings enabled. They introduced no warning
located in either probe file; the emitted warning inventory came from the
already active imported kernel. The warning-enabled logs are:

```text
logs/probes/univalence_path_utilities_design_probe-20260623-225203.log
logs/probes/univalence_type_equiv_design_probe-20260623-225203.log
```

These are append-only import probes. Promotion still requires an
owning-position temporary full-file probe because interaction with later
active rules is not tested merely by importing the kernel first.

A separate `Core_incl_func` ownership probe was refined after reviewing the
orientation of the proposed path-to-arrow composition rule:

```text
tmp/probes/univalence_core_incl_owner_probe.lp
logs/probes/univalence_core_incl_owner_probe-20260623-231555.log
logs/probes/univalence_core_incl_owner_probe-20260623-231648.log
```

The initial outward rule:

```text
core_path_to_hom(eq_trans(p,q))
  -> core_path_to_hom(q) o core_path_to_hom(p)
```

was the wrong runtime orientation and competed with transparent unfolding of
`eq_trans`. Reversing it gives the intended Došen-style inward fold, but a
generic rule on `comp_fapp0` still creates new overlaps with specialized
ambient-category composition for `Op_cat`, `Path_cat`, `Catd_cat`, `Cat_cat`,
and `Terminal_cat`.

The successful variant removes the specialized composition rule entirely.
It defines public `path_to_hom` as the arrow action of:

```text
Core_incl_func(C) : Core_cat(C) -> C
```

and leaves composition to the existing global `fapp1` functoriality rule.
Only the reflexivity projection bridge is needed because `Path_cat` can erase
the literal generic identity owner before `fapp1` sees it. The quiet and
warning-enabled import probes pass with no warning located in the probe file.
The computational core-inclusion interface is therefore feasible, subject to
the usual owning-position full-file promotion probe. Identification with the
canonical J-defined semantic map remains a proof-time side task.

Implementation checkpoint 2026-06-24: the first Phase 1 path utility and core
inclusion slice landed in `emdash3_2.lp`, with regression assertions in
`emdash3_2_checks.lp`.

Promoted symbols:

```text
PathOver;
pathover_refl;
eq_apd;
Core_incl_func;
path_to_hom.
```

Promoted runtime rules:

```text
eq_apd(f,refl_x) -> refl_(f x);
Core_incl_func(C)[x] -> x;
Core_incl_func(C)[refl_x] -> id_x.
```

There is still no specialized composition rule for `path_to_hom`. The checked
composition normal form remains the generic functoriality fold:

```text
path_to_hom(q) o path_to_hom(p)
  -> path_to_hom(eq_trans(p,q)).
```

Validation evidence:

```text
tmp/probes/univalence_phase1_path_api_probe.lp
logs/probes/univalence_phase1_path_api_probe-20260624-002805.log
logs/probes/univalence_phase1_path_api_probe-20260624-002811.log

tmp/probes/univalence_phase1_owner_position.lp
logs/probes/univalence_phase1_owner_position-20260624-002856.log
logs/probes/univalence_phase1_owner_position-20260624-002900.log

EMDASH_TYPECHECK_TIMEOUT=60s make check
make catalog
```

The warning-enabled owning-position probe produced no reports at the new
`eq_apd`, `Core_incl_func`, or `path_to_hom` rule lines. After promotion,
`make warning-summary` reports:

```text
1121 warnings = 958 unjoinable critical pairs + 163 replaceable patterns.
```

This is a +6 critical-pair delta over the prior 1115-warning inventory. The
six new reports are located at existing product-projection, hom-precomposition,
and transfor/functoriality rules, with terms involving the new
`Core_incl_func` object projection and reflexivity bridge. They are the
expected stable-projection boundary for exposing a global computational object
action:

```text
Core_incl_func(C)[x] -> x.
```

Per the project rewrite SOP, this warning delta is diagnostic evidence for
classification and follow-up joins; it is not a veto on a semantically intended
rewrite rule. The runtime projection is retained because it is the selected
normal form for the core-inclusion functor.

A diagnostic variant replacing this runtime object projection by a proof-time
unification rule still passed the Phase 1 assertions and reduced the delta to
about two critical-pair reports. That variant is not promoted: it relies on a
bare-variable-style unification helper and would make the core inclusion's
object action proof-time only, contrary to the selected computational
interface. If later consumers make this +6 boundary expensive or ambiguous,
reopen `UNI-CORE-INCL` and compare a stable intermediate object-action head
against the current direct runtime projection.

The primitive recursive `OmegaEquiv` interface was tested in:

```text
tmp/probes/univalence_omega_equiv_destructor_probe.lp
logs/probes/univalence_omega_equiv_destructor_probe-20260623-233648.log
```

The classifier, forward arrow, distinct left/right inverses, recursive inverse
cells, reflexivity generator, and recursively reflexive cells all typecheck.
The warning-enabled run produced no warning located in the probe file.

Implementation checkpoint 2026-06-24: the first groupoid Pi/type-equivalence
and groupoid-universe bridge slices landed in `emdash3_2.lp`, with regression
assertions in `emdash3_2_checks.lp`.

Promoted symbols and rules:

```text
ind_eqr;                         // primitive right-based dependent path induction
ind_eq;                          // transport specialization of ind_eqr
sigma_ind;                       // fixed-parameter Sigma eliminator wrapper
Pi_grpd; Function_grpd;
IsContr; is_contr_center; is_contr_path;
HFiber; hfiber_point; hfiber_path;
IsEquivMap; is_equiv_fiber;
TypeEquiv;
type_equiv_to; type_equiv_is_equiv; type_equiv_fiber;
type_equiv_from; type_equiv_left; type_equiv_right;
hfiber_id_path; hfiber_id_contr_path;
type_equiv_refl;
coe_grpd;
idtoequiv_grpd;
GrpdUnivalence;
ua_grpd.
```

The promoted runtime computation is deliberately limited to constructor and
reflexivity computation:

```text
ind_eqr(P,u,refl) -> u;
ind_eq(refl,P,u) -> u;            // by unfolding through ind_eqr
sigma_ind(Q,c,Struct_sigma(x,u)) -> c(x,u);
Pi_grpd decodes through τ;
type_equiv_refl.to -> id;
type_equiv_refl.from(a) -> a;
type_equiv_refl.left(a) -> refl_a;
type_equiv_refl.right(a) -> refl_a;
coe_grpd(refl_A,a) -> a;
coe_grpd(ua_grpd(U,e),a) -> type_equiv_to(e,a);
idtoequiv_grpd(refl_A) -> type_equiv_refl(A).
```

No primitive strict cancellation for arbitrary `TypeEquiv` was installed.
`type_equiv_from`, `type_equiv_left`, and `type_equiv_right` are selected from
contractible homotopy fibres. Symmetry and composition for `TypeEquiv` remain
deferred pending more path algebra over Sigma/fibre equality. This is not a
formation or feasibility blocker for the universe bridge.

Validation evidence:

```text
tmp/probes/univalence_phase2_type_equiv_owner_position.lp
logs/probes/univalence_phase2_type_equiv_owner_position-20260624-005746.log
logs/probes/univalence_phase2_type_equiv_owner_position-20260624-005751.log
logs/probes/univalence_phase2_type_equiv_owner_position-20260624-010104.log
logs/probes/univalence_phase2_type_equiv_owner_position-20260624-010111.log

EMDASH_TYPECHECK_TIMEOUT=60s make check
make catalog
make warning-summary
```

After promotion, `make warning-summary` still reports the same inventory as
the previous Phase 1 checkpoint:

```text
1121 warnings = 958 unjoinable critical pairs + 163 replaceable patterns.
```

The Phase 2/bridge slice therefore introduced no warning-count delta. The
warning-enabled owner-position probe reports no warning at the new `Pi_grpd`,
`ind_eqr`, `sigma_ind`, `TypeEquiv`, `coe_grpd`, `idtoequiv_grpd`,
`GrpdUnivalence`, or `ua_grpd` declarations/rules.

Follow-up implementation note 2026-06-24: the equality eliminator ownership
was tightened after review. `ind_eqr` is now the primitive J-like eliminator,
and `ind_eq` is defined as its path-independent transport specialization:

```text
ind_eq(p,P,u) := ind_eqr(λ x _, P(x), u, p).
```

The migration passed a full-file owner-position probe and warning-enabled
probe:

```text
tmp/probes/univalence_ind_eq_from_ind_eqr_owner_probe.lp
logs/probes/univalence_ind_eq_from_ind_eqr_owner_probe-20260624-014050.log
logs/probes/univalence_ind_eq_from_ind_eqr_owner_probe-20260624-014057.log
```

There was no warning located at the equality-eliminator section in the
warning-enabled probe. The Lambdapi builtin assignment remains:

```text
builtin "eqind" ≔ ind_eq;
```

so external equality-induction expectations continue to route through the
public transport head while the real computation owner is `ind_eqr`.
After promotion, `make warning-summary` reports:

```text
1119 warnings = 958 unjoinable critical pairs + 161 replaceable patterns.
```

This is a -2 replaceable-pattern delta and no critical-pair delta relative to
the previous Phase 2 checkpoint. The decrease is expected because the direct
`ind_eq` rewrite rule was removed.

Follow-up implementation note 2026-06-24: the first computational
groupoid-univalence law was promoted. `coe_grpd` is now a primitive stable
coercion head with rules for reflexivity and univalence paths:

```text
coe_grpd(refl_A,a) -> a;
coe_grpd(ua_grpd(U,e),a) -> type_equiv_to(e,a).
```

`ua_grpd` is also a primitive stable operational head parameterized by
`U : GrpdUnivalence`. It is no longer a transparent definition by directly
projecting the centre of the contractible fibre. This is intentional: a
transparent `ua_grpd` unfolds before the outer `coe_grpd` rule can reliably
match the selected univalence path, while Lambdapi does not allow installing a
rewrite rule on the previously defined `coe_grpd` head. The semantic
capability remains:

```text
GrpdUnivalence := Π A B, IsEquivMap(idtoequiv_grpd[A,B]).
```

The operational `ua_grpd` head is therefore the public inverse operation
associated with such a capability; inverse/cancellation coherence beyond
`coe(ua)` remains propositional/deferred unless a later consumer requires a
specific proof-time comparison.

Validation evidence:

```text
tmp/probes/univalence_ua_coe_stable_heads_owner_probe.lp
logs/probes/univalence_ua_coe_stable_heads_owner_probe-20260624-015040.log
logs/probes/univalence_ua_coe_stable_heads_owner_probe-20260624-015041.log

EMDASH_TYPECHECK_TIMEOUT=60s make check
make catalog
make warning-summary
```

After promotion, `make warning-summary` still reports:

```text
1119 warnings = 958 unjoinable critical pairs + 161 replaceable patterns.
```

The `coe(ua)` rule therefore introduced no warning-count delta. The
warning-enabled owner-position probe reports no warning located at the new
`coe_grpd`/`ua_grpd` rules after replacing the unused capability argument in
the rule LHS by `_`.

Implementation checkpoint 2026-06-24: the first Sigma observational path-view
slice landed. Promoted symbols:

```text
SigmaPathView;
sigma_path_base;
sigma_path_fibre;
sigma_path_refl;
sigma_path_encode.
```

The promoted computation is intentionally reflexive/projection-only:

```text
sigma_path_base(sigma_path_refl(u)) -> refl_(fst u);
sigma_path_fibre(sigma_path_refl(u)) -> pathover_refl(snd u);
sigma_path_encode(refl_u) -> sigma_path_refl(u).
```

No generic `sigma_path_decode`, encode/decode cancellation, or raw
`sigma_Fst(path-eliminator(...))` commuting conversion has been promoted.
Those remain separate probes because they are the overlap-sensitive part of
Sigma observational equality.

Validation evidence:

```text
tmp/probes/univalence_sigma_path_view_first_slice_probe.lp
logs/probes/univalence_sigma_path_view_first_slice_probe-20260624-015416.log
logs/probes/univalence_sigma_path_view_first_slice_probe-20260624-015421.log

EMDASH_TYPECHECK_TIMEOUT=60s make check
make catalog
make warning-summary
```

After promotion, `make warning-summary` remains:

```text
1119 warnings = 958 unjoinable critical pairs + 161 replaceable patterns.
```

The warning-enabled owner-position probe reports only the already existing
Sigma projection beta warnings at `sigma_Fst`/`sigma_Snd`, with no warning
located at the new Sigma path-view definitions.

Implementation checkpoint 2026-06-24: the next observational path-view slices
landed.

Promoted Sigma additions:

```text
sigma_path_intro;
sigma_path_decode.
```

Promoted Pi/function additions:

```text
PiPathView;
pi_path_apply;
pi_path_refl;
pi_path_encode.
```

The Sigma decode boundary is intentionally constructor-reflexive, not a
generic eta law:

```text
sigma_path_intro(refl_x,q) -> ap(λ z, (x,z), q);
sigma_path_decode(sigma_path_refl(Struct_sigma(x,a))) -> refl_(x,a).
```

For a variable pair `u`, `sigma_path_decode(sigma_path_refl(u))` is not a
judgmental normal form, because `sigma_path_decode` eliminates on the pair
structure. Adding a broad eta-like rule for that case would be a separate
overlap-sensitive conversion and is not promoted.

The Pi/function view follows the related-input observational shape:

```text
PiPathView(B,f,g)
  := Π x0 x1, Π p : x0 = x1,
       PathOver(B,p,f(x0),g(x1)).
```

Its promoted computation is reflexive application/encode only:

```text
pi_path_apply(pi_path_refl(f),x,x,refl_x) -> refl_(f x);
pi_path_encode(refl_f) -> pi_path_refl(f).
```

There is still no function-extensionality decode from `PiPathView` back to
`f = g`.

Validation evidence:

```text
tmp/probes/univalence_sigma_path_decode_probe.lp
logs/probes/univalence_sigma_path_decode_probe-20260624-160945.log
logs/probes/univalence_sigma_path_decode_probe-20260624-160953.log

tmp/probes/univalence_pi_path_view_first_slice_probe.lp
logs/probes/univalence_pi_path_view_first_slice_probe-20260624-161141.log
logs/probes/univalence_pi_path_view_first_slice_probe-20260624-161154.log

EMDASH_TYPECHECK_TIMEOUT=60s make check
make catalog
make warning-summary
```

After promotion, `make warning-summary` remains:

```text
1119 warnings = 958 unjoinable critical pairs + 161 replaceable patterns.
```

The warning-enabled owner-position probes report no warning located at
`sigma_path_intro`, `sigma_path_decode`, `PiPathView`, `pi_path_apply`,
`pi_path_refl`, or `pi_path_encode`.

Implementation checkpoint 2026-06-24: the first constructor-specific
computational-univalence skeleton landed.

Promoted constructor equivalence entries:

```text
Product_grpd;
Product_pair_grpd;
product_type_equiv;
sigma_type_equiv_same_base;
pi_type_equiv_same_domain.
```

The promoted computation is deliberately forward-map only. The equivalence
packages are transparent `TypeEquiv`/Sigma values, so `type_equiv_to` reduces
by ordinary pair projection rather than by a new rewrite rule:

```text
type_equiv_to(product_type_equiv(eA,eB),(x,y))
  -> (type_equiv_to(eA,x), type_equiv_to(eB,y));

type_equiv_to(sigma_type_equiv_same_base(e),(x,u))
  -> (x, type_equiv_to(e(x),u));

type_equiv_to(pi_type_equiv_same_domain(e),f)(x)
  -> type_equiv_to(e(x),f(x)).
```

Because `coe_grpd(ua_grpd(U,e),a)` already delegates to `type_equiv_to(e,a)`,
the corresponding univalence transports compute through the same maps:

```text
coe_grpd(ua_grpd(U,product_type_equiv(eA,eB)),(x,y))
  -> (type_equiv_to(eA,x), type_equiv_to(eB,y));

coe_grpd(ua_grpd(U,sigma_type_equiv_same_base(e)),(x,u))
  -> (x, type_equiv_to(e(x),u));

coe_grpd(ua_grpd(U,pi_type_equiv_same_domain(e)),f)(x)
  -> type_equiv_to(e(x),f(x)).
```

The `*_is_equiv` components are intentionally proof capabilities, not runtime
normalization owners. Product equivalence, same-base Sigma equivalence, and
same-domain Pi equivalence are mathematically standard, but deriving their
contractible-fibre witnesses inside the current kernel requires the still
deferred Sigma/Pi observational path algebra, especially generic
encode/decode cancellation and function-extensionality decode. Keeping these
witnesses isolated lets the computational skeleton land without postulating
strict inverse/cancellation rules or changing ordinary runtime reduction.

Validation evidence:

```text
tmp/probes/univalence_constructor_equiv_skeleton_probe.lp
logs/probes/univalence_constructor_equiv_skeleton_probe-20260624-163945.log

EMDASH_TYPECHECK_TIMEOUT=60s make check
make catalog
make warning-summary
make health
make ci
```

After promotion, `make warning-summary` remains:

```text
1119 warnings = 958 unjoinable critical pairs + 161 replaceable patterns.
```

No new rewrite rule was added for this skeleton, so the unchanged warning
inventory is expected.

## Two Related But Separate Programs

The work must be split into two programs.

### Program A: Observational Paths In `Grpd`

This program specifies how internal paths can be observed for type formers:

```text
Sigma;
dependent products/functions;
products;
inductive and coinductive classifiers;
the groupoid universe.
```

Its main concepts are:

```text
PathOver;
dependent ap;
path views/records for constructors;
TypeEquiv;
groupoid transport/coercion;
groupoid univalence.
```

### Program B: Univalent Object Equality In `Cat`

This program relates equality of objects of a category to invertible directed
structure:

```text
path x y  <->  OmegaEquiv(C,x,y).
```

Its main concepts are:

```text
OmegaEquiv;
CatUnivalence(C);
path_to_hom;
Core_incl_func(C);
Yoneda_cov_func(C);
HomComparison(C,x,y).
```

Program A is a prerequisite for the full semantics of Program B, but useful
parts of Program B—especially `path_to_hom`, Yoneda internalization, and
`HomComparison`—can be developed independently.

Program A is intended to provide computational univalence and observational
path computation for the standard implemented groupoid type formers, not only
an abstract noncomputing univalence axiom. In particular:

```text
Id_Grpd(A,B) behaves as TypeEquiv(A,B);
coe_grpd(ua_grpd(e),a) computes to e.to(a);
Sigma/Product paths expose component path data;
Pi/function paths expose related-input path data;
reflexivity and dependent ap compute through those views.
```

The coverage is incremental. Unit, naturals, inductive/coinductive
classifiers, W/M-style formers, and additional project-specific constructors
need their own closure entries before the phrase “most cases” is an
implementation-completeness claim. Missing cases remain well-typed and stuck.

Directed `Hom_cat` characterizations are complementary to these programs.
They define directed identity/hom structure. Univalence additionally states
that non-directed object paths classify the appropriate invertible directed
structure. The terms “directed univalence” and “Hom computation” should not be
used as exact synonyms in implementation comments.

## Equality And Observational Path Views

### Keep The Existing Equality Classifier Initially

The initial proposal suggested that observational computation might eventually
require changing `=` from `constant` to a rewrite-owning symbol. Further review
does not justify that migration.

The preferred first architecture keeps:

```text
constant symbol (=);
eq_refl;
ind_eq.
```

Constructor-specific computation should be exposed through stable view,
projection, introduction, and elimination heads around a path. For example:

```text
SigmaPathView(P,u,v);
sigma_path_base;
sigma_path_fibre;
sigma_path_intro;
sigma_path_elim;
```

This follows the record-like HOTT design in which an identity of a record is
observed through a corresponding identity record without forcing the identity
classifier to reduce literally to the ordinary record constructor.

Advantages in Lambdapi:

- `=` remains the sole owner of ordinary equality induction;
- constructor path views can be added independently;
- deferred constructors simply lack specialized projections;
- path views provide stable rewrite heads;
- no global competition is introduced between equality reduction and `ind_eq`;
- a future migration of `=` remains possible if a concrete consumer proves
  that views are insufficient.

Changing `=` or `eq_refl` from `constant` to `injective` is therefore not on
the initial critical path.

### Equality Eliminator Ownership

The promoted eliminator hierarchy is:

```text
ind_eqr
  : Π y, (Π x, (x = y) -> Grpd) -> P(y,refl_y)
      -> Π x, Π p : x = y, P(x,p)

ind_eq
  : Π p : x = y, (τ A -> Grpd) -> P(y) -> P(x)
```

`ind_eqr` is the primitive right-based path-induction owner. `ind_eq` is only
the transport specialization:

```text
ind_eq(p,P,u) := ind_eqr(λ x _, P(x), u, p).
```

This is a real normal-form decision. The previous primitive `ind_eq` rule was
not a downstream rewrite-LHS owner, so the migration is safe after the
owner-position probe recorded above. Keeping the public `ind_eq` symbol remains
useful because `PathOver`, `eq_trans`, `eq_sym`, `eq_ap`, `coe_grpd`,
`idtoequiv_grpd`, and the Lambdapi builtin `eqind` all speak the simpler
transport interface.

The alternate singleton/Sigma formulation is:

```text
ind_eqr_sig
  : Π (P : (Σ x : A, x = y) -> Grpd),
      P(y,refl_y) ->
      Π s : Σ x : A, x = y, P(s).
```

This formulation is equivalent in intent to the telescope form once encoded
Sigma elimination is available. The telescope form is definable from a
primitive `ind_eqr_sig` by applying it to the pair `(x,p)` and the motive
`λ s, P(fst(s),snd(s))`. Conversely, `ind_eqr_sig` is definable from the
promoted telescope `ind_eqr` plus `sigma_ind` by splitting `s` into `(x,p)` and
then applying `ind_eqr` to `p`.

The singleton eliminator is not derivable from the old transport-only
`ind_eq` without an additional principle such as UIP/path-proof
irrelevance. After splitting `s` into `(x,p)`, a transport-only eliminator can
make the target depend on `x`, but not on the particular proof `p`; producing
all `P(y,p)` from only `P(y,refl_y)` would require collapsing arbitrary loops.

Therefore the current owner should remain `ind_eqr`. A future
`ind_eqr_sig` may be added as a readable derived helper, but it should compute
by routing through `ind_eqr` or, if made primitive, `ind_eqr` should be routed
through it. Do not keep two independent primitive singleton/path-induction
owners with separate rewrite rules.

### Path-Over

Dependent equality requires a heterogeneous path over a base path:

```text
PathOver(P,p,u,v)
```

where:

```text
P : A -> Grpd;
p : x = y;
u : P(x);
v : P(y).
```

A first semantic definition can use the current backward transport:

```text
PathOver(P,p,u,v)
  := u = ind_eq(p,P,v).
```

This transport orientation is an implementation detail and should not become
the surface normal form. The public `PathOver` head should support:

```text
PathOver(P,refl_x,u,v) = (u = v);
pathover_refl(u);
pathover_sym;
pathover_comp;
eq_apd(f,p) : PathOver(P,p,f[x],f[y]).
```

The first probe must compare:

1. a transparent semantic definition;
2. a stable opaque/projection head with only reflexivity computation.

The stable variant is preferable only if the transparent definition unfolds
transport into brittle or expensive LHS conversions.

### Sigma Path View

For:

```text
u v : Σ x:A, P(x)
```

the observational view is:

```text
SigmaPathView(P,u,v)
  :=
  Σ p : fst(u) = fst(v),
    PathOver(P,p,snd(u),snd(v)).
```

The initial API should provide conversions:

```text
sigma_path_encode : (u = v) -> SigmaPathView(P,u,v);
sigma_path_decode : SigmaPathView(P,u,v) -> (u = v).
```

Current promoted boundary: `SigmaPathView`, base/fibre projections,
`sigma_path_refl`, reflexive `sigma_path_encode`, `sigma_path_intro`, and
`sigma_path_decode` are active. Decode is derived componentwise using
`ind_eqr`, `sigma_ind`, and `PathOver`, but its judgmental computation is only
constructor-reflexive. Generic encode/decode eta and cancellation remain
propositional/deferred until a concrete consumer requires judgmental
computation.

Only constructor/reflexivity projections should initially compute
judgmentally. Generic encode/decode cancellation should begin as propositional
evidence. A dedicated computational comparison can be introduced later if a
consumer needs judgmental beta/eta.

Do not install raw commuting conversions such as:

```text
sigma_Fst(path-eliminator(...)) -> ...
```

unless a stable path-view owner cannot express the required projection.

### Sigma Eliminator Ownership

The active encoded Sigma type has the generated eliminator `ind_τΣ_`, but the
promoted low-level groupoid-equivalence code uses:

```text
sigma_ind
  : Π (Q : τΣ(A,P) -> Grpd),
      (Π x u, Q(x,u)) ->
      Π s, Q(s).
```

`sigma_ind` is a fixed-parameter eliminator wrapper with the direct
constructor computation:

```text
sigma_ind(Q,c,Struct_sigma(x,u)) -> c(x,u).
```

This wrapper is semantically the eliminator expected for the fixed encoded
Sigma type. It is not currently defined from `ind_τΣ_`. The generated
eliminator quantifies over all parameters of `τΣ_`; deriving this
fixed-parameter wrapper from it would require packaging a higher-order motive
and branch family inside the `Grpd`/`τ` object language. The current kernel has
no general classifier for arbitrary motives

```text
Q : τΣ(A,P) -> Grpd
```

and their branches as first-class groupoid objects. Adding such a classifier
solely to remove `sigma_ind` would be premature.

This is a documented deferred alignment task, not an ignored discrepancy. The
future options are:

1. keep `sigma_ind` as the stable public eliminator and treat `ind_τΣ_` as
   generated backend infrastructure;
2. add enough motive/branch classifier infrastructure to derive `sigma_ind`
   from `ind_τΣ_`;
3. if a future proof-mode workflow emits `ind_τΣ_` normal forms that conflict
   with `sigma_ind` normal forms, add a narrow proof-time comparison or migrate
   to one canonical owner after a full warning-enabled probe.

Until such a consumer exists, `sigma_ind` should remain the computational owner
used by `type_equiv_refl` and related contractible-fibre proofs.

### Pi And Function Path View

The observational path for a dependent function must account for related
inputs, not only the same point on both sides:

```text
PiPathView(A,B,f,g)
  :=
  Π x0 x1,
  Π p : x0 = x1,
    PathOver(B,p,f[x0],g[x1]).
```

For a nondependent function type this specializes to:

```text
Π x0 x1,
Π p : x0 = x1,
  f(x0) = g(x1).
```

The pointwise same-input presentation can be derived using reflexivity, but it
is not the preferred higher observational owner. The related-input
presentation exposes `ap` and higher-dimensional substitution directly.

This phase requires a groupoid-level Pi classifier and is not part of the
first path-over slice.

Current promoted boundary: `PiPathView`, `pi_path_apply`, `pi_path_refl`, and
reflexive `pi_path_encode` are active. There is no promoted
function-extensionality decode from `PiPathView(B,f,g)` to `f = g`; that would
be the overlap-sensitive computational part of Pi univalence and should be
probed separately.

## Minimal Groupoid Type-Former Infrastructure

### Groupoid-Level Pi

The first missing groupoid constructor is:

```text
Pi_grpd [A : Grpd] (B : τ A -> Grpd) : Grpd;

τ(Pi_grpd(B))
  -> Π x : τ A, τ(B x).
```

The nondependent alias is:

```text
Function_grpd(A,B)
  := Pi_grpd(λ _ : τ A, B).
```

The initial implementation only needs decoding through `τ`. Observational
path computation for `Pi_grpd` is a later phase. This keeps formation separate
from its univalence closure.

### Contractibility And Equivalence

Once `Pi_grpd` exists, define:

```text
IsContr(X)
  := Σ centre : X,
       Π x : X, centre = x;

HFiber(f,b)
  := Σ a : A, f(a) = b;

IsEquivMap(f)
  := Π b : B, IsContr(HFiber(f,b));

TypeEquiv(A,B)
  := Σ f : Function_grpd(A,B), IsEquivMap(f).
```

This should be the target semantic definition. A temporary bi-invertible
prototype is allowed only if:

- it has a distinct provisional name;
- it maps into the final `TypeEquiv` interface;
- no proof-irrelevance or strict cancellation is inferred from it.

The usual operations should be derived:

```text
type_equiv_to;
type_equiv_from;
type_equiv_left;
type_equiv_right;
type_equiv_refl;
type_equiv_sym;
type_equiv_comp.
```

The inverse map can be selected from the centre of each homotopy fibre.
Inverse paths derive from contractibility and equality congruence.

This design does not require first completing `Grpd_cat` as a computational
category. `TypeEquiv` owns an ordinary decoded function directly. In
particular, it should not initially be defined as `IsoEvidence(Grpd_cat,A,B)`:
the current `Grpd_cat` lacks the required function-composition computation,
and ordinary isomorphism evidence is not the intended homotopy-equivalence
classifier.

## Groupoid Coercion And Univalence

Introduce an explicit path coercion:

```text
coe_grpd [A B : Grpd]
  : τ(@= Grpd_grpd A B) -> τ A -> τ B.
```

It should compute on reflexivity:

```text
coe_grpd(refl_A,a) -> a.
```

Path-to-equivalence is derivable by equality induction:

```text
idtoequiv_grpd
  : τ(@= Grpd_grpd A B) -> τ(TypeEquiv(A,B)).
```

Semantically, groupoid-universe univalence says that this canonical map is an
equivalence:

```text
GrpdUnivalence
  :=
  Pi_grpd [Grpd_grpd] (λ A,
    Pi_grpd [Grpd_grpd] (λ B,
      IsEquivMap(idtoequiv_grpd[A,B]))).
```

The public inverse operation associated with this capability is the stable
operational head:

```text
ua_grpd
  : τ(GrpdUnivalence) -> τ(TypeEquiv(A,B)) -> τ(@= Grpd_grpd A B).
```

The first desired computational-univalence law is:

```text
coe_grpd(ua_grpd(U,e),a)
  -> type_equiv_to(e,a).
```

This law directly exposes the runtime meaning of univalence. It is preferable
as the initial rule to demanding both generic conversion cancellations:

```text
idtoequiv_grpd(ua_grpd(U,e)) -> e;
ua_grpd(U,idtoequiv_grpd(p)) -> p.
```

Those two equations should begin as propositional coherence and may later be
tested as narrowly typed unification rules. Installing both as runtime
rewrites risks the same projection/cancellation competition seen in the
rejected `StrictIso` designs.

The capability and the runtime coercion law have different roles.
`GrpdUnivalence` states the semantic equivalence; the
`ua_grpd` head and `coe_grpd(ua_grpd(U,e),a)` rule choose the intended
computational presentation. The stable operational head is used because a
transparent fibre-centre selector unfolds before the outer `coe_grpd` rule can
reliably match. Both are operational foundational assumptions unless and until
they are derived from a fibrancy/observational universe construction.

### Computational-Univalence Closure By Constructor

The planned computational meaning of groupoid univalence has two layers.

First, the universe-level rule chooses how transport along a univalence path
acts on elements:

```text
coe_grpd(ua_grpd(U,e),a) -> type_equiv_to(e,a).
```

Second, each groupoid/type former must supply the equivalence `e` whose
forward map computes structurally for that constructor. Examples:

```text
ua_sigma(eA,eP)      // equivalence between Sigma types
ua_pi(eA,eP)         // equivalence between Pi/function types
ua_product(eA,eB)    // equivalence between products
```

The rule `coe_grpd(ua_grpd(U,e),a)` only delegates to `e.to`. It does not by
itself explain how `e.to` should reduce for Sigma, Pi, product, inductive, or
project-specific constructors. Those constructor-specific equivalences are the
recursive computational-univalence closure entries.

This is why Sigma/Pi observational path views are not merely optional algebra.
They are part of the computational-univalence implementation path:

- Sigma path views expose equality of dependent pairs as a base path plus a
  fibre `PathOver`. They are needed to prove and compute equality inside
  homotopy fibres such as `Σ a : A, f(a) = b`, which in turn supports
  `TypeEquiv` symmetry/composition and Sigma-constructor univalence.
- Pi/function path views expose equality of dependent functions by
  related-input paths

  ```text
  Π x0 x1, Π p : x0 = x1,
    PathOver(B,p,f(x0),g(x1)).
  ```

  This is the intended computational owner for function extensionality and
  Pi-constructor univalence; same-input pointwise equality is only a derived
  special case.

The implementation can remain partial. A constructor without a closure entry
still typechecks, but its univalence/path computation remains stuck at the
corresponding stable head. The phrase “computational univalence for most
cases” should therefore mean: for the constructors with installed closure
entries, transport through `ua` reduces recursively through their
constructor-specific equivalence maps.

## Categorical Path-To-Arrow Inclusion

The safe direction:

```text
path x y -> Hom_C(x,y)
```

does not require univalence. Its semantic reference map follows from equality
induction:

```text
path_to_hom(C,p)
  := ind_eq(p, λ t, Hom_C(t,y), id_y).
```

This gives:

```text
path_to_hom(C,refl_x) -> id_x.
```

A computational functor owner:

```text
Core_incl_func(C) : Core_cat(C) -> C
```

should expose the public map as its arrow action:

```text
path_to_hom(C,p)
  := fapp1_fapp0(Core_incl_func(C),p).
```

Then the existing generic functoriality rule owns composition:

```text
path_to_hom(q) o path_to_hom(p)
  -> path_to_hom(eq_trans(p,q)).
```

No constructor-specific composition rule is required. The only measured
bridge is:

```text
fapp1_fapp0(Core_incl_func(C),eq_refl(x))
  -> id_C(x).
```

This bridge joins projection-first reduction with ordinary functor identity.
The next full-file probe must additionally decide how to record proof-time
agreement between the functor-owned runtime map and the J-defined semantic
reference—preferably propositional evidence or a narrowly typed unification
rule, not a second runtime owner.

The reverse direction applies only to equivalence arrows and requires
`CatUnivalence(C)`.

## 1-Categorical Univalence Staging Layer

Before promoting the full recursive `OmegaEquiv` interface, it is useful to
stage the ordinary 1-categorical approximation that the kernel already has
most of the infrastructure to express:

```text
x = y  <->  IsoEvidence(C,x,y).
```

This layer is not the final meaning of categorical univalence. It is a
feasibility and regression scaffold for the familiar univalent-category
principle that isomorphism arrows are groupoidal object paths. It should be
kept explicitly separate from `OmegaEquiv`, because `IsoEvidence` is ordinary
propositional inverse data at the current hom level, while `OmegaEquiv` is
recursive through all hom-categories.

Semantic correction 2026-06-24: as final mathematics, `CatIsoUnivalence(C)` is
justified only for ordinary/1-truncated categories or under an explicit
1-truncation assumption on `C`. For arbitrary ω-categories, object univalence
must target `OmegaEquiv(C,x,y)`, not `IsoEvidence(C,x,y)`. The current global:

```text
cat_iso_univalence(C) : CatIsoUnivalence(C)
```

is therefore a temporary prototyping axiom for the 1-categorical staging
layer. A later semantics pass should replace or restrict it by one of:

```text
IsOneTruncatedCat(C) -> CatIsoUnivalence(C);
OneCat / OneCat_cat;
TruncCat(n) / IsNTruncatedCat(n,C).
```

Until then, report text should avoid presenting `cat_iso_univalence(C)` as a
correct global principle for all ω-categories.

The staged canonical map is:

```text
idtoiso_cat(C,p)
  : IsoEvidence(C,x,y)

idtoiso_cat(C,refl_x)
  -> iso_evidence_refl(C,x).
```

The corresponding capability mirrors groupoidal univalence:

```text
CatIsoUnivalence(C)
  :=
  Π x y : Obj(C),
    IsEquivMap(idtoiso_cat[C,x,y]);

isotoid_cat
  : CatIsoUnivalence(C)
    -> IsoEvidence(C,x,y)
    -> x = y.
```

As a prototype convenience for the staging layer, the current kernel may keep
the global operational instance:

```text
cat_iso_univalence(C) : CatIsoUnivalence(C).
```

This approximation demonstrates the ordinary 1-categorical statement
“isomorphisms are paths” without forcing any constructor-specific
ω-equivalence computation. It should not replace the later `CatUnivalence(C)`
interface; it is a staging layer and compatibility check.

## Omega-Categorical Equivalence

### Destructor-Oriented Interface

The intended weak equivalence classifier is:

```text
OmegaEquiv(C,x,y) : Grpd.
```

A first coinductive-style observation interface may expose:

```text
omega_equiv_to
  : Hom_C(x,y);

omega_equiv_left_inv
  : Hom_C(y,x);

omega_equiv_right_inv
  : Hom_C(y,x);

omega_equiv_left_cell
  : OmegaEquiv(
      Hom_cat(C,x,x),
      left_inv o to,
      id_x);

omega_equiv_right_cell
  : OmegaEquiv(
      Hom_cat(C,y,y),
      to o right_inv,
      id_y).
```

Distinct left and right inverses match the current higher observational
fibrancy experiments and avoid prematurely choosing one strict inverse.

This interface is recursive through hom-categories and therefore coinductive
in character. Lambdapi has no identified native generated coinductive
declaration or productivity checker in the current project. Nevertheless, an
operational primitive classifier with recursive destructors is accepted by
Lambdapi and has passed a focused probe.

The implementation should therefore distinguish:

1. the core primitive classifier/destructor interface, now syntactically
   feasible;
2. canonical generators and closure operations, to be promoted incrementally;
3. optional general copattern/corecursion support and productivity criteria;
4. a terminal-coalgebra or other external semantic justification;
5. finite-height or 2-categorical probes used only as diagnostics.

Finite approximations are diagnostic only. They must not silently become the
meaning of `OmegaEquiv`.

The project does not need a general user-facing corecursor before the
classifier is useful. Canonical inhabitants such as reflexivity,
`idtoequiv_cat`, and comparison-generated equivalences can be primitive or
derived individually, with destructor equations audited at their owners.

### No Unrestricted Introduction Record

Do not begin with:

```text
omega_equiv_intro(to,left,right,left_cell,right_cell)
```

plus unrestricted projection and cancellation rules. That repeats the
constructor-projection overlap that invalidated generic `StrictIso`.

The first inhabitants should be canonical generators:

```text
omega_equiv_refl;
idtoequiv_cat(p);
hom_comparison_to_omega(i);      // later
```

and perhaps selected constructor closures after their projection paths have
been audited.

### Reflexivity

The first required computation is:

```text
omega_equiv_to(omega_equiv_refl(x))
  -> id_x.
```

Recursive left/right cells should expose reflexive equivalences in the
appropriate endomorphism hom-categories. Symmetry, composition, and functorial
image should not be promoted until the destructor equations and warning
inventory are understood.

Once reflexivity exists, path-to-equivalence is canonical and does not require
categorical univalence:

```text
idtoequiv_cat(C,p)
  := ind_eq(
       p,
       λ t, OmegaEquiv(C,t,y),
       omega_equiv_refl(y))
  : OmegaEquiv(C,x,y).
```

This direction should be implemented before any univalence capability.

## Categorical Univalence Capability

The previous provisional report proposed a direct global contract:

```text
every C : Cat is univalent;
Cat_cat is univalent.
```

That remains a possible eventual project foundation, but it is too strong as
the first implementation step. The safe architecture introduces an explicit
capability. It should state that the canonical `idtoequiv_cat` map is an
equivalence, rather than packaging an unrelated pair of conversion functions:

```text
CatUnivalence(C)
  :=
  Pi_grpd [Obj(C)] (λ x,
    Pi_grpd [Obj(C)] (λ y,
      IsEquivMap(idtoequiv_cat[C,x,y])));

idtoequiv_cat
  : (x = y)
    -> OmegaEquiv(C,x,y);       // canonical; no capability argument

equivtoid_cat
  : CatUnivalence(C)
    -> OmegaEquiv(C,x,y)
    -> (x = y).
```

Constructor-specific instances can then be added incrementally. The intended
project convention is that `Cat` classifies only univalent categories, so add:

```text
cat_univalence(C) : CatUnivalence(C).
```

as an explicit global operational axiom or projection from category
structure. The explicit capability remains useful during implementation even
though the final surface supplies it globally:

- non-univalent intermediate categories remain expressible;
- constructor closure has a stable semantic owner;
- the global assumption is visible rather than hidden in conversion;
- `Cat_cat` self-univalence can remain separate;
- the universe-stratification decision is not forced by the first probe.

The eventual global contract must choose and document one interpretation:

```text
operational unstratified specification;
universe-stratified Cat_i : Cat_(i+1);
deliberate impredicative/self-universe model.
```

The current single `Cat`/`Cat_cat` implementation may support the first option
as a prototype. It must not be presented as a consistency or model-existence
result.

Under the project-level convention that every `C : Cat` is univalent, the
global operational instance:

```text
cat_univalence(C) : CatUnivalence(C)
```

applies to `Cat_cat` immediately because `Cat_cat : Cat`. Thus existence of a
`CatUnivalence(Cat_cat)` interface is not a separate implementation obstacle.

What remains separate is:

1. computational closure for the `Cat_cat`/category-universe constructor,
   which may remain stuck and be added case by case;
2. a semantic/model-theoretic justification of the unstratified convention
   `Cat_cat : Cat_cat`;
3. any later universe hierarchy or consistency claim.

Current HOTT work similarly treats fibrancy of the universe itself as work in
progress while establishing computational fibrancy for many ordinary type
formers. Emdash may adopt the global operational interface now and leave
universe-specific computation pluggable and deferred.

Implementation checkpoint 2026-06-24: the categorical-univalence skeleton
landed.

Promoted 1-categorical staging symbols:

```text
idtoiso_cat;
CatIsoUnivalence;
isotoid_cat;
cat_iso_univalence.
```

Promoted omega-categorical symbols:

```text
OmegaEquiv;
omega_equiv_to;
omega_equiv_left_inv;
omega_equiv_right_inv;
omega_equiv_left_cell;
omega_equiv_right_cell;
omega_equiv_refl;
idtoequiv_cat;
CatUnivalence;
equivtoid_cat;
cat_univalence.
```

The installed runtime computation is intentionally narrow:

```text
idtoiso_cat(refl_x) -> iso_evidence_refl(x);

omega_equiv_to(omega_equiv_refl(x)) -> id_x;
omega_equiv_left_inv(omega_equiv_refl(x)) -> id_x;
omega_equiv_right_inv(omega_equiv_refl(x)) -> id_x;
omega_equiv_left_cell(omega_equiv_refl(x))
  -> omega_equiv_refl(id_x);
omega_equiv_right_cell(omega_equiv_refl(x))
  -> omega_equiv_refl(id_x);

idtoequiv_cat(refl_x) -> omega_equiv_refl(x).
```

The inverse selections `isotoid_cat` and `equivtoid_cat` are transparent
projections through `type_equiv_from` applied to the corresponding
univalence capability, but no strict cancellation rule is installed. The
global operations:

```text
cat_iso_univalence(C) : CatIsoUnivalence(C);
cat_univalence(C)     : CatUnivalence(C);
```

make the project convention explicit: active categories are univalent. Since
`Cat_cat : Cat`, `cat_univalence(Cat_cat)` is a checked immediate interface.
This does not add universe-specific computation and is not a model-theoretic
consistency proof.

Validation evidence:

```text
tmp/probes/univalence_cat_skeleton_probe.lp
logs/probes/univalence_cat_skeleton_probe-20260624-172318.log
logs/probes/univalence_cat_skeleton_probe-20260624-172331.log

EMDASH_TYPECHECK_TIMEOUT=60s make check
make warning-summary
make catalog
make health
make ci
```

After promotion, `make warning-summary` remains:

```text
1119 warnings = 958 unjoinable critical pairs + 161 replaceable patterns.
```

The promoted categorical-univalence skeleton therefore introduces no warning
inventory delta.

## Yoneda Internalization

### Existing Semantic Owner

The covariant Yoneda embedding is already derivable:

```text
Yoneda_cov_func(C)
  : C -> Functor(C^op,Cat)

Yoneda_cov_func(C)
  := hom_int(id_{C^op}).
```

Its object action is:

```text
Yoneda_cov_func(C)[x]
  = Hom_C(-,x).
```

Its arrow action is:

```text
Yoneda_cov_func(C)[f](g)
  = f o g.
```

The focused probe:

```text
tmp/probes/univalence_yoneda_design_probe.lp
```

passed on 2026-06-23, with log:

```text
logs/probes/univalence_yoneda_design_probe-20260623-222337.log
```

Therefore a future `hom_con_int_func` or `Yoneda_cov_func` should begin as a
transparent readability alias. It must not duplicate the semantic body or
introduce constructor-specific functor laws.

### Generic Hom Comparison

The generic computational owner should internalize the incoming object through
Yoneda:

```text
HomComparison(C,x,y).
```

Its semantic operations are whole transformations between the two Yoneda
families:

```text
Yoneda_cov_catd(C,x)
  := Yoneda_cov_func(C)[x]
  : Catd(Op_cat(C));

hom_comparison_push_map(i)
  : Functord(
      Yoneda_cov_catd(C,x),
      Yoneda_cov_catd(C,y));

hom_comparison_pull_map(i)
  : Functord(
      Yoneda_cov_catd(C,y),
      Yoneda_cov_catd(C,x)).
```

Thus the whole operations use `Functord`, the existing kernel owner for
natural transformations between Cat-valued families. Their component at
`r : Obj(C)` is a functor:

```text
Hom_cat(C,r,x) -> Hom_cat(C,r,y)
```

or its reverse. Pointwise object eliminators are:

```text
hom_comparison_push_at(i,r,f)
  : Hom_C(r,y);

hom_comparison_pull_at(i,r,g)
  : Hom_C(r,x).
```

with dedicated beta/eta:

```text
pull_at(i,r,push_at(i,r,f)) -> f;
push_at(i,r,pull_at(i,r,g)) -> g.
```

The `Functord` maps should own naturality in `r` and higher action inside each
hom-category. Do not start by adding a generic inward-accumulation rule on the
shared `comp_fapp0` head. Such a rule would affect every category and would be
much broader than the successful `ProfComparison` rule on
`comp_catd_fapp0`.

Selected arrows are identity applications:

```text
hom_comparison_to(i)
  := push_at(i,x,id_x);

hom_comparison_from(i)
  := pull_at(i,y,id_y).
```

The forgetful layer is:

```text
hom_comparison_evidence
  : HomComparison(C,x,y) -> IsoEvidence(C,x,y).
```

Later:

```text
hom_comparison_to_omega
  : HomComparison(C,x,y) -> OmegaEquiv(C,x,y).
```

`ProfComparison` is mathematically the specialization to:

```text
C := Prof_cat(A,B).
```

It should not be migrated immediately. First prove that the generic owner
reproduces:

- dedicated pointwise push/pull beta/eta;
- selected-arrow/evidence agreement;
- generic higher action through Yoneda;
- the warning behavior needed by the current profunctor consumers.

Only then decide whether `ProfComparison` becomes a transparent alias, a
bridge, or a retained specialized stable projection.

## Incremental Constructor Closure

Constructor computation should follow semantic ownership:

| Constructor | Initial undirected owner | First computational target |
| --- | --- | --- |
| `Path_cat(A)` | existing equality and `Path_cat` | projection/extraction of paths before classifier collapse |
| `Op_cat(C)` | object identity plus reversed homs | orientation-preserving reversal `OmegaEquiv(C,x,y) -> OmegaEquiv(Op C,y,x)` |
| `Product_cat(A,B)` | Sigma/product path view | component equivalences |
| `Sigma_cat(E)` | `SigmaPathView` plus family `PathOver` | base/fibre path projections |
| `Pi_grpd(A,B)` | `PiPathView` | related-input path action |
| `Functor_cat(A,B)` | transformations and target univalence | natural pointwise equivalence |
| `Catd_cat(K)` | inherited `Functor_cat(K,Cat_cat)` | no duplicate owner initially |
| `Prof_cat(A,B)` | inherited `Catd_cat(A^op x B)` | only when weak representability consumes it |
| `Cat_cat` | category equivalence | generic interface before computation |

Suggested order:

```text
reflexivity;
PathOver;
Core inclusion and functor-owned path_to_hom;
Sigma/Product path views;
groupoid Pi formation;
TypeEquiv;
groupoid coercion/univalence;
Yoneda and HomComparison;
primitive recursive OmegaEquiv;
Path_cat extraction helpers;
Op_cat OmegaEquiv reversal;
Product categorical closure;
Functor/Catd/Prof closure;
global Cat univalence policy;
Cat_cat-specific computation last.
```

Constructors without specialized laws remain well-formed but stuck.

The first `Path_cat(A)` slice should not attempt to rewrite the whole
classifier `OmegaEquiv(Path_cat A,x,y)` to `x = y`. It is mathematically enough
for the first skeleton to expose the path carried by equivalence or ordinary
isomorphism evidence:

```text
path_cat_omega_path(e) := omega_equiv_to(e) : x = y;
path_cat_iso_path(i)   := iso_evidence_to(i) : x = y.
```

For `Op_cat(C)`, the safest first orientation is:

```text
omega_equiv_op(e : OmegaEquiv(C,x,y))
  : OmegaEquiv(Op_cat(C),y,x).
```

This preserves the forward arrow as `omega_equiv_to(e)` after the opposite
hom reduction. The required conversion goes through the existing primitive
`Hom_cat` rule:

```text
Hom(Op_cat C,y,x)
  := Obj(Hom_cat(Op_cat C,y,x))
   ↪ Obj(Hom_cat(C,x,y))
  := Hom(C,x,y).
```

A 2026-06-24 correction: the earlier failed probe was only the invalid helper:

```text
Hom(Op_cat C,x,y) ↪ Hom(C,y,x)
```

because `Hom` is a transparent defined symbol headed by `≔`. That helper is
unnecessary. An owning-position full-file probe confirmed the direct
`omega_equiv_op` destructor rules with and without warnings. The promoted
slice computes the forward arrow, inverse destructors, and recursive cells:

```text
omega_equiv_to(omega_equiv_op e)        ↪ omega_equiv_to(e);
omega_equiv_left_inv(omega_equiv_op e)  ↪ omega_equiv_right_inv(e);
omega_equiv_right_inv(omega_equiv_op e) ↪ omega_equiv_left_inv(e);
omega_equiv_left_cell(omega_equiv_op e) ↪ omega_equiv_right_cell(e);
omega_equiv_right_cell(omega_equiv_op e) ↪ omega_equiv_left_cell(e).
```

Warning classification: promoting these rules raises the warning-enabled
inventory from 1,119 to 1,134 warnings, all as critical-pair diagnostics. The
new families are the expected overlaps between `omega_equiv_op` destructors
and existing constructor reductions for `Op_cat(Op_cat _)`, `Op_cat(Path_cat
_)`, and `Op_cat(Terminal_cat)`. They are not treated as a veto because the
rules are the intended normal form and the active checks/CI pass.

The alternative target `OmegaEquiv(Op_cat(C),x,y)` would force the forward
arrow to be one of the inverse destructors and should be treated as a later
derived operation.

For `Product_cat(A,B)`, the first categorical closure is the explicit pair
case:

```text
omega_equiv_product
  (eA : OmegaEquiv(A,x0,x1))
  (eB : OmegaEquiv(B,y0,y1))
  : OmegaEquiv(Product_cat(A,B),(x0,y0),(x1,y1)).
```

The intended runtime computation is componentwise:

```text
omega_equiv_to(omega_equiv_product eA eB)
  ↪ (omega_equiv_to(eA), omega_equiv_to(eB));
omega_equiv_left_inv(omega_equiv_product eA eB)
  ↪ (omega_equiv_left_inv(eA), omega_equiv_left_inv(eB));
omega_equiv_right_inv(omega_equiv_product eA eB)
  ↪ (omega_equiv_right_inv(eA), omega_equiv_right_inv(eB));
omega_equiv_left_cell(omega_equiv_product eA eB)
  ↪ omega_equiv_product(omega_equiv_left_cell(eA), omega_equiv_left_cell(eB));
omega_equiv_right_cell(omega_equiv_product eA eB)
  ↪ omega_equiv_product(omega_equiv_right_cell(eA), omega_equiv_right_cell(eB)).
```

This slice targets `Struct_sigma`/`Product_pair` objects whose components are
visible. Opaque product objects and product eta can remain later refinements;
existing product projection rules already expose many opaque component
consumers without forcing broad eta expansion.

2026-06-24 implementation status: promoted. A full-file owning-position probe
confirmed the explicit-pair `omega_equiv_product` symbol, reflexive collapse,
componentwise forward/inverse destructors, and recursive left/right cell
destructors. The active regression checks cover formation, component
projection of forward/inverse destructors, reflexive collapse, and both
recursive cell equations. Warning summary after promotion remains 1,134
warnings, so the Product closure adds no warning-count delta beyond the
previous `Op_cat` inventory.

## Rewrite And Unification Discipline

### Runtime Rewrite Candidates

Prefer runtime rules for:

```text
PathOver(...,refl,...);
path-view projections of explicit reflexive/constructor data;
coe_grpd(refl,...);
coe_grpd(ua_grpd(e),a);
omega_equiv_to(omega_equiv_refl(x));
dedicated HomComparison push/pull beta/eta;
canonical constructor closure with one visible owner.
```

### Proof-Time Candidates

Prefer propositional evidence or narrowly typed `unif_rule` for:

```text
encode/decode agreement of path views;
selected comparison arrows versus evidence projections;
associativity/bracketing;
idtoequiv/ua coherence not needed at runtime;
semantic aliases whose two rigid heads should elaborate together.
```

### Prohibited Initial Rules

Do not initially add:

```text
arbitrary equivalence evidence -> computational comparison;
generic inverse cancellation under comp_fapp0;
both directions of idtoequiv/equivtoid runtime cancellation;
rewrites that identify arbitrary category objects from equivalence evidence;
evidence irrelevance for paths or equivalences;
constructor-specific ordinary functor identity/composition laws;
outer projection directly over an independently active equality/composition cut.
```

Every promoted rule must be checked at its owning position, not only in an
append-only import probe.

## Implementation Phases

### Phase 0: Documentation And Baseline

1. Keep this report as the active design owner.
2. Record the baseline warning inventory and typecheck timings before each
   promoted slice.
3. Add no global univalence axiom during exploratory path-view work.

### Phase 1: Path Utilities

1. Probe `PathOver` as a transparent semantic definition.
2. Add reflexivity, symmetry, composition, and dependent `ap` only as required.
3. Add `Core_incl_func(C)` and define public `path_to_hom` through its arrow
   action.
4. Add only the measured reflexivity projection bridge.
5. Verify composition through generic `fapp1` functoriality.
6. Probe proof-time agreement with the J-defined semantic reference.

Acceptance:

```text
PathOver(P,refl,u,v) computes to u=v;
eq_apd computes on reflexivity;
path_to_hom(refl) computes to id;
path_to_hom(q) o path_to_hom(p) folds through generic functoriality;
no specialized path-to-arrow composition rule is installed;
no change to the global equality classifier;
warning-enabled full-file delta classified.
```

### Phase 2: Groupoid Pi And Type Equivalence

1. Add `Pi_grpd` with only `τ` decoding.
2. Define `Function_grpd`, `IsContr`, `HFiber`, `IsEquivMap`, and `TypeEquiv`.
3. Derive forward, inverse, inverse paths, and reflexivity.
4. Defer symmetry and composition until Sigma/fibre path algebra is ready.
5. Keep observational Pi paths deferred.

Acceptance:

```text
TypeEquiv has no primitive strict cancellation;
the inverse is selected from contractible fibres;
identity typechecks without universe-path axioms;
symmetry and composition are explicitly deferred rather than postulated;
no dependency on unfinished Grpd_cat composition.
```

### Phase 3: Groupoid Univalence Probe

1. Add stable `coe_grpd`.
2. Define `idtoequiv_grpd` by equality induction.
3. State `GrpdUnivalence` as equivalence of the canonical map.
4. Add stable operational `ua_grpd` parameterized by that capability.
5. Promote `coe_grpd(ua_grpd(e),a) -> e.to(a)` as a separate operational
   computation rule.
6. Keep other inverse laws propositional.

Acceptance:

```text
reflexive coercion computes;
the univalence capability and ua operation typecheck;
univalence coercion computes to the selected forward map through the explicit
  operational rule;
subject reduction and warning-enabled checks pass;
the report labels ua_grpd as an operational assumption.
```

### Phase 4: Observational Constructor Views

1. Add Sigma/Product path views.
2. Add encode/decode and reflexivity projections. The first Sigma slice has
   promoted the view, projections, reflexive view, reflexive encode,
   componentwise intro, and constructor-reflexive decode.
3. Add Pi/function path views only after `Pi_grpd`. The first Pi slice has
   promoted the related-input view, application, reflexive view, and reflexive
   encode; function-extensionality decode remains deferred.
4. Do not make generic encode/decode cancellation judgmental without a
   consumer.

### Phase 5: Yoneda And Generic Comparison

1. Promote a transparent `Yoneda_cov_func` alias if useful.
2. Probe whole natural-transformation ownership for `HomComparison`.
3. Add dedicated pointwise beta/eta.
4. Add the `IsoEvidence` forgetful map.
5. Compare specialization to `ProfComparison` without migrating it.

### Phase 6: Omega Equivalence

0. Optionally promote the 1-categorical staging layer
   `idtoiso_cat`/`CatIsoUnivalence`/`cat_iso_univalence` first. This shows the
   ordinary univalent-category approximation while the recursive
   `OmegaEquiv` skeleton is being installed.
1. Promote the probed primitive classifier and recursive destructors in an
   owning-position full-file copy.
2. Promote the canonical reflexivity generator and recursive reflexivity
   cells.
3. Derive `idtoequiv_cat` by equality induction.
4. Add symmetry, composition, functorial image, and selected constructor
   closures incrementally.
5. Add no unrestricted introduction record.
6. Keep optional general corecursion/productivity and terminal-coalgebra
   semantics as separate research/implementation tasks.

### Phase 7: Categorical Univalence

1. Define explicit `CatUnivalence(C)` as equivalence of canonical
   `idtoequiv_cat`.
2. Select `equivtoid_cat` and add only required coherence computation.
3. Add instances for `Path_cat`, `Op_cat`, and products.
4. Adopt global `cat_univalence(C)` as the intended operational foundation.
5. Record the immediate `Cat_cat` instance while leaving universe-specific
   computation deferred.

### Phase 8: Weak Representability Integration

1. Define weak/path representability separately from `IsoEvidence` and
   computational comparison.
2. Map `HomComparison` and `ProfComparison` into `OmegaEquiv`.
3. Use `CatUnivalence(Prof_cat(A,B))` to obtain paths.
4. Compare projected maps with the existing computational weighted-limit API.
5. Do not replace `ProfComparison` unless the path-owned projections compute
   without theorem-specific rules.

## Side-Task Ledger

| ID | Status | Depends on | Resume trigger | Next action |
| --- | --- | --- | --- | --- |
| `UNI-PATHOVER` | first semantic slice promoted | none | Sigma/Product path views begin | Add `pathover_sym`/`pathover_comp` only when consumed; keep stable-head variant as a fallback if transparent unfolding becomes brittle. |
| `UNI-EQ-ELIM` | `ind_eqr` primitive; `ind_eq` derived and builtin route preserved | none | singleton eliminator syntax is consumed | Add derived `ind_eqr_sig` only if it improves readability; keep one primitive owner. |
| `UNI-SIGMA-IND` | fixed-parameter `sigma_ind` promoted; relation to generated `ind_τΣ_` documented deferred | none | proof-mode or generated eliminator normal forms become visible consumers | Either derive `sigma_ind` from richer motive infrastructure or add a narrow comparison after probing. |
| `UNI-PATH-HOM` | functor-owned map promoted | none | proof-time J agreement is needed | Probe propositional or narrow unification agreement between `path_to_hom` and the J-defined reference. |
| `UNI-CORE-INCL` | promoted with object and reflexivity projection rules | none | a consumer needs more core-inclusion computation | Monitor stable-projection joins; do not add a specialized composition rule. |
| `UNI-GRPD-PI` | promoted | none | further Pi equality/univalence begins | Use the promoted related-input Pi path view; defer function-extensionality decode until consumed. |
| `UNI-TYPE-EQUIV` | first contractible-fibre slice promoted | promoted `UNI-GRPD-PI` | symmetry/composition are consumed | Probe the required Sigma/fibre path algebra; do not postulate strict cancellation. |
| `UNI-UA-GRPD` | first computational rule and constructor-equivalence skeleton promoted | `UNI-TYPE-EQUIV` | more constructor-specific univalence computation is consumed | Extend closure beyond Product, same-base Sigma, and same-domain Pi; keep inverse cancellation propositional unless consumed. |
| `UNI-SIGMA-VIEW` | componentwise intro and constructor-reflexive decode promoted | `UNI-PATHOVER` | Sigma-constructor univalence or eta is consumed | Keep generic encode/decode cancellation propositional unless a consumer needs judgmental beta/eta. |
| `UNI-PI-VIEW` | related-input reflexive view/encode promoted | `UNI-PATHOVER`, `UNI-GRPD-PI` | function extensionality or Pi-constructor univalence is consumed | Probe `PiPathView -> f = g` decode separately; do not add eta/cancellation rules speculatively. |
| `UNI-CTOR-EQUIV` | forward-computing Product, same-base Sigma, and same-domain Pi skeleton promoted | `UNI-UA-GRPD`, `UNI-SIGMA-VIEW`, `UNI-PI-VIEW` | full proof witnesses or base-changing constructors are consumed | Derive or refine `*_is_equiv` witnesses from observational path algebra; add base-changing Sigma/Pi only after transport/pathover computation is stable. |
| `UNI-YONEDA` | semantic feasibility confirmed | none | a generic comparison consumer is selected | Promote transparent alias only if it improves ownership. |
| `UNI-HOM-COMP` | proposed | `UNI-YONEDA` | generic comparison work begins | Probe transformation-owned naturality and dedicated point beta/eta. |
| `UNI-CAT-ISO` | promoted provisional 1-truncated staging layer | promoted `UNI-PATH-HOM`, existing `IsoEvidence` | 1-categorical univalence computations are consumed | Restrict or replace by `IsOneTruncatedCat(C) -> CatIsoUnivalence(C)`/`OneCat` later; do not identify it with final `OmegaEquiv`. |
| `UNI-OMEGA` | primitive recursive interface and reflexivity promoted | promoted path utilities | more omega-equivalence computation is consumed | Continue selected constructor closures incrementally; `Path_cat`, `Op_cat`, and explicit `Product_cat` closure are active before functor/category-universe computation. |
| `UNI-PATH-CAT-CLOSURE` | promoted 2026-06-24 | promoted `UNI-OMEGA` | Path-category equivalence computation is consumed | `path_cat_omega_path` and `path_cat_iso_path` extract paths and compute on reflexivity; do not collapse the classifier yet. |
| `UNI-OP-CAT-CLOSURE` | promoted 2026-06-24 | promoted `UNI-OMEGA` | opposite-category equivalence computation is consumed | `omega_equiv_op : OmegaEquiv(C,x,y) -> OmegaEquiv(Op_cat C,y,x)` computes through forward/inverse/cell destructors; same-orientation derived opposite equivalence remains later. |
| `UNI-PRODUCT-CAT-CLOSURE` | promoted 2026-06-24 | promoted `UNI-OMEGA`, product category core | product-category omega-equivalence computation is consumed | `omega_equiv_product` handles explicit product pairs componentwise, including recursive cells; opaque product-object eta remains later. |
| `UNI-EQ-COMPUTE` | proposed 2026-06-25 | `UNI-SIGMA-VIEW`, `UNI-PATHOVER` | direct computational equality is consumed | Migrate `=` to `injective`; make Sigma equality reduce to `SigmaPathView`; keep `eq_refl` eliminator-visible and add projection rules instead of rewriting `eq_refl` itself. |
| `UNI-OPERATIONAL-DECODE` | proposed 2026-06-25 | `UNI-EQ-COMPUTE`, `UNI-OMEGA`, global univalence policy | equivalence-to-path computation is consumed | Add stable decoder heads such as `omega_equiv_path`; compute by constructor cases; relate later to `equivtoid_cat`/`isotoid_cat`/`ua_grpd` inverse selections. |
| `UNI-OMEGA-COREC` | deferred/optional | `UNI-OMEGA` | a general user-facing corecursor is required | Specify productivity or external terminal-coalgebra semantics. |
| `UNI-CAT-CAP` | promoted | `UNI-OMEGA` | categorical inverse/path computation is consumed | Keep `equivtoid_cat` as capability projection; add cancellation/coherence only for concrete consumers. |
| `UNI-CAT-GLOBAL` | promoted as explicit operational assumption | `UNI-CAT-CAP` | constructor-specific category univalence is consumed | Add constructor closure entries case by case; keep the global assumption visible. |
| `UNI-CAT-SELF` | interface promoted through global policy; computation deferred | `UNI-CAT-GLOBAL` | universe-specific computation is consumed | Add `Cat_cat`-specific computation only when a concrete consumer needs it; keep model justification separate. |
| `UNI-PROF-WEAK` | deferred | `UNI-CAT-CAP`, `UNI-HOM-COMP` | weak representability has a concrete theorem consumer | Compare weak/path and computational weighted limits. |

## Feasibility Assessment

| Slice | Feasibility | Main risk |
| --- | --- | --- |
| `PathOver` formation/reflexivity | promoted | transport orientation and unwanted unfolding in later path views |
| dependent ap | reflexive computation promoted | stable public normal form beyond reflexivity |
| functor-owned `path_to_hom` reflexivity | promoted | proof-time agreement with J semantics |
| strict `Core_incl_func` composition | promoted through generic functoriality | future projection-ladder consumers |
| `Pi_grpd` formation/decoding | promoted | future interaction with observational Pi equality |
| contractible-fibre `TypeEquiv` formation/inverse/reflexivity | promoted | symmetry/composition require more Sigma-fibre path algebra |
| Sigma path-view intro/decode | promoted at constructor-reflexive boundary | generic eta/cancellation remain overlap-sensitive |
| Product path views | high | encode/decode orientation and projection overlap |
| observational Pi path | first related-input slice promoted | function-extensionality decode and higher substitution |
| `coe_grpd` and canonical `idtoequiv_grpd` on reflexivity | promoted | no non-reflexive computation without univalence capability |
| `GrpdUnivalence` capability and stable `ua_grpd` operation | promoted | inverse/cancellation coherence remains propositional/deferred |
| `coe_grpd(ua(e))` | promoted | constructor-specific `e.to` computation still needed |
| Product/Sigma/Pi constructor equivalence skeleton | promoted for Product, same-base Sigma, and same-domain Pi | `IsEquivMap` witnesses are capabilities until Sigma/Pi path algebra can derive them |
| transparent Yoneda embedding | confirmed | naming/normal-form choice only |
| generic `HomComparison` | medium-high | avoiding generic `comp_fapp0` accumulation |
| 1-categorical `CatIsoUnivalence` staging | promoted | ordinary iso/path coherence beyond reflexivity remains capability-driven |
| primitive recursive `OmegaEquiv` interface | promoted with reflexivity | closure operations and constructor-specific destructor computation |
| general `OmegaEquiv` corecursor/productivity checking | deferred/optional | Lambdapi has no native generated codata checker |
| explicit `CatUnivalence(C)` | promoted | coherence and constructor ownership |
| global univalence for every `C` | promoted as operational assumption | model/universe interpretation |
| `Cat_cat` self-univalence interface | promoted through global policy | constructor-specific computation remains deferred |
| semantic justification of `Cat_cat : Cat_cat` | outside near-term kernel implementation | universe stratification/consistency |

The operational architecture is feasible across all major layers. The
remaining uncertainty concerns completeness of constructor-specific
computation, optional general coinduction/productivity infrastructure, and
semantic justification of the self-universe—not the basic availability of
computational groupoid univalence, recursive categorical equivalence, or a
global categorical-univalence interface.

## Acceptance Criteria

The first foundational milestone is now complete:

```text
PathOver and dependent ap are active;
Pi_grpd decodes;
TypeEquiv is defined from contractible fibres;
type_equiv_refl computes through to/from/left/right;
idtoequiv_grpd computes on reflexivity;
coe_grpd computes on reflexivity;
no generic strictification or ordinary-composition cancellation is installed;
make check and warning-enabled owning-position checks pass.
```

The first computational-univalence milestone is complete when:

```text
ua_grpd has an explicit foundational status;
GrpdUnivalence is stated as equivalence of canonical idtoequiv_grpd;
coe_grpd(ua_grpd(U,e),a) computes to type_equiv_to(e,a);
Sigma/Product path views compute on reflexivity;
inverse coherence not needed at runtime remains propositional;
constructor views can remain stuck outside implemented cases.
```

The first constructor-specific computational-univalence skeleton is complete
when:

```text
Product_grpd decodes as a constant-family Sigma;
product_type_equiv computes on paired inputs;
sigma_type_equiv_same_base computes on Sigma constructors;
pi_type_equiv_same_domain computes on application;
coe_grpd(ua_grpd(U,e),a) exposes those same constructorwise maps;
the equivalence witnesses are isolated proof capabilities, not runtime
rewrite owners;
full base-changing Sigma/Pi and derived fibre-contractibility proofs remain
deferred until the observational path algebra can support them.
```

The first categorical-univalence skeleton is complete when:

```text
idtoiso_cat maps reflexive paths to iso_evidence_refl;
CatIsoUnivalence and global cat_iso_univalence are active staging interfaces;
OmegaEquiv has primitive destructors;
omega_equiv_refl computes through to/left/right destructors and recursive
left/right cells;
path_cat_omega_path and path_cat_iso_path extract paths and compute on
reflexivity;
omega_equiv_op closes omega-equivalence under opposites and computes through
forward, inverse, and recursive-cell destructors;
idtoequiv_cat maps reflexive paths to omega_equiv_refl;
CatUnivalence, equivtoid_cat, and global cat_univalence are active;
Cat_cat receives the global interface;
broader constructor-specific categorical computation and strict cancellation
remain deferred.
```

The first categorical milestone is complete when:

```text
path_to_hom computes on reflexivity;
Core_incl_func composition is owned by generic fapp1 functoriality;
Yoneda_cov_func is owned by hom_int(id_{C^op});
HomComparison beta/eta uses dedicated heads;
HomComparison forgets to IsoEvidence;
the primitive recursive OmegaEquiv interface and reflexivity compute;
idtoequiv_cat is canonical and independent of CatUnivalence(C);
CatUnivalence(C) states that idtoequiv_cat is an equivalence;
Cat_cat receives the global interface if adopted, with computation separately
classified.
```

The path-owned representability milestone is complete only when:

```text
Prof_cat univalence is available through inherited semantic owners or a
documented specialized bridge;
comparison-to-path-to-comparison projections recover nonidentity maps;
weak/path representability remains distinct from IsoEvidence and
ProfComparison;
right-adjoint preservation introduces no theorem-specific path fold.
```

## Primary References

The project is not required to reproduce any external system, but the following
primary materials inform the design:

- Thorsten Altenkirch, Ambrus Kaposi, and Michael Shulman,
  “Towards Higher Observational Type Theory,” TYPES 2022:
  <https://akaposi.github.io/pres_types_2022.pdf>.
- Michael Shulman, “Towards an Implementation of Higher Observational Type
  Theory,” 2024:
  <https://home.sandiego.edu/~shulman/papers/running-hott.pdf>.
- Thorsten Altenkirch, Ambrus Kaposi, Michael Shulman, Elif Usküplü, and
  collaborators, “From parametricity to identity types,” TYPES 2025:
  <https://msp.cis.strath.ac.uk/types2025/slides/TYPES2025-slides60.pdf>.
- The corresponding TYPES 2025 abstract, including the higher-coinductive
  fibrancy interface:
  <https://msp.cis.strath.ac.uk/types2025/TYPES2025-book-of-abstract.pdf>.
- Thorsten Altenkirch, Yorgo Chamoun, Ambrus Kaposi, and Michael Shulman,
  “Internal parametricity, without an interval”:
  <https://arxiv.org/abs/2307.06448>.
- Michael Shulman's Agda HOTT experiment:
  <https://github.com/mikeshulman/ohtt>.
- Narya:
  <https://github.com/gwaithimirdain/narya>.

The external state of HOTT remains work in progress. In particular, the 2025
material reports substantial type-former fibrancy progress while fibrancy of
the fibrant universe remains unresolved. For emdash this is evidence to defer
universe-specific computational closure and semantic claims; it does not
prevent adopting the project's global operational univalence interface.
