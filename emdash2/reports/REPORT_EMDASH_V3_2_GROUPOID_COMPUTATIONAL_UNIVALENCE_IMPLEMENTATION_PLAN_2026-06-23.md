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
`GrpdUnivalence`, and `ua_grpd` as a selector from that capability. The
computational law `coe_grpd(ua_grpd(U,e),a) -> type_equiv_to(e,a)` is not yet
installed; it remains the next explicit operational-univalence decision. No
`OmegaEquiv`, `CatUnivalence`, or generic `HomComparison` symbol from this
report has yet been promoted. The existing equality, `Path_cat`,
`IsoEvidence`, and `ProfComparison` implementations remain active. Focused
probes have confirmed derivability of the covariant Yoneda embedding from
`hom_int` over the opposite category. A primitive recursive-destructor
`OmegaEquiv` interface with reflexivity and recursively reflexive inverse
cells has also passed an isolated warning-enabled probe.

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

These corrections are architectural, not merely notational. In particular,
they prevent a chosen pair of conversion functions from competing with the
canonical equality eliminator and prevent ordinary isomorphism evidence from
becoming the accidental definition of homotopy equivalence.

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

The inverse selected from this capability is the univalence operation:

```text
ua_grpd
  : τ(TypeEquiv(A,B)) -> τ(@= Grpd_grpd A B).
```

The first desired computational-univalence law is:

```text
coe_grpd(ua_grpd(e),a)
  -> type_equiv_to(e,a).
```

This law directly exposes the runtime meaning of univalence. It is preferable
as the initial rule to demanding both generic conversion cancellations:

```text
idtoequiv_grpd(ua_grpd(e)) -> e;
ua_grpd(idtoequiv_grpd(p)) -> p.
```

Those two equations should begin as propositional coherence and may later be
tested as narrowly typed unification rules. Installing both as runtime
rewrites risks the same projection/cancellation competition seen in the
rejected `StrictIso` designs.

The capability and the runtime coercion law have different roles.
`GrpdUnivalence` states the semantic equivalence; the
`coe_grpd(ua_grpd(e),a)` rule chooses the intended computational presentation.
Both are operational foundational assumptions unless and until they are
derived from a fibrancy/observational universe construction.

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
| `Path_cat(A)` | existing equality and `Path_cat` | reflexive/path algebra only |
| `Op_cat(C)` | object identity plus reversed homs | reverse `OmegaEquiv` projections |
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
Op/Product categorical closure;
Functor/Catd/Prof closure;
global Cat univalence policy;
Cat_cat-specific computation last.
```

Constructors without specialized laws remain well-formed but stuck.

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
4. Select provisional `ua_grpd` from that capability.
5. Probe `coe_grpd(ua_grpd(e),a) -> e.to(a)` as a separate operational
   computation rule.
6. Keep other inverse laws propositional.

Acceptance:

```text
reflexive coercion computes;
the univalence capability and ua selector typecheck;
univalence coercion computes to the selected forward map only after the
  explicit operational rule is adopted;
subject reduction and warning-enabled checks pass;
the report labels ua_grpd as an operational assumption.
```

### Phase 4: Observational Constructor Views

1. Add Sigma/Product path views.
2. Add encode/decode and reflexivity projections.
3. Add Pi/function path views only after `Pi_grpd`.
4. Do not make generic encode/decode cancellation judgmental without a
   consumer.

### Phase 5: Yoneda And Generic Comparison

1. Promote a transparent `Yoneda_cov_func` alias if useful.
2. Probe whole natural-transformation ownership for `HomComparison`.
3. Add dedicated pointwise beta/eta.
4. Add the `IsoEvidence` forgetful map.
5. Compare specialization to `ProfComparison` without migrating it.

### Phase 6: Omega Equivalence

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
| `UNI-GRPD-PI` | promoted | none | observational Pi equality begins | Add related-input Pi path view only after Sigma path views stabilize. |
| `UNI-TYPE-EQUIV` | first contractible-fibre slice promoted | promoted `UNI-GRPD-PI` | symmetry/composition are consumed | Probe the required Sigma/fibre path algebra; do not postulate strict cancellation. |
| `UNI-UA-GRPD` | capability and selector promoted; computation rule deferred | `UNI-TYPE-EQUIV` | computational univalence law is needed | Decide whether `coe_grpd(ua_grpd(U,e),a)` is an explicit operational axiom/rule or waits for a fuller observational universe construction. |
| `UNI-SIGMA-VIEW` | unblocked by first `UNI-PATHOVER` slice | `UNI-PATHOVER` | Phase 4 begins | Probe encode/decode and reflexivity projections. |
| `UNI-PI-VIEW` | blocked | `UNI-PATHOVER`, `UNI-GRPD-PI` | Sigma view and Pi formation stable | Define related-input observational Pi path. |
| `UNI-YONEDA` | semantic feasibility confirmed | none | a generic comparison consumer is selected | Promote transparent alias only if it improves ownership. |
| `UNI-HOM-COMP` | proposed | `UNI-YONEDA` | generic comparison work begins | Probe transformation-owned naturality and dedicated point beta/eta. |
| `UNI-OMEGA` | primitive recursive interface feasibility confirmed | promoted path utilities | Phase 6 promotion begins | Run owning-position probe; add reflexivity, then closure operations incrementally. |
| `UNI-OMEGA-COREC` | deferred/optional | `UNI-OMEGA` | a general user-facing corecursor is required | Specify productivity or external terminal-coalgebra semantics. |
| `UNI-CAT-CAP` | architecturally ready after `UNI-OMEGA` promotion | `UNI-OMEGA` | Canonical `idtoequiv_cat` lands | Define `CatUnivalence(C)` as `IsEquivMap(idtoequiv_cat)`. |
| `UNI-CAT-GLOBAL` | design decision adopted; implementation awaits capability | `UNI-CAT-CAP` | `CatUnivalence` interface lands | Add the global operational instance for every `C : Cat`. |
| `UNI-CAT-SELF` | operational instance follows from global policy; computation deferred | `UNI-CAT-GLOBAL` | global `cat_univalence` is adopted | Record the immediate instance; add universe-specific computation only when consumed. |
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
| Sigma/Product path views | high | encode/decode orientation and projection overlap |
| observational Pi path | medium | related-input dependency and higher substitution |
| `coe_grpd` and canonical `idtoequiv_grpd` on reflexivity | promoted | no non-reflexive computation without univalence capability |
| `GrpdUnivalence` capability and `ua_grpd` selector | promoted as interface | computational `coe(ua)` law still needs explicit operational status |
| `coe_grpd(ua(e))` | medium syntactically | foundational status and rewrite overlap |
| transparent Yoneda embedding | confirmed | naming/normal-form choice only |
| generic `HomComparison` | medium-high | avoiding generic `comp_fapp0` accumulation |
| primitive recursive `OmegaEquiv` interface | confirmed in isolated probe | owning-position promotion and closure operations |
| general `OmegaEquiv` corecursor/productivity checking | deferred/optional | Lambdapi has no native generated codata checker |
| explicit `CatUnivalence(C)` | high after Omega promotion | coherence and constructor ownership |
| global univalence for every `C` | operationally straightforward, foundationally assumed | model/universe interpretation |
| `Cat_cat` self-univalence interface | immediate under global policy | constructor-specific computation remains deferred |
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
