# EMDASH v3.2 Groupoid And Computational Univalence Implementation Plan

Date: 2026-06-23
Last reviewed: 2026-06-23

Plan-ID: EMDASH-V3-2-GROUPOID-COMPUTATIONAL-UNIVALENCE-2026-06-23
Depends-On: none
Supersedes: EMDASH-V3-2-PROFUNCTOR-REPRESENTABILITY-2026-06-19 (univalence track only)
Side-Task-Ledger: #side-task-ledger
Infinity-Codex-Origin: infinity-codex:019ef47a-919d-77b3-93f9-7af7a7848c73:019ef4a2-2e56-7513-9c26-878b2df22426
Infinity-Codex-Decision-Responses: infinity-codex:019ef47a-919d-77b3-93f9-7af7a7848c73:019ef4a2-2e56-7513-9c26-878b2df22426

Status: active architecture and feasibility plan. No groupoid-univalence,
`TypeEquiv`, `OmegaEquiv`, `CatUnivalence`, or generic `HomComparison` symbol
from this report has been promoted to `emdash3_2.lp`. The existing equality,
`Path_cat`, `IsoEvidence`, and `ProfComparison` implementations remain active.
Focused probes have confirmed the transparent `PathOver` and reflexive
`path_to_hom` definitions, the minimal decoded `Pi_grpd` and
contractible-fibre `TypeEquiv` encoding, and derivability of the covariant
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
- avoid requiring full recursive omega-equivalence or universe self-univalence
  before useful lower layers can land.

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
7. Treat full recursive `OmegaEquiv` and `Cat_cat` self-univalence as separate
   feasibility gates, not prerequisites for observational paths or groupoid
   type equivalence.
8. Let `Core_incl_func` and generic `fapp1` functoriality own computational
   path-to-arrow composition. Do not add either orientation of a specialized
   composition rule when the generic owner remains visible.

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

This interface is recursive through hom-categories and therefore
coinductive in character. Lambdapi has no identified native coinductive
declaration mechanism in the current project. The first implementation must
therefore compare:

1. a primitive classifier with recursive destructors and canonical generators;
2. finite-height `OmegaEquiv_n` probes;
3. a 2-categorical approximation;
4. a path-first interface that leaves non-reflexive destructors stuck.

Finite approximations are diagnostic only. They must not silently become the
meaning of `OmegaEquiv`.

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

Constructor-specific instances can then be added incrementally. If the
project later confirms that `Cat` classifies only univalent categories, add:

```text
cat_univalence(C) : CatUnivalence(C).
```

as an explicit global operational axiom or projection from category
structure. Keeping the capability explicit during development has several
advantages:

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

`Cat_cat` self-univalence is the highest-risk instance. Current HOTT work can
construct fibrancy for several type formers while fibrancy of the universe
itself remains open. Emdash should not make `Cat_cat` computation a gate for
lower constructor instances.

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
2-dimensional OmegaEquiv probe;
Op/Product categorical closure;
Functor/Catd/Prof closure;
Cat_cat self-univalence last.
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
3. Derive forward, inverse, inverse paths, reflexivity, symmetry, and
   composition.
4. Keep observational Pi paths deferred.

Acceptance:

```text
TypeEquiv has no primitive strict cancellation;
the inverse is selected from contractible fibres;
identity and composition typecheck without universe-path axioms;
no dependency on unfinished Grpd_cat composition.
```

### Phase 3: Groupoid Univalence Probe

1. Add stable `coe_grpd`.
2. Define `idtoequiv_grpd` by equality induction.
3. State `GrpdUnivalence` as equivalence of the canonical map.
4. Select provisional `ua_grpd` from that capability.
5. Probe `coe_grpd(ua_grpd(e),a) -> e.to(a)`.
6. Keep other inverse laws propositional.

Acceptance:

```text
reflexive coercion computes;
univalence coercion computes to the selected forward map;
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

1. Probe a 2-dimensional approximation.
2. Probe primitive recursive destructors.
3. Select a canonical reflexivity generator.
4. Derive `idtoequiv_cat` by equality induction.
5. Add no general introduction record.
6. Record whether the intended interface is modelled coinductively or remains
   an operational specification.

### Phase 7: Categorical Univalence

1. Define explicit `CatUnivalence(C)` as equivalence of canonical
   `idtoequiv_cat`.
2. Select `equivtoid_cat` and add only required coherence computation.
3. Add instances for `Path_cat`, `Op_cat`, and products.
4. Defer `Cat_cat` self-univalence.
5. Only after universe policy review decide whether to add global
   `cat_univalence(C)`.

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
| `UNI-PATHOVER` | semantic feasibility confirmed | none | implementation begins | Compare transparent and stable owning-position variants; add dependent-ap checks. |
| `UNI-PATH-HOM` | functor-owned computation feasible | none | path-to-arrow implementation begins | Define the public map through `Core_incl_func`; probe proof-time J agreement. |
| `UNI-CORE-INCL` | composition feasibility confirmed in import probe | none | Phase 1 promotion begins | Run owning-position full-file probe with only object and reflexivity projection rules. |
| `UNI-GRPD-PI` | formation/decoding feasibility confirmed | none | `TypeEquiv` promotion begins | Probe the decoder at its intended owning position. |
| `UNI-TYPE-EQUIV` | semantic formation confirmed | promoted `UNI-GRPD-PI` | Pi decoder lands | Derive inverse selection, inverse paths, symmetry, and composition. |
| `UNI-UA-GRPD` | blocked on `UNI-TYPE-EQUIV` | `UNI-TYPE-EQUIV` | Type equivalence algebra passes | Define universe-univalence capability and probe `coe_grpd(ua(e))`. |
| `UNI-SIGMA-VIEW` | blocked on `UNI-PATHOVER` | `UNI-PATHOVER` | Path-over normal form selected | Probe encode/decode and reflexivity projections. |
| `UNI-PI-VIEW` | blocked | `UNI-PATHOVER`, `UNI-GRPD-PI` | Sigma view and Pi formation stable | Define related-input observational Pi path. |
| `UNI-YONEDA` | semantic feasibility confirmed | none | a generic comparison consumer is selected | Promote transparent alias only if it improves ownership. |
| `UNI-HOM-COMP` | proposed | `UNI-YONEDA` | generic comparison work begins | Probe transformation-owned naturality and dedicated point beta/eta. |
| `UNI-OMEGA` | unresolved foundational design | path utilities | 2-categorical consumer or weak representability begins | Compare recursive destructors with finite-height probes. |
| `UNI-CAT-CAP` | blocked on `UNI-OMEGA` | `UNI-OMEGA` | Canonical `idtoequiv_cat` is available | Define `CatUnivalence(C)` as `IsEquivMap(idtoequiv_cat)`. |
| `UNI-CAT-GLOBAL` | deferred | `UNI-CAT-CAP` | universe interpretation chosen | Decide whether every `C : Cat` receives a global instance. |
| `UNI-CAT-SELF` | deferred/high risk | `UNI-CAT-CAP`, universe policy | lower constructor closure stable | Probe `Cat_cat` only as a separate universe milestone. |
| `UNI-PROF-WEAK` | deferred | `UNI-CAT-CAP`, `UNI-HOM-COMP` | weak representability has a concrete theorem consumer | Compare weak/path and computational weighted limits. |

## Feasibility Assessment

| Slice | Feasibility | Main risk |
| --- | --- | --- |
| `PathOver` formation/reflexivity | confirmed in isolated probe | transport orientation and unwanted unfolding |
| dependent ap | high | stable public normal form and reflexivity computation |
| functor-owned `path_to_hom` reflexivity | confirmed in isolated probe | owning-position overlap audit |
| strict `Core_incl_func` composition | confirmed through generic functoriality | proof-time agreement with J semantics |
| `Pi_grpd` formation/decoding | confirmed in isolated probe | future interaction with observational Pi equality |
| contractible-fibre `TypeEquiv` formation | confirmed in isolated probe | inverse derivation, proof term size, and Sigma-fibre equality |
| Sigma/Product path views | high | encode/decode orientation and projection overlap |
| observational Pi path | medium | related-input dependency and higher substitution |
| `coe_grpd(ua(e))` | medium syntactically | foundational status and rewrite overlap |
| transparent Yoneda embedding | confirmed | naming/normal-form choice only |
| generic `HomComparison` | medium-high | avoiding generic `comp_fapp0` accumulation |
| finite/2D `OmegaEquiv` | medium | choosing a prototype that does not become semantics |
| full recursive `OmegaEquiv` | unresolved | coinductive meaning and productivity |
| explicit `CatUnivalence(C)` | medium after Omega interface | coherence and constructor ownership |
| global univalence for every `C` | foundationally risky | model/universe interpretation |
| `Cat_cat` self-univalence | highest risk | universe fibrancy/stratification |

The architecture is feasible even if full `OmegaEquiv` and `Cat_cat`
self-univalence remain unresolved. The first four phases can provide useful
computational non-directed equality and type equivalence independently.

## Acceptance Criteria

The first foundational milestone is complete when:

```text
PathOver and dependent ap are active;
Pi_grpd decodes;
TypeEquiv is defined from contractible fibres;
idtoequiv_grpd computes on reflexivity;
coe_grpd computes on reflexivity;
no generic strictification or ordinary-composition cancellation is installed;
make check and warning-enabled owning-position checks pass.
```

The first computational-univalence milestone is complete when:

```text
ua_grpd has an explicit foundational status;
GrpdUnivalence is stated as equivalence of canonical idtoequiv_grpd;
coe_grpd(ua_grpd(e),a) computes to type_equiv_to(e,a);
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
a finite or recursive OmegaEquiv interface has a documented semantics;
idtoequiv_cat is canonical and independent of CatUnivalence(C);
CatUnivalence(C) states that idtoequiv_cat is an equivalence;
Cat_cat self-univalence remains separately classified.
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
material reports substantial type-former fibrancy progress while universe
fibrancy remains unresolved. Emdash should use that as risk evidence, not as a
reason to postpone the lower computational layers.
