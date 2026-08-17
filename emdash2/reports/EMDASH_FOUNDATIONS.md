# emdash Foundations

Draft status: this document is a mathematician-facing reading guide for the
current `emdash3_2.lp` theory, its one-way derived native equality-valued hom-action
extension `emdash3_2_eq1_hom_action.lp`, and the transparent evidence-property
and finite-dimension extension `emdash3_2_eq1_evidence_property.lp`. It
presents the intended mathematics in ordinary category/type-theory notation
and deliberately suppresses most Lambdapi rewrite engineering details.
Reusable Nat addition, canonical successor path functor, and sethood live in the one-way
`emdash3_2_nat_arithmetic.lp` module. The walking-endomorphism directed-HIT/
`BNat` presentation and its restricted-CoreIncl spiral specialization live
downstream in `emdash3_2_walking_end_hit.lp` under the July 17 living plan.
The successor-localized Integer, groupoidal Circle HIT and loop-space
calculation, concrete WalkingEnd-to-Circle comparison, and representative
product closure live in the four downstream `emdash3_2_*` modules recorded by
the August 14 groupoidal-closure plan.
The isolated binary-Sum experiment was retired on 2026-07-20 for later
consumer-led redesign; it is not part of the active foundation.

The implementation is still evolving. This note describes the current directed
categorical foundation and the first checked equivalence, profunctor,
directed-inductive, and Eckmann–Hilton staging layers. It is not a finished
proof-assistant surface language, and a named capability interface should not
be read as a completed metatheory.
For parser/comment notation, use
`REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md` as the authority.
The chapter-sized sources under `../book/` develop this mathematics
as exposition, beginning with the WalkingEnd/Nat computation. The book's
evidence register points back to active declarations and checks; the book is
not an additional implementation authority.

## 1. Reading Guide

The central idea is to treat categories, functors, transformations, functorial
families of categories, dependent sums, dependent products, and dependent homs
as one computational theory.

The current one-way libraries carry that theory into local geometry. They
develop Cat-valued presheaves, ordinary sieves and sites, least generated
topologies, and a direct fixed-site Cat-valued sheafification reflector. A
separate universal-property algebraic route constructs rings, localizations,
polynomials, and affine chart computations, then packages assumption-explicit
affine and site-relative schemes and a supplied projective line. Constructed
Cat-valued sheafification must not be conflated with the supplied
commutative-ring structure-sheaf and locality capabilities used in those later
packages.

The notation is intentionally close to dependent type theory:

```text
F : A ⊢ B              ordinary functor
F[x]                    action of F on an object
F[f]                    action of F on an arrow
E : K ⊢ Cat            functorial family of categories over K
E[k]                    fibre category at k
Σ_k E[k]                total category of a family
Π_k E[k]                category of sections of a family
s[k]                    value of a section at k
s[f]                    action of a section over f : x ->^K y
```

The word "directed" matters. The base `K` is a category with real arrows, not
just a type of points. Consequently, pointwise constructions must usually carry
naturality data over base arrows.

### Implementation Reading Note

This document gives the mathematical surface. The Lambdapi file also contains
stable projection heads such as `tapp0_fapp0`, `homd_src_func`,
`fdapp1_int_hom_fapp0`, and `fdapp1_int_cell`. These names are kernel
normalization artifacts: they preserve enough structure for rewrite rules and
higher hom-actions to keep computing.

When planning implementation work, use this document to understand the
mathematics, then use
`REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md` for the rewrite
hygiene and stable-head ownership rules. Do not infer from the surface formula
alone that a new primitive head is needed; first locate the current semantic
owner in `emdash3_2.lp` or, for native equality-valued next-hom preservation
and its groupoidality consumers, `emdash3_2_eq1_hom_action.lp`. Native
equality-valued evidence-property and finite-`NCat` object-truncation theorems live in
`emdash3_2_eq1_evidence_property.lp`. Nat arithmetic/sethood and the concrete
walking-endomorphism construction are owned by their two one-way modules,
rather than by the kernel.
The former D0/D1 and categorical-decoder compatibility material, its seven
self-only examples, and its two-sided legacy OneCat theorem are retired. The
unsuffixed names in this guide denote the native equality-valued API. Native
OneCat structure and the one-way ordinary-isomorphism lift remain; any fully
native two-sided object-equality/isomorphism theorem is optional future work.

## 2. Categories And Hom-Categories

A category `A` has:

```text
Obj(A)                  objects of A
Hom_A(x,y)              category of arrows from x to y
id_x                    identity arrow
g ∘ f                   composition
```

The hom between two objects is itself a category. This is the basic
ω-categorical shape: arrows, higher arrows, and higher comparisons are
represented by iterating `Hom`.

The opposite category reverses homs:

```text
Obj(A^op) = Obj(A)
Hom_{A^op}(x,y) = Hom_A(y,x)
```

There is also a terminal category `1`, whose object and hom data are all
contractible.

## 3. Equality And Path Categories

The theory includes a HoTT-style equality infrastructure at the groupoid/type
level:

```text
x =_A y       : Grpd
refl_x        : x = x
J             equality induction
```

The decoded elementary object layer now also contains Empty, Unit, Bool, and
natural numbers. Their public classifiers and decoded carriers are:

```text
τ(Empty_grpd) = empty       τ(Unit_grpd) = unit
τ(Bool_grpd)  = bool        τ(Nat_grpd)  = nat.
```

Visible Unit, Boolean, and natural-number constructor equality now have the
bounded observational cases

```text
tt = tt       = Unit_grpd
false = false = Unit_grpd       false = true  = Empty_grpd
true  = false = Empty_grpd      true  = true  = Unit_grpd
zero = zero = Unit_grpd         zero = succ(m) = Empty_grpd
succ(n) = zero = Empty_grpd     succ(n) = succ(m) = (n = m).
```

These computations select only the classifier. Closed generic reflexivity
remains `eq_refl Unit_grpd tt`, `eq_refl Bool_grpd false`, or
`eq_refl Bool_grpd true`; Nat reflexivity remains `eq_refl Nat_grpd zero` or
`eq_refl Nat_grpd (succ n)`. These terms are merely typed by the reduced Unit
or predecessor-equality classifier and are not erased to `tt` or
`eq_refl Nat_grpd n`. The generic J beta repeats its category and endpoint on
the rule LHS. This is a subject-reduction guard: distinct elementary paths can
share a reduced classifier, but a foreign, predecessor, or component
reflexivity proof must not trigger a branch indexed by the outer proof. Normal
outer reflexivity still computes through generic J, path symmetry, Core
inclusion, path-category units, and the ordinary/omega categorical encoders
without an elementary-former registry. The alternative proofs receive no
extra endpoint-guarded beta, and no proof-time `unif_rule` identifies the proof
presentations. Open Unit, Boolean, and Nat endpoints retain primitive
equality. These are runtime boundaries, not eta, canonicity, equality-
reflection, or non-derivability theorems.

The Empty, Bool, and Nat eliminator facades are dependent and compute on their
constructors through Lambdapi's generated induction principles. Empty
observational identity, broader no-confusion, higher action for the other
elementary formers, canonicity, and categorical initial or natural-number-
object properties remain separate tasks. The retired Sum former and its
observational/action experiments remain dated plan history rather than an
inactive compatibility API.

The one-way Nat arithmetic extension provides the reusable prerequisites

```text
nat_add(0,n)       = n
nat_add(succ(m),n) = succ(nat_add(m,n))
nat_add(m,0)       = m
```

and proves associativity by native Nat induction. It also constructs
`nat_is_set : IsSetGrpd(Nat_grpd)` internally: nested Nat induction reduces
each visible path classifier to `Unit_grpd` or `Empty_grpd`, whose
proposition-valuedness is supplied by explicit contractibility/elimination
terms. This is genuine truncation evidence, not a conclusion inferred only
from the no-confusion rewrite table. Open addition is not normalized by
commutativity.

### Integer, Circle, And Representative Groupoidal Closure

The set-truncated telescope localization of Nat successor has a transparent
integer-facing presentation. Write `Integer` for its carrier. Its selected
shift and inverse give successor and predecessor, with both inverse laws; Nat
embeds as the nonnegative stages, and the opposite boundary supplies negative
representatives. The inherited set-targeted eliminator is the induction
principle used below. This is one computational localization presentation,
not a second signed-integer syntax or a claim about every possible quotient.

The groupoidal Circle is an opaque one-dimensional HIT with

```text
base : Circle
loop : base = base.
```

Its dependent eliminator computes judgmentally at `base`; its action on
`loop` is an explicit propositional `PathOver` equation. There is still one
primitive equality eliminator, `ind_eqr`. Circle recursion and the more
structured interfaces are derived facades around it rather than competing
notions of `J`.

Circle recursion into the groupoid universe constructs the universal cover
whose fibre at `base` is `Integer` and whose loop monodromy is successor.
Transporting zero defines `encode`; integer-indexed positive and negative loop
powers define `decode`. Endpoint path induction, Integer induction, and
proposition-valued Circle induction establish both round trips. Consequently
the active development contains checked equivalences

```text
TypeEquiv(base = base, Integer)
TypeEquiv(Hom_Circle(base,base), Integer).
```

The directed WalkingEnd comparison sends its generator to `loop`. Every Nat
power maps to the corresponding nonnegative Circle power, and encoding either
directly through Circle or first through the WalkingEnd/Nat normal form gives
the same Integer. This is the concrete completion behavior required by the
current consumer; a generic reflector from categories to groupoids remains a
separate, consumer-gated project.

Products supply a representative closure theorem. The canonical functor

```text
Path_cat(A x B) -> Path_cat(A) x Path_cat(B)
```

is identity on objects and an explicit split/join equivalence on every hom
carrier. For a family `P : A x B -> Grpd`, transport along a paired path agrees
with transport first in `A` then in `B`, and also with the reverse order; the
two comparisons form the expected coherence diamond. Existing structured
displayed transport and structured `PathOut` induction agree propositionally
with the same primitive right-`J` transport. Ordinary Cartesian path induction
therefore settles this ordering question. No Gray tensor, category-head
rewrite, new unification rule, or second equality eliminator is involved.

The Nat extension also exposes successor as an iterable equality action:

```text
NatSucc_func : Path_cat(Nat) -> Path_cat(Nat)
NatSucc_func[n] = succ(n).
```

This is a specialization of the kernel's internal path-category functor

```text
Path_cat_func : Grpd_cat -> Cat_cat.
```

For an ordinary function `f : A -> B`, its first action is
`path_map_func(f) : Path_cat(A) -> Path_cat(B)`. It maps objects by `f`, maps
an equality `p` by `eq_ap(f,p)`, and retains the complete next-hom functor.
For a function equality `h : f = g`, the second action
`path_map_transf(h)` has point component `PiHapply(h,x)` and an iterable
off-diagonal equality action. Thus ordinary equality action is internalized
without reflecting an arbitrary directed cell back into equality.

For every fixed ordinary functor `F : C -> D`, restricted Core inclusion has
an explicit directed naturality square

```text
κ_F : F o CoreIncl_C => CoreIncl_D o path_map_func(F_0),
```

where `F_0(x) = F[x]`. The two boundary functors deliberately do not convert.
The point components of κ are identities on their common diagonal functor,
while the full and capped off-diagonal projections are that diagonal's
iterable action. Thus κ is not globally an identity transfor. This does not
define a global directed `Core : Cat_cat -> Cat_cat`: an arbitrary directed
transfor does not provide equality between its component objects. The semantic
lift

```text
path_lift_func
  : Path(Function(A,Obj(C))) -> Functor(Path_cat(A),C)
```

is composition of the first Path action with postcomposition by
`CoreIncl_C`, not a primitive second implementation. Its equality action and
the explicit κ square construct the exact Nat iteration spiral and retain the
full higher action.

There is now also a restricted equality-local internalization of Core
inclusion. For every category `A`, define recursively

```text
Sk⁼(0,A)       = Core_cat(A)
Obj(Sk⁼(n+1,A)) = Obj(A)
Hom_{Sk⁼(n+1,A)}(x,y) = Sk⁼(n,Hom_A(x,y)).
```

Identities and composition at each retained successor dimension compute as in
`A`; all later dimensions recurse into equality action. The construction acts
simultaneously on ordinary functors and has a recursive inclusion
`Sk⁼(n,A) → A`. In particular,

```text
Cat₁⁼ = Sk⁼(1,Cat_cat)
Hom_{Cat₁⁼}(C,D) = Path_cat(Functor(C,D)).
```

Thus `Cat₁⁼` retains categories and ordinary functors but replaces arbitrary
directed transformations between functors by equality paths. It is not a
universal 1-truncation and does not assert that the functor classifiers are
sets.

On this restricted source, `Core₁(C)=Core_cat(C)` and
`Core₁(F)=PathMap(F₀)` form a genuine functor, and the canonical inclusions are
the object components of

```text
CoreInclTransf : Core₁ => Cat₁⁼Incl.
```

The capped first-hom projection at `F` is the common diagonal functor
`Core(C) → D`, not the naturality 2-cell itself. The separate explicit cell
`core_incl_transf_kappa(F)` compares
`F o CoreIncl_C` with `CoreIncl_D o PathMap(F₀)`. Whiskering this comparison
uses generic functor precomposition. Explicit equality proofs and
equality-induced directed adjustments align associativity and the readable
semantic `PathLift` endpoints without a global reassociation rewrite or a new
proof-time unification rule.

The walking-endomorphism extension is implemented on this infrastructure
through its selected G6 boundary. The former generated-word `walking_end_hom` presentation has
been removed and is not a mathematical foundation for new work. The active
signature is opaque and one-dimensional:

```text
WalkingEnd_cat : Cat
walking_base   : Obj(WalkingEnd_cat)
walking_loop   : Hom(WalkingEnd_cat,walking_base,walking_base)

walking_end_is_one_cat
  : IsNCat(1,WalkingEnd_cat).
```

The last field means that each hom-category is discrete; it does not make
`WalkingEnd_cat` itself discrete and does not make the generating loop
invertible. The elimination interface is contextual. Given directed families
`R,D : WalkingEnd_cat -> Cat`, a base functor `u : R(base) -> D(base)`, and a
structured loop cell

```text
D(loop) o u => u o R(loop),
```

it constructs `ind^d(R,D,u,sigma) : Functord(R,D)`, with judgmental base and
loop computation. This single whole-HIT eliminator supplies action at every
opaque arrow; there is no separate Hom datatype or special arrow eliminator.
The derived section computes at its canonical `piapp0` and `piapp1`
observers, and the ordinary constant recursor also computes at its literal
base and loop observers through narrow projection-order clauses. These are two
semantic constructor betas exposed at four necessary observers, not new
identity or composition owners. For an open composite `loop o p`, generic
strict functoriality and the literal loop beta instead yield an ordinary
equality theorem; no custom runtime bridge or unification rule is used.

The transparent family `walking_Code_catd` sends the opaque base to
`Path_cat(Nat)` and the literal loop to `NatSucc_func`. Together with the
based representable and the power functor it constructs the exact directed
spiral. Its canonical point equation reduces to reflexivity. The final
endpoint-adjusted representable presentation intentionally remains under the
generic stable-postcomposition owner instead of reducing to a raw identity;
that is a normal-form boundary, not a missing HIT beta.

The restricted construction supplies the selected explicit-κ form

```text
PathLift(step) o κₗ.
```

Here κ-left is genuine generic whiskering of the explicit square, including
its directed endpoint adjustments. The right comparison is judgmentally the
identity by ordinary Path functoriality, so it remains separately checked but
is not inserted as a redundant third factor. `walking_power_spiral_coreincl`
is the selected `walking_power_spiral`, and the contextual decoder consumes
it. The former strict spiral is deleted rather than retained as a fallback.

The decoder target is the existing directed representable family

```text
Rep_catd(base)[x] = Hom_cat(WalkingEnd_cat,base,x).
```

Its displayed action is postcomposition and its higher action is whiskering.
After specializing the contextual eliminator, the generic
`fdapp1_int_cell` at an arbitrary arrow `p` produces a directed normalization
cell `p -> power(encode(p))`. Only afterward does
`walking_end_is_one_cat(base,x)` convert that directed cell to equality via
`hom_to_path`. This directed-first order prevents the Hom--Nat result or a
word carrier from being smuggled into the HIT signature. The directed cell and
explicit discreteness prove `power(encode(p)) = p`; Nat induction proves
`encode(power(n)) = n`. These support the structured forward encoder, an
explicit inverse package, the Hom--Nat carrier and native equality-valued equivalences,
two independent sethood proofs, and the results that `walking_loop` is not an
identity, has no right inverse, and is not an omega-equivalence.

A separate concrete `BNat` category interprets the opaque constructors and
satisfies the one-dimensionality contract as consistency evidence; it is not
the definitional Hom. A reverse functor from that model and a full
hom-category equivalence need reusable monoid-action and functor-extensionality
infrastructure and remain deferred. No full functor-category initiality
metatheorem is claimed.

The first named finite dependent record is

```text
PathRecord_A = { src : A; dst : A; witness : src = dst }.
```

It is represented by one dependent constructor, with named source, target, and
witness projections and a dependent eliminator that computes on that
constructor. Its equality now exposes the nested dependent-Sigma view

```text
PathRecordPathView_A(r,s)
  = Path_{Σ src:A, Σ dst:A, src=dst}(asSigma(r),asSigma(s)).
```

Literal reflexivity reduces to the stable
`PathRecordPathRefl_A(r)` presentation. The source and dependent-tail
components compute, and reflexive path induction computes whether J sees the
literal spelling first or the shaped head first. The same reflexive head is
registered with path-category units, path symmetry, Core inclusion, and the
two categorical equality encoders. This is a bounded shaped-reflexivity
layer: runtime record eta and additional J computation on raw structured path
constructors remain separate.

The existing componentwise Sigma path maps now have both arbitrary
propositional round trips:

```text
sigma_path_decode_encode(p) : decode(encode(p)) = p
sigma_path_encode_decode(w) : encode(decode(w)) = w.
```

Generic path induction proves the arbitrary statements. Constructor-exposed
reflexivity computes, but neither open composite is a new runtime eta rule.
The literal-reflexivity base used by the second proof is deliberately separate
from the canonical `sigma_path_refl` theorem: Lambdapi's proof-time Sigma
reflexivity comparison does not propagate transitively through the nested
decode application.

Because public `PathRecord` equality already reduces directly to
`PathRecordPathView`, `path_record_path_encode` and
`path_record_path_decode` are transparent identity views. Their two named
round trips compute to reflexivity, preserve `PathRecordPathRefl`, retain the
dependent-tail observer, and iterate through a nested `PathRecord`. They do
not introduce a second normalization through the Sigma maps or imply
fibrancy.

Every ordinary function has one canonical, iterable path action. For
`f : A -> B`, the kernel constructs

```text
path_map_func(f) : Functor(Path_cat(A),Path_cat(B)).
```

Its object component is `f`, and its capped first-path component is exactly

```text
fapp1_fapp0(Path_cat(A), Path_cat(B), path_map_func(f), x, y, p)
  = eq_ap(f,p).
```

This is a definitional computation, not merely a comparison theorem. The
uncapped `fapp1_func` projection retains the whole next-hom functor, so the
same owner remains iterable at higher cells. Equality between functions acts
through `path_map_transf`, while identity, composition, and ordinary
naturality remain the generic `fapp*`/`tapp*` calculus's responsibility.
Where nested `eq_ap` and action by a composite are not judgmentally identical,
`eq_ap_comp` supplies the ordinary propositional comparison; no parallel
runtime channel is needed.

The 2026-07-20 corrective audit therefore removed the short-lived
`PathActionRefinement` Sigma interface. Although that package was type-correct,
it stored only a selected first-path operation and its agreement with the term
above: it constructed no functor, supplied no higher action, and had no
semantic consumer requiring a different definitional normal form. Keeping it
would have made the canonical action look optional and forced clients to carry
a redundant `act` argument. A client that simply needs the action of `f` on
`p` should use the displayed `fapp1_fapp0(path_map_func(f),p)` term directly.
A genuinely exceptional future former may prove a local comparison theorem,
but that alone does not justify restoring a generic selected-action registry.

Dependent transport is similarly direct. `path_record_witness_action` is
`eq_apd` for the witness family. There is no active `ObsDAction` or dependent
refinement registry. If a later consumer needs an iterable dependent action,
the principled object is a displayed functor or section over the base path
functor, not an ordinary `Path_cat(A) -> Path_cat(B)` functor and not a Sigma
of pointwise operations. `PathOut`/J is distinct again: it starts from a
functorial `Catd` motive whose directed action is already part of its input.

Recursive natural-number equality still exposes

```text
(succ(m) = succ(n)) = (m = n),
```

and `NatSucc_func` is the canonical functor induced by the successor function.
The retired selected-action layer had introduced a proof basis solely to
compare the exposed predecessor path with `eq_ap(succ,p)`; no downstream
arithmetic or WalkingEnd theorem consumed that comparison. The basis,
comparison theorem, two proof-time rules, and refinement wrapper are therefore
absent. This removes an ad hoc proof-provenance bridge without changing Nat
equality, `NatSucc_func`, or the WalkingEnd construction.

The recursive classifier also supports a sound first former-specific
dependent-elimination facade without changing generic J. For an arbitrary
proof-dependent motive

```text
P(m,p),  where p : succ(m) = succ(n),
```

`nat_succ_ind_eqr(P,u,p)` regards the already-exposed proof as `m = n` and
delegates to ordinary right-based `ind_eqr`. Consequently a component proof
`eq_refl(n)` computes to the supplied branch `u`, and the construction
iterates by reindexing at `succ(n)`. Outer `eq_refl(succ(n))` and an open
predecessor path do not acquire a beta. This is a transparent former-specific
facade, not a new rewrite, `unif_rule`, global fibrancy package, or arbitrary
structured-path J principle.

For an ordinary map between shaped records, clients use
`path_map_func` exactly as for any other function. The dependent witness field
uses

```text
path_record_witness_action(p)
  : PathOver(witness-family,p,witness(r),witness(s)),
```

which reduces to direct `eq_apd`. Neither operation makes J compute on an
arbitrary structured loop; that stronger claim remains the separate
fibrancy/dependent-elimination boundary.

The isolated binary-Sum experiment—including its decoded former, eliminator,
map, selected branchwise action, proof-time bases, extension module,
diagnostics, and reviewer examples—was retired on 2026-07-20. It had no Nat,
WalkingEnd, native equality-valued, evidence-property, or compatibility consumer. A future
Sum may be redesigned from its actual universal-property or computation
requirements; the retired experiment is not an inactive compatibility API.

Homotopy truncation properties use explicit levels beginning at `-2`:

```text
IsTruncGrpd(-2,A)   = IsContr(A)
IsTruncGrpd(n+1,A)  = Π x y : A, IsTruncGrpd(n,x = y).
```

The readable `IsPropGrpd`, `IsSetGrpd`, and `IsGroupoidGrpd` views denote
levels `-1`, `0`, and `1`. The successor equation computes, so evidence that
`A` is `(n+1)`-truncated can be applied to `x,y` to obtain evidence that
`x = y` is `n`-truncated. This predicate says that an existing classifier is
already truncated; it is distinct from a future higher-inductive truncation
reflector and from the directed categorical-dimension predicate over iterated
homs.

One-step monotonicity is also constructive and level-recursive. At the base,
`contractible_path_center(c,x,y)` chooses the path through the centre of
`c : IsContr(A)`, and `contractible_path_contract` contracts every competing
path to it. Thus `is_contr_is_prop(c) : IsPropGrpd(A)`. The classifier
`TruncMonotonicity(n)` records the general implication, and

```text
is_trunc_grpd_succ(n)
  : IsTruncGrpd(n,A) -> IsTruncGrpd(trunc_succ(n),A)
```

recurses through the native `TruncLevel` eliminator. Its base and successor
equations compute, but no global weakening rewrite or proof erasure is
installed; in particular, a chosen path from open contractibility evidence is
not identified definitionally with reflexivity.

The evidence classifiers are themselves proposition-valued. Equality of two
`IsContr(A)` witnesses uses the active Sigma path view: the second contraction
function is transported along the selected path between centres, and
`PiFunext` compares the functions pointwise in contractible path spaces.
`is_contr_pi` constructs dependent products of contractible classifiers, while
`is_prop_pi` is the proposition-level Pi closure used by the recursive theorem

```text
is_trunc_grpd_evidence_is_prop(n,A)
  : IsPropGrpd(IsTruncGrpd(n,A)).
```

The transparent native recursor inhabits this theorem, but unfolding its
successor through the reducible Pi/equivalence motive exceeds the bounded
conversion check. The public theorem therefore has a stable head with local
base and successor consumer equations. Open witnesses remain distinct at
runtime: proposition-valuedness supplies paths and their contractions, not
definitional proof erasure.

Dependent products preserve every native truncation level. The classifier
`PiTruncClosure(n)` states the general family theorem, and

```text
is_trunc_pi(n,A,B,h)
  : IsTruncGrpd(n,Pi_grpd(A,B))
```

uses `is_contr_pi` at level `-2`. At a successor, the recursive theorem
truncates the pointwise path family and
`is_trunc_grpd_equiv_from(pi_happly_type_equiv(f,g))` transports that evidence
back to function equality. A stable theorem head exposes only the base and
successor consumer equations. The readable proposition-level lemma
`is_prop_pi` is the `-1` specialization of this owner rather than a duplicate
pointwise proof. Open pointwise evidence remains visible at runtime.

Dependent sums preserve a native truncation level when both the base and every
fibre have that level:

```text
is_trunc_sigma(n,A,B,hA,hB)
  : IsTruncGrpd(n,Sigma_grpd(A,B)).
```

The `-2` base `is_contr_sigma` pairs the chosen base and fibre centres; its
contraction transports the target fibre component along the base contraction.
At a successor, Sigma equality already reduces to `SigmaPathView`: the base
path is truncated by `hA`, and `PathOver` is definitionally an equality in the
source fibre after transport, so `hB` supplies the fibre-path evidence. The
recursive Sigma theorem then truncates that total path view. The stable owner
computes only when both hypotheses are supplied, and neither is erased.

Truncation evidence is invariant under an ordinary type equivalence. Given
`e : TypeEquiv(A,B)`, the active construction maps the decoder-selected
universe path `grpd_equiv_path(e)` through the family
`X |-> IsTruncGrpd(n,X)` and then applies `idtoequiv_grpd`:

```text
is_trunc_grpd_type_equiv(e)
  : TypeEquiv(IsTruncGrpd(n,A), IsTruncGrpd(n,B)).
```

Its `to` and `from` projections transport evidence in both directions, their
round trips are inherited from `TypeEquiv`, and the reflexive case computes.
An arbitrary self-equivalence is not collapsed to reflexivity at runtime.
This is the ordinary groupoid/type theorem; categorical fixed-map invariance
is a separate consumer below.

The corresponding universe of already-truncated classifiers is the named
dependent package

```text
TruncGrpdU(n) = { carrier : Grpd;
                  evidence : IsTruncGrpd(n,carrier) }.
```

Both fields project computationally, and the evidence remains part of the
package. The low-level aliases are

```text
PropU_grpd     = TruncGrpdU(-1)
SetU_grpd      = TruncGrpdU(0)
GroupoidU_grpd = TruncGrpdU(1).
```

No runtime package eta or proof erasure is selected. Proposition-valued
truncation evidence now controls package equality through

```text
TruncGrpdPathView(n,X,Y)
  = Sigma(p : carrier(X) = carrier(Y)),
      PathOver(IsTruncGrpd(n,-),p,evidence(X),evidence(Y)).
```

The named encode/decode maps give propositional package-path round trips.
Every carrier path supplies its dependent evidence component, and carrier
projection is packaged as

```text
(X = Y) ~= (carrier(X) = carrier(Y)).
```

The forward and selected inverse maps compute, including reconstruction at a
reflexive carrier path, while the inverse laws remain propositional. This is
not runtime package eta. The canonical ambient decoder is itself packaged as

```text
(A = B) ~= TypeEquiv(A,B),
```

and composing the two packages gives restricted truncated-universe
univalence:

```text
(X = Y) ~= TypeEquiv(carrier(X),carrier(Y)).
```

The forward map is ambient `idtoequiv_grpd` after carrier projection; the
selected inverse is `grpd_equiv_path` followed by evidence reconstruction.
Both round trips and inverse reflexivity remain propositional, while forward
reflexivity computes. This is still decoder-mediated compatibility, not direct
observational universe identity. Nor is `TruncGrpdU(n)` asserted to be
`n`-truncated: under univalence its expected level is generally `n+1`.

That expected-level theorem is now active. At level `-2`, every function
between contractible classifiers has the constant inverse at the chosen source
centre; `contractible_map_by_inverse` records both paths, and
`is_equiv_map_evidence_is_prop` makes the inhabited equivalence-evidence fibre
contractible. Dependent Pi and Sigma closure then give

```text
contractible_type_equiv(hA,hB) : IsContr(TypeEquiv(A,B)).
```

At a successor level, the function space inherits the truncation of its target
and `IsEquivMap(f)` is proposition-valued, hence truncated at every successor
by `prop_is_trunc_succ`. Therefore the successor branch needs only target
evidence; source evidence remains in the all-level signature because the
contractible base genuinely uses it. The stable owner exposes exactly the two
consumer equations:

```text
is_trunc_type_equiv(-2,A,B,hA,hB)
  = contractible_type_equiv(hA,hB)

is_trunc_type_equiv(succ(n),A,B,hA,hB)
  = trunc_type_equiv_succ(n,A,B,hB).
```

Finally, `is_trunc_grpd_universe(n)` transports this same-level carrier-
equivalence bound backward through `trunc_grpd_univalence_type_equiv`, proving

```text
IsTruncGrpd(succ(n), TruncGrpdU(n)).
```

The theorem keeps base/source and successor/target evidence observable where
used. It adds neither broad proof erasure nor direct universe computation.

Ordinary dependent-function extensionality is exposed without discarding the
related-input Pi path view. For `f,g : Π x:A, B(x)`, the diagonal classifier is

```text
PiPointwisePath(f,g) = Π x:A, f(x) = g(x).
```

`PiHapply(p)` observes a structured Pi path `p` on the diagonal, while
`PiFunext(h)` extends diagonal data to arbitrary `x0,x1:A` and
`q:x0=x1` by ordinary right-based path induction. Their selected equations
are deliberately asymmetric:

```text
PiHapply(PiFunext(h))(x) = h(x)                 runtime;
pi_funext_eta(p) : PiFunext(PiHapply(p)) = p   propositional.
```

The generic-J eta proof needs the reflexive equation
`PiFunext(PiHapply(refl_f)) = refl_f`. Stable `PiHapply` and `PiFunext` heads
retain this as a narrow two-rigid-head proof-time definitional law. A separate
transparent presentation reduces to the same equation and supplies its
semantic justification; typed `eq_refl` only tests that the selected
`unif_rule` fires. The stable terms remain non-convertible at runtime, and
applying them first joins the existing shaped Pi-reflexivity computation.

The transparent theorem `is_equiv_map_by_inverse` converts explicit left and
right inverse paths to the active contractible-fibre `IsEquivMap` notion.
Left-oriented path induction reduces a general fibre path to the generic
half-adjoint triangle; the resulting contraction is then re-centred at the
specified inverse and right-inverse path. Consequently
`pi_happly_type_equiv` has executable forward map, inverse, and right path.
The contraction path remains propositional data rather than a proof-erasure
runtime equation. Arbitrary structured-Pi J computation, Sigma/record
structural action, and computational fibrancy remain separate work.

At the groupoid-classifier category, the whole hom-category is now explicit:

```text
Hom_Grpd(A,B) = Path(Function(A,B)).
```

The stable `grpd_id_function(A)` and `grpd_comp_function(g,f)` heads compute
pointwise. Generic categorical identity compares at proof time. Generic
composition retains its categorical whole-term head and proof-time comparison,
while capped application computes pointwise. With eta equality enabled this is
observationally convertible to the corresponding lambda, although there is no
whole-term rewrite to `grpd_comp_function`. This retains the global category
owner while giving `PiFunext` and `PiHapply` rigid endpoints for function-path
laws.

There are explicit defined adapters in both directions between
contractible-fibre `TypeEquiv(A,B)` and equality-valued
`OmegaEquiv(Grpd_cat,A,B)`. From `TypeEquiv`, its selected inverse and two
round-trip paths directly form the omega package. Conversely, if `f` has
separate left and right inverse functions, the right law shows that those
functions agree pointwise; the left inverse therefore also has a right law
and yields `EquivByInverse`. This construction then invokes
`is_equiv_map_by_inverse`. Forward maps, selected inverse points, and the
derived right law compute, but package eta is not definitional. No universe
decoder, opaque bridge, or bodyless fibre theorem is used.

From any groupoid/type `A`, there is a path category:

```text
Path(A)
Obj(Path(A)) = A
Hom_{Path(A)}(x,y) = Path(x =_A y)
```

Composition in `Path(A)` uses the same `comp_fapp0` owner as every category:

```text
q ∘ p = comp_fapp0(Path(A),q,p).
```

The J-derived operation `eq_trans(p,q)` is propositionally equal to this
composition through `path_comp_eq_trans(p,q)`; it is not its runtime normal
form. Two narrow bridges compute either unit after `id` has projected to
`eq_refl`, so the generic-identity-first and projection-first orders join.
Associativity remains the generic proof-time category law.

The opposite `Path(A)^op` is not definitionally collapsed to `Path(A)`.
Its homs reverse endpoints. Path reversal is instead the arrow action of

```text
PathSym_A : Path(A)^op -> Path(A).
```

`PathSym_A` fixes objects and maps reflexivity to reflexivity. Generic functor
composition supplies the ordered anti-composition law; there is no second
constructor-specific composition rewrite. The J-derived `eq_sym` operation
agrees propositionally through `path_sym_agrees_eq_sym`, and involution is
initially the proposition `path_sym_invol`, not an open runtime cancellation.
The pointwise `path_sym_core_incl_agreement` theorem states that reversing a
path and then including it into `C^op` gives the same underlying arrow as
including the original path into `C`. Functor-level natural packaging and the
fixed-map omega-equivalence package remain later owners.

Likewise, the postcomposition and precomposition action heads remain distinct
runtime presentations. Their existing typed proof-time comparisons with
shared composition prove the expected unit equalities, while the open
projected action terms deliberately do not reduce to the underlying path.

This is motivation and infrastructure, not yet the full HoTT program. The
current v3.2 theory now has computational path views for the encoded Sigma/Pi
object layers, ordinary Pi extensionality packaged as an equivalence, explicit
type-equivalence data, and groupoid/categorical univalence capability
interfaces. Section 13 explains that staging. General higher-inductive
pushouts and a complete computational account of structured Pi and universe
equality remain deferred. Arbitrary Sigma and first-record path round trips
are active, with the intentionally propositional/runtime split above.

## 4. The Universe Of Categories

The category universe `Cat` is itself a category:

```text
Obj(Cat) = categories
Hom_Cat(A,B) = Functor(A,B)
```

Thus an arrow in the universe of categories is a functor. This is the directed
universe principle used throughout the development.

Ordinary functors have object and arrow actions:

```text
F : A → B
F[x] : Obj(B)
F[f] : Hom_B(F[x],F[y])
```

Functoriality is structural, not constructor-specific. Once a construction is
an object of `Functor(A,B)`, its identity and composition laws come from the
single global functor calculus. A formula that appears to require separate
identity/composition rules for a named action usually indicates that the
underlying operation has not yet been internalized far enough as a functor.
The same principle applies to naturality after a construction has been
internalized as a transformation.

The public identity names follow this discipline uniformly. `id_func(A)`,
`id_funcd(E)`, and `id_transfd(FF)` are transparent views of generic `id` at
`Cat_cat`, `Catd_cat(K)`, and `Functord_cat(E,D)`, respectively. There is no
second ordinary `id_transf` constructor. Because `Functord_cat(E,D)` and
`Transf_cat(K,Cat,E,D)` are proof-time-comparable stable facades rather than
runtime aliases, identity-specialized displayed consumers accept the two
typed generic-`id` presentations explicitly.

This is a useful discipline throughout the development: an equation such as
`E[x] = ...` is only the object part of a functorial or natural construction.
When `x` ranges over a directed category, the corresponding arrow action over
`p : x -> y` is part of the structure, not a later cosmetic detail.

The same warning applies one level up. A displayed equation such as
`eta[x] = ...` gives only the component of a natural transformation. Its
functorial/naturality action over arrows is represented primarily by
`tapp1_func eta`; capped projections such as `tapp1_fapp0 eta p`, or
constructor-specific `*_tapp1_*` helpers, may be the relevant implementation
surface. That arrow action must still be specified or explicitly deferred
before the construction is treated as implemented.

The theory also has transformation categories:

```text
Transf(F,G)
```

whose objects are transformations from `F` to `G`. A transformation
`ϵ : F => G` has point components:

```text
ϵ[x] : Hom_B(F[x],G[x])
```

Implementation note: Cat-valued horizontal action is now expressed through the
generic product-composition owners `comp_prod_fapp1_func` and
`comp_prod_fapp1_fapp0`, including their Cat instance projection ladder. The
former compatibility-only `comp_cat_cov_*` and `comp_cat_con_*` heads are no
longer active kernel owners.

That construction is polymorphic in its ambient category. At
`A = Catd_cat(K)` it gives horizontal action on displayed transformations:

```text
(eta,id_H) |-> H eta
(id_L,eta) |-> eta L.
```

These are whole `Transfd` objects, not pointwise arrows supplemented by an
external naturality square. Projecting at `k : K` computes to the corresponding
ordinary horizontal action in the fibre, while the original whole term still
supplies base-arrow and higher-cell behavior through the displayed internal
action. Thus the contextual readings `lambda^nd a. H(eta[a])` and
`lambda^nd a. eta[L[a]]` reuse one already-internalized action owner. The
additional kernel clause is only the missing component evaluator beta; it does
not introduce a new classifier or a second coherence calculus. A future
construction in which the complete `Transf_catd` classifier itself varies is
a different problem and is not implied by this fixed-head case.

### Hom-Actions And Controlled Associativity

The represented hom-actions are meant to compute with composition before a
proof has to appeal to a separate associativity principle. In ordinary
notation:

```text
(F p)_*(g) = F[p] o g
(F p)^*(g) = g o F[p]
```

The useful computational normal forms keep the stable hom-action owner visible
and accumulate consecutive actions into the action indexed by the composite
arrow. For example:

```text
(F q)_*((F p)_*(g))        -> (F(q o p))_*(g)
((F f)_*(g)) o h           -> (F f)_*(g o h)
(F p)^*((F q)^*(g))        -> (F(q o p))^*(g)
```

Covariant and contravariant represented families now remain distinct during
runtime normalization:

```text
hom_(F,W)       owns postcomposition in the varying target
hom_con(W,F)    owns precomposition in the varying source
hom_int(F)      internalizes the represented source endpoint
hom_con_int(F)  internalizes the represented target endpoint.
```

Their mathematical comparison through opposite categories, and the comparison
between identity-family precomposition and postcomposition, are proof-time
unification facts rather than runtime orientations. This preserves the
antecedential/consequential distinction needed by the cut-elimination reading.

When both endpoints move, the simultaneous owner is the hom bifunctor action:

```text
Hom_func(g,f)[h] = Hom_fapp0(g,f,h) = f o h o g.
```

Direct action of `Unit_prof` normalizes through the rigid `Hom_*` projection
ladder. Independently factored pre/postcomposition orders and the cases with
one active endpoint remain distinct runtime presentations; narrow proof-time
unification rules identify them with the corresponding `Hom_func` /
`Hom_fapp0` values when typed elaboration needs the mathematical comparison.
The rigid owner itself computes its full identity and composition laws:

```text
Hom_func(id,id) = id
Hom_func(g2,f2) o Hom_func(g1,f1)
  = Hom_func(g1 o g2,f2 o f1),
```

with matching point-action rules for `Hom_fapp0`. `Unit_prof(A)` is the
uncurried product form of this same hom bifunctor.

Ordinary composition identity eliminates an identity arrow independently of
the chosen external endpoint presentation. Its kernel rules retain the shared
middle object as the composition-interface guard and infer the outer
endpoints, so rewrite matching may use the proof-time compatibility between
the covariant and contravariant presentations above. In the PathOut/Sigma
benchmark this reduces the composite fibre proof to one identity; the two
possible runtime identity spellings are joined by typed reflexivity through
the pre/post unification bridge.

These are the higher-categorical analogue of keeping substitution or
cut-elimination under the constructor that owns it. Raw expanded presentations
such as `F[q] o ((F[p])_*(g))` and `((F[p])^*(g)) o F[q]` normally remain raw
ordinary composites at runtime. The kernel records their relation to stable
hom-action syntax by proof-time unification rules, and it also has proof-time
associativity for raw ordinary composition. For reviewer-facing examples,
prefer statements whose runtime normalization remains in the hom-action layer
when that layer is the intended mathematical mechanism; use typed equality
proofs when the proof naturally passes through a raw composite.

## 5. Directed Families

A directed family of categories over `K` is a functor:

```text
E : K ⊢ Cat
```

The theory writes this as a category-valued family:

```text
E : Catd(K)
E[k] = fibre of E at k
```

Terminology used in this note:

- A **functorial family** is a category-valued functor `E : K ⊢ Cat`.
- A **natural family morphism** `FF : E ⊢ D` is a family of functors that is
  natural in the base variable.
- A **natural family transformation** `ϵ : FF => GG` is a family of
  transformations that is natural in the base variable.

The implementation names for these are `Catd`, `Functord`, and `Transfd`,
respectively. The words "displayed" and "family" still occur in implementation
names, but this document uses "functorial" and "natural" to emphasize the
variance over base arrows.

These displayed names are stable category facades, not runtime abbreviations
that erase the ordinary hierarchy. `Catd_cat`, `Functord_cat`, and
`Transfd_cat` compare at proof time with the corresponding ordinary
`Functor_cat`, `Transf_cat`, and iterated-hom presentations. Their object and
hom projections provide the runtime passage between the two views.

A natural family morphism has fibre functors:

```text
FF : k :^n K ; E[k] ⊢ D[k]
FF[k] : E[k] ⊢ D[k]
```

A natural family transformation has fibrewise components:

```text
ϵ : FF => GG
ϵ[k] : FF[k] => GG[k]
ϵ[k](u) : Hom_{D[k]}(FF[k](u), GG[k](u))
```

Basic family operations:

```text
Const_K(A)[k] = A
1_K = Const_K(1)
E^op[k] = E[k]^op
F^*E[a] = E[F[a]]
```

### Cat-Valued Presheaf Facade

The one-way presheaf library packages the contravariant specialization of a
directed family without adding another family calculus:

```text
Psh_cat(K) = Catd_cat(K^op)
Psh(K)     = Obj(Psh_cat(K)).
```

The displayed equation describes the mathematical presentation, not a runtime
rewrite between category heads. `Psh_cat(K)` is rigid and remains visible at
runtime. Its object and hom projections compute to the existing directed-
family hierarchy on `K^op`, while one narrow proof-time comparison relates it
directly to `Catd_cat(K^op)`. In particular, a typed reflexivity proof can use
the comparison, but a bare conversion does not erase the facade.

For an ordinary functor `F : A -> B`, presheaf restriction is the already
existing family pullback along the opposite functor:

```text
Psh_pullback_func(F) : Psh_cat(B) -> Psh_cat(A)
Psh_pullback_func(F)[P]
  = Pullback_catd(P,Op_func(F)).
```

The object action computes through `Pullback_catd_func`. The action on
presheaf maps is the generic functor action of that same functor; the library
does not restate identity, composition, or naturality. The current facade is
Cat-valued. Ordinary Set-valued presheaves will be a later discrete-fibre
specialization, and an arbitrary Cat-valued presheaf is not called a stack
without separately selected descent data.

The same library names the contravariant Yoneda functor without installing a
second action theory:

```text
yoneda_psh_func(K) : K -> Psh_cat(K)
yoneda_psh(U)[V]   = Hom_K(V,U).
```

It is transparently `hom_con_int(id_K)`, so an arrow `p : V -> U` acts by the
existing represented-target postcomposition owner. In particular, its
component at `W` computes to postcomposition by `p` in `K`.

For later site constructions the direction of the arrow category is kept
explicit:

```text
Into_restr_cat(U) = Sigma_(V : K^op) Hom_K(V,U)
Slice_cat(U)      = Op_cat(Into_restr_cat(U)).
```

The first category points in the restriction direction; its opposite is the
conventional slice `K/U`. A Cat-valued higher sieve is then a directed family
on the restriction category:

```text
HigherSieveClassifier(K)[U] = Catd_cat(Into_restr_cat(U))
HigherSieve_cat(U)           = Fibre_cat(HigherSieveClassifier(K),U)
maximal_higher_sieve(U)      = Terminal_catd(Into_restr_cat(U)).
```

Equivalently, it is a Cat-valued presheaf on `Slice_cat(U)`. In the formal
presentation these two descriptions each compare at proof time with the
stable intermediary `Catd_cat(Into_restr_cat(U))`; they do not directly
runtime-collapse, and no extra unification rule is added merely to chain the
comparisons. Restriction of a higher sieve is the existing Catd pullback along
the Sigma-total map, and the maximal higher sieve is stable under it.

This higher notion is deliberately not an ordinary sieve. The downstream
one-way sieve module now selects ordinary sieves by native pointwise
subterminality:

```text
IsSubterminalCat(C)
  = Sigma obj_prop : IsPropGrpd(Obj(C)), IsGroupoidalCat(C)
IsOrdinarySieve(S)
  = Pi f : Obj(Into_restr_cat(U)),
      IsSubterminalCat(Fibre_cat(S,f))
Sieve(U)
  = Sigma S : HigherSieve(U), IsOrdinarySieve(S).
```

Proposition-valued objects alone would be too weak: a one-object directed
category may retain nontrivial endomorphisms. Native `IsGroupoidalCat` says
that every retained categorical cell comes from object equality. The selected
pair therefore derives the existing exact `IsDiscreteCat` contract, while a
literal `Path_cat(A)` for proposition-valued `A` supplies a canonical
subterminal example.

Both retained evidence layers are themselves propositions. Nevertheless,
ordinary-sieve pullback keeps the Sigma evidence explicitly. It reuses the
existing higher-sieve/Catd pullback action and selects the old witness at each
postcomposed arrow; no new action rule is needed. Consequently pullback along
an identity has the correct mathematical value but does not judgmentally
reduce the reconstructed package to the original package.

The public name `Sieve` now belongs to this ordinary property subtype. The
name `Omega` remains reserved and unbound: a true classifier still needs
setness of `Sieve(U)` plus an owner-aligned contravariant family assembly.
Neither topology nor descent follows merely from forming ordinary sieves.

### Direct Grothendieck Topologies On Ordinary Sieves

The downstream sites module defines membership without adding a Boolean
classifier. An object of `Into_restr_cat(U)` is a pair `(V,f)` with
`f : V -> U`, and

```text
SieveMembership(R,(V,f)) = Obj(R(V,f)).
```

This classifier is proposition-valued because `R(V,f)` is a native
subterminal category. The maximal ordinary sieve is the constant family at
the literal path category `Path_cat(Unit_grpd)`. It is pointwise true, and its
pullback computes to the maximal sieve on the source through ordinary
constant-family pullback. This presentation intentionally does not identify
`Path_cat(Unit_grpd)` with `Terminal_cat`; consequently its underlying higher
sieve does not definitionally equal `maximal_higher_sieve`.

A direct sieve coverage is first-class proposition-valued data:

```text
SieveCoverage(K)
  = Pi U : Obj(K), Sieve(U) -> PropU_grpd
Covers(J,R)
  = trunc_grpd_carrier(J(U,R)).
```

The `PropU_grpd` evidence projection proves each `Covers(J,R)` a proposition.
The selected Grothendieck topology laws are exactly:

```text
maximal:  Covers(J,maximal_sieve(U))
stable:   Covers(J,R) -> Covers(J,p^*R)
local:    Covers(J,R)
       -> (forall f in R, Covers(J,f^*S))
       -> Covers(J,S).
```

Here “`f in R`” is `SieveMembership(R,f)`, and every pullback is the existing
ordinary-sieve pullback. `GrothTopology(K)` retains the selected coverage and
these three laws, with named projections for each observation. The chaotic
topology sends every sieve to the true Unit proposition; all three laws then
compute to `tt`, giving a direct model on every category and in particular on
`Terminal_cat`.

This is a direct topology presentation, not a cover-family generator. The
sites module itself has no `Omega`, free saturation, sheafification, descent,
or assertion that every concrete family coverage automatically generates a
topology. The separate downstream generated-topology module supplies the
universal-property construction described next.

### Internally Generated Grothendieck Topologies

A generator family may retain arbitrary presentation witnesses rather than
first erasing them into a proposition:

```text
SieveGeneratorFamily(K)
  = Pi U : Obj(K), Sieve(U) -> Grpd.
```

A topology `T` accepts `G` when every `g : G(U,R)` produces a covering
witness for `R` in `T`. Generated coverhood is the impredicative intersection

```text
GeneratedSieveCover(G,U,R)
  = Pi T : GrothTopology(K),
      GrothTopologyAcceptsGenerators(G,T)
      -> groth_topology_covers(T,R).
```

Every target coverhood is proposition-valued, so the existing dependent-Pi
proposition theorem makes this whole intersection proposition-valued without
truncating `G`. Maximality, pullback stability, and local character are
inherited by applying the corresponding law in every accepting topology.
The resulting `generated_groth_topology(G)` accepts every generator and is
below every other accepting topology under pointwise inclusion of cover
predicates. Both observations compute: inclusion applies the competing
topology's acceptance witness, and leastness evaluates a generated-cover
witness at that topology. The chaotic topology is a closed accepting upper
bound, so the intersection is nonvacuous.

This is a Church-/intersection-style least topology, not an inductive syntax
of cover-generation steps. It deliberately provides no induction principle,
normal form, or decision procedure for arbitrary coverhood. A future
truncated/HIT presentation is justified only if a consumer needs those
additional interfaces; it is not required for the universal property or the
computational affine-site MVP.

### Internal Direct-Cover Sheaves And Their Completion

For a fixed site `(K,T)`, the eligible ordinary covering sieves form the
internal category `DirectCoverQuestion_cat(K,T)`. Given a Cat-valued presheaf
`X`, the matching families and sections for all those questions are displayed
Cat-valued families over that category, and restriction is one displayed
functor

```text
restriction_X : Section_X ->_Q Matching_X.
```

The selected Pédrot-style algebraic sheaf structure is likewise whole:

```text
DirectCoverSheafStructure(T,X)
  = Sigma glue : Functord_Q(Matching_X,Section_X),
      glue o restriction_X = id_Section_X.
```

Thus question pullback, matching-arrow action, and both naturality dimensions
are carried by `glue` itself. `silent` is one path between displayed functors,
not a family of component equations. Evaluation and `eq_ap` merely project
literal-cover observations from these whole owners. The older
`DirectCoverAlgebra` is retained as a forgetful view for the deployed
recursor; it is not the semantic owner of the sheaf structure.

`DirectCoverSheaf(T)` is the transparent total of a presheaf and this
structure. The primitive `DirectCoverCompletionPsh(T,P)` supplies its whole
unit, recursive glue, and silent path and therefore inhabits that syntactic
sheaf package. This package is still not definitionally identified with the
rigid supplied `Sheaf_cat(K,T,Cat_cat)` facade. Conventional locality is now a
separate derived comparison rather than a missing constructor.

For each eligible question `q=(R,covers)`, canonical cover pullback, internal
matching naturality, recursive glue, and silent derive the retained-member
calculation

```text
restriction_q(glue_q(m))[V](p,member) = m[V](p,member).
```

One whole transformation `rho : restriction o glue => id_Matching` owns these
components through ordinary, displayed, and fibre projection. The point
component computes to `path_to_hom` of the displayed equation above.
Pointwise path equivalences are then lifted through a generic strict
pointwise-to-whole `OmegaEquivAlong` closure. That closure consumes an
already-whole transformation, so its naturality is internal; it does not
construct a transformation from a bare component family. The resulting path

```text
restriction_q o glue_q = id_Matching(q)
```

and the primitive whole `silent_q : glue_q o restriction_q = id_Section(q)`
make restriction the fixed-forward equivalence required by
`PshLocalAtOrdinarySieve`. Quantifying over `U`, `R`, and `covers` gives

```text
IsTopologyLocalPsh(K,T,DirectCoverCompletionPsh(K,T,P)).
```

The retained-member equality is an opaque proof owner in the active library,
but not a new runtime operation or consumer-supplied sheaf field. Its complete
internal endpoint derivation and non-collapse controls are retained in the
CS-12 living plan and focused probes. The computational data remain the whole
restriction, glue, transformation projections, and selected inverse arrows.

The categorical-HIT eliminator is also whole in its seed.  For one selected
target algebra `A_Y`, its recursor is a functor

```text
rec_func(A_Y) : Hom(P,Y) -> Hom(Completion(P),Y),
rec_func(A_Y)[seed] = rec(A_Y,seed).
```

The existing constructor beta is retained as a narrow runtime computation;
its functorial form is the whole higher beta

```text
precomp_unit o rec_func(A_Y) = id_Hom(P,Y).
```

At a topology-local target, locality selects the canonical target algebra and
the categorical-HIT uniqueness clause is

```text
rec_func(canonical_algebra(Y)) o precomp_unit
  = id_Hom(Completion(P),Y).
```

This eta law is intentionally local-target scoped: it does not assert that an
arbitrary underlying map preserves an independently selected one-sided cover
algebra.  The two whole laws construct

```text
Hom(Completion(P),Y) ≃ Hom(P,Y)
```

as `OmegaEquivAlong Cat_cat` with fixed forward map `precomp_unit`. Arrow
action and naturality are those of the whole restriction and recursor
functors, not external component squares.

The Cat-valued fixed-site reflector is now assembled into the existing rigid
sheaf facade rather than a parallel local-object category:

```text
Obj(Sheaf_cat(K,T,Cat_cat))
  = Sigma P:Psh(K), IsTopologyLocalPsh(K,T,P),

include(P,local) = P,
sheafify_T(P) = (Completion_T(P), completion_is_local_T(P)).
```

The Hom categories and category operations are inherited from `Psh_cat(K)`.
The reflector's whole action sends `f:P->Q` to the unique recursive extension
of `unit_Q o f`; its action and naturality remain at one functor owner. The
generic supplied capability is indexed by
`Functor_cat(Op_cat(K),Cat_cat)`, so the adjunction is declared at that raw
boundary while the scoped proof-time comparison retains `Psh_cat(K)` as the
computational/public owner. No runtime category-head identification is added.

At a local sheaf `Y`, the adjunction counit computes to recursion from
`id_Y`. Recursor beta gives `counit o unit = id_Y`. Applying whole local eta
to `unit o counit`, after the internally derived unit-precomposition path,
gives the other cancellation. These arrows and paths construct the exact
fixed-forward `OmegaEquivAlong` required by the existing
`SheafificationCapability(K,T,Cat_cat)`. This completes fixed-site Cat-valued
sheafification; it does not yet lift the reflector to CommRing-valued objects,
prove left exactness, transport it to slices, or construct schemes.

If strict equality later becomes too restrictive, a separate directed or
pseudo/lax completion may retain whole categorical cells and coherence.
Univalence can turn an appropriate whole equivalence or isomorphism into a
path when the ambient category supplies that capability; it does not turn an
arbitrary noninvertible lax cell into equality. The current direct-cover
completion therefore retains the strict whole-path interface while the richer
variant remains consumer-gated.

### Set-Carrier Commutative-Ring Objects

The first algebra layer packages a commutative ring over an explicitly
set-valued carrier.  Its operation data are separate from its law evidence:

```text
CommRingOps(A) = (0, 1, add, neg, mul)

IsCommRing(A,ops)
  = AddAssoc x AddComm x AddZero x AddInv
      x MulAssoc x MulComm x MulOne x LeftDistrib

CommRingStructure(A)
  = Sigma ops : CommRingOps(A), IsCommRing(A,ops)

CommRing
  = Sigma A : SetU_grpd,
      CommRingStructure(trunc_grpd_carrier(A)).
```

The retained additive unit and inverse laws are right-handed, as are the
multiplicative unit law and the selected left-distributivity orientation.
Commutativity derives their omitted mirror equations, so storing both sides
would duplicate evidence rather than strengthen the algebraic structure.
Nothing requires `0` and `1` to be distinct; the one-element zero ring is a
checked inhabitant.

For `R : CommRing`, `comm_ring_carrier R` is its decoded carrier,
`comm_ring_carrier_is_set R` retains sethood, and the named operations
`comm_ring_zero`, `comm_ring_one`, `comm_ring_add`, `comm_ring_neg`, and
`comm_ring_mul` are transparent observations of the operation package.  The
eight `comm_ring_*_law` projections expose the corresponding equality
witnesses.  Constructors and observations reduce through the existing Sigma,
function, and equality owners; this module adds no rewrite or unification
rule.

The concrete `zero_comm_ring` uses `Unit_grpd`.  Because an open Unit variable
does not judgmentally eta-reduce to `tt`, its open additive-zero and
multiplicative-one laws use the existing contraction witness rather than an
invalid reflexivity proof.  This object layer deliberately declares no
morphism/category, carrier functor, exponentiation, localization, finite
family, or polynomial interface.  The first two of those are considered in a
separate downstream module so the rule-free object package remains reusable.

### Structured Commutative-Ring Morphisms

For commutative rings `R` and `S`, a structured morphism retains an ordinary
carrier function and five preservation witnesses:

```text
CommRingHomLaws(R,S,f)
  = PreservesZero(f)
      x PreservesOne(f)
      x PreservesAdd(f)
      x PreservesNeg(f)
      x PreservesMul(f)

CommRingHom(R,S)
  = Sigma f : (|R| -> |S|), CommRingHomLaws(R,S,f).
```

Negation and zero preservation are stored explicitly. They are derivable in
ordinary algebra from smaller sets of axioms, but retaining them avoids making
the first morphism API depend on a not-yet-selected cancellation theorem
library. `comm_ring_hom_intro` constructs a map;
`comm_ring_hom_function`, `comm_ring_hom_laws`, and the five named
`comm_ring_hom_*_law` observations expose its fields.
`comm_ring_hom_apply(h,x)` is the transparent application of the retained
function and computes on explicit constructors.

Pointwise equality of those retained functions extends to equality of the
full structured maps. `comm_ring_hom_ext` first uses `PiFunext` on carrier
functions, then fills the dependent law path from proposition-valued
`CommRingHomLaws`. This is a theorem about Sigma packages, not a global
package-eta reduction.

Every preservation classifier is proposition-valued because its equations
live in the set-valued target carrier. Dependent-Pi and dependent-Sigma
truncation closure therefore prove `CommRingHomLaws(R,S,f)` a proposition and
`CommRingHom(R,S)` a set. The ordinary category facade is then:

```text
Obj(CommRing_cat) = CommRing
Hom_cat(CommRing_cat,R,S) = Path_cat(CommRingHom(R,S)).
```

The sethood theorem makes `CommRing_cat` a checked `OneCat`. Whole identities
and composites remain the generic `id` and `comp_fapp0` category owners;
`comm_ring_hom_id` and `comm_ring_hom_comp` are readable aliases. The library
does not reconstruct those opaque whole arrows as Sigma packages: retained
proof fields have no judgmental package eta, so doing so would compete with
the generic category unit rules. Consequently, application of an explicitly
constructed map computes, while `comm_ring_hom_apply(comm_ring_hom_id(R),x)`
is deliberately not advertised as a runtime reduction to `x`.

Two later consumers select rigid pointwise comparisons without changing those
whole-arrow owners. Iterated localization selects
`comm_ring_hom_comp_pointwise(g,f)`, whose carrier projection computes to
`x |-> g(f(x))`. The empty-variable polynomial-algebra model selects
`comm_ring_hom_id_pointwise(R)`, whose carrier projection computes to
`x |-> x`. Each rigid head compares with its generic category arrow only at
proof time. Generic identity and composite applications remain deliberately
non-computational.

There is not yet a carrier functor from `CommRing_cat` to `Grpd_cat`.
`Grpd_cat` compares whole identity/composition functions only at proof time
and computes their stable point observations separately; a direct carrier
action rule would otherwise create a competing runtime presentation at the
generic functoriality owner. The two selected identity/composition heads are
not themselves a functor action. The first ring-valued-presheaf consumer now
selects element-level identity/composition paths through those heads, but it
does not supply the complete object/arrow/higher action needed by a carrier
functor. Whole invertibility-sieve assembly remains the next concrete gate.

### Universal-Property Localization At One Element

For `x : |R|`, explicit unit evidence is

```text
CommRingUnitEvidence(R,x)
  = Sigma inverse : |R|, x * inverse = 1.
```

This evidence is proposition-valued. If `y` and `z` are two selected
inverses, commutative-monoid laws give

```text
y = y*1 = y*(x*z) = (y*x)*z = (x*y)*z = 1*z = z.
```

The carrier is a set, so the resulting inverse path is contractible. The
dependent path between the two multiplication-law witnesses is likewise an
equality between proofs in a proposition-valued carrier equality. The Sigma
path view therefore makes the whole unit-witness identity space contractible.

Unit evidence transports along an element path and is preserved by every
structured ring map. If `u^-1` is the inverse stored by `u`, the preserved
witness stores `h(u^-1)` as the inverse of `h(x)`; multiplication and one
preservation prove its law. This is computational data, not merely a
proposition that some inverse exists. These generic operations live with the
unit classifier because both localization comparison and ring-valued
presheaves consume them.

For a structure map `iota : R -> L` and a target map `h : R -> S`, the
factorization classifier is

```text
CommRingLocalizationFactor(iota,h)
  = Sigma factor : CommRingHom(L,S),
      Pi a : |R|, factor(iota(a)) = h(a).
```

The triangle is pointwise on carrier applications. This is intentional:
whole `CommRing_cat` identity and composition arrows retain generic category
owners, and their carrier projections do not have extra runtime equations.
The universal property does not require such projected computation.

Localization at `f : |R|` is then expressed by

```text
IsCommRingLocalizationAt(R,f,L,iota)
  = UnitEvidence_L(iota(f))
      x Pi S h,
          UnitEvidence_S(h(f)) ->
            IsContr(CommRingLocalizationFactor(iota,h))

CommRingLocalizationAt(R,f)
  = Sigma L : CommRing,
      Sigma iota : CommRingHom(R,L),
        IsCommRingLocalizationAt(R,f,L,iota).
```

Named constructors and projections expose the chosen target, structure map,
unit, and contractible factorization evidence. The module introduces no
rewrite or unification rule and no eta reduction for opaque chosen
localizations. A concrete reviewer proves that localizing the one-element
zero ring at its unique element yields the zero ring itself: Unit
contractibility supplies every factor triangle, `comm_ring_hom_ext` supplies
uniqueness of structured factors, and proposition-valued triangle evidence
completes the dependent Sigma path.

The separate rule-free unit-localization layer gives the first parametric
model. If `u : CommRingUnitEvidence(R,f)`, the pointwise identity map has the
full localization universal property:

```text
comm_ring_unit_identity_localization(R,f,u) : Loc_R(f)
target(comm_ring_unit_identity_localization(R,f,u)) = R
map(comm_ring_unit_identity_localization(R,f,u))(x) = x.
```

For a target map `h : R -> S`, the selected factor is `h` itself. Any
competing factor's triangle supplies pointwise equality with `h`;
structured-map extensionality and the proposition-valued triangle fibre then
give equality of the complete Sigma factors. Thus the factorization
classifier is constructively contractible, rather than merely assumed. The
multiplicative identity carries canonical unit evidence with inverse one, so
every ring has the closed parametric computation

```text
comm_ring_identity_localization_at_one(R) : Loc_R(1)
R[1/1] = R.
```

This closes only the identity-localization stage of the computational-scheme
audit. The fixed-image construction below supplies the next potentially
nontrivial representation; the representation-independent iterated/basic-
open overlap theorem is a separate downstream layer.

The next rule-free layer computes the opposite degenerate endpoint. The ring
axioms first derive

```text
x * 0 = 0,
0 * x = 0,
-0 = 0.
```

Consequently explicit unit evidence for zero gives `0=1`, after which every
carrier element equals zero. The unique point map from `R` to the zero ring
therefore satisfies the full localization universal property:

```text
comm_ring_zero_localization(R) : Loc_R(0)
target(comm_ring_zero_localization(R)) = zero_comm_ring
map(comm_ring_zero_localization(R))(x) = tt.
```

An admissible map `h:R->S` sends zero to an invertible element; transport along
its zero-preservation path makes `0_S` invertible and hence proves `0_S=1_S`.
That path constructs the unique structured factor `zero_comm_ring -> S`, and
structured-map extensionality plus the proposition-valued agreement fibre
makes the complete factorization Sigma contractible. This is the
computational empty-basic-open case. It is not yet a nondegenerate fraction
model, and by itself it does not establish the general affine-overlap law.

The next rule-free model handles every supplied multiplicative idempotent
`e^2=e` without fractions or quotients. Its carrier is the fixed image

```text
eR = Sigma x : |R|, e*x=x,
```

which is a set because `|R|` is a set and each fixed-point equation is a
proposition. It inherits zero, addition, negation, and multiplication from
`R`; its multiplicative unit is `e`. Equality of fixed-image elements is
therefore controlled by equality of their underlying elements, with the
equation fibre filled uniquely. The scaling map

```text
iota_e : R -> eR,
iota_e(x) = e*x
```

is a structured ring map. Idempotence supplies closure and multiplicativity;
the latter is the ordinary calculation `(e*x)*(e*y)=e*(x*y)`.

If `h:R->S` makes `h(e)` a unit, structured-map preservation makes `h(e)`
idempotent as well. An invertible idempotent equals one: for inverse `u`,

```text
a = a*1 = a*(a*u) = (a*a)*u = a*u = 1.
```

Consequently the selected factor sends `(x,e*x=x)` to `h(x)`. Its triangle
computes from `h(e*x)=h(e)*h(x)=h(x)`. For uniqueness, every fixed point `x`
is literally recovered propositionally by scaling its underlying element;
the competing factor triangle and structured-map extensionality then identify
the whole factor map, and the proposition-valued agreement fibre identifies
the complete factor package. Thus

```text
comm_ring_idempotent_image_localization(R,e,e2) : Loc_R(e)
target(...) = eR
element(map(...)(x)) = e*x.
```

This is an explicit computing localization representation and is genuinely
nondegenerate whenever `R` comes with a nontrivial idempotent. The separate
product layer now constructs `R x S` componentwise, including structured-map
action and whole identity/composition paths. It does not introduce a new
primitive functor head or duplicate generic functoriality. The closed Boolean
ring `F2` supplies a concrete factor, with its complete ring laws established
internally by finite elimination.

In `F2 x F2`, take

```text
e = (1,0),
e*e = e,
e != 0,
e != 1.
```

The last two statements are constructive maps from the corresponding path
types to `Empty`, obtained by projecting a hypothetical product path to the
Boolean component where `true=false`. The fixed-image localization therefore
gives a closed non-endpoint model. Its affine-basic-open arrow has target
`e(F2 x F2)`, and its carrier map executes as

```text
(x,y) |-> (x,0).
```

Thus the computation is observably neither the identity-localization example
nor the zero-localization example. This closes the concrete nondegenerate
localization/basic-open representation gate. It does not prove that arbitrary
localizations admit a fixed-image representation, and it does not by itself
identify Cartier matching sections with a whole internal descent equivalence,
construct the intended Zariski topology, or define `Spec` and schemes.

This is a representation-independent interface. Concrete fractions,
finite/unimodular families, powers, concrete polynomial representations, and
Zariski constructions remain separately consumer-gated layers.

### Iterated Localization And The Product Comparison

For `f,g : |R|`, the selected two-stage package is

```text
CommRingIteratedLocalizationAt(R,f,g)
  = Sigma Lf : CommRingLocalizationAt(R,f),
      CommRingLocalizationAt(target(Lf), map(Lf)(g)).
```

Its structure map is the stable pointwise composite of the two chosen maps.
The first-stage image of `f` remains a unit after applying the second map, and
the second stage makes the first-stage image of `g` a unit. Products of units
are units, so the composite sends `f*g` to a unit after transport across the
structured-map multiplication law.

Conversely, a localization map at `f*g` sends both `f` and `g` to units. If
`x*y` has inverse `u`, then `y*u` is an inverse for `x`, while `x*u` is an
inverse for `y` (with commutativity used for the latter equation). These
explicit witnesses let the map factor through localization at `f`; its factor
triangle transports the unit evidence for `g` to the intermediate map, which
then factors through the second localization.

Thus the universal properties supply two comparison factors:

```text
R[1/(f*g)]  ->  R[1/f][1/g]
R[1/f][1/g] ->  R[1/(f*g)].
```

Each factor retains a pointwise triangle over the original map from `R`.
`CommRingIteratedLocalizationComparison` packages these forward and reverse
factors with named map/agreement projections. It does not identify the two
chosen localization packages, and the comparison-data module itself does not
store inverse laws.

The downstream overlap module now supplies those laws without changing either
localization representation. First, if two inhabitants lie in the same
contractible factorization classifier, applying the factor-map projection to
their canonical path gives equality of the whole structured maps. On the
product-localization side, the composite of the staged reverse and forward
maps and the identity map are both factors of the original map
`R -> R[1/(f*g)]`. Contractibility therefore gives

```text
reverse * forward = id_[R[1/(f*g)]].
```

The opposite law uses the two universal properties in sequence. Over the
first localization map, `(forward*reverse)*second` and `second` are two
factors of the original two-stage map, so first-stage uniqueness identifies
them as whole maps. Evaluating that map equality supplies the triangle needed
at the second localization stage. Second-stage uniqueness then gives

```text
forward * reverse = id_[R[1/f][1/g]].
```

Both paths are explicitly transported from the stable pointwise composition
and identity witnesses to the generic `CommRing_cat` composition and identity
owners. No new reduction rule is introduced. The canonical forward comparison
therefore carries

```text
OmegaEquivAlong
  CommRing_cat
  R[1/(f*g)]
  R[1/f][1/g]
  forward,
```

with the staged reverse map selected in both inverse slots; a first-class
`OmegaEquiv` facade is derived from the same evidence. This is a whole
internal algebraic overlap equivalence, not an external pair of pointwise
cancellation observations. It still assumes chosen universal-property
localization packages and supplies neither fractions nor a concrete
nondegenerate localization model. Equality of the chosen packages, presheaf
restriction coherence, topology, `Spec`, and schemes remain separate gates.

### CommRing-Valued Presheaves And Invertibility Support

A commutative-ring-valued presheaf uses the direct ordinary functor
presentation

```text
CommRingPsh_cat(K) = Functor_cat(Op_cat(K), CommRing_cat)
CommRingPsh(K)     = Obj(CommRingPsh_cat(K)).
```

This classifier is a transparent definition rather than a rigid facade at the
current boundary. Cat-valued `Psh_cat(K)` has a useful separate head because
it mediates the public presheaf category and the distinct active
`Catd_cat(Op(K))` representation, with controlled recovery of the base. Here
the ordinary functor category is the sole selected representation, and current
consumers retain `K` explicitly. A later whole-sieve or ringed-site consumer
could justify an audited rigid-facade migration if it needs stable head
recognition, base recovery, or representation independence. For
`O : CommRingPsh(K)`, `f : V -> U`, and `s : |O(U)|`, the current observations are

```text
comm_ring_psh_value(O,U)           = O[U]
comm_ring_psh_restriction_hom(O,f) = O[f] : O(U) -> O(V)
comm_ring_psh_restrict(O,f,s)      = O[f](s).
```

The last term applies the actual retained carrier function of the structured
ring map, so an explicit restriction map remains computational. Generic
identity and composition in `CommRing_cat` still do not reduce on carrier
elements. The library instead proves

```text
O[id_U](s)     = s
O[f ∘ g](s) = O[g](O[f](s))
```

through the selected pointwise identity/composition maps. After specializing
to `Op_cat(K)`, opposite identity has already normalized to the identity of
`K`, so the generic projection-order bridge makes the whole restriction arrow
reduce to the generic `CommRing_cat` identity. The rule-free
`fapp1_id_path` theorem retains the same boundary as typed proof evidence,
while the selected pointwise identity path crosses from that generic whole
identity to a carrier-computing map. No presheaf-specific rule is installed,
and application of the generic whole identity remains deliberately opaque on
carrier elements.

The semantic support of a section is currently exposed arrowwise:

```text
CommRingPshInvertibleAlong(O,s,f)
  = CommRingUnitEvidence(O(V), O[f](s)).
```

It is a proposition because explicit unit evidence is a proposition. If the
predicate holds for `f : V -> U` and `g : W -> V`, preservation of units by
`O[g]` gives a unit witness for the nested restriction; the composite path
transports it to `O[f ∘ g](s)`. Thus the expected downward-closure
calculation is present at ordinary arrows.

The maintained zero-ring model makes this nonvacuous. The constant
`zero_comm_ring` presheaf has generic structured identities as restrictions;
the pointwise identity path evaluates each restriction on `tt`, and the
explicit zero-ring unit witness transports to every arrow.

The downstream carrier/unit-family construction now assembles this predicate
as an ordinary `Sieve(K,U)`. Its higher fibre at a literal `(V,f)` reduces to
`Path_cat(CommRingPshInvertibleAlong(O,s,f))`, and ordinary
`SieveMembership(D(s),(V,f))` reduces to the unit-evidence classifier above.
The full higher action is inherited from pullback and Sigma/Catd owners; no
ad hoc identity or composition rule is added.

A first locality bridge then keeps two logically different observations
separate. For a supplied topology `T`,

```text
CommRingPshInvertibilityCover(T,O,U,s) = Covers_T(D_O(s))
```

is proposition-valued. It says that `s` is invertible locally everywhere; it
does not say that every section has this property, nor does it define a local
ring. Independently, if `ell` is a chosen universal-property localization of
`O(U)` at `s` and `(f,m)` is an actual member of `D_O(s)`, then `m` is exactly
unit evidence for `O[f](s)`. The localization property therefore selects

```text
factor(ell,f,m) : O(U)[1/s]_ell -> O(V)
factor(ell,f,m)(ell(x)) = O[f](x).
```

The second line is retained as a pointwise path on carrier elements. The
category

```text
Elem(D_O(s)) = Sigma_cat(sieve_higher(D_O(s)))
```

has literal objects `(V,f,m)`. Its two Sigma projections give a functor
`dom:Elem(D_O(s))->Op(K)`, and `O o dom` is the CommRing-valued value diagram.
The selected factors are packaged as the internal cone

```text
factorCone(ell) : Const(O(U)[1/s]_ell) => O o dom
factorCone(ell)[(V,f,m)] = factor(ell,f,m).
```

The cone is an ordinary `Transf`, so its full off-diagonal action and
naturality are inherited from the generic `tapp1` calculus. Downstream
consumers do not carry an external family of commutative squares. In the
closed constant zero-ring model, the literal cone component reduces to the
actual presheaf restriction map.

This typed owner is supported by the universal-property proof rather than an
independent naturality axiom: factorization is contractible, ordinary-sieve
membership fibres are subterminal, and `CommRing_cat` homs are equality
categories on a set of structured maps. The restriction comparison below is
the explicit construction audit; the remaining proof-fibre/higher coherence
is propositionally unique and is packaged by the primitive `Transf` boundary.

There is also a theorem-level construction audit. If `g:W->V`, the unit
witness at `f` restricts to one at `f o g`. Mapping the factor triangle by
`O[g]` and composing with presheaf functoriality makes
`O[g] o factor(ell,f,m)` another localization factor over `O[f o g]`.
Contractibility of that factorization space therefore supplies

```text
factor(ell,f o g,g^*m) = O[g] o factor(ell,f,m).
```

This external equation validates the literal component presentation; it is
not a second public naturality field. The internal cone is the computational
front of the historical Cartier comparison
`lim_{V in D(s)} O(V) = O(U)[1/s]`. The current module does not yet identify
that cone as a limit, compare it with selected descent, or claim sheafhood or
a ringed-site package.

The first direct consumer applies the internal cone to actual localization
elements without externalizing its coherence. Pull the Path-valued carrier
family back along the value diagram:

```text
MatchingCarrier_O(s)[V,f,m] = Path_cat(|O(V)|)
Matching_O(s) = Pi_(V,f,m in Elem(D_O(s))) MatchingCarrier_O(s)[V,f,m].
```

An object of `Matching_O(s)` is therefore one internally coherent family of
carrier elements. For every `x : |O(U)[1/s]_ell|`, the selected section has
literal component

```text
matchingSection(ell,x)[V,f,m] = factor(ell,f,m)(x).
```

This computation uses the full displayed carrier action: first fix `x` in the
source fibre, then apply `fib_cov_tapp0_func` to the selected structured factor
map. Postcomposing the ring-valued cone and capping its action first would lose
that executable element application. No direct capped carrier rule is added;
the existing full-action owner remains the unique route.

Finally, `path_lift_fapp0` packages the assignment as

```text
restrict_ell : Path_cat(|O(U)[1/s]_ell|) -> Matching_O(s).
```

Thus an equality path between localization elements is mapped to an arrow
between their coherent matching sections. Pi owns compatibility over arrows
of `Elem(D_O(s))`, Catd owns the carrier-family action, and PathLift owns the
source path action. No separate naturality square, identity proof, or
composition proof is propagated through the public API. The closed zero-ring
consumer evaluates the section to the actual restriction of `tt`.

This matching module itself owns only the localization-to-matching direction.
The downstream glue/locality layer may accept a selected whole inverse and
its laws without changing this construction. A general generated topology,
truncation reflector, or sheafification construction is not a prerequisite
for this direction and is not implied by it.

The selected glue layer closes the next, specifically Cartier-locality,
boundary. It is important not to confuse this with ordinary sheaf descent:
the invertibility sieve `D(s)` describes the basic open where `s` is
invertible and need not cover `U`. For a chosen localization, selected glue is
a genuine functor

```text
glue_ell : Matching_O(s) -> Path_cat(|O(U)[1/s]_ell|).
```

Thus every arrow between coherent matching families is mapped internally to
an equality path between their glued localization elements. The earlier
compatibility package also retains

```text
glue_ell(restrict_ell(x)) = x
restrict_ell(glue_ell(m))[V,f,r] = m[V,f,r].
```

The second equation is stored as a component observation of already coherent
Pi objects, not as an external naturality family. Its literal left endpoint
computes further to

```text
factor_O(ell;f,r)(glue_ell(m)).
```

This is the computational content of the historical Cartier
`mod_loc_elim` rule, now separated from the old global sheafification fold and
expressed entirely through active functor, Pi, and localization owners. The
package and all its observations are transparent and rule-free. The derived
zero-ring model takes glue to the constant functor at `tt`; Unit
contractibility proves both observed laws, while the closed component theorem
reaches the actual zero-presheaf restriction. That model is intentionally not
advertised as constructing the stronger whole capability below.

For a scheme-facing consumer, the stronger supplied boundary is

```text
CommRingPshLocalizationLocality(K,O,U,s,ell)
  = OmegaEquivAlong Cat_cat
      Path_cat(|O(U)[1/s]_ell|)
      Matching_O(s)
      restrict_ell.
```

The forward functor is fixed to the already-computing `restrict_ell`. The
selected left inverse is `glue_ell`, and the two retained paths are equality
of whole functor objects:

```text
glue_ell o restrict_ell = id
restrict_ell o glue_ell = id.
```

The native `OmegaEquivAlong` data initially carries separate left and right
inverse functors. The transparent equality/hom-action extension proves that
they agree and publicly exposes the consequence that the selected left
inverse also satisfies the right whole-functor law. Thus the commutative-
algebra layer does not duplicate a half-adjoint proof. Evaluating the first
whole path at a localization element and the second at a matching object and
support element derives the earlier two observations; a transparent adapter
reconstructs `CommRingPshLocalizationGlue` for its existing consumers.

This whole locality is supplied capability data, not a theorem derived from
the earlier component observations. The bounded whole-comparison audit
correctly found that promoting those observations alone to equality of whole
functor objects would require additional section/functor extensionality. No
such extensionality, univalence, or equality rule is added here. Conversely,
`DefIso` would demand judgmental cancellation and is therefore too strict.

### Global Reflective CommRinged Objects And Covers

The first non-affine continuation deliberately stops before affineness or a
scheme record. On a fixed base category `K`, it packages

```text
ReflectiveCommRingedSpaceCover(K)
  = Sigma A : ReflectiveCommRingedSite(K),
    Sigma X : Obj(K),
    Sigma R : Sieve_K(X),
      Covers(topology(A),R).
```

The distinguished `X` supplies a global-first object and `R` supplies a
selected covering atlas in sieve form. The included structure presheaf is
routed through `A`; it is not copied into the package. For every arrow
`f : V -> X`, the existing Grothendieck-stability theorem constructs

```text
Covers(topology(A),f^*R).
```

An actual selected cover chart is the dependent pair of a restriction-total
object `(V,f)` and evidence that it belongs to `R`. Its domain and arrow are
the existing `into_restr_domain` and `into_restr_arrow` projections. Pulling
the global cover back along that arrow gives the chart's internally derived
overlap cover; later pairwise overlap candidates are members of this
pullback. No external overlap square or cocycle family is stored.

This package does not say that the cover is finite or that any member is
affine. A later affine-realization capability must compare the ambient chart
restriction honestly with an affine presentation; merely attaching an
unrelated ring would not establish affineness. Locally-ringed support,
finite-qcqs selection, gluing realization, and a scheme category remain
separate downstream gates.

### Binary Generation Of A Selected Covering Sieve

Two arrows that merely belong to a covering sieve need not themselves cover.
For selected members `c0 : U0 -> X` and `c1 : U1 -> X`, the binary generation
capability therefore retains, for every `q : V -> X` in the selected sieve
`R`, constructive data

```text
b : Bool,
h : V -> U_b,
q = c_b o h.
```

This is `BinarySelectedCoverGeneration`. It is witness-rich rather than
propositionally truncated: chart selection and the factor map remain
executable. The factorization says that `R` is contained in the sieve
generated by `c0,c1`; their already-retained membership and sieve closure give
the reverse containment. Hence the two selected arrows generate the known
covering sieve without constructing a second sieve object or a new coverage
law.

The selected arrows are atlas generators. Arbitrary members of `R` are their
further restrictions and are not asserted affine. Closure under still further
restriction follows by generic composition; it is not stored as a naturality
or coherence field. This binary interface is the first finite arity and can
later generalize to Nat-indexed choice when a higher-arity consumer requires
it.

### Whole Ambient Chart Slices And Supplied Reflective Presentations

For an object `U : Obj(K)`, the restriction-oriented arrow total has the
whole generic Sigma projection

```text
into_restr_domain_func(U) : Into_restr_cat(K,U) -> K^op.
```

Taking opposites gives the conventional whole slice-domain functor

```text
slice_domain_func(U) : Slice_cat(K,U) -> K.
```

Consequently a CommRing-valued presheaf restricts without a new action
calculus:

```text
comm_ring_psh_pullback(F,O) = O o Op(F),
O_X|_U = comm_ring_psh_pullback(slice_domain_func(U),O_X).
```

These are whole functors. Generic composition owns their object action,
structured restriction maps, functoriality, and naturality. At an arbitrary
encoded-Sigma slice object the stable value endpoint remains evaluation of
`slice_domain_func`; no package eta identifies that term with a separately
projected `sigma_Fst`. At a literal arrow `(V,f)` the whole domain functor and
therefore the ambient presheaf value compute to `V` and `O_X(V)`.

The assumption-explicit classifier

```text
SuppliedReflectiveCommRingedSlicePresentation(A,U)
  = Sigma B : ReflectiveCommRingedSite(Slice_cat(K,U)),
      DefIso(include(O_B), O_A|_U)
```

retains a supplied reflective CommRinged site on the actual slice and a whole
computational presentation of its included structure presheaf. The `DefIso`
owns both whole transformations and their strict cancellation, so readable
components are observations rather than external naturality laws.

This package deliberately does **not** claim that the topology, sheaf
category, reflector, or structure-sheaf object of `B` was induced from `A`.
The active site library has no general topology transport along a site
functor, and the supplied `Sheaf_cat` facade has no pullback-reflector theorem.
An honest continuity/induced-topology capability remains separate from this
computational presentation and from later affine-chart realization.

### Whole Sheaf-Basis Comparisons

For a selected functor `i : A -> B`, ordinary opposite precomposition gives
the whole restriction functor

```text
i^* : Functor(B^op,V) -> Functor(A^op,V).
```

The generic precomposition owner's runtime object action remains in its
cut-oriented normal form. `psh_restriction_value_path(i,P)` proves at proof
time that this value equals the direct composition spelling `P o Op(i)`, and
`psh_restriction_value_iso(i,P)` turns that path into ordinary
`IsoEvidence`. These are presentation bridges, not a new runtime fold; whole
arrow action remains owned by generic precomposition. Scheme-facing
specializations may use direct composition when judgmental value computation
is part of their public contract.

Given supplied sheafification capabilities on `(A,T_A)` and `(B,T_B)`, a
`SuppliedSheafRestrictionAlong(i)` retains a whole functor between their sheaf
categories and one `IsoEvidence` comparing the two whole composites into
`Functor(A^op,V)`: include after sheaf restriction versus presheaf
restriction after include. A `SuppliedSheafBasisEquivalenceAlong(i)` adds
`OmegaEquivAlong Cat_cat` for that exact selected restriction functor.

This is comparison-lemma strength, not an equivalence of the raw base
categories. The `IsoEvidence` and `OmegaEquivAlong` objects own their complete
transformation/functor action, so no family of component naturality or
commutative-square equations is retained. A locally exact site square is one
possible semantic route to a stronger sheafification Beck--Chevalley mate;
it is neither a field of this basis package nor yet consumed here.

### Computational Big Affine Spec Slice

The first scheme-facing facade is the conventional big affine slice

```text
AffineSpecBigSlice_cat(R) = Slice_cat(Op(CommRing_cat),R).
```

Its objects are structured maps `R -> S`, while arrows point geometrically
from `Spec(T)` to `Spec(S)`. The opposite slice is definitionally the existing
Sigma total of the represented presheaf, so the coordinate-ring presheaf is
simply

```text
affine_spec_coordinate_psh(R)
  = Sigma_proj1_func(CommRing_cat, yoneda_psh(Op(CommRing_cat),R)).
```

This is a whole CommRing-valued functor, not an object-only assignment. At the
identity chart its value computes to `R`; at a selected basic-open chart
`D(f)` it computes to the chosen localization target `R[1/f]`. A commuting
structured triangle `R -> S -> T` constructs an actual internal slice arrow
`Spec(T) -> Spec(S)` through the generic Sigma-arrow owner, and coordinate
restriction along it computes to the supplied whole structured map `S -> T`.

For the first overlap, the universal-property comparison between
`R[1/(f*g)]` and `R[1/f][1/g]` already supplies forward and reverse structured
maps, their triangles over `R`, and whole cancellation paths. The affine Spec
facade lifts the two maps to geometric chart arrows in opposite directions.
The coordinate presheaf restricts along them to exactly those maps and reuses
their existing `OmegaEquiv CommRing_cat`. No fraction representation,
localization-package equality, new naturality data, functor equality, or
univalence principle is added. The split idempotent in `F2 x F2` supplies a
closed non-endpoint basic-open chart.

This big slice is a computational precursor, not the selected small Zariski
site and not yet a locally ringed space or complete scheme. The finite
basic-open atlas, chart restriction, and overlap computations are separate
downstream consumers. The direct topology on this same big slice is supplied
by the next layer; sheaf descent, subcanonicity, comparison with the small
site, and canonical sheafification remain independent theorem/interface
layers.

### Direct Big-Affine Zariski Topology

Fix a base ring `R` and a literal chart `h : R -> S`. For a selected
localization package `ell : CommRingLocalizationAt(S,f)`, the exact internal
base map of the localized chart is the existing opposite-precomposition
endpoint

```text
R --h--> S --iota_ell--> S[1/f]_ell.
```

Using this endpoint, `affine_spec_chart_localization_arrow` is a whole arrow

```text
Spec(S[1/f]_ell) -> Spec(S)
```

inside `AffineSpecBigSlice_cat(R)`. Its slice triangle is reflexive by
construction, and applying the whole coordinate presheaf computes to the
existing structured localization map `iota_ell : S -> S[1/f]_ell`. No
external commutative triangle, point-only restriction field, or
constructor-specific naturality law is stored.

For a selected finite Zariski family on `S`,
`AffineSpecChartZariskiCoverFamilyMembership` says that each of these whole
localization-chart arrows belongs to a sieve `Q` on the literal chart. The
arbitrary-object generator

```text
AffineSpecBigZariskiGenerators(R)
  : SieveGeneratorFamily(AffineSpecBigSlice_cat(R))
```

uses one outer `sigma_ind` to expose the retained coordinate ring and
structure map of a general slice object. This eliminator is semantically
important: encoded Sigma packages have no global eta rule, so rebuilding an
arbitrary chart from projections is not assumed convertible to the original
object. The branch then retains a selected
`CommRingZariskiCoverFamily(S)` together with literal containment of all its
lifted arrows in `Q`.

Applying the generic intersection construction gives

```text
affine_spec_big_zariski_topology(R)
  : GrothTopology(AffineSpecBigSlice_cat(R)).
```

Every selected finite chart family covers, and
`affine_spec_big_zariski_topology_least` maps its coverhood into any other
topology accepting the same generators. The presentation witnesses remain
available; only generated coverhood is proposition-valued. This is the least
topology in the public inclusion order, without a cover-derivation syntax,
decision procedure, truncation/HIT, coverhood rewrite, or global localization
choice.

The construction is the selected topology route for the first computational
affine MVP. It does not identify the big affine site with the small site of
opens, prove subcanonicity, construct sheafification, or package a scheme.
Those are later consumers of this topology and of the already-computing chart,
restriction, overlap, and Cartier-locality maps.

### Assumption-Explicit Affine Reflective Structure Sheaves

The first structure-sheaf layer consumes the exact big-affine topology above
without pretending to construct sheafification. For a base ring `R`, an
`AffineStructureSheafPresentation(R)` retains:

```text
S : SheafificationCapability(AffineSpecBigSlice_cat(R), BigZar(R), CommRing)
O : Obj(Sheaf_cat(AffineSpecBigSlice_cat(R), BigZar(R), CommRing))
i : DefIso(CommRingPsh_cat(AffineSpecBigSlice_cat(R)), include_S(O), O_coord).
```

Here `O_coord` is the existing whole `affine_spec_coordinate_psh(R)`. Thus the
presentation determines a `ReflectiveCommRingedSite` whose topology is
definitionally the internally generated `BigZar(R)`, while
`affine_structure_sheaf_coordinate_defiso` relates its included structure
sheaf to the presheaf whose chart restrictions already compute.

The comparison is deliberately a whole `DefIso` in the functor category.
Its forward and inverse arrows are transformations, so ordinary action and
naturality remain at the generic transformation owners. The readable
`affine_structure_sheaf_to_coordinate_at` and
`affine_structure_sheaf_from_coordinate_at` operations only project those
transformations at one site object. At a literal chart `R -> S`, their
coordinate endpoint computes to the whole ring `S`; they are not an
object-only substitute for the comparison.

This layer is assumption-explicit in two independent ways: the reflector is
supplied, and the computational comparison is supplied. It proves neither
that the coordinate presheaf is a sheaf nor that arbitrary sheafification
constructs it. It also does not yet supply the historical `D(f)`
localization/glue capability on the relative big site, a stalk-local-ring
condition, a small-site comparison, or a scheme record. Those distinctions
keep the next computational-locality tranche honest.

### Assumption-Explicit Affine Coordinate Locality

The next capability retains the whole locality above uniformly over the
computing coordinate presheaf:

```text
AffineCoordinateLocalizationLocality(R)
  = Pi U : AffineSpecBigSlice_cat(R),
    Pi s : O_coord(U),
    Pi ell : CommRingLocalizationAt(O_coord(U),s),
      CommRingPshLocalizationLocality(O_coord,U,s,ell).
```

At a literal chart `h : R -> S`, `O_coord(h)` reduces to `S`, so the endpoint
is the supplied localization `S[1/s]_ell` and the existing whole restriction
functor. `affine_coordinate_localization_locality_at` exposes that selected
whole equivalence. The compatibility operation
`affine_coordinate_localization_legacy_glue` derives the earlier
point/component glue package rather than postulating a second glue map.

This is deliberately independent of the chosen PSSS-11a structure-sheaf
presentation: the final scheme record can pair the computing coordinate
locality with the whole `DefIso` relating that coordinate presheaf to its
selected included sheaf. The capability quantifies over every localization
package that is supplied; it does not make a global localization choice or
construct an inhabitant. Since `D(s)` need not cover the ambient chart, this
is Cartier/Zeuner localization locality, not ordinary covering-sieve descent,
subcanonicity, or a stalk-local-ring theorem.

### Thin Computational Affine-Scheme Presentations

Once the whole structure-sheaf presentation and whole coordinate locality are
available, an affine scheme needs no second copy of their derived operations:

```text
AffineSchemePresentation(R)
  = Sigma P : AffineStructureSheafPresentation(R),
      AffineCoordinateLocalizationLocality(R).
```

The first projection determines the reflective CommRinged site on the exact
internally generated big-Zariski topology and supplies a whole `DefIso` from
the included structure sheaf to the computing coordinate presheaf. The second
projection fixes canonical localization restriction as a whole equivalence at
every chart and selected localization. Thus the record is small because its
fields are already internal, functorial structures—not because action or
coherence has been discarded.

The ring remains an index and continues to determine the affine slice,
coordinate presheaf, whole chart, and unit cover. A nontrivial finite atlas is
consumer data. In the first closed-base example, `R = F2 x F2`; the two
structure/locality capabilities are visibly supplied, while the generated
topology, complementary-idempotent cover, fixed-image chart rings, whole
restrictions, and zero overlap compute from existing owners.

This is an assumption-explicit computational affine presentation. It does not
construct sheafification or locality, and it does not yet supply a category of
schemes, general non-affine gluing, a small-site comparison, stalks, or a
stalk-local-ring theorem. The later TypeScript structure macro may generate
its Sigma constructor/projection boilerplate, but that authoring convenience
does not alter the kernel contract.

### Whole Ambient Affine-Basis Realizations

For an ambient reflective ringed site `A` on `K`, an object `U`, a supplied
reflective presentation of the actual slice `K/U`, and an affine presentation
`X_R`, select a whole basis functor

```text
i : AffineSpecBigSlice_cat(R) -> Slice_cat(K,U).
```

The ambient structure presheaf restricted along `i` is ordinary whole
precomposition, so its value at an affine basis object computes by evaluating
the ambient slice presheaf at `i(q)`. The realization package is

```text
AffineBasisRealizationAlong(A,U,P,R,X_R,i)
  = Sigma basis : SuppliedSheafBasisEquivalenceAlong(i),
      DefIso(ambient_O|_i, affine_scheme_underlying_psh(X_R)).
```

Composing the retained `DefIso` with the affine presentation's existing
coordinate `DefIso` gives one whole comparison from the actual ambient
restriction to `affine_spec_coordinate_psh(R)`. The semantic basis
equivalence and computational presheaf bridge are complementary: the first
prevents an unrelated affine label; the second preserves executable
coordinate normal forms. Neither duplicates naturality, asserts equivalence
of the raw slice categories, or transports generic glue. A sheafification
Beck--Chevalley mate remains a separately consumer-gated capability.

### Global-First Binary Affine-Cover Presentations

For one selected generator `c : U -> X`, an
`AffineCoverChartRealization(P,c)` retains exactly the data needed to make its
domain honestly affine relative to the ambient structure:

```text
Sigma slice : SuppliedReflectiveCommRingedSlicePresentation(A,U),
Sigma R : CommRing,
Sigma affine : AffineSchemePresentation(R),
Sigma i : Functor(AffineSpecBigSlice_cat(R), Slice_cat(K,U)),
  AffineBasisRealizationAlong(A,U,slice,R,affine,i).
```

The existing basis owner carries whole sheaf semantics and the whole
computational presheaf bridge. Its composed coordinate `DefIso` is derived,
so the chart package stores no objectwise naturality or restriction squares.
Readable observations are exposed, while dependent projection types retain
literal nested-Sigma endpoints; no package eta, rewrite, or unifier is needed.

The global-first binary package is then

```text
BinaryAffineCoverPresentation(P)
  = Sigma c0,c1,
    Sigma generation : BinarySelectedCoverGeneration(P,c0,c1),
      AffineCoverChartRealization(P,c0)
      * AffineCoverChartRealization(P,c1).
```

Thus the two selected generators cover and each generator has a whole affine
realization. Other sieve members remain refinements, not additional affine
fields. Pairwise overlaps and repeated restrictions continue to be derived
from the existing global object, sieve pullback, and generic composition. The
package is deliberately called an affine-cover presentation: point-free
locally-ringed support, an explicit open-immersion classifier, a semantic
scheme category, and atlas-first gluing realization remain separate gates.

### Computing The Affine Generator Of A Sieve Refinement

For `q : V -> X` in the retained covering sieve, evaluating
`binary_affine_cover_refinement_at(Q,q,member)` returns the existing
`BinaryCoverChartFactorization`. Its Boolean side selects `c0` or `c1`, and
the factorization supplies `h : V -> U_b` with `q = c_b o h`. The same side
then computes:

```text
binary_affine_cover_refinement_chart       : the selected generator c_b
binary_affine_cover_refinement_realization : its whole affine realization
binary_affine_cover_refinement_ring        : its coordinate ring
```

These observations do not form another record. The presentation already owns
both realizations, so Boolean elimination derives the matching one without
duplicating data. For an open Boolean side the realization stays in its
canonical branch-indexed family; the readable selected-chart observation is
not promoted to a dependent fusion rule. Most importantly, `q` is a
refinement through an affine chart, not necessarily another affine chart.

### Topology-Local Local-Ring Presentations

For a CommRing-valued presheaf `O` on `(K,T)`, the two nonautomatic local-ring
support laws can be expressed without first constructing finite joins of raw
sieves. The literal empty sieve is

```text
empty_sieve(U) = const_{Into(U)} Path(Empty).
```

Its membership computes to `Empty`. A topology-local presentation supplies:

```text
zero_local(U) : Unit_O(U)(0) -> Covers_T(empty_sieve(U))

sum_local(U,s,t) : Unit_O(U)(s+t) ->
  Sigma R : Sieve(U),
    Covers_T(R) *
    Pi q in R,
      Sigma b : Bool,
        if b=false then Unit(O(q)(s)) else Unit(O(q)(t)).
```

This is the Kripke--Joyal computational reading of `D(0)=bottom` and
`D(s+t)<=D(s) join D(t)`: if a sum is a unit, a selected cover exposes where
one summand is a unit. The selected sieve, member, and Boolean branch are
presentation data rather than a propositionally truncated existence claim.
The whole sieve owns restriction closure, so no external naturality family is
stored. The laws `D(1)=top` and `D(st)=D(s) meet D(t)` are algebraically
automatic and remain a later derived comparison; no duplicate runtime owner
is introduced merely to restate them.

For a distinguished object `X` of an ambient reflective ringed site, locality
belongs on the actual slice `K/X`. A
`ReflectiveCommRingedWholeObjectLocalPresentation(P)` therefore retains a
`SuppliedReflectiveCommRingedSlicePresentation(A,X)` and applies
`CommRingPshTopologyLocalRingPresentation` to the whole computing ambient
restriction, using the supplied slice topology. The slice package continues
to own sheaf semantics and one whole `DefIso` from its included sheaf to that
computing target.

Finally,

```text
BinaryLocallyRingedAffineCoverPresentation(P)
  = Sigma local : ReflectiveCommRingedWholeObjectLocalPresentation(P),
      BinaryAffineCoverPresentation(P).
```

This is the fibrewise locally-ringed plus computational-atlas certificate over
the retained global object. Its site-relative semantics do not require a
second generic `IsOpen` field: the supplied site and topology already select
the admissible chart geometry. In particular, only the two selected cover
generators are required to carry affine realizations. Arbitrary arrows in the
sieve they generate are refinements and need not themselves have affine
domains.

The end-user total is

```text
BinarySiteRelativeSchemePresentation(K)
  = Sigma P : ReflectiveCommRingedSpaceCover(K),
      BinaryLocallyRingedAffineCoverPresentation(P).
```

It retains the global object and its structure presheaf once, together with
the topology-local capability, constructively generated binary cover, and the
two whole affine chart realizations. Restriction, overlap, and cocycle
compatibility are inherited from the already-global object and whole generic
composition; they are not record fields. This is a computational scheme
presentation relative to the selected site. It does not by itself identify
that site with the classical Zariski site, supply Zeuner's compact-open
classifier, construct the global object by atlas gluing, or define a
representation-independent category of schemes.

### Complementary-Idempotent Affine Atlas

The first finite atlas consumer uses product rings rather than postulating a
general chart-family abstraction. In `R x S`, let

```text
e  = (1,0),
e' = (0,1).
```

Both are idempotent, `e+e'=1`, and `e*e'=0`. The existing fixed-image
localizations at `e` and `e'`, together with unit coefficients, therefore
inhabit the existing `CommRingZariskiCoverFamily(R x S)`. That package remains
the source of truth for the finite presentation and its selected localization
data; there is no parallel record of charts and no global choice operation.

The two charts are the internal affine-slice objects `D(e)` and `D(e')`.
Their overlap is selected as the already-computing `D(0)`, whose coordinate
ring is `zero_comm_ring`. The canonical point maps into the zero ring satisfy
the required triangles over `R x S`, so the generic Sigma-arrow constructor
produces genuine geometric arrows

```text
D(0) -> D(e),
D(0) -> D(e').
```

The coordinate presheaf restricts along these arrows to the corresponding
whole structured ring maps from the chart rings to the zero ring. Thus both
object values and arrow action remain internal and computational at existing
functor, Sigma, localization, and CommRing owners; no external naturality
square is added. In the closed `F2 x F2` instance, `e*e'` reduces literally
to zero, giving a concrete non-endpoint two-chart affine atlas with empty
overlap.

This is an atlas/glue *presentation*, not yet a universal gluing theorem or a
scheme object. It does not construct a colimit, prove sheaf descent, package a
locally ringed space, or supply a general affine-atlas record. A recursive
facade tabulating every dependent affine chart from an arbitrary finite cover
was tested but crossed the bounded elaboration-performance threshold; the
existing cover family plus directly consumed chart observations is the
smaller and more stable interface. The optional whole-functor
extensionality/univalence boundary is unrelated to this computation.

### Affine Functor Of Points And Represented Basic Opens

The scheme-facing functor of points does not require a new primitive `Spec`
head. For a commutative ring `R`, use the existing Yoneda construction

```text
affine_spec_functor_of_points(R)
  = yoneda_psh(Op(CommRing_cat),R).
```

At a test ring `S`, its fibre computes to the whole structured-map classifier
`CommRingHom(R,S)`. This is not an object-only assignment: Yoneda already
supplies restriction along every map of test rings, and generic functor/hom
owners carry the corresponding arrow action and naturality.

For `f:R`, the semantic basic open is the existing invertibility sieve of the
shared identity CommRing-valued presheaf. Its `S`-points compute as

```text
D(f)(S) = Sigma(h : CommRingHom(R,S), UnitEvidence_S(h(f))).
```

Given a selected localization `i:R->R[1/f]`, precomposition sends a map
`k:R[1/f]->S` to the point `(k o i, k(i(f)) is a unit)`. Conversely, the
localization universal property selects a factor for every point of `D(f)(S)`.
Contractibility of the factorization classifier identifies a selected factor
with any supplied `k`; CommRing-map extensionality proves the whole-map
triangle, and proposition-valued unit evidence supplies the dependent Sigma
path in the other direction. These data construct directly

```text
TypeEquiv(CommRingHom(R[1/f],S), D(f)(S)).
```

No univalence principle is used: the equivalence is explicit data, not a
reflection of equivalence into equality. It is componentwise in the test ring
`S`, but both compared objects already retain their whole functorial action
internally. A natural equivalence of presheaves would additionally require
assembling the components with the relevant internal transformation data; it
is not silently replaced by external naturality fields or an ad hoc equality
rule. Generated topology, sheafhood, subcanonicity, locally ringed structure,
and a general scheme record remain separate gates.

This is the first direct functor-of-points bridge back to the computational
scheme MVP: basic-open membership is executable data and localization is shown
to represent it constructively. The later qcqs/spectral or Zeuner-style
comparison remains a different, substantially broader research problem.

### Finite Families And Unimodular Cover Presentations

A finite homogeneous family uses only the existing natural-number and Sigma
calculus:

```text
FiniteFamily(A,0)       = Unit
FiniteFamily(A,succ n)  = Sigma(x : A), FiniteFamily(A,n).
```

Thus a visible successor family is a head followed by a shorter tail, and a
visible zero family is the terminal record. `finite_family_map` acts
pointwise by Nat recursion. If `A` is a set, repeated Sigma truncation closure
proves `FiniteFamily(A,n)` a set. The successor is intentionally the literal
constant-family Sigma rather than the rigid `Product_grpd` head: the finite-
family consumer needs generic Sigma sethood and no independent product
identity or comparison rule. This representation introduces no `Fin`, lookup,
list append, permutation quotient, or new inductive declaration.

The same Nat recursion also defines dependent pointwise evidence:

```text
FiniteFamilyAll(P, [], ())          = Unit
FiniteFamilyAll(P, x::xs, (u,us))   = P(x) x FiniteFamilyAll(P,xs,us).
```

Its nil/cons and head/tail observations preserve the alignment between each
element and its evidence. This is a transparent fold over the selected tuple
representation, not another inductive family or a hidden lookup operation.

The downstream finite-containment consumer also needs evidence indexed by an
already-selected evidence family:

```text
FiniteFamilyAllOver(P,Q,[],(),()) = Unit
FiniteFamilyAllOver(P,Q,x::xs,px::ps,qx::qs)
  = Q(x,px) x FiniteFamilyAllOver(P,Q,xs,ps,qs).
```

Its generic map accepts both source and target `FiniteFamilyAll` witnesses
explicitly and maps every `Q(x,px)` to `Q'(f(x),py)`. It therefore does not
choose dependent target data and does not identify different choices. This
is still transparent Nat/Sigma recursion, with no new inductive family or
rewrite owner.

For a commutative ring `R`, the selected ordered folds are

```text
sum_R([])          = 0
sum_R(x :: xs)     = x + sum_R(xs)

dot_R([],[])       = 0
dot_R(a::as,f::fs) = a*f + dot_R(as,fs).
```

The ring laws can later compare alternative parenthesizations; computation
has only this right-associated owner. Nat induction proves that every
structured map `h : R -> S` preserves both folds. These are theorem-level
paths assembled from the stored zero, addition, multiplication, and unit
preservation fields, not new rewrite rules.

A finite family `f=(f_i)` is supplied as Zariski generating data together
with explicit coefficients:

```text
CommRingUnimodularPresentation(R,n,f)
  = Sigma(a : FiniteFamily(|R|,n)), dot_R(a,f) = 1.

CommRingZariskiCoverPresentation(R)
  = Sigma(n : Nat),
      Sigma(f : FiniteFamily(|R|,n)),
        CommRingUnimodularPresentation(R,n,f).
```

The first classifier is intentionally presentation data rather than a mere
existence proposition: different coefficient choices need not coincide, and
no propositional-truncation reflector has been selected. It is nevertheless
set-valued because coefficient families are sets and the equation fibre is a
property. The complete cover presentation is set-valued as well.

Applying `h` pointwise to generators and coefficients preserves the dot
equation and transports `1` through `h(1)=1`. Therefore
`comm_ring_zariski_cover_map` constructs a presentation over `S`. The derived
singleton `[1]` is a nonempty presentation over every ring; the binary helper
accepts the familiar correct unit-ideal equation `a*f+b*g=1`. For an affine
scheme, this is exactly the algebraic criterion that the basic opens
`D(f_i)` cover the whole spectrum.

This module stops before geometric interpretation. It does not yet build the
chosen localization maps `R -> R[1/f_i]`, `Spec`, basic-open objects, a sieve
coverage, or a Grothendieck topology. A cover of a relative basic open
`D(s)` additionally needs radical data such as
`s^N = sum_i a_i*f_i`; powers and that relative interface remain downstream
consumer gates.

### Presented Affine Basic Opens And Elementwise Base Change

The downstream Zariski module supplies geometric presentation data without
prematurely asserting a topology.  A selected localization family is

```text
CommRingLocalizationFamily(R,n,f)
  = FiniteFamilyAll(lambda f_i. CommRingLocalizationAt(R,f_i),n,f),

CommRingZariskiCoverFamily(R)
  = Sigma cover : CommRingZariskiCoverPresentation(R),
      CommRingLocalizationFamily(R,length(cover),generators(cover)).
```

Thus every generator retains a chosen universal-property localization. The
package makes no global choice and does not identify different chosen
localizations. In particular, the `[1]` family constructor accepts a selected
localization at `1` as input.

For `ell : CommRingLocalizationAt(R,f)`, the affine basic-open arrow is the
literal restriction-total object

```text
(R[1/f]_ell, iota_ell)
  : Into_restr_cat(Op(CommRing_cat),R).
```

Given `h : R -> S` and a target choice `m : Loc_S(h(f))`, the pointwise
composite `R -> S -> S[1/h(f)]_m` sends `f` to a unit. The universal property
of `ell` supplies a factor

```text
R[1/f]_ell -> S[1/h(f)]_m
```

and a pointwise triangle. Ring-map extensionality makes the triangle a path of
structured maps; the existing Sigma-arrow constructor then realizes the
comparison inside `Into_restr_cat(Op(CommRing_cat),R)`.

For an ordinary sieve `Q` containing the source basic-open arrow, Catd
transport along that Sigma arrow gives membership at the pointwise composite.
A theorem-level comparison moves from the pointwise composite to the stable
postcomposition object selected by `arrow_into_catd`; the transparent generic
observation `sieve_pullback_membership` finally returns membership of the
target basic open in `h^*Q`. The carrier action of the pointwise composite
computes literally as `x |-> iota_m(h(x))`.

No new rewrite or unification rule is needed. Runtime computation remains
owned by finite Nat recursion, the selected pointwise ring-map projection,
localization factorization, Sigma action, and Catd transport. The variance
crossings are named equality paths through existing post/precomposition
owners. This is selected elementwise base-change data, not yet a
proposition-valued coverage: the active library has no propositional-
truncation reflector that could erase coefficient, localization, and
containment choices honestly.

The bounded finite-containment layer now defines

```text
BasicOpenMembers_R(n,f,ell,Q)
  = FiniteFamilyAllOver(
      lambda f_i. Loc_R(f_i),
      lambda f_i ell_i. SieveMembership(Q,D_R(f_i;ell_i)),
      n,f,ell).
```

`comm_ring_zariski_cover_family_map(h,c,m)` maps the algebraic presentation
and accepts the entire target localization family `m` explicitly.
`comm_ring_unit_basic_open_family_pullback_membership` is the maintained
nonempty singleton consumer: it applies the elementwise theorem to the head
and the generic nil/cons recursion to return actual membership for the mapped
singleton. Arbitrary-length recursion remains owned by
`finite_family_all_over_map`.

The fully expanded specialization of that recursive map to ordinary-sieve
membership, and even a convenience specialized head projection, exceed the
60-second Lambdapi elaboration budget. A diagnostic rigid membership facade
did not improve this and is rejected. The active API therefore keeps
membership transparent, promotes no new rule, and treats only those expanded
convenience spellings as a performance gate. Generated or supplied Zariski
topology, propositionally reflected coverhood, subcanonicity, `Spec`, and
schemes remain later gates.

The first supplied-topology boundary can nevertheless be stated without any
truncation constructor. For an already lawful topology `T` on
`CommRing^op`, define

```text
PresentationCovers_T(c)
  = forall Q : Sieve(R), BasicOpenMembers_R(c,Q) -> Covers_T(Q),

IsZariskiCompatible(T)
  = forall R c, PresentationCovers_T(c).
```

Both classifiers are proposition-valued by dependent-Pi closure and the
existing proposition evidence for `Covers_T(Q)`. The package
`CommRingZariskiCompatibleTopology` retains `T` and this compatibility proof;
its consumer maps explicit family-containment terms to coverhood. It does not
truncate `c`, choose localizations, or construct the least topology generated
by these presentations. The checked chaotic instance establishes nonempty
feasibility only: it is generally finer than the intended Zariski topology
and proves neither exactness nor subcanonicity.

### Polynomial Algebras By Universal Property

For a base ring `R` and a variable classifier `X`, candidate polynomial data
are a commutative ring `P`, a structured base map, and a variable map:

```text
iota : CommRingHom(R,P)
vars : X -> |P|.
```

For another ring `S`, a base map `h : CommRingHom(R,S)`, and a valuation
`v : X -> |S|`, an extension is

```text
CommRingPolynomialFactor(iota,vars,h,v)
  = Sigma k : CommRingHom(P,S),
      (Pi r : |R|, k(iota(r)) = h(r))
      x
      (Pi x : X, k(vars(x)) = v(x)).
```

The classifier `IsCommRingPolynomialAlgebra(R,X,P,iota,vars)` requires this
extension space to be contractible for every `S`, `h`, and `v`.
`CommRingPolynomialAlgebra(R,X)` packages a chosen `P`, `iota`, `vars`, and
that universal property. This is precisely the free commutative `R`-algebra
interface: existence provides evaluation at every valuation, while
contractibility provides uniqueness together with both displayed triangles.

Both agreement fields are proposition-valued because their equations live in
the set-valued carrier of `S`; their dependent Sigma is therefore a property.
Consequently a path between two structured extension maps lifts uniquely to a
path between complete factor packages. The module uses this theorem-level
transport but adds no runtime rule, unification rule, or package eta.

The variable classifier is intentionally independent of `FiniteFamily`.
Finite families own ordered tuples, finite folds, and retained cover
presentations; polynomial freeness is naturally parameterized by the
classifier of variables itself. Since every valuation lands in a set-valued
ring carrier, paths in `X` are respected automatically. No `Fin`, list,
monomial, coefficient, quotient, or new inductive interface is selected.

The reviewer proves the generic zero-variable equation

```text
R[Empty] = R.
```

The base map is `comm_ring_hom_id_pointwise(R)`, the variable map is empty,
and the centre extension of `h : R -> S` is `h` itself. Its base agreement is
reflexive and its variable agreement follows by empty elimination. A
competitor's base triangle gives pointwise equality with `h`;
`comm_ring_hom_ext` and proposition-valued agreement transport complete the
contractibility proof. This is an executable model for every base ring, but
it does not pretend to be a concrete positive-variable representation. Such
a representation may later inhabit the same universal interface without
changing it.

Two independent families over the same base have a fibrewise product without
introducing a new primitive family former:

```text
P(B,C)[k] = B[k] × C[k].
```

The kernel constructs `P(B,C)` from ordinary product functoriality and pairs
family morphisms componentwise. Its internalized action is likewise
componentwise:

```text
cell(pair(FF,GG),p,u)
  = (cell(FF,p,u), cell(GG,p,u)).
```

This equation is computational at the existing displayed-cell and pairing
owners. It supplies the arrow/higher-action half of independent fibred
siblings; it does not assert that genuinely dependent telescope variables can
be exchanged. The TypeScript elaborator uses it in one bounded mixed context
`a; b,c; d`, where only `b` and `c` are siblings over the same prefix.

## 6. Dependent Sums: Total Categories

For a functorial family `E : K → Cat`, the dependent sum or total category is:

```text
Σ_K E = Σ_k E[k]
```

Its objects are dependent pairs:

```text
Obj(Σ_K E) = Σ (k : Obj K), Obj(E[k])
```

An object is written `(k,u)` with `u : E[k]`.

The hom category between two total objects is a directed dependent hom over the
base hom:

```text
Hom_{Σ E}((x,u),(y,v))
  = total category over Hom_K(x,y)
    whose fibre at f : x → y is
      Hom_{E[y]}(E[f](u), v)
```

Equivalently, an arrow `(x,u) → (y,v)` consists of:

```text
f : Hom_K(x,y)
α : Hom_{E[y]}(E[f](u), v)
```

The implementation presents this through an opposite-total convention, but the
mathematical content is exactly the base arrow plus dependent fibre arrow.

A natural family morphism `FF : E → D` induces a map on totals:

```text
Σ(FF)(k,u) = (k, FF[k](u))
```

A natural family transformation `eta : FF => GG` induces an ordinary
transformation between the two total maps:

```text
Σ(eta) : Σ(FF) => Σ(GG)
Σ(eta)[(k,u)] = (id_k, eta[k](u)).
```

The kernel names this higher projection `sigma_map_transf`. It is the next
generic hom action of `Sigma_func`; it is distinct from
`Sigma_transfd_funcd`, whose result is itself a displayed functor between
uncurried telescope families.

The current kernel also exposes the canonical total arrow over a base arrow:

```text
sigma_transport(E,p,u) : (x,u) → (y,E[p](u))
```

and the action of a Sigma map on such arrows:

```text
Σ(FF)[sigma_transport(E,p,u)]
  = sigma_map_transport(FF,p,u).
```

These are now definitions over the smaller Sigma-arrow constructor for total
arrows as `(base arrow, fibre arrow)` pairs, not additional axioms.

The first projection is a functor:

```text
π₁ : Σ_k E[k] → K
π₁(k,u) = k
```

For a constant family, the expected non-dependent sum is the product:

```text
Σ_K Const_K(A) = K × A
```

The current v3.2 file represents this by the direct normal form:

```text
Sigma_cat(Const_catd K A) ↪ Product_cat K A
```

The product projections have the expected readings:

```text
π₁ : K × A → K
π₂ : K × A → A
```

Product-valued functors now use the product normal form:

```text
Functor(X, A × B) = Functor(X,A) × Functor(X,B)
```

The projection functors are stable computational heads:

```text
Product_projL_func(A,B) : A × B → A
Product_projR_func(A,B) : A × B → B
```

Projection computation is consumer-oriented:

```text
π₁(H[i]) = (π₁ H)[i]
π₁(eta[i]) = (π₁ eta)[i]
π₁(eta[p]) = (π₁ eta)[p]
```

and homs reduce pointwise:

```text
Hom_{K×A}((x,u),(y,v)) = Hom_K(x,y) × Hom_A(u,v)
```

## 7. Dependent Products: Section Categories

For a functorial family `E : K → Cat`, the dependent product is the category of
sections:

```text
Π_K E = Π_k E[k]
```

An object `s : Π_K E` assigns:

```text
s[k] : E[k]
```

and carries coherent action over base arrows. For a base arrow `f : x → y`, the
section has a comparison arrow:

```text
s[f] : Hom_{E[y]}(E[f](s[x]), s[y])
```

For a constant family, sections are ordinary functors:

```text
Π_K Const_K(A) = Functor(K,A)
```

and evaluation of a section in the constant-family case agrees with ordinary
functor application:

```text
F[k] as a section = F[k] as an ordinary functor value
```

In `emdash3_2.lp`, `Pi_cat E` is the stable primitive section facade. It is
proof-time-comparable with both the terminal-source displayed presentation
`Functord_cat(Terminal_catd K,E)` and its ordinary Cat-valued-transfor
presentation. Its `Obj` classifier projects to the represented section
objects, while `Hom_cat(Pi_cat E,s,t)` projects to the corresponding
`Transfd_cat` next hom. For a constant family there is also a direct proof-time
comparison with `Functor_cat K A`. Runtime evaluation crosses the boundary
through the semantic `piapp0_func` / `piapp0` interface. Its object action is
terminal-source component evaluation; its hom action projects through the
generic ordinary higher-component observation `tapp0_hom_fapp0`, specializes
through the displayed-component functor `tdapp0_func`, and caps at
`tdapp0_fapp0`, which is named at the section surface by `pi_hom_fapp0`.
These Pi-facing eliminator names are definitions, not a second primitive
calculus. In the constant-family case `piapp0 F k` computes to ordinary
`fapp0 F k`.

More generally, if `Theta : eta -> eta'` is a higher arrow between ordinary
transfors, component evaluation has the stable observation

```text
tapp0_hom_fapp0(Y,Theta) : eta[Y] -> eta'[Y].
```

It is the capped hom action of the whole functor `tapp0_func(Y)`, preserves
higher identity and vertical composition computationally, and specializes at
`B := Cat_cat` to the existing `tdapp0_fapp0` head. Thus the Cat-valued
displayed notation is one selected runtime normal form of the generic
component calculus, not a parallel theory. The whole `fapp1_func` route still
lands in `tdapp0_func`, retaining its next action.

The capped projection remains coherent with higher ordinary naturality. If a
generic action component has already projected from `fapp1_fapp0(tapp0_func)`
to `tdapp0_fapp0`, the pre/right and post/left naturality cuts still accumulate
to the corresponding `tapp1_fapp0` at the composite displayed arrow. The two
identity-base cases also join after `tapp1_fapp0(epsilon,id)` has reduced to
`tapp0_fapp0(epsilon)`. These are projection-order joins around the existing
ordinary naturality owner, not new laws attached independently to Pi.

Vertical composition follows the same evaluator ladder as ordinary transfor
components:

```text
(eta o epsilon)[k] -> eta[k] o epsilon[k].
```

At the generic action layer, strict functoriality still contracts
`Ev_k[eta] o Ev_k[epsilon]` to `Ev_k[eta o epsilon]`. After projection to the
stable displayed-component head, the component beta expands that result back
to the pointwise composite. The two orientations are not competing global
normal forms: they operate at the generic action and stable evaluator heads,
respectively, and form a joining diamond. The displayed rule has two typed
clauses for the stable `Functord_cat` and ordinary `Transf_cat` presentations,
with the rigid category of the inner composite retaining the information
needed for subject reduction. The reverse contraction of two already-capped
components is neither required nor selected.

The same policy continues one dimension higher. `piapp1_func(s,x,y)` is the
terminal-source specialization of the generic displayed internal-hom action,
and `piapp1_fapp0(s,f)` evaluates that section at `f`. Its action on a cell
between base arrows reduces to `fdapp1_int_hom_fapp0`; consequently the result
remains inside the generic iterated-hom architecture rather than stopping at
an ad hoc Pi-specific component.

For the Sigma first projection, this stable head makes section uncurrying a
direct proof-time comparison:

```text
Π_(k,r) D[k] = (k :^n K ; R[k] ⊢ D[k]).
```

Runtime object and next-hom projections supply the corresponding displayed
functor and transfor components; the whole section category does not reduce to
the displayed-functor category.

Displayed-functor uncurrying itself varies through one whole ordinary functor:

```text
sigma_functord_sec_func(R,D)
  : Functor(Functord_cat(R,D),Pi_cat(Sigma(R),pi1^*D)),
sigma_functord_sec_func[FF] -> sigma_functord_sec(FF).
```

For a whole displayed transformation `eta : FF => GG`, its generic functor
action already owns one transformation between the two uncurried sections.
Projecting that whole arrow at an internal total object computes by the direct
evaluator beta

```text
sigma_functord_sec_func[eta][(k,r)]
  -> Const_transf(eta[k][r]).
```

This beta and naturality have different roles.  The beta defines the component
of the uncurrying lift; naturality of the already-whole generic action makes
those components coherent along every arrow of `Sigma(R)`.  Naturality alone
would not determine the component formula.  A separately named intermediate
`sigma_functord_sec_transfd` would merely factor this same projection through
another runtime head, so no such owner is selected.

Likewise, the hom action of `const_section_{K,A}` stays in the displayed
transformation facade (`Const_transfd_func` / `Const_transfd`). Ordinary
weakening has a separate stable owner `Const_func_func`; it no longer unfolds
through the displayed section constructor.

Conceptually, a section should also determine a functor into the total
category:

```text
section_total(s) : K → Σ_K E
section_total(s)(k) = (k, s[k])
π₁ ∘ section_total(s) = id_K
```

The named `section_total` facade is not currently exposed as a primitive in
v3.2, but its construction is no longer semantically missing. A transparent
terminal-total functor

```text
K → Σ_K Const_K(1)
```

followed by `sigma_map_func(s)` gives the section totalization. More
generally, for `F : A → K` and `D : Catd(K)`, the active owner

```text
sigma_pullback_total_func(F,D) : Σ_A(F^*D) → Σ_K D
```

computes on both levels:

```text
(a,u)       ↦ (F[a],u)
(p,alpha)   ↦ (F[p],alpha).
```

Thus a contextual pair over `F` is expressed transparently as terminal
totalization, then `sigma_map_func(s)` into `Σ_A(F^*D)`, then
`sigma_pullback_total_func(F,D)`. This is the Grothendieck totalization of the
existing asymmetric family reindexing `Pullback_catd D F`; it is not a
pullback constructor for arbitrary functors between total categories. The
direct section action `s[f]` remains available, with the dependent hom
construction as the shared internal architecture.

Independent displayed siblings over one base also have a computational
fibrewise product without a new primitive family owner. For
`B,C : Catd(K)`, regard both as Cat-valued functors and form the transparent
composite

```text
P(B,C)
  = uncurry(Product_cat_func) o Product_pair(B,C)
  : K -> Cat.
```

The existing product/uncurry semantics plus two owner-position projections
now compute

```text
P(B,C)[k] = Product_cat(B[k],C[k])
P(B,C)[p] = Product_map_func(B[p],C[p]).
```

The second equation deliberately recognizes the two component actions over
the same literal base arrow `p`. It does not assert an unrestricted
off-diagonal product action for unrelated `p` and `q`. Consequently this
transparent product supplies the first grouped-sibling fibre and transport
semantics while preserving `Product_map_func` as the iterable result.

Its fixed-base cartesian universal property is supplied by the active
displayed functors

```text
projL_d(B,C) : P(B,C) ⊢_K B
projR_d(B,C) : P(B,C) ⊢_K C
pair_d(FF,GG) : E ⊢_K P(B,C).
```

They compute at objects, on their full off-diagonal action, and on capped
base-arrow action. Both projection-after-pairing composites reduce to the
corresponding component. The full-action equations, rather than only their
capped instances, preserve the functor-valued result needed for iteration at
the next cell. Fibrewise exchange and contraction are therefore derived:

```text
swap_d(B,C) = pair_d(projR_d(B,C),projL_d(B,C))
diag_d(B)   = pair_d(id_d(B),id_d(B)).
```

This is structural logic for independent siblings over one fixed base, not
exchange across a genuine dependency edge. A primitive `Product_catd`,
global
`Functord_cat(E,P(B,C)) = Product_cat(Functord_cat(E,B),Functord_cat(E,C))`,
universe-level projection transfors, and full base-two-cell action are still
not consequences of the fixed-base closure.

Reindexing stability is currently a canonical elaboration choice rather than
a kernel equality. A dependency-aware frontend lowers reindexing of a grouped
product directly to

```text
P(Pullback_catd(B,F),Pullback_catd(C,F)).
```

The raw whole-family expression `Pullback_catd(P(B,C),F)` deliberately
remains non-convertible to this form. No generic pullback of total categories
is assumed.

## 8. Arrows Between Sections

In non-directed HoTT notation one might expect:

```text
Hom_{Π E}(s,t) = Π_k Hom_{E[k]}(s[k],t[k])
```

For a directed base `K`, this pointwise slogan is incomplete. The components
must be natural with respect to all arrows of `K`.

The directed form used in v3.2 is:

```text
Hom_{Π E}(s,t)
  = natural family transformations from s to t
```

Pointwise, such a transformation `α : s => t` still has components:

```text
α[k] : Hom_{E[k]}(s[k], t[k])
```

but these components are constrained by naturality over every base arrow
`f : x ->^K y`. This is why the implementation uses `Transfd`, not a naive
pointwise dependent product of homs.

When the base is non-directed or only path-like, the distinction between
"functorial in k" and "natural in k" collapses. In the directed theory, it is
essential.

## 9. Dependent Homs And Fibre Transport

Given a family `E : K → Cat`, an object `u : E[x]`, and a base arrow
`f : x → y`, the theory has covariant fibre transport:

```text
E[f](u) : E[y]
```

The covariant transport of the object `u` is represented by a functor:

```text
transport_{E,x,u,y} : Hom_K(x,y) → E[y]
transport_{E,x,u,y}(f) = E[f](u)
```

The dependent hom construction is contravariant in the base hom. It is a
category-valued functor:

```text
homd_E(x,u,y,v) : Hom_K(x,y)^op → Cat
homd_E(x,u,y,v)[f]
  = Hom_{E[y]}(E[f](u), v)
```

Here "packages" means that `homd_E(x,u,y,v)` is not merely a pointwise formula:
it is one functorial object carrying the object, arrow, and higher action of
dependent fibre arrows over the base hom.

### Simplicial Reading

The same construction has a simplicial/Grothendieck reading. The Sigma total
over `homd_E(x,u,y,v)` packages a base arrow `f : x → y` together with a fibre
arrow `E[f](u) → v`, so it is a cell living over a chosen base edge. Ordinary
`hom_int`, after fixing a source object `W`, gives the first triangle/surface
presentation over an edge; dependent `homd_E`, after fixing `x,u`, is the
dependent iteration step. When the family itself is hom-shaped, this
Sigma-of-hom pattern supplies the next "cell over a cell" layer. This is an
interpretation of the existing hom/Sigma architecture, not a separate primitive
or rewrite surface.

This also motivates a recurring v3.2 implementation idiom: when one endpoint
of a hom varies by a functor, write the family as a hom-indexed family rather
than as a raw composition of endpoint functors. For example, for `f : A ⊢ B`,
the family:

```text
b ↦ (a ↦ Hom_B(b,f[a]))
```

is the internal package:

```text
hom_int B A f : Op_cat B ⊢ Catd_cat A.
```

This packages the pre/postcomposition actions under the hom constructor, which
is better aligned with cut-elimination than first introducing an explicit
`comp_cat*` pipeline and later trying to fold it away.

More generally, dependent homs can be formed along a natural family morphism
`FF : D → E`, allowing endpoint data in different families. The endpoint form
specializes to the identity-family case above.

This same dependent hom architecture is shared by total-category homs and
section action:

```text
Hom_{Σ E}((x,u),(y,v))
  uses the total category over homd_E(x,u,y,v)

s[f] : homd_E(x,s[x],y,s[y])[f]
```

or, unfolded:

```text
s[f] : Hom_{E[y]}(E[f](s[x]), s[y])
```

### Whole Displayed Laxity From The Internal Action

For a displayed functor `FF : E → D` and a base arrow `p : x → y`, there are
two functors from `E[x]` to `D[y]`:

```text
D[p] o FF[x]
FF[y] o E[p].
```

The active whole laxity transformation is written

```text
lambda_FF(p) : D[p] o FF[x] => FF[y] o E[p].
```

Its component at `u : E[x]` is not separately postulated:

```text
lambda_FF(p)[u] = fdapp1_int_cell(FF,p,u).
```

Computationally, the kernel starts from the whole internal action
`fdapp1_int_transfd(FF)`, projects it through the dependent-hom ladder, and
evaluates it at the canonical identity section of the self-comma family
`u |-> (E[p] downarrow E[p](u))`. The section computes both at `(u,id)` and
on a fibre arrow `h`; consequently `lambda_FF(p)` retains a whole `tapp1`
action in `u` rather than stopping at a pointwise cell. The public kernel owner
is `functord_laxity_transf`. This construction exposes laxity already present
in the internal action; it does not add an independent naturality square.

The existing transparent `piapp*` presentation is sufficient for this first
consumer. A primitive redesign of section application remains consumer-gated.

The ordinary internal action now has both fixed-object projections. For
`epsilon : F => G`, fixing the source gives

```text
tapp1_at_transf(epsilon,X)
  : Hom_A(X,-) => Hom_B(F[X],G[-]),
```

while fixing the target gives the contravariant mirror

```text
tapp1_con_at_transf(epsilon,Y)
  : Hom_A(-,Y) => Hom_B(F[-],G[Y]).
```

The second owner is transparently the first internal action applied to
`Op_transf(epsilon)`, in its native opposite presentation. Its component at
`X` computes to the same `tapp1_func(epsilon,X,Y)` off-diagonal hom functor.
Consequently applying `functord_laxity_transf` over an arrow `h : W -> X`
extracts the pre/right witness from the existing `fdapp1_int_cell` ladder;
no independent naturality square is declared. The identity specializations
are `fapp1_con_int_transf(F)` and `fapp1_con_at_transf(F,Y)`.

The ordinary public surfaces now retain that whole provenance explicitly:

```text
tapp1_post_laxity_transf(epsilon,X,g)
  : G[g] o epsilon[-] ==> epsilon[g o -]

tapp1_pre_laxity_transf(epsilon,Y,h)
  : epsilon[-] o F[h] ==> epsilon[- o h].
```

Their component projections are `tapp1_post_laxity_cell(epsilon,g,f)` and
`tapp1_pre_laxity_cell(epsilon,h,q)`. Both unfold to the corresponding
`fdapp1_int_cell` of the fixed-source or fixed-target action. The normal-lax
composition witness

```text
fapp1_compositor(F,g,f) : F[g] o F[f] ==> F[g o f]
```

is the post/left cell of the identity transfor. These names add no runtime or
proof-time rule; their displayed `functord_transport_*_func` endpoints remain
the computational types. Existing whole strict naturality paths compare those
owners with the readable raw-composition presentation, so no duplicate capped
pre/post unification rule is installed.

This boundary retains the whole contravariant source-variable action. A
separate functor varying a higher arrow between ordinary transfors is still
consumer-gated; this first ordinary consumer does not require an
`Op_transf_func` package or displayed `homd_con_int` mirror.

A future named `section_total(s) : K → Σ_K E` facade would make this sharing
more visible at the presentation level, but its transparent total-category
construction and the more general base-change totalization are active. The
common arrow core remains the dependent-hom construction.

## 10. Mixed-Variance Families

Several useful families are mixed-variance. If:

```text
A : K^op → Cat
B : K → Cat
```

then the pointwise functor family is:

```text
Functor_catd(A,B)[k] = Functor(A[k], B[k])
```

The mixed variance is in the two inputs: precomposition in the source family is
contravariant, while postcomposition in the target family is covariant.

For one family `E : K → Cat` and two sections:

```text
X : Π_k E[k]^op
Y : Π_k E[k]
```

the fibrewise hom family is:

```text
Hom_catd(E,X,Y)[k] = Hom_{E[k]}(X[k], Y[k])
```

For two families of functors, the fibrewise transformation family has the same
mixed-variance shape. A source section `FF` is read in the opposite of the
functor family, and a target section `GG` is read in the original functor
family:

```text
FF : Π_k Functor(A[k],B[k])^op
GG : Π_k Functor(A[k],B[k])
Transf_catd(A,B,FF,GG)[k] = Transf(FF[k], GG[k])
```

These pointwise constructions are useful, but they do not replace the full
natural transformation structure when arrows over the base must be tracked.

The active kernel now also has coherent evaluation for the important
constant-domain specialization. For an ordinary category `A` and a
Cat-valued displayed family `B : K → Cat`, let:

```text
S(A,B) = Functor_catd(Const_catd(Op_cat K,A),B).
```

Thus `S(A,B)[k] = Functor(A,B[k])`. The stable displayed evaluator is:

```text
Eval_funcd(B) : P(S(A,B),Const_catd(K,A)) →_K B
Eval_funcd(B)[k] = Eval_func(A,B[k]).
```

Here `P` is the transparent fibrewise sibling product, not a new product
family owner. The formula is deliberately constant-domain: an arbitrary
contravariant family cannot simultaneously be reused as the covariant
argument family. The generic `fapp`/`tapp` calculus supplies base-arrow
action and higher naturality, so the evaluator needs only its stable owner
and point-component computation.

Fixed arguments are derived from reusable displayed weakening:

```text
Terminal_funcd(E) : E →_K Const_catd(K,Terminal_cat)
Terminal_funcd(E)[k] = Terminal_func(E[k]).
```

Composing `Terminal_funcd(E)` with a constant section gives a coherent map
from any displayed source to `Const_catd(K,A)`. Pairing that map with a
varying subject and then applying `Eval_funcd` accounts for expressions such
as `F a` without a separate fixed-argument evaluator. This closure handles
recursive constant-domain displayed application. Arbitrary mixed-domain
evaluation, general contravariant occurrence lowering, and abstraction
across a genuine dependent telescope edge remain separate problems.

A complementary constant-*middle* construction composes two varying
functors. If

```text
F : A[k] -> X
G : X -> B[k],
```

where `X` is an ordinary category independent of `k`, then

```text
comp_d(A;X;B)
  : P(Functor_catd(A,Const_catd(K,X)),
      Functor_catd(Const_catd(Op K,X),B))
      ->_K Functor_catd(A,B)
comp_d(A;X;B)[k](F,G) = G o F.
```

The two constant-family spellings encode the two variances, but both fibres
reduce to `X`. The displayed owner retains the whole base-arrow action by
delegating to the already-internalized target `Functor_catd` action; its
object, inner-arrow, base-arrow, and next-cell behavior therefore does not
require externally supplied naturality equations. This is the internal
application combinator needed to elaborate a direct nested-binder body such
as `G[k](c)(F[k](c)(a))`. It is not a curry theorem and does not replace the
fundamental direct introduction
`lambda^n k. lambda^f c. lambda^f a. t`.

There is intentionally no corresponding construction for an arbitrary
middle family `M`: the first input would require `M : Catd K`, while the
second requires a negative family over `Op K`. Relating those presentations
needs additional mathematical structure, not an elaborator cast or an
unchecked equality.

## 11. Basic Sigma/Pi Operations And Adjunction Shadows

The active v3.2 implementation includes an ordinary functor adjunction
relation indexed by the already-named functors. For categories `R` and `L`,
functors `F : R ⊢ L` and `G : L ⊢ R`, an adjunction witness has type

```text
J : Adjunction(F,G).
```

The compatibility views of the functors are transparent, while the unit and
counit remain stable observations:

```text
left_adj_func(J)     := F
right_adj_func(J)    := G
unit_adj_transf(J)   : id_R => G o F
counit_adj_transf(J) : F o G => id_L.
```

The package also has the two component-level triangle cut-elimination rules:

```text
counit[f] o F(unit[g]) -> f o F(g)
G(counit[g]) o unit[f] -> G(g) o f.
```

Opposite adjunction swaps the indices:

```text
Op_adjunction(J) : Adjunction(Op_func(G), Op_func(F)).
```

The hom-profunctor mate and weighted-limit/colimit preservation interfaces
also consume `F` and `G` directly. No existential package is active because no
consumer needs to recover unknown functors. Likewise, no equation identifies
an independently named unit or counit with the stable observations: such an
equation needs declaration-backed agreement or an explicitly classified
trusted postulate. Raw named-operation composites therefore do not inherit
triangle computation accidentally.

The current theory includes the expected basic operations:

```text
sigma_intro_E : E → Const_K(Σ_k E[k])
sigma_intro_E[k](u) = (k,u)
```

```text
pi_eval_E : Const_K(Π_k E[k]) → E
pi_eval_E[k](s) = s[k]
```

```text
const_section_{K,A} : A → Π_K Const_K(A)
const_section_{K,A}(a) = const(a)
```

Here `const(a)` is the constant functor/section with value `a`:

```text
const(a)[k] = a
```

When `K = 1`, this specializes to the ordinary object functor:

```text
const_section_{1,A}(a) = Obj_func(a) : 1 → A
```

In the implementation, `Obj_func(a)` is a defined alias for the terminal-domain
constant functor `Const_func(1,A,a)`.

On an arrow `p : x ->^A y`, the constant-section constructor produces the
displayed constant transformation `Const_transfd(p)`. Its component at every
base object is the ordinary terminal-source constant transfor with value `p`.

Pullback of sections along a base functor is also present:

```text
section_pullback_F : Π_b E[b] → Π_a E[F[a]]
section_pullback_F(s)[a] = s[F[a]]
```

Weakening an already internal section across a new displayed variable has a
separate whole displayed owner:

```text
section_weaken(R,E,s) : R ->_K E
section_weaken(R,E,s)[k] = const_{R[k]}(s[k]).
```

The construction ignores the new fibre object but not the directed base: its
action over `p : k -> k'` is inherited internally from the section `s`.
When the weakened variable must again be presented as a section over the
total category `Sigma_K(R)`, the existing `sigma_functord_sec` uncurries this
displayed functor.  This explicit sequence is the computational recursive-
context operation.

Accordingly, the generic families

```text
E o Sigma_proj1_func(R)
Pullback_catd(E,Sigma_proj1_func(R))
```

compare with the stable `Sigma_proj1_pullback_catd(R,E)` only at proof time.
They do not runtime-reduce to it.  Code needing stable fibre/action and
uncurrying computation names `Sigma_proj1_pullback_catd` explicitly, while
generic section pullback remains generic.

These are currently basic operations and beta laws, not a completed general
adjunction package. They should be read as visible instances or shadows of the
expected future dependent adjunctions along a functor `F : A → B`:

```text
Σ_F ⊣ F^* ⊣ Π_F
```

Some higher action/coherence rules for these helpers remain future work. The
object-level beta laws above are the current intended reading.

## 12. Synthetic Path Induction

For a category `Z` and source object `x : Z`, the outgoing-path category is:

```text
PathOut_Z(x) = Σ y : Z, Hom_Z(x,y)
```

An object is written `(y,p)`, where `p : Hom_Z(x,y)`. The reflexive outgoing
path is:

```text
reflout_x = (x,id_x).
```

A path-induction motive at fixed `x` is a directed family:

```text
E : PathOut_Z(x) → Cat.
```

The fixed-`x` eliminator has the expected dependent-product shape:

```text
path_ind_sec(Z,x,E,u) : Π q : PathOut_Z(x), E[q]
u : E[reflout_x]
```

and computes at `(y,p)` by transporting `u` along the canonical arrow:

```text
rho_{x,y,p} : reflout_x → (y,p)
```

In the current implementation this arrow is not axiomatic. It is the canonical
Sigma transport arrow for the representable family:

```text
rho_{x,y,p} =
  sigma_transport_arrow(Rep_Z(x), p, id_x)
```

using the endpoint computation:

```text
Rep_Z(x)[p](id_x) = p.
```

The canonical Sigma transport arrow itself is defined from the fundamental
Sigma-hom characterization: a total arrow is a base arrow plus a fibre arrow,
and `sigma_transport_arrow(E,p,u)` is the special case with the identity fibre
arrow at `E[p](u)`.

The primary internalized theorem is the telescope form over varying `x`:

```text
PathInd_transfd(Z)
  : x :^n Z ; PathOutReflEval_Z[x] => PathOutPi_Z[x]
```

where:

```text
PathOutReflEval_Z[x][E] = E[reflout_x]
PathOutPi_Z[x][E]       = Π q : PathOut_Z(x), E[q].
```

Its component is the fixed-`x` theorem:

```text
PathInd_transfd(Z)[x] = PathInd_func(Z,x)
PathInd_transfd(Z)[x][E](u) = path_ind_sec(Z,x,E,u).
```

The fixed-`x` rho-section is the path induction instance for the representable
motive on `PathOut_Z(x)`:

```text
pathout_refl_arrow_sec(x)
  = path_ind_sec(Rep_{PathOut_Z(x)}((x,id_x)), id_{(x,id_x)}),
pathout_refl_arrow_sec(x)[(y,p)] = rho_{x,y,p}.
```

The Sigma-total presentation is now derived from this telescope theorem:

```text
PathInd_funcd(Z) =
  Sigma_transfd_funcd(PathInd_transfd(Z)).
```

The generic uncurrying law is:

```text
Sigma_transfd_funcd(eta)[(k,r)] = eta[k][r].
```

For canonical total arrows, the intended internal normal form is the existing
off-diagonal transfor component:

```text
Sigma_transfd_funcd(eta)[sigma_transport(R,p,r)]
  is represented by
tapp1_fapp0(Sigma_transfd_funcd(eta), sigma_transport(R,p,r)).
```

The kernel deliberately does not fold this to one external route around a
naturality square, such as `T[p](eta[x](c))`. Action over arbitrary Sigma-total
arrows remains outside the immediate milestone.

This keeps the theorem surface sequential:

```text
(x :^n Z) →
  (E :^n Catd(PathOut_Z(x))) →
    E[reflout_x] → Π q : PathOut_Z(x), E[q]
```

while still providing the compiled Sigma-total form needed by existing
transport and total-category infrastructure.

## 13. Equivalence And Univalence Staging

The active kernel distinguishes several levels of equivalence rather than
using one overloaded notion.

At the groupoid/type level, an equivalence package contains forward and inverse
maps with path witnesses:

```text
e : TypeEquiv(A,B)
e.to   : A -> B
e.from : B -> A
e.from(e.to(a)) = a
e.to(e.from(b)) = b.
```

The ordinary algebra is active:

```text
type_equiv_refl(A)                  : A ≃ A
type_equiv_sym(e)                   : B ≃ A
type_equiv_comp(eBC,eAB)            : A ≃ C
type_equiv_to(comp(eBC,eAB))(a)     = eBC.to(eAB.to(a)).
```

Composition follows categorical order, with the later map first. Symmetry and
composition build explicit quasi-inverse paths from the selected inverse data
and then use the reviewed quasi-inverse-to-contractible-fibre theorem. Their
packages are transparent Sigma values: forward maps, selected inverse maps,
and selected right-inverse paths compute. The other contraction-derived left
path stays opaque, and neither double symmetry nor identity composition is a
runtime package eta. Forward-map unit and associativity shapes compute without
adding rewrite or proof-time equations.

Reflexivity computes, and the encoded product, Sigma, and Pi object layers have
the first constructor-specific closure operations. Paths can be decoded to
equivalences by `idtoequiv_grpd`; the converse direction is exposed through a
groupoid-univalence capability:

```text
U : GrpdUnivalence
ua_grpd(U,e) : A = B.
```

The kernel also exposes a decoder-oriented witness
`grpd_univalence_by_decoder`. Its two fields now have named projections:

```text
grpd_equiv_path_idtoequiv(p)
  : grpd_equiv_path(idtoequiv_grpd(p)) = p

idtoequiv_grpd_equiv_path(e)
  : idtoequiv_grpd(grpd_equiv_path(e)) = e.
```

The same specified-inverse package derives
`grpd_univalence_from_decoder : GrpdUnivalence`. Its selected
contractible-fibre inverse, exposed as `grpd_univalence_selected_path`,
computes to the one operational decoder `grpd_equiv_path`. This avoids
postulating that every unrelated legacy `ua_grpd(U,e)` head selects the same
inverse; new coherence consumers use the decoder package, while arbitrary
`ua_grpd` remains a compatibility facade with its existing transport beta.

Generic path induction proves `coe_grpd_idtoequiv(p,a)`, and the decoder right
round trip then proves
`grpd_equiv_path_coe(e,a) : coe(grpd_equiv_path(e),a)=e.to(a)`. This square is
propositional, not a broad runtime rewrite: reducing the existing Product
decoder first otherwise leaves transport along `product_grpd_path` stuck. The
pointwise `grpd_equiv_path_pi_action` is the first nontrivial Pi-universe
consumer. The Phase-13 groupoid identity boundary now packages exactly this
surface as

```text
GrpdPathView(A,B) = TypeEquiv(A,B),
grpd_path_encode(p) = idtoequiv_grpd(p),
grpd_path_decode(e) = grpd_equiv_path(e).
```

`grpd_path_refl(A)` is `type_equiv_refl(A)`. Both inverse laws and transport
agreement are the existing decoder propositions under named aliases, so no
semantic univalence body, rewrite rule, or `unif_rule` is duplicated. Product
encode/decode computation and Pi action remain owned by their established
rules; same-base Sigma equivalence passes through the generic view.

Public `A =_{Grpd_grpd} B` deliberately does not reduce to this view. The
owner-position direct candidate was warning-neutral and passed the existing
suite, but it made normalization of
`τ(Grpd_grpd =_{Grpd_grpd} Grpd_grpd)` recursively reopen the same universe
equality and exceed the 20-second bound. The named view normalizes finitely
because nested public universe equalities stay opaque. Thus the groupoid
fallback is active while direct public groupoid-universe identity and future
constructor action remain separate.

The active categorical universe has a different measured boundary. Its rigid
owner rule is native equality-valued equivalence:

```text
A =_{Obj(Cat_cat)} B  -->  OmegaEquiv(Cat_cat,A,B).
```

It has a finite self-universe normal form and is warning-neutral. Explicit
`omega_equiv_refl` and `object_path_equiv` packages own observer
computation; generic `eq_refl` retains guarded J/`eq_ap` provenance and is not
rewritten to the explicit package. The rejected reflexivity-collapse probe
still records why those presentations remain distinct. This operational result
is not a consistency or stratification claim about `Cat_cat : Cat`.

The former D0-backed `CatPathView`, `cat_path_*`, `idtoequiv_cat` decoder
round trips, Product action, and D0b next-hom witness no longer define public
kernel equality. Their temporary extracted compatibility module and explicit
legacy clients are now deleted. Dated plans retain the old computation as
historical evidence, but there is no alternative active universe foundation.

Two earlier D0 observation experiments are no longer part of the current
surface. The one-layer nested observation record/path view and the
`CatDim`-indexed finite observation tree were useful probes of the opaque
certificate boundary, but neither supplied a reverse decoder, evidence eta,
or proposition-valuedness theorem. The P4 consumer audit found no theorem or
nonself consumer and retired both families, their diagnostics, and their
reviewer examples on 2026-07-19. Their dated normalization and expected-
failure evidence remains in the July 13 redesign ledger; it is historical
probe evidence, not an implementation authority or a compatibility promise.

At the ordinary categorical level:

```text
IsoEvidence_C(x,y)
```

contains an arrow, an inverse arrow, and propositional left/right inverse
paths. The 1-categorical univalence capability compares object equality with
this ordinary isomorphism evidence.

The July 17 equality-valued overlay now has two promoted parallel staging
layers. For a fixed arrow `f : Hom_C(x,y)`,
`OmegaEquivAlong(f)` is decoded native data consisting of separate left
and right inverse arrows and cancellation witnesses expressed directly as
equalities in `Hom_C(x,x)` and `Hom_C(y,y)`. Its four fields and native indexed
eliminator compute on introduced data. This realizes the intended recursive
mathematical reading—higher equivalence information is carried by equality in
the next hom-category—without an opaque encoder or decoder.

The parallel `OmegaEquiv(C,x,y)` facade packages a selected arrow and this
fixed-arrow evidence behind a stable primitive record-like classifier. Its
constructor, forward/evidence projections, and dependent eliminator have
explicit beta rules; eta is propositional. A transparent Sigma view has maps
in both directions and propositional round trips. For
`p : x =_{Obj C} y`, the transparent `object_path_equiv(p)` package uses
`path_to_hom(p)`, `path_to_hom(path_sym(p))`, and two J-derived cancellation
laws, so all documented observations compute without a bodyless reification
capability. The stable facade is primitive but not observationally opaque; the
derived path adapter is not primitive.

For a literal path category there is now a narrower computational interface.
`OmegaEquiv(Path_cat(A),x,y)` compares at proof time with `x =_A y`, and
`path_equiv(p)` packages `p` itself with two `path_sym(p)` inverse choices
and J-derived laws. The comparison lets a raw path be *typed* as facade data,
but does not reify it: facade projections on that raw path remain stuck. A
measured direct raw-path projection rule conflicts with ordinary package beta,
so observable computation must go through `path_equiv(p)`.

The staged internal groupoidality predicate is

```text
IsGroupoidalCat(C)
  := OmegaEquivAlong(Core_incl_func(C)).
```

Thus it says that `Core_cat(C) -> C` is an omega-equivalence. In a setting
where the categories are internally univalent/complete, this is the intended
version of “all arrows are invertible.” Without that surrounding intent it is
strictly stronger than ordinary external groupoidality, because it also says
that directed arrows are represented by object paths. The path category has a
canonical witness, using a proof-time comparison between its Core inclusion
and identity functor; that comparison is not a runtime collapse.

General groupoidality is now consumed one hom-category at a time. Given
`g : IsGroupoidalCat(C)`, the public
`groupoidal_core_homwise(g,x,y)` is fixed-map equality-valued evidence for

```text
core_incl_hom_func(C,x,y) : Path_cat(x = y) -> Hom_cat(C,x,y).
```

Operationally the one-way derived module
`emdash3_2_eq1_hom_action.lp` applies the native
`omega_equiv_along_fapp1` theorem directly to `g`. The public mathematical
result is equality-valued and iterable, and this consumer chain no longer
crosses any D0 compatibility conversion. The theorem and its proof helpers are
transparent; helpers are protected at the module boundary and no new decoder,
univalence capability, rewrite, or unification rule was added.

The selected right inverse functor sends a directed arrow `f : x -> y` to an
object path. Its equality-valued right cancellation law says that applying
the Core inclusion again recovers `f`; `eq_ap` gives the corresponding
pointwise path. The underlying bi-invertibility evidence retains a separate
left inverse and left law, so this interface does not silently identify the
two inverse choices or assert quasi-inverse eta. Existing `IsDiscreteCat`
evidence and a packaged `ZeroCat` carrier provide nonliteral instances.

That pointwise path now reconstructs native equivalence evidence for the
original arrow. Its reverse path is sent through `path_to_hom` to obtain a
selected inverse; re-inclusion rewrites the original arrow to the image of the
selected path, and the J-derived object-path cancellation laws prove both
inverse equations. Thus `groupoidal_arrow_equiv_along(g,f)` is a defined
package, not an all-arrows axiom. More generally,
`omega_equiv_along_fapp1_fapp0(F,u)` maps any fixed-arrow equality-valued evidence
through ordinary functor action. Specializing this theorem to a displayed
family `D : C -> Cat_cat` gives
`groupoidal_fibre_transport_equiv(g,D,f)`: the existing directed fibre
transport is an equivalence, and its inverse projections compute as transport
along the selected inverse arrow. No encoder, decoder, new transport
operation, or runtime rule is required. The arrow-to-path selection now comes
from the native next-hom theorem rather than the retained D0b compatibility
owner.

The transparent classifier
`AllArrowsEquiv(C) = Pi x y, Pi f : Hom_C(x,y),
OmegaEquivAlong(C,f)` records the pointwise consequence, and
`groupoidal_all_arrows_equiv` computes from coherent core groupoidality to
that classifier. The converse is not automatic: arbitrary pointwise inverse
choices do not yet assemble the coherent inverse omega-functor
`C -> Core_cat(C)`. That direction is a structured-functor
assembly/extensionality question, not an equality decoder question.

The needed coherence is not a new axiom. From maps `f : A -> B` and
`l : B -> A` with equality-valued homotopies `l(f x) = x` and
`f(l b) = b`, the transparent `half_adjoint_counit` makes the standard
adjustment

```text
epsilon'(b) = epsilon(f(l b))^-1 ; ap(f, eta(l b)) ; epsilon(b),
```

and `half_adjoint_triangle` proves `ap(f,eta(x)) = epsilon'(f x)` by ordinary
path induction and path algebra. Both specialize computationally to
reflexivity. This closes the mathematical endpoint-coherence gap in the active
D0b-free next-hom theorem. Its one-way module exposes one ordinary public
owner and retains 56 protected transparent implementation lemmas; projection
diagnostics and reflexive normalization to `id_func` confirm that the module
boundary does not introduce opacity.

The equality-valued evidence itself is proposition-valued at every category,
not only at a finite or locally set-valued boundary. For fixed
`f : Hom_C(x,y)`, write

```text
L_f(k) = k o f : Hom_C(x,x),
R_f(k) = f o k : Hom_C(y,y).
```

Given one bi-inverse witness for `f`, ordinary associativity and unit laws
show that `L_f` and `R_f` have explicit quasi-inverses. The transparent
quasi-inverse theorem therefore contracts the homotopy fibres

```text
Sigma l, L_f(l) = id_x,
Sigma r, R_f(r) = id_y.
```

Their product is the transparent view of `OmegaEquivAlong(f)`, and native
record eta transfers contractibility back to the record. Hence
`omega_equiv_along_evidence_is_prop(C,x,y,f)` is derived with no
truncation hypothesis, extensionality axiom, decoder, or proof erasure. The
literal-path, discrete, and locally-set constructions remain independently
checked specializations. These theorems live downstream in
`emdash3_2_eq1_evidence_property.lp`; they add no rewrite or unification rule.

The uniform equality/equivalence cast does not make that proof disappear. It preserves
the term while changing the accepted classifier, so a raw category path does
not acquire an equivalence package head and its forward projection remains
stuck. The explicit transparent `object_path_equiv` construction performs
the required reification. This is why classifier-level interchange can be
identity syntax while computational package observation still uses a named
constructor; neither operation requires an opaque decoder.

At a literal `Path_cat(A)`, the generic half-adjoint selected inverse is well
typed but does not definitionally reduce to the input path. This is a
provenance boundary rather than a semantic failure: the direct
`path_equiv(p)` witness remains the canonical literal computation and its
forward projection reduces to `p`.

Structured groupoidal path induction continues to use the existing
`path_ind_sec`. Its Sigma-pullback motive equation still reduces to
`fib_cov_transf` in a context carrying groupoidality evidence, without a
second eliminator or a raw-fibrancy capability. For a general `C`, carrying a
groupoidality witness is still specialization by weakening—the action exists
for every directed source—so this fact alone does not consume `g`.

At a literal `Path_cat(A)` source, the missing comparison is now explicit.
`path_cat_structured_transport(D,u,p)` applies the displayed functor
action along `p`, whereas `path_cat_ind_eqr_transport(D,u,p)` uses
primitive right `ind_eqr` with a function-valued motive. Path induction proves
these values equal for every `p`. Evaluating the existing `path_ind_sec` at
`(y,p)` gives a third presentation, `path_cat_path_ind_app`; another
path-induction theorem compares it with the structured action, and transitivity
compares it with primitive J.

Only primitive J definitionally computes to `u` at reflexivity. The displayed
action and section application deliberately retain their directed runtime
normal forms. Two narrowly typed proof-time comparisons reconcile the
identity and component-projection orders in the reflexive proof: one compares
Cat-valued functor action on `eq_refl` with identity, and the other decomposes
the exact PathOut/Sigma-pullback component presentation into four residual
constraints. Neither is an encoder, decoder, new eliminator, runtime
commuting conversion, or claim that every structured component is constant.

The direct-univalence boundary is now active but deliberately hybrid. For a
syntactically abstract category `C`, a proof-time unification rule compares
`OmegaEquiv(C,x,y)` with `x =_{Obj C} y`; it does not make the classifiers
runtime-convertible and does not insert a package. The rigid Cat and Grpd
universe equalities runtime-reduce directly to their equality-valued
classifiers, with a finite Cat self case. Explicit native reflexivity packages have computational
observers, while raw `eq_refl` retains its generic-J provenance and has no
facade projection beta.

This comparison has an important normal-form boundary. An abstract
`lambda p, p` cast experiment typechecks while `C` remains a variable, but is
not stable after Product or opposite equality has reduced to a different
classifier. The bare alias is not exported.

The selected explicit cast instead stages the stable carrier classifier

```text
ObjectPathCastView(C,x,y).
```

Its carrier reduces to `x =_{Obj C} y`, while one direct proof-time equation
compares it with `OmegaEquiv(C,x,y)`. Equality and the stable equivalence
facade therefore each enter through exactly one conversion step. The two public casts use a typed
`let`, beta-reduce to their input, and have definitional round trips after all
measured specializations. This is a primitive classifier view, not an opaque
encoder or decoder term.

Product equality separately retains
the rigid classifier

```text
ProductPathView(A,B,p,q),
```

whose carrier is definitionally the previous constant-family
`SigmaPathView`. Its base/fibre constructor, projections, fixed-endpoint
eliminator, and canonical reflexivity therefore reuse the established Sigma
path data. `product_path_to_sigma_view` and its reverse are literal identity
functions. The Product/equivalence cast names route through the uniform view. The
classifier heads themselves remain runtime-distinct, and generic `eq_refl` is
not collapsed to canonical `product_path_refl`.

Opposite categories preserve objects but erase the `Op_cat` head before the
generic comparison can match. A direct opposite-specific equation failed on
composite formers. Its successful Phase-6 local carrier intermediate has now
been retired: the opposite cast names use the uniform stable view and pass
Product, path-category, and nested-opposite specializations.

The identity casts do not construct a facade package. Consequently their
forward/inverse/law projections remain stuck. The transparent
`object_path_equiv(p)` package is still the uniform computational
path-to-equivalence operation whenever observers are required. No primitive
nonreducing cast term is active. This choice is local to the July 17 plan, not
a repository-wide rewrite/unification rule.

The native equality-valued facade is therefore the active direct classifier at the abstract proof-time,
rigid Cat/Grpd, stable Product, and explicit opposite boundaries, but it is not
claimed as an automatically inherited runtime normal form for every former;
the explicit stable casts provide term interchange without that claim.
The former D0/public `OmegaEquiv` surface and its compatibility module are
deleted. No runtime facade eta, proof erasure, compatibility alias, or silently
coerced raw-path observer has been promoted.

The completed decoder migration removed the redundant standalone
`cat_univalence(C)` inhabitant, migrated native-worthy consumers, and then
extracted the operational `idtoequiv_cat`/`omega_equiv_path` pair and the
specified-inverse `cat_univalence_by_decoder` library with their shaped
computation before that compatibility closure was retired. The stable carrier
view supplies the active explicit equivalence-to-path and path-to-equivalence
operations. Its carrier rewrite and proof-time equation are
explicitly trusted; its term operations are transparent identities. This is
plan-local architecture, not a general logical-framework convention.

### Retired D0/D1 decoder history

This subsection records the representation and computation that justified the
earlier extraction boundary. The described module, declarations, and examples
are now deleted; it is historical rationale, not an active API or an
invitation to restore compatibility.

Inside the former frozen compatibility module, the defined
operation `object_path_equiv_D0(p)` composed the transparent native package with
the observation-complete migration constructor. It was used by
both recursive cells of the ordinary-isomorphism lift and by the D1
category-path next-hom construction. In particular the latter's selected
functor computes directly to `path_to_hom(Cat_cat,p)`. This is a migration
adapter into the old representation, not a second foundational encoder.

At that historical completion boundary, the kernel, both native one-way modules,
Nat, WalkingEnd, main diagnostics, and their native reviewer examples contain
no Cat/Grpd decoder, D0/D0b/D1, or migration-constructor reference. The later
retirement of the isolated Sum experiment does not alter that compatibility
boundary. Exactly seven legacy examples imported the frozen module explicitly;
P10 later deleted that eight-file closure.

Within that module, explicit D0/native migration was retained in both directions.
Old D0
evidence is decoded to the new inverse fields and equality laws. In the other
direction, a stable compatibility constructor inhabits the otherwise
constructorless D0 classifier; its inverse observations project the new
fields, while its recursive-cell observations use
`object_path_equiv(law)` and recur. This constructor cannot currently be
the literal identity function: D0 and EQ1 are not transparently the same data
representation, and D0 observers need a stable head on which to compute. It is
not an opaque univalence decoder theorem, however—all four public D0
observations are specified, including recursive computation. D0 still lacks
an eliminator or eta/extensionality theorem, so neither evidence round trip is
claimed. This is a migration fact local to the July 17 redesign, not a general
rewrite/unification policy.

Within the frozen module, the historical fixed-arrow redesign is the
compatibility omega-equivalence normal form:

```text
u : OmegaEquivAlong_C(f)
(f,u) : OmegaEquiv_C(x,y)
```

`OmegaEquiv_C(x,y)` is definitionally the dependent sum of a selected arrow
`f : Hom_C(x,y)` and neutral fixed-arrow evidence. `omega_equiv_to` and
`omega_equiv_evidence` are the generic Sigma projections. The public inverse
and recursive-cell observations route through that evidence; there is no
parallel semantic body. Reflexive, opposite, and Product evidence are stable
generators. Product evidence retains its componentwise constructor provenance
when both components are reflexive instead of collapsing to the unrelated
generic reflexive evidence head. Its forward/inverse projections and decoder
components still compute; selected inverse-arrow observations happen to join
the generic Product identity presentation, while recursive cells and the full
decoder path retain their structured Product heads. The same policy applies to
ordinary `iso_evidence_product`. No proof-time equation identifies the two
provenance choices, no raw inverse composite is rewritten to identity, and no
open package eta is installed.

The semantic compatibility fibre
`OmegaEquivFibre_C(f) := Sigma e : OmegaEquiv_C(x,y), e.to = f` is retained as
a reference construction. Fixed-arrow evidence maps into this fibre and back,
with a one-sided retraction. The reverse fibre eta and public package eta are
intentionally absent, so this comparison does not claim that evidence is
property-valued. `IsOmegaEquivArrow` remains reserved until such a theorem is
proved.

The frozen module also retained the variable-evidence hom-action. For
`u : OmegaEquivAlong_D0_{Cat_cat}(F)` it constructs

```text
omega_equiv_along_fapp1_D0(u,x,y)
  : OmegaEquivAlong_D0_{Cat_cat}(F_1[x,y]).
```

If `L` and `R` are the selected inverse functors, raw `L_1[F x,F y]` and
`R_1[F x,F y]` land at homs between `L(Fx),L(Fy)` and `R(Fx),R(Fy)`, not
between `x,y`. The left selected inverse therefore uses
`Hom(eta_x,epsilon_y) o L_1`. The right selected inverse first combines the
components of `L o F ~ id_A` and `F o R ~ id_B` to obtain endpoint
comparisons `L(b) <-> R(b)`, then conjugates `R_1`. Both higher inverse cells
are returned as transparent D0 packages with stable forward-cell and evidence
observations, so they can be projected and observed once more. These are
canonical generator observations, not raw cancellation rewrites, a
per-instance unification equation, or an unrestricted corecursor.

For this legacy iterated-hom reading, omega-equivalence is recursive:

```text
e : OmegaEquiv_C(x,y)
e.to        : Hom_C(x,y)
e.left_inv  : Hom_C(y,x)
e.right_inv : Hom_C(y,x)
```

together with omega-equivalences in the appropriate hom-categories witnessing
the two inverse composites. `omega_equiv_path` is the single public
evidence-indexed decoder. The decoder-oriented capability owns both
propositional round trips with `idtoequiv_cat`; it derives
`cat_univalence_from_decoder` and the named
`cat_univalence_type_equiv(C,x,y)`, whose selected inverse computes back to
`omega_equiv_path`. The encoder's forward arrow agrees propositionally with
`path_to_hom`; no open runtime fold is installed.

For a category path `p : A = B`, `idtoequiv_cat_fapp1_D1(p,x,y)` applies the
variable-evidence hom action to the selected functor and packages the result
as a public omega-equivalence between the corresponding hom-categories. Its
forward arrow is exactly the selected functor's hom action, its evidence
projection is exact, and its recursive left cell is iterable. This is the
retained integrated next-hom univalence/action witness; it uses no per-instance
unification equation or unrestricted corecursor.

This historical module was frozen against new consumers and features. Its sole
selected retention reason was the complete OneCat two-sided theorem below.
P10 subsequently dropped backward compatibility and deleted both without
requiring a native re-proof.

### Native discrete and finite-dimensional spine

The first finite-dimensional specialization is now active. A discrete category
is exactly the two-field product

```text
IsDiscreteCat(C)
  := IsSetGrpd(Obj(C))
     × IsGroupoidalCat(C),

IsGroupoidalCat(C)
  := OmegaEquivAlong_{Cat_cat}(Core_incl_func(C)).
```

The second field is native equality-valued groupoidality and is not duplicated
homwise. The one-way native hom-action extension gives

```text
discrete_core_homwise(d,x,y)
  : OmegaEquivAlong_{Cat_cat}(core_incl_hom_func(C,x,y)),

core_incl_hom_func(C,x,y)
  : Path_cat(x = y) -> Hom_cat(C,x,y).
```

Its object action is definitionally `path_to_hom`; the selected inverse object
action is `hom_to_path(d,f)`. The native right law supplies the equality
`path_to_hom_hom_to_path_path(d,f)`, and the retained directed-cell surface is
its image under `path_to_hom` in the next hom-category. Object sethood supplies
`hom_to_path(path_to_hom(p)) = p`. Both are named propositional witnesses, not
runtime cancellation rules. This chain uses
`groupoidal_core_homwise`, `groupoidal_arrow_to_path`, and
`groupoidal_path_to_arrow_retract` directly, with no D0/D1 conversion.
Set truncation alone does not inhabit `IsDiscreteCat`, and the two-field
package has no runtime eta or evidence erasure.

Object truncation and directed categorical dimension are now separate active
interfaces:

```text
IsObjTruncCat(n,C) := IsTruncGrpd(n,Obj(C)),

cat_dim_trunc_level(cat_zero)   := trunc_zero,
cat_dim_trunc_level(cat_succ n) := trunc_succ(cat_dim_trunc_level(n)),

IsNCat(cat_zero,C)   := IsDiscreteCat(C),
IsNCat(cat_succ n,C) := Pi x y : Obj(C), IsNCat(n,Hom_cat(C,x,y)).
```

`CatDim` is a native nonnegative code, independent of the `TruncLevel` code
that starts at -2. The recursive `cat_dim_trunc_level` map records the
object-level truncation predicted by directed dimension: discrete categories
have set-valued objects, and each hom-recursive successor raises the predicted
level once.

For native fixed-map evidence
`u : OmegaEquivAlong(F)` with `F : A -> B`, package `F` and `u` in the
stable facade, cast it to `A = B`, map `Obj` over that path, and apply
`idtoequiv_grpd`. This gives
`omega_equiv_along_obj_type_equiv(u) : TypeEquiv(Obj(A),Obj(B))`;
composing it with ordinary truncation invariance gives
`is_obj_trunc_cat_equiv_type_equiv(u)` and its forward/backward evidence
maps. No categorical decoder or D0 bridge is used. Explicit native
reflexivity deliberately retains its facade/package provenance and does not
collapse to a raw object path or reflexive `TypeEquiv`.

The dimension map remains an index calculation, but native equality-valued
evidence now supplies the recursive theorem. Truncation is first proved closed
under an explicit retraction at every `TruncLevel`: the contractible base is
direct, while the successor observes equality in the retract as a retract of
equality between selected representatives. At a successor `CatDim`, the hom
induction hypothesis truncates the arrow base, the general evidence-property
theorem truncates every fixed-arrow fibre, and `is_trunc_sigma` truncates the
transparent first-class Sigma. Two explicit retractions then transfer this
bound first to the stable facade and then to object equality. Thus

```text
ncat_obj_trunc(n,C,h)
  : IsObjTruncCat(cat_dim_trunc_level(n),C)
```

is defined for every `h : IsNCat(n,C)`. The zero case computes to the stored
`is_discrete_cat_obj_set(h)`; the successor computes to the described hom
recursion, Sigma closure, and casts. This proof uses native equality-valued evidence only and
introduces no global capability, decoder, or new conversion rule.

The earlier uninhabited D0 evidence-property capability and its conditional
object-truncation theorem are retired. They had no consumer beyond their own
diagnostics/example and are superseded by the unconditional native theorem
above. The representation-independent `prop_is_trunc_cat_dim` lemma is
retained because the native proof uses it twice.

`NCat(n)` packages a carrier category and retained
`IsNCat(n,carrier)` evidence; `ZeroCat` and `OneCat` are its zero and successor-
zero aliases. Constructor decoding and both projections compute, while package
eta and proof-field erasure do not. In particular, for `X : OneCat`,
`one_cat_hom_discrete(X,x,y)` exposes discreteness of `Hom(x,y)`, and
the native-extension owner `one_cat_hom_core_homwise(X,x,y,f,g)` applies the
promoted equality-valued discrete theorem at the next hom level between
parallel arrows. Applying `ncat_obj_trunc` to
the package evidence gives its carrier the predicted object truncation; the
readable `one_cat_obj_trunc` name is the successor-zero specialization.

The older D0 OneCat ordinary-isomorphism decoder, its two-sided
`one_cat_iso_type_equiv`, and its reviewer example are retired. They were not
used by `IsDiscreteCat`/`IsNCat` formation, the native hom-action/evidence-
property modules, WalkingEnd, Nat, or the main diagnostics.

There is a direct one-way native bridge from ordinary isomorphism evidence:
`iso_evidence_omega_along(i)` uses the ordinary inverse in both native
inverse slots and the two ordinary equations as its equality-valued laws, and
`iso_evidence_omega_equiv(i)` packages the result. The native forward,
inverse, and law projections compute. This does not by itself replace the
two-sided OneCat theorem. The stable native cast returns an object path but
intentionally does not reify an explicit native package as that raw path; even
the reflexive package is not judgmentally `eq_refl`. A focused owner probe
therefore leaves the first decoder base case unresolved at precisely that
package/path comparison. No coherence theorem or proof-time identification is
invented. The old theorem was deleted rather than made a cleanup prerequisite;
a fully native OneCat object-equality/ordinary-isomorphism `TypeEquiv` is
optional future work if a concrete consumer appears.

#### Retired OneCat compatibility proof history

The following paragraphs record how the deleted compatibility module had
constructed its stronger two-sided OneCat result. The declarations do not
exist in the active API.

The frozen module retained a separate recursive bridge from ordinary
isomorphism evidence. For

```text
i : IsoEvidence(C,x,y),
```

`iso_evidence_omega_along_D0(i)` selects the ordinary inverse in both inverse
slots and encodes `iso_evidence_left(i)` and `iso_evidence_right(i)` with
`idtoequiv_cat` in the two endomorphism hom-categories. Packaging this evidence
gives `iso_evidence_omega_equiv(i) : OmegaEquiv(C,x,y)`. Its forward arrow,
both inverse arrows, and both recursive cells compute through those owners.
The lift of explicit ordinary reflexivity compares with canonical recursive
reflexivity only at proof time through one semantically backed `unif_rule`;
runtime provenance remains distinct. Generic J then proves that lifting
`idtoiso_cat(p)` agrees propositionally with `idtoequiv_cat(p)`.

For `X : OneCat`, `one_cat_iso_path(X,i)` decodes that lifted omega-equivalence
through the canonical categorical decoder, and
`one_cat_iso_path_idtoiso(X,p)` proves decoder after encoder. An arbitrary
omega-equivalence still stores separate left and right inverse arrows, but its
recursive cells now supply their missing comparison constructively.
`omega_equiv_along_left_cell_to_D0` and
`omega_equiv_along_right_cell_from_D0` expose the selected directed cell
arrows. Stable post- and prewhiskering, joined by the explicit propositional
associator `omega_equiv_along_inverse_assoc_path_D0`, compose to
`omega_equiv_along_left_to_right_D0 : left_inv -> right_inv` in the inverse
hom-category. This explicit path/cell construction is necessary because a
direct `Hom_func` composite leaves unit and associativity comparisons to
non-transitive proof-time unification.

For a packaged one-category, `one_cat_omega_inverse_path(X,e)` sends that cell
through hom discreteness and obtains `left_inv = right_inv`. At canonical
omega reflexivity the generic directed comparison reduces to the identity
2-cell through existing generic owners; its decoded equality deliberately
does not runtime-collapse to `eq_refl`, so decoder provenance remains visible.
No new rewrite or `unif_rule` identifies the inverses.

The path now transports the decoded right recursive law from
`f o right_inv = id` to `f o left_inv = id` through ordinary `eq_ap` and
`eq_trans`. Together with the decoded left law this constructs
`one_cat_omega_iso_evidence(X,e) : IsoEvidence(C,x,y)`. Reapplying this
construction to an ordinary lift preserves the forward arrow and inverse
definitionally. Its two law proofs are paths between arrows in discrete
endomorphism hom-categories, so `discrete_cat_path_proof` compares them using
the stored set truncation. The promoted nested-Sigma path view then gives
`one_cat_omega_iso_lift_retract`; no proof erasure or package eta is needed.

Encoder agreement for the ordinary lift and the categorical decoder's second
round trip compose with that retract to prove
`one_cat_idtoiso_iso_path(X,i)`. Thus `one_cat_iso_path_idtoiso` and
`one_cat_idtoiso_iso_path` are the two specified inverse laws. The former
global `CatIsoUnivalenceByDecoder(C)` could not package them because its type
hardcoded the legacy `iso_evidence_path` decoder. The selected owner is instead
`OneCatIsoUnivalenceByDecoder(X)`, indexed by the evidence-retaining OneCat
package and its `one_cat_iso_path`. It derives the contractible-fibre
`one_cat_iso_univalence(X)` and the named
`one_cat_iso_type_equiv(X,x,y)`. The selected inverse and right path compute;
the contraction-derived left path has the same propositional endpoint but
remains runtime-distinct from the directly constructed first round trip. The
unused arbitrary-`Cat` capability inhabitants and hardcoded classifier are
retired; the general capability type and `isotoid_cat` eliminator remain and
are exercised by the scoped inhabitant. `iso_evidence_path` remains only as a
legacy reflexive/Product computation owner.

The distinction between `IsoEvidence` and `OmegaEquiv` is intentional.
Ordinary isomorphism data is the 1-categorical staging layer; recursive
omega-equivalence accounts for higher inverse cells.

## 14. Computational Isomorphism And Hom-Action Cancellation

Ordinary `IsoEvidence` records inverse laws propositionally. Some kernel
computations need a stricter selected normal form in which inverse cuts cancel
judgmentally under the stable hom-action owner. This is represented by:

```text
i : DefIso_C(x,y)
defiso_to(i)   : x -> y
defiso_from(i) : y -> x.
```

The selected cancellation laws compute at the represented postcomposition
head. Reflexivity, symmetry, composition, and functorial image are active, and
`defiso_iso_evidence(i)` forgets the computational package to ordinary
isomorphism evidence.

This is a Lambdapi/kernel notion of a chosen computational comparison. It does
not redefine mathematical categorical equivalence. The narrower normal form is
used when beta/eta cancellation must remain visible to rewriting.

## 15. Cat-Valued Profunctors And Weighted Representability

A v3.2 profunctor from `A` to `B` is a Cat-valued functor on the product base:

```text
R : Prof(A,B)
R : A^op x B -> Cat.
```

`Prof_cat(A,B)` is the fixed-endpoint category of such profunctors. Its
vertical maps are `ProfMap(P,Q)`. Endpoint variation is owned by reindexing:

```text
Prof_reindex(R,F,G)(a,b) = R(F[a],G[b]),
```

with the contravariant source endpoint implemented by the product base map
`Product_map_func(Op_func(F),G)`.

The unit profunctor is the uncurried hom bifunctor:

```text
Unit_prof(A)(x,y) = Hom_A(x,y).
```

Its simultaneous base action uses the rigid hom owner:

```text
Hom_A(g,f)[h] = f o h o g.
```

Readable representables are obtained by reindexing `Unit_prof`:

```text
Hom_prof_along(F,G)
Companion_prof(F)
Conjoint_prof(F).
```

The primitive tensor is symbolic composition of profunctors:

```text
Prof_tensor(P,Q) : Prof(A,X)
```

for `P : Prof(A,B)` and `Q : Prof(B,X)`. The current kernel does not contain a
general coend/coinserter quotient, so the tensor object is opaque and its
computational meaning is exposed through reindexing, shaped introduction, and
co-Yoneda maps.

Covariant and contravariant profunctor implications provide the two fixed-
endpoint closed directions. The active eval/lambda pairs are inverse on
vertical maps:

```text
ProfMap(P, O => Q)  <->  ProfMap(P tensor Q, O)
ProfMap(Q, P => O)  <->  ProfMap(P tensor Q, O).
```

Weighted cones are expressed through covariant implication. A weighted-limit
candidate `L` carries a computational comparison between the cone profunctor
and its representable:

```text
IsWeightedLimit_cov_comp(F,W,L)
  = ProfComparison(WeightedCone_prof(F,W), Hom_prof(L)).
```

Here `ProfComparison` is the profunctor-facing transparent view of `DefIso`.
Reindexing the one ambient comparison supplies push/pull operations for every
probe functor. Adjunction mate comparisons then give the checked
right-adjoint-preserves-weighted-limits construction. Weighted colimits and
left-adjoint preservation are obtained by the active opposite duality.

## 16. Directed Join And Eckmann–Hilton

The first directed-inductive join slice is primitive:

```text
Join_cat(A,B)
join_fst_func : A -> Join_cat(A,B)
join_snd_func : B -> Join_cat(A,B).
```

Instead of externally quantifying a separate cross arrow for every pair, the
join carries one internally natural profunctor cell containing all arrows from
the left inclusion to the right inclusion. `join_cross_hom(a,b)` is the shaped
projection of that cell. The nondependent recursor computes on both inclusions
and the cross cell.

This is a checked directed-inductive staging point, not yet a semantic collage
construction or general dependent eliminator.

The first Eckmann–Hilton application uses an iterated hom-category:

```text
EH_2End(B,x) = Hom_{Hom_B(x,x)}(id_x,id_x).
```

Vertical composition is ordinary composition in `Hom_B(x,x)`. Horizontal
composition is represented postcomposition/whiskering specialized to the
identity 1-cell, rather than a second primitive operation. The two operations
are connected through shared-middle interchange equalities, yielding:

```text
EH_comm(alpha,beta) : beta · alpha = alpha · beta.
```

This example is important architecturally: it demonstrates that the existing
hom-action and transfor projection calculus can express a classical
2-categorical theorem while remaining inside the iterated-hom omega-friendly
representation.

## 17. What Is Deferred

The current foundations intentionally do not yet include:

- observational identity for Empty, broader elementary
  no-confusion, higher action for the elementary classifiers, or their
  categorical universal properties; the visible Unit/Boolean/Nat
  constructor equality cases, generic-reflexivity provenance boundary, and
  guarded generic J beta are active, while the isolated Sum experiment is
  retired;
- arbitrary structural action/substitution, additional nonreflexive
  structured-J computation, and runtime eta for the named dependent
  `PathRecord` convention; its observational path view, stable reflexivity,
  projection betas, reflexive J, and named arbitrary path round trips are
  active;
- truncation reflectors and universe metatheory; direct Cat/Grpd universe
  identity now uses the native equality-valued facade, while the D0-free
  `GrpdPathView` remains a kernel library interface and the former decoder-
  owned `CatPathView` is retired,
  while restricted truncated-universe univalence, carrier/evidence package paths,
  the expected successor-level package-universe theorem, general one-step
  monotonicity, dependent-Pi/Sigma closure, `TypeEquiv` invariance, and its fixed-map
  categorical object-truncation consumer are active. Native equality-valued
  evidence is proposition-valued and finite-`NCat` object truncation is
  unconditional;
- additional computation of J on nonreflexive structured Pi paths; ordinary
  `PiHapply`/`PiFunext` equivalence and arbitrary Sigma/first-record
  path-characterization round trips are active;
- a completed universe/univalence metatheory beyond the active explicit
  capabilities and constructor/reflexivity computations;
- raw unreified-path observer computation, reverse pointwise-to-coherent-core
  assembly, and consumer-led core-universe inclusion functors. A full native
  two-sided OneCat object-equality/ordinary-isomorphism equivalence remains
  optional future work; the old compatibility theorem and module are deleted;
- general higher-inductive pushouts and a generic directed-inductive schema;
- generic abstraction of the completed walking-endomorphism presentation into
  a reusable directed-HIT/free-category schema, full functor-category
  initiality, a displayed dependent path-action/section construction, and
  generic groupoidification beyond the checked WalkingEnd-to-Circle
  comparison and `Hom(Circle,Circle) ≃ Integer` calculation; the
  ordinary raw-function `path_map_func` is already the complete selected
  nondependent action, and no generic selected-action registry is planned
  without a concrete new consumer;
- dependent join elimination or a semantic collage construction;
- a finalized surface syntax for the future proof assistant;
- full coherence APIs for every Sigma/Pi helper;
- a named `section_total(s) : K → Σ_K E` presentation facade and packaged
  projection laws; its transparent terminal-total/`sigma_map_func`
  construction and the general
  `sigma_pullback_total_func(F,D) : Σ_A(F^*D) → Σ_K D` are active;
- full product/curry adjunction coherence for `Product_cat`, beyond the
  current product normal form, projection computation, and functor-level
  curry/uncurry action laws; the transparent fibrewise product of two
  Cat-valued displayed families, its same-base object/arrow action, fixed-base
  displayed projection/pairing, derived swap/diagonal, and universal-property
  betas are active, while universe-level projection transfors, raw kernel
  pullback stability, global displayed-functor/product conversion,
  dependent-chain exchange, and full family higher action remain future work;
- general dependent adjunctions `Σ_F ⊣ F^* ⊣ Π_F` along arbitrary base
  functors;
- a general coend/coinserter implementation of profunctor tensor;
- full tensor associativity/coherence and complete co-Yoneda equivalences;
- all endpoint-changing closed/equipment APIs derivable from the fixed-
  endpoint profunctor core.

These are compatible future directions. The current v3.2 milestone combines
the directed categorical foundation with explicit equivalence/univalence
staging, a first computational profunctor/weighted-representability layer,
primitive directed join, synthetic path induction, and the Eckmann–Hilton
application.

## 18. Implementation Glossary

This table maps the mathematical notation above to the current active v3.2
kernel and one-way library vocabulary.

| Mathematical notation | Current implementation name |
| --- | --- |
| `Cat` | `Cat_cat` as the category of categories; `Cat` as the meta-class of categories |
| `Obj(A)` | `Obj A` |
| `Hom_A(x,y)` | `Hom_cat A x y` |
| `Functor(A,B)` | `Functor_cat A B` / `Functor A B` |
| `F[x]` | `fapp0 F x` |
| `F[f]` | `fapp1_fapp0 F f` |
| `u_*` / `u_*(g)` | `hom_postcomp_func` / `hom_postcomp_fapp0` |
| `u^*` / `u^*(h)` | `hom_precomp_along_func` / `hom_precomp_along_fapp0` |
| `Hom_A(g,f)[h] = f o h o g` | `Hom_func g f` / `Hom_fapp0 g f h` |
| `Transf(F,G)` | `Transf_cat F G` / `Transf F G` |
| `ϵ[x]` | `tapp0_fapp0 x ϵ` |
| path category `Path(A)` | `Path_cat A` |
| equality-local skeleton `Sk⁼(n,A)` | `EqSkeleton_cat n A` |
| equality-local category of categories `Cat₁⁼` | `Cat1Eq_cat` |
| restricted Core functor `Core₁` | `Core1_func` |
| restricted Core-inclusion transformation | `CoreInclTransf` |
| restricted Core-inclusion κ square | `core_incl_transf_kappa F` |
| `PathLift(h) o κₗ` (with judgmental-identity `κᵣ` omitted) | `path_lift_non_strict_spiral S p s h` |
| `Catd(K)` | `Catd_cat K` / `Catd K` |
| Cat-valued presheaves on `K` | `Psh_cat K` / `Psh K` |
| presheaf restriction `F^*` | `Psh_pullback_func F` |
| contravariant Yoneda functor/object | `yoneda_psh_func K` / `yoneda_psh U` |
| restriction-oriented arrows into `U` | `Into_restr_cat U` |
| conventional slice `K/U` | `Slice_cat U` |
| Cat-valued higher sieves on `U` | `HigherSieve_cat U` / `HigherSieve U` |
| maximal Cat-valued higher sieve | `maximal_higher_sieve U` |
| native subterminal category | `IsSubterminalCat C` |
| pointwise ordinary-sieve property | `IsOrdinarySieve S` |
| ordinary sieves on `U` | `Sieve U` |
| ordinary-sieve pullback along `p` | `sieve_pullback p` / `sieve_pullback_function p` |
| membership of `(V,f)` in `R` | `SieveMembership R (V,f)` |
| maximal ordinary sieve | `maximal_sieve U` |
| proposition-valued sieve coverage | `SieveCoverage K` / `Covers J R` |
| Grothendieck topology laws/package | `IsGrothTopology J` / `GrothTopology K` |
| chaotic topology | `chaotic_groth_topology K` |
| witness-rich sieve generators | `SieveGeneratorFamily K` |
| topology acceptance / cover inclusion | `GrothTopologyAcceptsGenerators G T` / `GrothTopologyLe T U` |
| generated coverhood and least topology | `GeneratedSieveCover G U R` / `generated_groth_topology G` |
| internal eligible covering-question category | `DirectCoverQuestion_cat K T` |
| whole matching/section displayed families and restriction | `DirectCoverQuestionMatching_catd K T X` / `DirectCoverQuestionSection_catd K T X` / `direct_cover_question_restriction_funcd K T X` |
| internal Pédrot-style direct-cover sheaf structure | `DirectCoverSheafStructure K T X` |
| total syntactic direct-cover sheaf | `DirectCoverSheaf K T` |
| direct cover-completion presheaf and its internal sheaf package | `DirectCoverCompletionPsh K T P` / `direct_cover_completion_sheaf K T P` |
| conventional locality of direct cover completion | `direct_cover_completion_is_topology_local K T P` |
| functorial completion recursor in a seed | `direct_cover_completion_rec_func K T P Y AY` |
| Hom universality into a topology-local target | `direct_cover_completion_hom_omega K T P Y local` |
| Cat-valued local-sheaf facade | `CatValuedSheafData K T` / `Sheaf_cat K T Cat_cat` |
| whole completion reflector and inclusion | `direct_cover_sheafification_func K T` / `cat_valued_sheaf_include_psh_func K T` |
| constructed fixed-site sheafification capability | `direct_cover_sheafification_capability K T` |
| global reflective ringed object with selected covering sieve | `ReflectiveCommRingedSpaceCover K` |
| actual member arrow of that selected sieve | `ReflectiveCommRingedSpaceCoverChart P` |
| factorization of one retained arrow through a selected chart | `CoverChartFactorization chart q` |
| two selected arrows generate the retained covering sieve | `BinarySelectedCoverGeneration P chart0 chart1` |
| whole affine realization of one selected chart generator | `AffineCoverChartRealization P chart` |
| global-first two-generator affine-cover presentation | `BinaryAffineCoverPresentation P` |
| selected affine generator/realization/ring for a retained refinement | `binary_affine_cover_refinement_chart` / `binary_affine_cover_refinement_realization` / `binary_affine_cover_refinement_ring` |
| literal bottom ordinary sieve | `empty_sieve U` |
| selected local unit branch and covering refinement | `CommRingPshLocalUnitBranch O s t q` / `CommRingPshLocalUnitCover T O s t` |
| topology-local local-ring presentation | `CommRingPshTopologyLocalRingPresentation T O` |
| locally-ringed whole object and binary affine atlas | `ReflectiveCommRingedWholeObjectLocalPresentation P` / `BinaryLocallyRingedAffineCoverPresentation P` |
| set-carrier commutative rings | `CommRing` |
| carrier and retained sethood of `R` | `comm_ring_carrier R` / `comm_ring_carrier_is_set R` |
| operation/law packages on `A` | `CommRingOps A` / `IsCommRing A ops` |
| ring operations `0`, `1`, `+`, unary `-`, `*` | `comm_ring_zero`, `comm_ring_one`, `comm_ring_add`, `comm_ring_neg`, `comm_ring_mul` |
| one-element zero ring | `zero_comm_ring` |
| structured ring morphisms `R -> S` | `CommRingHom R S` |
| carrier function/application of `h` | `comm_ring_hom_function h` / `comm_ring_hom_apply h x` |
| ring-morphism preservation evidence | `CommRingHomLaws` / `comm_ring_hom_zero_law` through `comm_ring_hom_mul_law` |
| ordinary category of commutative rings | `CommRing_cat` |
| pointwise equality/extensionality of ring maps | `CommRingHomPointwisePath` / `comm_ring_hom_ext` |
| explicit unit evidence and inverse | `CommRingUnitEvidence R x` / `comm_ring_unit_inverse` |
| proposition-valued unit theorem | `comm_ring_unit_evidence_is_prop R x` |
| factor through a localization map | `CommRingLocalizationFactor iota h` |
| localization property/package at `f` | `IsCommRingLocalizationAt R f L iota` / `CommRingLocalizationAt R f` |
| chosen localization target/map | `comm_ring_localization_target` / `comm_ring_localization_map` |
| internally coherent localization matching category/restriction | `CommRingPshLocalizationMatching_cat` / `comm_ring_psh_localization_matching_restriction_func` |
| fixed-forward whole localization locality | `CommRingPshLocalizationLocality` |
| selected whole glue and composite-functor paths | `comm_ring_psh_localization_locality_glue_func` / `comm_ring_psh_localization_locality_glue_restrict_functor_path` / `comm_ring_psh_localization_locality_restrict_glue_functor_path` |
| compatibility view of whole locality | `comm_ring_psh_localization_locality_legacy_glue` |
| identity localization of an already-unit element | `comm_ring_unit_identity_localization R f unit` |
| canonical computing localization at one | `comm_ring_identity_localization_at_one R` |
| canonical computing localization at zero | `comm_ring_zero_localization R` |
| structured point map to the zero ring | `comm_ring_hom_to_zero R` |
| stable pointwise structured-map identity | `comm_ring_hom_id_pointwise R` |
| stable pointwise structured-map composite | `comm_ring_hom_comp_pointwise g f` |
| localization first at `f`, then at the image of `g` | `CommRingIteratedLocalizationAt R f g` |
| comparison with localization at `f*g` | `CommRingIteratedLocalizationComparison` / `comm_ring_iterated_localization_comparison` |
| forward/reverse localization comparison maps | `comm_ring_iterated_localization_comparison_forward_map` / `comm_ring_iterated_localization_comparison_reverse_map` |
| whole product/iterated localization cancellation paths | `comm_ring_iterated_localization_comparison_left_law` / `comm_ring_iterated_localization_comparison_right_law` |
| fixed-forward product/iterated localization equivalence | `comm_ring_iterated_localization_comparison_omega_equiv_along` |
| first-class product/iterated localization equivalence | `comm_ring_iterated_localization_comparison_omega_equiv` |
| Nat-indexed finite families | `FiniteFamily A n` / `finite_family_nil` / `finite_family_cons` |
| finite-family pointwise map and sethood | `finite_family_map` / `finite_family_is_set` |
| dependent evidence over a finite family | `FiniteFamilyAll P n xs` / `finite_family_all_cons` |
| selected finite ring sum and dot product | `comm_ring_finite_sum` / `comm_ring_finite_dot` |
| retained unit-ideal coefficient data | `CommRingUnimodularPresentation` / `comm_ring_unimodular_intro` |
| finite affine Zariski-cover presentation | `CommRingZariskiCoverPresentation` / `comm_ring_zariski_cover_map` |
| singleton and binary cover presentations | `comm_ring_unit_zariski_cover` / `comm_ring_binary_zariski_cover` |
| selected localization family over generators | `CommRingLocalizationFamily R n generators` |
| presented finite basic-open cover family | `CommRingZariskiCoverFamily R` |
| big affine slice and coordinate presheaf | `AffineSpecBigSlice_cat R` / `affine_spec_coordinate_psh R` |
| localized chart as a whole big-slice arrow | `affine_spec_chart_localization_arrow h localization` |
| big-affine Zariski generator family | `AffineSpecBigZariskiGenerators R` |
| least generated big-affine Zariski topology | `affine_spec_big_zariski_topology R` |
| selected-family coverhood and leastness | `affine_spec_big_zariski_topology_covers` / `affine_spec_big_zariski_topology_least` |
| supplied affine reflective structure sheaf | `AffineStructureSheafPresentation R` |
| exact generated-topology ringed site | `affine_structure_sheaf_ringed_site P` |
| whole structure/coordinate comparison | `affine_structure_sheaf_coordinate_defiso P` |
| chart components of that whole comparison | `affine_structure_sheaf_to_coordinate_at P U` / `affine_structure_sheaf_from_coordinate_at P U` |
| whole affine coordinate localization locality | `AffineCoordinateLocalizationLocality R` / `affine_coordinate_localization_locality_at` |
| affine compatibility glue view | `affine_coordinate_localization_legacy_glue` |
| thin computational affine-scheme presentation | `AffineSchemePresentation R` / `affine_scheme_intro` |
| affine-scheme structure/locality projections | `affine_scheme_structure` / `affine_scheme_locality` |
| affine-scheme whole ringed-site/computation views | `affine_scheme_ringed_site` / `affine_scheme_coordinate_defiso` / `affine_scheme_locality_at` |
| chosen affine basic-open arrow | `comm_ring_basic_open_arrow localization` |
| basic-open base-change factor and triangle | `comm_ring_basic_open_base_change_factor_map` / `comm_ring_basic_open_base_change_triangle` |
| elementwise basic-open pullback membership | `comm_ring_basic_open_pullback_membership` |
| affine Yoneda functor of points | `affine_spec_functor_of_points R` |
| affine point classifier at a test ring | `AffineSpecPoint R S` |
| semantic basic-open point classifier | `AffineSpecBasicOpenPoint R f S` |
| represented-basic-open equivalence | `affine_spec_basic_open_point_type_equiv localization S` |
| polynomial extension factor | `CommRingPolynomialFactor iota vars h valuation` |
| polynomial-algebra universal property | `IsCommRingPolynomialAlgebra R X P iota vars` |
| chosen polynomial algebra | `CommRingPolynomialAlgebra R X` / `comm_ring_polynomial_target` |
| `E[k]` | `Fibre_cat E k` |
| `F^*E` | `Pullback_catd E F` |
| `Const_K(A)` | `Const_catd K A` |
| `E^op` | `Op_catd E` |
| `Π_k E[k]` | `Pi_cat E` |
| section evaluation functor `s ↦ s[k]` | `piapp0_func E k` |
| `s[k]` | `piapp0 s k` |
| `eta[k] : s[k] → t[k]` | `pi_hom_fapp0 eta k` |
| section-action family `f ↦ s[f]` | `piapp1_func s x y` |
| `s[f]` | `piapp1_fapp0 s f` |
| `Π_K Const_K(A) = Functor(K,A)` | proof-time comparison for `Pi_cat (Const_catd K A)` |
| `const_section_{K,A}` | `const_section_func K A` |
| `const_section_{K,A}(a)` | `Const_func K A a` |
| `const_section_{K,A}(p)` | `Const_transfd K A p` |
| `Σ_k E[k]` | `Sigma_cat E` |
| `(k,u)` | `Struct_sigma k u` |
| `Σ_A(F^*D) → Σ_K D` | `sigma_pullback_total_func F D` |
| `{src,dst : A; witness : src = dst}` | `PathRecord_grpd A` / `Struct_path_record` |
| shaped paths of dependent records | `PathRecordPathView A r s` / `PathRecordPathRefl A r` |
| source/dependent-tail path observers | `path_record_path_src` / `path_record_path_tail` |
| Sigma path encode/decode round trips | `sigma_path_decode_encode` / `sigma_path_encode_decode` |
| PathRecord path encode/decode round trips | `path_record_path_decode_encode` / `path_record_path_encode_decode` |
| `A` is `n`-truncated | `IsTruncGrpd n A` |
| universe of `n`-truncated classifiers | `TruncGrpdU n` |
| proposition/set/groupoid universes | `PropU_grpd` / `SetU_grpd` / `GroupoidU_grpd` |
| proposition / set / ordinary groupoid property | `IsPropGrpd A` / `IsSetGrpd A` / `IsGroupoidGrpd A` |
| pointwise paths between dependent functions | `PiPointwisePath A B f g` |
| diagonal Pi path observation / extension | `PiHapply p` / `PiFunext h` |
| Pi happly/funext equivalence | `pi_happly_type_equiv A B f g` |
| `π₁` | `Sigma_proj1_func E` |
| `Σ(FF)` | `sigma_map_func FF` |
| `Σ(eta) : Σ(FF) => Σ(GG)` | `sigma_map_transf eta` |
| `E[f](u)` | `fapp0 (fib_cov_tapp0_func E x y u) f` |
| `homd_E(x,u,y,v)` | `homd_ (id_funcd E) x u y v` |
| Natural family morphisms | `Functord_cat E D` / `Functord E D` |
| Natural family transformations | `Transfd_cat FF GG` / `Transfd FF GG` |
| `Functor_catd(A,B)` | `Functor_catd A B` |
| `S(A,B)[k] = Functor(A,B[k])` for constant `A` | `Functor_catd (Const_catd (Op_cat K) A) B` |
| coherent displayed evaluation `P(S(A,B),Const_K(A)) →_K B` | `Eval_funcd B` |
| displayed terminal weakening `E →_K Const_K(1)` | `Terminal_funcd E` |
| `Hom_catd(E,X,Y)` | `Hom_catd E X Y` |
| `Transf_catd(A,B,FF,GG)` | `Transf_catd A B FF GG` |
| `PathOut_Z(x)` | `PathOut_cat Z x` |
| `(y,p) : PathOut_Z(x)` | `pathout_obj Z x y p` |
| `reflout_x` | `pathout_refl_obj Z x` |
| `rho_{x,y,p}` | `pathout_refl_arrow Z x y p` |
| `PathInd_transfd(Z)` | `PathInd_transfd Z` |
| `Sigma_transfd_funcd(eta)` | `Sigma_transfd_funcd eta` |
| Sigma-total path induction | `PathInd_funcd Z` |
| `section_total(s)` | future named facade; transparently expressible through terminal totalization and `sigma_map_func(s)` |
| `K × A` | `Product_cat K A`; also the normal form of `Sigma_cat(Const_catd K A)` |
| `π₁ : K × A → K` | `Product_projL_func K A` |
| `π₂ : K × A → A` | `Product_projR_func K A` |
| type equivalence `A ≃ B` | `TypeEquiv A B` |
| groupoid-universe identity view | `GrpdPathView A B` |
| encode/decode the groupoid-universe identity view | `grpd_path_encode p` / `grpd_path_decode e` |
| direct categorical-universe identity classifier | `OmegaEquiv Cat_cat A B` |
| native equality-valued fixed-arrow equivalence | `OmegaEquivAlong C x y f` |
| native first-class omega-equivalence facade | `OmegaEquiv C x y` |
| explicit object-path equivalence package | `object_path_equiv p` |
| literal path-category equivalence package | `path_equiv p` |
| explicit equality/equivalence identity casts | `object_path_to_equiv_cast` / `omega_equiv_to_object_path_cast` |
| native next-hom preservation of equivalence | `omega_equiv_along_fapp1 F u` |
| coherent internal groupoidality | `IsGroupoidalCat C` |
| groupoidal arrow/path selection and re-inclusion | `groupoidal_arrow_to_path g f` / `groupoidal_path_to_arrow_retract g f` |
| equivalence-valued displayed transport | `groupoidal_fibre_transport_equiv g D f` |
| unrestricted uniqueness of native fixed-arrow evidence | `omega_equiv_along_evidence_is_prop C x y f` |
| truncation closure under an explicit retraction | `is_trunc_retract n r h` |
| finite-dimensional object truncation | `ncat_obj_trunc n C h` |
| ordinary iso to native fixed-arrow evidence | `iso_evidence_omega_along i` |
| ordinary iso to native omega-equivalence facade | `iso_evidence_omega_equiv i` |
| former-specific successor path induction | `nat_succ_ind_eqr P u p` |
| proposition lift to a native categorical dimension | `prop_is_trunc_cat_dim n h` |
| inverse type equivalence | `type_equiv_sym e` |
| composite type equivalence `eBC ∘ eAB` | `type_equiv_comp eBC eAB` |
| groupoid univalence capability | `GrpdUnivalence` / `grpd_univalence_by_decoder` |
| ordinary categorical isomorphism evidence | `IsoEvidence C x y` |
| categorical univalence capability type | `CatUnivalence C` |
| computational isomorphism | `DefIso C x y` |
| profunctors `A -/-> B` | `Prof_cat A B` / `Prof A B` |
| vertical profunctor maps | `ProfMap P Q` |
| unit hom profunctor | `Unit_prof A` |
| endpoint reindexing | `Prof_reindex R F G` |
| profunctor tensor | `Prof_tensor P Q` |
| computational profunctor comparison | `ProfComparison P Q` (transparent `DefIso` view) |
| weighted-limit comparison | `IsWeightedLimit_cov_comp F W L` |
| directed join | `Join_cat A B` |
| 2-endomorphisms of `id_x` | `EH_2End B x` |
| Eckmann–Hilton commutativity | `EH_comm B x alpha beta` |

The implementation contains additional projection heads to make Lambdapi
normalization reliable. They are part of the checked kernel engineering, not
part of the conceptual surface theory described in this note.
