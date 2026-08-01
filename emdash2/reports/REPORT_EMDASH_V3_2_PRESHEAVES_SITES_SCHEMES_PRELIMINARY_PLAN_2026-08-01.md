# Emdash v3.2 Presheaves, Sites, And Schemes Living Preliminary Plan

Date: 2026-08-01 (America/Toronto)

Plan-ID: `PRESHEAVES-SITES-SCHEMES-V3.2`

Depends-On: active `emdash3_2.lp`; the promoted displayed-facade, Sigma/Pi,
contravariant-hom, `DefIso`, adjunction, and profunctor owners; the completed
record/structure usability tranche for a later TypeScript API mirror

Supersedes: no active v3.2 plan; this replaces only the idea of mechanically
porting the ignored `cartierSolution13.lp`/`cartierSolution16.lp.txt` sources

Side-Task-Ledger: `PSSS-00` through `PSSS-12` below

Infinity-Codex-Origin: session
`019fbb03-cc64-7cf2-be18-24c35b0dfab0`, continuation turn
`019fbc5c-646c-7250-af9f-5a7b29c16240`

Infinity-Codex-Decision-Responses: the same session's checkpointed
record/structure response plus the comprehensive architecture review archived
as
`/home/user1/emdash1/emdash2/tmp/ai-responses/sessions/2026-08-01_019fbb03cc64/responses/0004_2026-08-01T08-39-07Z_019fbc5c-646c-7250-af9f-5a7b29c16240.md`
(`infinity-codex:019fbb03-cc64-7cf2-be18-24c35b0dfab0:019fbc5c-646c-7250-af9f-5a7b29c16240`);
recovery index
`/home/user1/emdash1/emdash2/tmp/ai-responses/sessions/2026-08-01_019fbb03cc64/INDEX.md`

Status: active living implementation architecture. `PSSS-00` is complete.
`PSSS-01`, `PSSS-02`, bounded `PSSS-03a`, direct-topology `PSSS-04a`,
`PSSS-06a`, `PSSS-06b`, and `PSSS-07a` through `PSSS-07d` are green and
included in the authorized local foundation checkpoint. `PSSS-03b` remains
the named `Omega` research gate. `PSSS-05a` retains a green anchored-descent
research probe and nonempty assumption-explicit API consumer, but no promoted
source or derived nonempty semantic model; its later rigid-adapter promotion
trial was rejected and removed. Carrier-functor action, localization inverse
laws, geometric cover interpretation, and positive-variable polynomial
representation remain separately consumer-gated. The synchronized catalog
contains 1,860 checks across 73 areas. Health passes all 61 targets in 314.231
seconds at source snapshot
`sha256:35a1d735feeea679e12e62b3bc14690783758c0da59ed1e8f20522f898f075df`.
After the PSSS-05a adapter removal, the final combined checkpoint gate passes
all 61 Lambdapi targets in 342.266 seconds, followed by 39 Python tests, five
registry tests, all source/header/reference and book checks, the strict kernel
audit, and fresh strict catalog verification

Branch: `goal/presheaves-sites-schemes-v3.2`

Worktree: `/home/user1/emdash1-presheaves-sites-schemes`

Parent checkpoint: `ba4fe3c50705035c84e6b64a525303efba19c9eb`
(`docs: plan presheaf and scheme library`)

Git authorization: the parent record/structure tranche was explicitly
authorized and locally checkpointed. On 2026-08-01 the user explicitly
authorized checkpointing this reviewed documentation baseline, creating a
dedicated implementation branch/worktree, starting implementation, and
starting a corresponding persistent goal. During the implementation
continuation the user also explicitly authorized local green checkpoint
commits as the iterative safety boundary. Each checkpoint still requires a
bounded coherent tranche, synchronized living-plan evidence, a green SOP
gate, and an exact staged-diff audit. Authorization still excludes push,
merge, publication, history rewrite, cleanup, branch deletion, and worktree
removal.

## 1. Objective

Design a v3.2 standard-library path from the active categorical kernel to:

- Cat-valued presheaves and their Set/discrete specializations;
- ordinary and higher sieve presentations;
- coverages, Grothendieck topologies, descent, and sheaves;
- commutative rings, localization, polynomial-algebra consumers, and the
  Zariski coverage;
- ringed and locally ringed sites;
- affine charts, schemes, and functor-of-points comparisons.

The target is not a line-by-line translation of the historical Cartier
sources. The target is a small sequence of owner-aligned, independently
checkable one-way library modules whose definitions reuse the active v3.2
calculus and whose computation is carried by existing generic owners whenever
possible.

The authorized implementation line began with only the `PSSS-01` presheaf
facade. After its full green gate, the separately scoped `PSSS-02` tranche
promoted the already-probed Yoneda/Sigma/slice and Cat-valued higher-sieve
formulas. `PSSS-03a` now crosses only the separately audited ordinary-sieve
property boundary: it adds native subterminal categories, ordinary-sieve
packages, and pullback preservation, but no `Omega`, topology, descent,
algebra, or scheme declaration. Those later layers remain behind their named
gates.

### 1.1. Living-Plan Protocol

This report is the active design, decision, implementation, and recovery
ledger for the PSSS line of work. It is deliberately preliminary in the sense
that names, boundaries, and mathematical presentations remain revisable as
typed consumers and kernel diagnostics provide stronger evidence. It is
living in the stronger operational sense that every implementation tranche
must update this report in the same bounded change whenever it:

- confirms, refines, rejects, or supersedes a decision in Section 18;
- changes a phase gate, module boundary, normal form, or success criterion;
- discovers a new owner, consumer requirement, warning, or trust-boundary
  consequence; or
- promotes a formula from research evidence to checked standard-library API.

Decision changes must preserve the old conclusion as dated recovery evidence
and explain why the new evidence wins; they must not silently rewrite the
history into an appearance of inevitability. Phase statuses use at least
`proposed`, `in progress`, `blocked by named gate`, `green`, and `promoted`.
An attractive formula in this report is not immutable kernel policy until its
own phase is typed, audited, documented, and promoted through the stated SOP.

This revision comprehensively integrates the architecture review named in the
`Infinity-Codex-Decision-Responses` header: the rigid one-parameter
Cat-valued presheaf facade, its deliberately one-way comparison, reindexing
through opposite functors, Yoneda/Sigma/slice formulas, the ordinary-versus-
higher-sieve boundary, Zeuner's compact-open support versus sieve-valued
support, separation of coverage/topology/modality, descent via selected
`DefIso` or weighted comparison, universal-property-first algebra,
consumer-gated polynomial and coinductive interfaces, the proposed module
sequence, concurrency assessment, and validation gates. The archived response
is recovery evidence; active code, SOP, and this subsequently updated ledger
remain authoritative in the order stated below.

## 2. Authority And Reviewed Evidence

Use this order on every continuation:

1. `../emdash3_2.lp` for active mathematical declarations and computation;
2. `../emdash3_2_presheaves.lp` and `../emdash3_2_sieves.lp` for the selected
   one-way presheaf/higher-sieve and ordinary-sieve APIs;
3. `../AGENTS.md` and the current-status/SOP report for the Lambdapi workflow;
4. `../emdash3_2_checks.lp` for durable diagnostics;
5. `EMDASH_FOUNDATIONS.md` and the canonical-syntax report;
6. this plan for the selected standard-library staging;
7. `../../docs/RECORD_STRUCTURE_USABILITY_V3_2_PLAN.md` only for the
   TypeScript outer-LF record API boundary; and
8. the explicitly authorized ignored Cartier sources and local Zeuner review
   only as historical consumer/research evidence.

The review inspected:

- the active `Op_cat`, `Catd_cat`, `Pullback_catd_func`, `hom_con`,
  `hom_con_int`, `Sigma_cat`, `Sigma_func`, `Catd_catd_con`, `Pi_cat`,
  `DefIso`, `Adjunction`, `Prof_cat`, and weighted-representability owners;
- the displayed-facade plan's direct-comparison and nontransitive-unification
  requirements;
- the complete historical sieve/site/ring/localization/locally-ringed-site/
  affine/scheme sections of `cartierSolution16.lp.txt` and the relevant
  profunctor/context infrastructure of `cartierSolution13.lp`;
- the local review of Max Zeuner; and
- visually rendered PDF pages containing Zeuner's Definition 3.4,
  Corollary 3.21, Definition 4.22, Theorem 5.22, the Zariski coverage, and the
  affine-cover record.

The supplied Poppler extraction and page rendering were sufficient. No host
package installation was necessary.

## 3. Main Assessment

The project is ready for a presheaf and higher-sieve foundation. It is not yet
ready for a single monolithic `schemes.lp` port.

Three active v3.2 improvements materially change the architecture relative to
the historical source:

1. `Catd_cat` is now a stable facade for Cat-valued functorial families, with
   explicit runtime projections and narrow proof-time comparisons.
2. contravariant representables, Sigma totals, reindexing, computational
   `DefIso`, indexed adjunctions, and Cat-valued profunctors already have
   selected generic owners;
3. the new TypeScript structure declaration removes outer-LF record
   boilerplate for future API consumers, while deliberately remaining outside
   the Lambdapi parser and trusted Core.

The historical file nevertheless exposes valuable consumer requirements:

- a sieve classifier with pullback, maximal sieve, intersection, and
  dependent sub-sieve operations;
- a distinction between presheaves, sheaves, and sheafification/glue;
- a sieve-valued invertibility locus `D : O -> Omega`;
- a localization comparison over that locus;
- induced sites and sheaves on slices;
- affine-basic-open computation;
- affine covers and a hybrid locally-ringed-site/functor-of-points view.

Its ad hoc rewrite rules, opaque topology assumptions, incomplete ring
signature, direct fraction representation, and self-referential affine
interface are not suitable owners for v3.2.

## 4. Zeuner And The Sieve-Valued Upgrade

Zeuner's locally ringed lattice uses

```text
D_u(s) : downarrow(u),
```

the largest compact open below `u` on which the restriction of `s` is
invertible. In the coherent/qcqs setting this is a deliberate and valid
point-free presentation, not a failed definition. It supports the checked
localization statement

```text
O_X(D_u(s)) ~= O_X(u)[1/s]
```

and participates in the equivalence between functorial and geometrical qcqs
schemes.

The Cartier proposal retains more information:

```text
D : O -> Omega,
```

where `D_u(s)` is the sieve of arrows `v -> u` along which `s` becomes
invertible. This should be treated as a generalization/refinement:

- on a coherent posetal site, the sieve may be represented by Zeuner's
  largest compact open;
- on a general site, it need not have a single representing open;
- in a higher setting, the fibres may retain witnesses and coherence rather
  than only a truth value.

The library should therefore expose a comparison between these
presentations, not select one as the universal replacement for the other.
In particular, a future compact-support extraction should state when an
invertibility sieve is representable by a compact open.

There is a second important qualification. A classical Grothendieck sieve is
subterminal/proposition-valued. An arbitrary Cat-valued presheaf on a slice is
a useful **higher sieve** or descent coefficient system, but it is not
literally the ordinary subobject classifier. The names and APIs must preserve
this distinction.

## 5. Presheaf Facade Decision

### 5.1 Selected first candidate

The smallest useful rigid facade is the Cat-valued convention:

```lambdapi
injective symbol Psh_cat (K : Cat) : Cat;

rule Obj (Psh_cat $K)
  ↪ Obj (Catd_cat (Op_cat $K));

rule Hom_cat (Psh_cat $K) $P $Q
  ↪ @Functord_cat (Op_cat $K) $P $Q;

unif_rule Psh_cat $K ≡ Catd_cat $K0
  ↪ [ $K ≡ Op_cat $K0 ];

symbol Psh (K : Cat) : Grpd
≔ Obj (Psh_cat K);
```

This uses one comparison, not both suggested mirror rules. The generated
constraint mirrors the active `Prof_cat` endpoint-recovery pattern. It
recovers `K0 = Op_cat K` through opposite involution without installing two
overlapping equations.

`Psh_cat K` and `Catd_cat(Op_cat K)` remain distinct runtime heads. `Obj` and
`Hom_cat` are the explicit computation boundary; the `unif_rule` is only a
proof-construction/elaboration comparison. Typed `eq_refl`, not a bare
conversion assertion, must test it.

### 5.2 Reindexing

For `F : A -> B`, presheaf restriction is already the ordinary Catd pullback
along `F^op`:

```text
Psh_pullback_func(F)
  : Psh_cat(B) -> Psh_cat(A)
  := Pullback_catd_func(Op_func(F)).
```

The facade therefore adds no new functoriality, identity, composition, or
naturality owner.

### 5.3 Set-valued versus Cat-valued

The first facade is Cat-valued because that is the active `Catd` universe and
because it immediately supports higher descent. A later pointwise property
can select discrete/Set-valued fibres. This lets variance, Yoneda, pullback,
slice, and classifier construction proceed uniformly while keeping the actual
descent level explicit.

Do not call every Cat-valued presheaf a stack. Stackhood additionally requires
a selected descent condition, and the current kernel uses strict functorial
owners rather than a completed weak `(infinity,1)`-categorical coherence
theory.

A value-category-parameterized `PresheafInto_cat(K,V)` remains a reasonable
later API when `CommRing_cat` or another concrete target category requires it.
It is not part of the first facade because no current consumer justifies a
second direct comparison with raw `Functor_cat`.

## 6. Yoneda, Slices, And Higher Sieves

### 6.1 Contravariant Yoneda object

For `U : Obj K`, the existing contravariant represented family already is the
Yoneda presheaf:

```text
y_K(U)[V] = Hom_K(V,U)
y_K(U)    = hom_con(U,id_K) : Psh(K).
```

No parallel Yoneda action owner is needed. `hom_con_int(id_K)` internalizes
the variation in `U`.

### 6.2 Restriction-oriented category of arrows and the slice

The Sigma total

```text
Into^-_K(U) = Sigma_(V : K^op) Hom_K(V,U)
```

has arrows in the restriction direction: a witness over `f : V -> U` maps to
one over `f o a : W -> U`. Its opposite is the conventional slice:

```text
Slice_cat(K,U) = Op_cat(Into^-_K(U)).
```

This uses the active Sigma hom/action calculus rather than a new comma
constructor.

### 6.3 Higher-sieve classifier

The family of categories of Cat-valued predicates on arrows into `U` is
definable from current owners:

```text
ArrowInto_catd(K)[U]
  = Sigma_(V : K^op) Hom_K(V,U)

HigherSieveClassifier(K)
  = Catd_catd_con(ArrowInto_catd(K))
  : Psh(K).
```

Pointwise:

```text
HigherSieveClassifier(K)[U]
  = Functor_cat(Into^-_K(U),Cat_cat)
  = Cat-valued presheaves on Slice_cat(K,U).
```

The action on `p : V -> U` is inherited from:

1. postcomposition `y(V) -> y(U)` owned by `hom_con_int`;
2. functorial Sigma totalization; and
3. `Catd_cat_func` pullback.

Thus pullback of higher sieves needs no constructor-specific identity or
composition rule. The maximal higher sieve is the existing terminal family on
`Into^-_K(U)`. Fibrewise intersection can reuse the existing transparent
displayed product once a consumer fixes the desired truncation level.

### 6.4 Probe and promotion evidence

An ephemeral full-import Lambdapi probe checked all of the following against
the unchanged active kernel:

- the proposed `Psh_cat` `Obj`/`Hom_cat` projections and single unification
  comparison;
- `Psh_pullback_func(F) = Pullback_catd_func(Op_func(F))` at object action;
- `y_K(U)[V] = Hom_K(V,U)`;
- the `ArrowInto_catd` Sigma fibre;
- the `HigherSieveClassifier` point fibre; and
- the terminal/maximal higher sieve.

The initial bounded check completed successfully in approximately ten
seconds. A second owner-focused probe before promotion additionally checked:

- `yoneda_psh_func(K) : Functor(K,Psh_cat(K))` as the transparent
  `hom_con_int(id_K)` facade;
- facade-level Yoneda arrow action and its point component reducing to
  ordinary `hom_postcomp_func`;
- Sigma-total arrow action;
- higher-sieve restriction reducing to the existing `Pullback_catd_func`;
- stability of `maximal_higher_sieve` under that restriction; and
- the exact proof-time boundary between `HigherSieve_cat(U)` and
  `Psh_cat(Slice_cat(U))`.

The final quiet probe completed in `4.3s`; the warning-enabled probe remained
at the inherited `1179 = 1020 + 159` kernel warnings. The ignored probe is
diagnostic evidence only. Its selected declarations and assertions are now
retained in `emdash3_2_presheaves.lp`, central diagnostics, and
`examples/higher_sieve_classifier.lp`.

One plausible direct comparison was deliberately rejected. Lambdapi accepts
typed reflexivity from each public presentation to the common intermediary
`Catd_cat(Into_restr_cat(U))`, but it does not transitively chain those two
experimental unification steps to make
`HigherSieve_cat(U) = Psh_cat(Slice_cat(U))` directly reflexive. PSSS-02 keeps
the stable intermediary and a runtime non-collapse diagnostic rather than
installing a convenience unifier with no independent owner semantics.

### 6.5 Ordinary sieves

`PSSS-03a` selects the following native categorical contract:

```text
IsSubterminalCat(C)
  = Sigma obj_prop : IsPropGrpd(Obj(C)), IsGroupoidalCat(C).

IsOrdinarySieve(S)
  = Pi f : Obj(Into_restr_cat(U)),
      IsSubterminalCat(Fibre_cat(S,f)).

Sieve(U)
  = Sigma S : HigherSieve(U), IsOrdinarySieve(S).
```

The first field of `IsSubterminalCat` says that there is at most one object.
It is not sufficient alone: a one-object directed category can still have
nontrivial endomorphisms. The active native `IsGroupoidalCat(C)` field says
that the core inclusion is an equivalence, so all retained categorical cells
come from object equality. Together these fields select the empty/terminal
categorical possibilities without requiring every input to be definitionally
presented as `Path_cat(A)`. Literal `Path_cat(A)` for proposition-valued `A`
is nevertheless a canonical checked example, and every selected subterminal
category derives the existing exact `IsDiscreteCat` contract.

The ordinary-sieve package retains the entire higher-sieve functor, hence all
restriction and higher action already owned by the Catd calculus. The added
field is pointwise evidence only; it does not introduce another action
calculus. Pullback along `p : V -> U` uses the existing
`HigherSieveClassifier` arrow action, and its ordinary witness at an arrow
`f` into `V` is the old witness selected at the arrow-total image of `f` under
postcomposition with `p`. The implementation adds no rewrite or unification
rule.

Both property layers are themselves proposition-valued. The checked proof for
`IsSubterminalCat(C)` combines the active proposition theorem for truncation
evidence, the active proposition theorem for `OmegaEquivAlong` evidence, and
Sigma closure. The proof for `IsOrdinarySieve(S)` then uses dependent-Pi
closure. Retaining these witnesses is therefore mathematically harmless, but
it is not judgmentally invisible: `sieve_pullback(id,R)` reconstructs a Sigma
package and deliberately does **not** reduce to `R`.

This last negative result is the main boundary for `PSSS-03b`. A genuine

```text
Omega : Psh(K)
Omega[U] = Sieve(U)
```

still needs both:

1. a theorem `IsSetGrpd(Sieve(U))`, which in turn needs an extensionality
   route for the underlying functor/subterminal data; and
2. an owner-aligned contravariant family assembly whose identity and
   composition behavior does not rely on reconstructing retained evidence
   packages.

An ephemeral candidate primitive `Omega` with an inferred-source fibre rule
and explicit pullback action typechecked and remained warning-neutral, but its
identity object action still failed to compute to the input sieve. An earlier
explicit-`Op_cat` form additionally created three avoidable critical pairs.
Neither candidate establishes the required classifier, so no `Omega` symbol
or rule is promoted.

Two other attractive shortcuts are rejected by the audit:

- `IsPropGrpd(Obj(C))` alone is too weak because it permits nontrivial
  directed endomorphisms; and
- simply mapping into `Path_cat(PropU_grpd)` does not provide the desired
  proposition-and-function category: its arrows are equalities/equivalences
  of propositions, not implication functions, and the active library has no
  selected full-subcategory/comprehension owner that repairs this mismatch.

The successful focused evidence is retained in
`tmp/probes/psss03_ordinary_sieve_boundary.lp`, with quiet log
`logs/probes/psss03_ordinary_sieve_boundary-20260801-064518.log` and
warning-enabled log
`logs/probes/psss03_ordinary_sieve_boundary-20260801-064527.log`. The latter
inherits exactly `1179 = 1020 + 159` warnings. Promoted declarations live in
a separate one-way `emdash3_2_sieves.lp` importing the basic presheaf module
and the equality-valued evidence-property module.

## 7. Coverage, Topology, And Modality Are Different Layers

The historical `site` symbol implicitly bundled topology, closed sieves,
sheafification, and glue. v3.2 should separate three presentations.

### 7.1 Coverage presentation

An end-user-friendly coverage presents generating cover families. A cover
family should expose at least:

- an index shape;
- a diagram of domains;
- a coherent family of arrows to the covered object; and
- selected base-change data or an equivalent stability witness.

This is the right input layer for:

- Zariski covers generated by localizations;
- etale, smooth, or other algebraic cover families;
- finite combinatorial sites; and
- manually generated/direct presentations.

### 7.2 Grothendieck topology

A topology classifies covering **ordinary** sieves and supplies maximality,
pullback stability, and local character/transitivity. Pullback stability should
reuse presheaf transport. Local character is the genuinely new operation.

A generic free saturation from coverage generators is not an early target. It
is a closure/quotient or higher-inductive construction and belongs with the
postponed higher-inductive declaration problem. Initial concrete coverages may
instead supply their topology witnesses directly.

### 7.3 Sheafification modality

A reflector/sheafification is additional computational structure, not part of
the bare topology definition. When present it should be packaged as:

```text
a_J      : Psh_cat(K) -> Sheaf_cat(J)
include  : Sheaf_cat(J) -> Psh_cat(K)
a_J |- include
```

using the active `Adjunction` relation. Left exactness is a separate field or
property. This replaces the historical global `mod_smod` fold and its ad hoc
glue cancellation rule.

## 8. Descent And Sheaves

The primary sheaf condition should compare a fibre with a category of matching
or descent data. For each selected cover `c` of `U`, prefer a computational
comparison of the form:

```text
DefIso(Cat_cat, P[U], Descent(P,c)).
```

The existing `DefIso` push/pull and cancellation owners then implement
restriction and glue. This avoids one rewrite rule per sheaf constructor.

When a cover supplies a weight or Cech/descent shape, reuse the existing
weighted-limit comparison rather than inventing a second limit calculus. A
coverage may initially carry its descent shape explicitly; a generic Cech
nerve construction can wait for concrete pullback and simplicial consumers.

This formulation is uniform in the following controlled sense:

- Cat-valued fibres give category-valued descent;
- pointwise discrete fibres specialize to ordinary Set-valued sheaves; and
- proposition-valued fibres specialize to subterminal sheaves/sieves.

It does not claim that strict Cat-valued descent is already the complete theory
of weak higher stacks.

`Sheaf_cat(J)` may later be a stable subcategory facade whose objects package
`P : Psh(K)` with `IsSheaf(J,P)` and whose homs project to presheaf natural
maps. No sheafification functor is required to form this category.

## 9. Commutative Algebra Boundary

Do not copy the historical `ring` interface. It omits most ring laws, treats
localization as explicit numerator/exponent syntax, and installs computations
that belong to one concrete representation.

The algebra module should eventually provide:

- a category `CommRing_cat` with explicit carrier and morphism observations;
- zero, one, addition, multiplication, negation, and the commutative-ring laws;
- a functorial carrier into the chosen discrete/type-like categorical
  presentation;
- localization `R -> R[1/f]` by a universal property;
- selected computational comparison data for iterated localization; and
- polynomial algebras by their universal property before selecting a concrete
  syntax of monomials.

The Zariski coverage depends on localization and finite/unimodular families,
not on polynomial algebras specifically. Polynomial algebras are important
consumers and examples, but the topology module must not depend on them.

For a finite family `(f_i)`, the covering condition is the appropriate
unit-ideal/radical condition, not the historical binary shortcut `f_1+f_2`.
Base change sends `(f_i)` to `(phi(f_i))`; the localization universal property
should own the induced comparison maps.

Finite lists/vectors and finite sums are a separate algebraic prerequisite.
They do not justify reviving a generic ordinary-inductive declaration macro;
the future higher-inductive-category design remains independently postponed.

## 10. Ringed And Locally Ringed Sites

A ring-valued presheaf should preferably be a presheaf into `CommRing_cat`,
with its underlying Cat-valued presheaf obtained through the carrier functor.
This makes restriction maps ring morphisms by functoriality rather than by a
parallel family of axioms.

For a section `f` over `U`, define the semantic invertibility sieve by:

```text
InvSieve(O,U,f)(v : V -> U)
  = witnesses that restrict_v(f) is invertible in O(V).
```

Functoriality of restriction makes this a sieve. In ordinary commutative
rings the witness type is proposition-valued; enriched variants may retain
higher witness data.

For usability and stable computation, a locally ringed site may store a
selected transformation

```text
D : O -> HigherSieveClassifier(K)
```

together with a typed computational/propositional comparison to
`InvSieve(O)`. This follows the v3.2 principle used elsewhere: retain a stable
selected observation, but do not globally identify an arbitrary user name
with a canonical owner by an unbacked rewrite.

The localization law should be a selected comparison between sections/descent
over `D(f)` and `O(U)[1/f]`, preferably through `DefIso` or the weighted-limit
API. Keep this separate from the mere formation of `D(f)`.

Morphisms also need separation:

- a continuous functor between sites;
- an induced geometric morphism/sheaf adjunction when constructed;
- left exactness of inverse image; and
- a local morphism of ring sheaves for locally ringed sites.

The historical `site_morph` required an adjoint pair and continuity in one
package. That is useful for its slice consumer but too restrictive as the
general definition.

## 11. Schemes And Functor Of Points

### 11.1 Affine schemes and basic opens

`Spec` should be a functorial construction from commutative rings to locally
ringed sites. The central computational basic-open theorem is a selected
comparison:

```text
Spec(R) / D(f)  ~=  Spec(R[1/f]).
```

This comparison, plus iterated-localization coherence, should own the concrete
behavior historically spread across `ascheme_*` rewrite rules.

### 11.2 Scheme atlas

Prefer a conventional computational atlas package:

- a locally ringed site `X`;
- a covering family of opens/charts;
- a ring `R_i` for each chart; and
- selected computational equivalences between each ringed slice and
  `Spec(R_i)`, with overlap coherence as required.

The historical source rejected isomorphism-to-affine because its old
isomorphisms did not compute. Active `DefIso` changes that assessment: a
selected equivalence with cancellation can support computation. Therefore the
self-referential/coinductive `ascheme` interface should be an optional optimized
view, not the foundational definition, until a consumer proves it necessary.

### 11.3 Functor of points

Once `Spec` and a category of locally ringed sites exist, the functor of points
is represented by existing contravariant hom/profunctor infrastructure. In
particular, `hom_con`, `Conjoint_prof`, and `Hom_prof_along` already express
the required variance. Do not add a bespoke functor-of-points action owner.

A Zeuner-style equivalence should be scoped to its intended qcqs/spectral
subcategories. The later hybrid theorem can compare:

- the locally-ringed-site/atlas presentation; and
- the local functor-of-points presentation.

It is not part of the first site or scheme implementation tranche.

## 12. Standard-Library Module Layout

Keep `emdash3_2.lp` unchanged for the first experiment. Follow the existing
one-way module precedent:

```text
emdash3_2_presheaves.lp
emdash3_2_sieves.lp
emdash3_2_sites.lp
emdash3_2_commutative_algebra.lp
emdash3_2_ringed_sites.lp
emdash3_2_schemes.lp
```

The dependency direction is one way:

```text
kernel
  -> presheaves

kernel -> native equality evidence
       + presheaves
  -> sieves

sieves + reusable Unit proposition evidence
  -> sites

kernel + algebra
  -> ringed sites
  -> schemes
```

The separate sieve module is now justified rather than merely proposed:
ordinary subterminality uses the downstream equality-evidence property layer,
whereas basic Cat-valued presheaves and higher sieves do not. This preserves a
one-way dependency and avoids forcing truncation/evidence theorems into the
basic presheaf facade. A single giant `emdash3_2_adjunctions`-style or
`schemes` file must not mix foundational presheaf variance with topology,
algebra, and atlas rules.

Each promoted module needs a focused check/example module, explicit inclusion
in the bounded check script, catalog/health synchronization where applicable,
warning comparison, strict LHS audit, and the normal full CI gate at its
integration boundary.

## 13. TypeScript Structure Macro Role

The completed record/structure declaration is relevant but is not callable
inside a `.lp` file. There is currently no approved workflow in which the
TypeScript elaborator is the source of truth for standard-library Lambdapi
modules.

For the Lambdapi-first work:

- use ordinary checked Lambdapi declarations as authority;
- use the TypeScript macro later to mirror or generate consumer declarations
  only after source ownership and freshness checking are designed; and
- keep the string parser restricted to expressions/terms.

The current macro is unparameterized. Many top-level structures can still be
represented by making the base category/site the first field of one package,
as in the historical `struct_mod_loc`. Truly indexed record declarations
remain a separate macro extension.

## 14. Concurrent Elaborator Work

The concurrent `goal/typescript-elaborator-v3.2` worktree is dirty and owns an
uncheckpointed mixed-introduction tranche. This preliminary design neither
imports nor edits it.

The explicit Lambdapi compositions used by the green presheaf/sieve probe do
not depend on the new TypeScript `^n/^f/^f` presentation. There is therefore
no reason to pause the architecture review. Before a future implementation
branch is created, inspect whether that other tranche has reached a green
checkpoint and select a common descendant if its kernel rule has been
promoted. Never copy its uncommitted files.

## 15. Proposed Implementation Sequence

### Phase PSSS-00 — Review and formula probe

Status: complete.

- inspect active owners and historical consumers;
- inspect and visually verify the Zeuner sources;
- typecheck the candidate `Psh_cat`, reindexing, Yoneda, slice, higher-sieve
  classifier, and maximal sieve in an ephemeral probe;
- record the ordinary/higher sieve distinction and the staged architecture.

### Phase PSSS-01 — Presheaf facade

Status: green and included in the authorized local foundation checkpoint;
declarations, diagnostics, reviewer example, warning/audit comparison,
synchronized catalog/health, and full integration CI pass.

- add the one-way presheaf module;
- promote only `Psh_cat`, `Psh`, the two runtime projections, the single
  direct `Catd_cat` comparison, and `Psh_pullback_func`;
- add typed `eq_refl`, object/hom, abstract/opposite/nested-opposite, and
  reindexing diagnostics;
- compare warnings and prove no duplicate generic action owner was added.

Implementation evidence, 2026-08-01:

- `emdash3_2_presheaves.lp` now contains exactly the selected rigid facade,
  its two runtime projections, its one proof-time comparison, the `Psh`
  classifier, and transparent restriction through
  `Pullback_catd_func(Op_func(F))`;
- the central diagnostics exercise runtime object/hom projection, abstract,
  opposite, and nested-opposite typed reflexivity, runtime non-collapse,
  wrong-variance non-collapse, restriction object action, and inherited map
  action typing;
- `examples/presheaf_facade.lp` provides the focused reviewer surface, and the
  bounded check/health file registries include the new module;
- the quiet owner, central-diagnostic, and reviewer checks pass; the
  warning-enabled owner probe remains exactly at the inherited `1179`
  warnings (`1020` critical pairs plus `159` replaceable variables), with no
  warning located in the new module;
- strict LHS audit reports zero unreviewed candidates both for the active
  kernel (`52` annotated slots across `32` clauses) and for the new module
  (`0` annotated slots);
- the regenerated catalog contains `1736` checks across `64` mapped areas
  with zero legacy or unclassified checks, and health passes all `43`
  source/example targets with source snapshot
  `sha256:d03049c2f455698cc3cc15fed38a03162bd49e27813b51651e2bb74f4d9b24fa`;
- full `make ci` passes: the Lambdapi metrics sweep checks all `43` targets in
  `118.511s`, followed by `39` Python tests, `5` document-registry tests,
  source TOC/reference/header lints, book evidence/typography/KaTeX/assembly,
  strict kernel audit, and fresh strict catalog verification.

The owner probe also measured a useful facade boundary. Generic
`fapp1_fapp0(Psh_pullback_func(F),eta)` is well typed and inherits its law from
the global functor action. A further `tapp0_fapp0` observation does not
currently runtime-fold through the existing Catd-specific pullback component
projection when the explicit source/target heads remain `Psh_cat`. PSSS-01
does not add a duplicate point-component rule or broaden the kernel owner.
PSSS-02 must first present a real pointwise consumer; it may then select a
narrow facade projection bridge or continue using the canonical underlying
Catd presentation. This negative result is a measured gate, not evidence that
restriction lacks a map action.

### Phase PSSS-02 — Yoneda, slice, and higher-sieve classifier

Status: green and included in the authorized local foundation checkpoint;
declarations, central diagnostics, reviewer example, catalog, audits, warning
comparison, synchronized health, and full integration CI pass.

- promote the transparent formulas proven by the probe;
- name the restriction-oriented total and conventional slice clearly;
- expose point and pullback diagnostics;
- add maximal higher sieve; defer intersection/sub-sieve until consumed.

Implementation evidence, 2026-08-01:

- `yoneda_psh_func(K)` and `yoneda_psh(U)` transparently reuse
  `hom_con_int(id_K)` and its existing object, arrow, and point-component
  computations;
- `arrow_into_catd(K)` composes the existing `Sigma_func(Op_cat(K))` with
  Yoneda, `Into_restr_cat(U)` names its restriction-oriented fibre, and
  `Slice_cat(U)` is its conventional opposite;
- `HigherSieveClassifier(K)` transparently reuses
  `Catd_catd_con(arrow_into_catd(K))`; `HigherSieve_cat`, `HigherSieve`, and
  `maximal_higher_sieve` add only readable classifier names and the existing
  terminal family;
- no rewrite or unification rule was added by PSSS-02, and no Psh-specific
  point-component bridge was needed: the actual Yoneda component consumer
  computes at the canonical represented-hom owner, while higher-sieve
  restriction computes at the canonical Catd pullback owner;
- both slice-presheaf and higher-sieve category presentations receive typed
  reflexivity diagnostics through `Catd_cat(Into_restr_cat(U))`, plus an
  explicit negative direct-conversion diagnostic; and
- `examples/higher_sieve_classifier.lp` records the ordinary/higher boundary
  and the computational route without introducing `Sieve`, `Omega`, topology,
  descent, algebra, or schemes;
- the synchronized catalog has `1749` checks across `65` mapped areas with
  zero legacy or unclassified checks; health passes all `44` source/example
  targets in `177.462s` at source snapshot
  `sha256:ed32de14c4750aac2dd92b537a24983ee471697c2d0f4379ecad482e0284936e`;
  and
- strict LHS audit remains at zero unreviewed candidates for both the kernel
  (`52` annotated slots across `32` clauses) and presheaf module (`0`/`0`),
  while the warning inventory remains `1179 = 1020 + 159` with PSSS-02 adding
  no rule and therefore no new warning family; and
- full `make ci` passes: its fresh Lambdapi sweep checks all `44` targets in
  `191.463s`, followed by `39` Python tests, `5` document-registry tests,
  shell/source/header/reference lints, book evidence/typography/KaTeX and
  assembly checks, strict kernel audit, and fresh strict catalog verification.

### Phase PSSS-03a — Ordinary sieve/property boundary

Status: green and included in the authorized local foundation checkpoint;
declarations, central diagnostics, reviewer example, catalog, health,
documentation, audits, warning comparison, and full integration CI pass.

- define native `IsSubterminalCat(C)` as proposition-valued objects plus
  `IsGroupoidalCat(C)`, not proposition-valued objects alone;
- prove the retained witness proposition-valued and derive
  `IsDiscreteCat(C)`;
- validate proposition-valued `Path_cat(A)` as the canonical literal example;
- package `Sieve(U)` as a higher sieve with pointwise subterminal evidence;
- prove ordinary-sieve evidence proposition-valued;
- preserve ordinary sieves under the existing higher-sieve pullback action;
- add no rewrite/unification owner; and
- retain the negative identity-package eta diagnostic.

The promoted surface is in `emdash3_2_sieves.lp` with reviewer example
`examples/ordinary_sieves.lp`. The maximal **ordinary** sieve is deliberately
not part of PSSS-03a: its elementary terminal-category subterminal witness
should have a natural foundational dependency owner rather than importing Nat
arithmetic solely to borrow `unit_is_prop` or duplicating that theorem locally.

Implementation evidence, 2026-08-01:

- the new module is `201` lines with `16` transparent symbol declarations and
  no rewrite or unification rule; the basic presheaf module grows only by the
  two transparent names `HigherSieve_pullback_func` and
  `higher_sieve_pullback`;
- the reviewer example has seven positive assertions and the identity/package
  eta negative; the central suite adds eight positive assertions and the same
  negative under one new mapped area;
- the regenerated catalog has `1758` checks across `66` areas with zero legacy
  or unclassified checks;
- strict LHS audits report zero unreviewed candidates for the kernel, basic
  presheaf module, and sieve module; the kernel retains `52` annotated slots
  across `32` intentional clauses, and both one-way modules are `0`/`0`;
- the warning-enabled owner probe inherits exactly
  `1179 = 1020 + 159`, so PSSS-03a adds no warning family; and
- health passes all `46` source/example targets in `245.978s` at source
  snapshot
  `sha256:60e1b0a1b2bb2a7d2ada8b87bb333dba1aeb3bcd2cdfa3bd3d4c8f046114dbe2`;
  and
- full `make ci` passes: its fresh Lambdapi sweep checks all `46` targets in
  `169.931s`, followed by `39` Python tests, `5` document-registry tests,
  shell/source/header/reference lints, book evidence/typography/KaTeX and
  assembly checks, strict kernel audit, and fresh strict catalog verification.

### Phase PSSS-03b — Genuine ordinary-sieve classifier

Status: named research gate; no `Omega` declaration is active.

- prove `IsSetGrpd(Sieve(U))` using a selected extensionality route for
  higher-sieve functors and pointwise subterminal values;
- select a contravariant family owner whose action laws do not depend on
  reconstructing retained property packages;
- retest identity, composition, opposite normalization, subject reduction,
  and warning interactions at the owner position;
- only then bind the name `Omega` and its fibre/action observations; and
- keep `HigherSieveClassifier` available under its explicit higher name.

PSSS-03b is not automatically a prerequisite for PSSS-04. A topology may be
formulated objectwise over `Sieve(U)` and `sieve_pullback(p)` once PSSS-03a is
fully green. `Omega` is the classifier/family usability layer, not permission
to state maximality, pullback stability, and local character as indexed
properties.

### Phase PSSS-04a — Direct ordinary-sieve topology

Status: green through full integration CI and included in the authorized local
foundation checkpoint. It does not depend on PSSS-03b.

The selected direct presentation is:

```text
SieveMembership(R,(V,f)) = Obj(R(V,f))

SieveCoverage(K)
  = Pi U : Obj(K), Sieve(U) -> PropU

Covers(J,R) = carrier(J(U,R))

GrothMaximal(J)
  = Pi U, Covers(J,maximal_sieve(U))

GrothStable(J)
  = Pi (p : V -> U) (R : Sieve(U)),
      Covers(J,R) -> Covers(J,p^*R)

SieveLocalityPremise(J,R,S)
  = Pi (f : V -> U),
      SieveMembership(R,f) -> Covers(J,f^*S)

GrothLocal(J)
  = Pi (R S : Sieve(U)),
      Covers(J,R) ->
      SieveLocalityPremise(J,R,S) ->
      Covers(J,S).
```

`IsGrothTopology(J)` packages exactly these three laws, and
`GrothTopology(K)` retains the proposition-valued sieve coverage plus its law
evidence. Named projections expose the coverage, laws, maximality, pullback,
local character, and the resulting `groth_topology_covers(T,R)` classifier.
No Boolean membership test, topology-specific pullback rule, or proof erasure
is introduced.

The maximal ordinary sieve uses the constant family
`Path_cat(Unit_grpd)`, whose proposition and groupoidality evidence are
already checked. This is preferable to asserting that `Terminal_cat` and
`Path_cat(Unit_grpd)` are the same category head. Its pullback computes to the
maximal sieve on the source through the existing constant-family pullback
owner; the underlying higher sieve deliberately does not convert to
`maximal_higher_sieve`, which uses `Terminal_catd`.

The concrete consumer is the chaotic topology on arbitrary `K`, where every
sieve covers. Its three laws reduce to the unique Unit witness; the reviewer
example also instantiates it on `Terminal_cat` as a small direct combinatorial
site. This exercises formation, membership, maximality, pullback stability,
local-character wiring, named projections, and the non-collapse boundary.

The final quiet probe is
`logs/probes/psss04_topology_boundary-20260801-072029.log`; the final
warning-enabled probe is
`logs/probes/psss04_topology_boundary-20260801-072214.log` and inherits
exactly `1179 = 1020 + 159`. Promoted definitions are in the separate rule-free
`emdash3_2_sites.lp`, and reviewer diagnostics are in
`examples/grothendieck_topology.lp`.

Implementation evidence, 2026-08-01:

- the new sites module is `303` lines with `25` transparent symbol
  declarations and no rewrite or unification rule;
- the reviewer example has eleven positive assertions and the deliberate
  `Path_cat(Unit_grpd)`/`Terminal_catd` non-collapse negative; the central
  suite adds the same eleven positive assertions and negative under one new
  mapped area;
- bounded `make check` and the complete `make examples` suite pass, including
  the promoted source and reviewer;
- the regenerated catalog has `1770` checks across `67` areas with zero
  legacy or unclassified checks;
- strict LHS audits report zero unreviewed candidates for the kernel,
  presheaf, sieve, and sites modules; the kernel retains `52` annotated slots
  across `32` intentional clauses, while all three one-way modules are
  `0`/`0`;
- the final warning-enabled owner probe inherits exactly
  `1179 = 1020 + 159`, so the rule-free PSSS-04a module adds no warning
  family; and
- health passes all `48` source/example targets in `197.788s` at source
  snapshot
  `sha256:9681de378d85eaca33fe79d6ebf13682e3c26f0488a54cc9bc49b1c1281c09c9`;
  and
- full `make ci` passes: its fresh Lambdapi sweep checks all `48` targets in
  `190.427s`, followed by `39` Python tests, `5` document-registry tests,
  shell/source/header/reference lints, book evidence/typography/KaTeX and
  assembly checks, strict kernel audit, and fresh strict catalog verification.

A local checkpoint still requires separate user authorization.

### Phase PSSS-04b — Cover-family presentations and generated topology

Status: proposed after a nontrivial combinatorial or algebraic cover-family
consumer is selected.

- design an end-user cover-family package with index shape, domains, arrows,
  and selected base-change data;
- compare a supplied family coverage with the direct sieve predicate;
- test one nontrivial finite/combinatorial coverage before Zariski generation;
- permit concrete inputs to supply their saturation/topology witnesses; and
- do not implement a generic free saturation, quotient, or higher-inductive
  closure without the postponed higher-inductive-category infrastructure and
  a genuine consumer.

### Phase PSSS-05a — Canonical ordinary-sieve descent boundary

Status: canonical anchoring and an assumption-explicit nonempty API consumer
are green in the bounded research probe. Source promotion remains deferred
until a nonempty semantic consumer derives, rather than postulates, the
weighted comparison and its canonical agreement. PSSS-04b is not required
because the input is already a covering ordinary sieve.

The selected restriction-oriented descent shape is:

```text
Elements(R) = Sigma_cat(sieve_higher(R))

domain_R : Elements(R) -> K^op
  = Sigma_proj1(yoneda(U)) o Sigma_proj1(sieve_higher(R))

DescentDiagram(P,R) : Elements(R) -> Cat
  = P o domain_R

DescentWeight(R) = Terminal_prof(1,Elements(R))
DescentCandidate(P,U) = Obj_func(P[U]) : 1 -> Cat

SieveDescent(P,R)
  = IsWeightedLimit_cov_comp(
      DescentDiagram(P,R),
      DescentWeight(R),
      DescentCandidate(P,U)).
```

This uses only the existing Sigma-total, presheaf-action, profunctor, and
weighted-limit owners. A selected comparison still supplies generic `glue`
and `restrict` through `weighted_limit_cov_push/pull`; both cancellation
directions reduce without a sheaf-specific rewrite rule. The new point is
that the selected comparison is no longer accepted by itself.

#### Canonical cone at the profunctor boundary

The earlier section-first route correctly computes components but exposes the
wrong family presentation for the weighted-limit API. The selected replacement
constructs the canonical restriction cone directly in the profunctor language
that `IsWeightedLimit_cov_comp` consumes:

```text
CanonicalRestrictionCell(P,R)
  : Terminal_prof(1,Elements(R))
      ==> Hom_prof_along(DescentCandidate(P,U),DescentDiagram(P,R))

CanonicalRestrictionCell(P,R)(*,(V,f,r))
  = Obj_func(P[f])
  : Obj(Hom_Cat(P[U],P[V])).
```

In the checked term this is an object of the corresponding
`Prof_transf_cat`. Naturality is therefore part of the ambient profunctor-cell
shape rather than a separately quantified family of equations. Its one
probe-local component rule selects the already-owned presheaf arrow action
`fapp1_fapp0(P,f)`; it does not duplicate functor identity or composition.

The canonical matching map is then assembled only from generic equipment
owners:

1. compose the cell after `Prof_coyoneda_con_map`, obtaining a map from
   `Unit_1 tensor DescentWeight(R)` to the hom-along profunctor;
2. curry that map with `Prof_lambda_cov_map`, obtaining
   `CanonicalSieveMatchingMap(P,R) : Unit_1 -> Matching(P,R)`; and
3. independently evaluate the selected weighted comparison's restriction
   operation on the identity-shaped element
   `Prof_func_hom(DescentCandidate(P,U))`, obtaining
   `SelectedSieveMatchingMap(d) : Unit_1 -> Matching(P,R)`.

The anchoring condition is the equality

```text
SieveDescentAgreement(d)
  = (SelectedSieveMatchingMap(d) = CanonicalSieveMatchingMap(P,R))
```

in the relevant `ProfMap` carrier. The proposed computational sheaf datum is
therefore not bare representability but the evidence-retaining package

```text
AnchoredSieveDescent(P,R)
  = Sigma(d : IsWeightedLimit_cov_comp(...),
          SieveDescentAgreement(d)).
```

The probe supplies an explicit constructor and both projections. Its
`SheafDescentStructure(T,P)` now returns this anchored package for every
covering ordinary sieve. Thus consumers retain both the chosen inverse
operations and the fact that the chosen restriction of the identity is the
actual presheaf restriction cone.

Equality of the entire selected inverse `ProfMap` with a separately assembled
inverse was considered and rejected at the current boundary. Constructing
that full inverse from a cone requires a natural composition map

```text
Hom_prof(L) tensor Hom_prof_along(L,F) -> Hom_prof(F).
```

The active `Prof_tensor_hom_hom` composes shaped elements, but no owner
internalizes this whole natural map. Adding one merely for sheaves would
silently implement another fragment of the deliberately deferred
coend/Yoneda semantics. Agreement on `Prof_func_hom(L)` is the narrow
available Yoneda-shaped observation: it is mathematically determining for a
map out of the representable and is exactly what the checked co-Yoneda and
currying owners can express today.

#### Diagnostic section and transformation routes

The older pointwise route remains useful negative and localization evidence:

- `fapp1_at_transf`, `sigma_functord_sec`, and section pullback assemble a
  section whose literal `(V,f,r)` component reduces to `P[f]`;
- that diagnostic section still needs a probe-local represented-hom
  proof-time bridge, which is not approved for promotion;
- its pulled Catd family does not convert to the literal
  `Functor_catd(const(P[U]),DescentDiagram(P,R))` presentation;
- a second derivation starts with the tautological slice transformation
  `(V,f) |-> f`, precomposes it along the sieve projection, and postcomposes
  it by `P`; this also reaches `P[f]`, but its stable endpoints retain
  `hom_postcomp(hom_precomp(...))` rather than the literal endpoint pair; and
- consequently no broad Sigma eta, represented-hom eta, endpoint eta, or
  mixed-family unification rule is justified.

The ineffective normal-form unification experiment, abstract
`expected_sec`, and disconnected displayed-Eval pipeline have been removed
from the probe. The direct `Functord` reinterpretation remains commented out
with the exact endpoint mismatch. These failed routes are recorded here so a
later continuation does not recreate them as if they were unfinished proof
terms.

#### Nonempty consumer and its exact evidential strength

The probe now instantiates:

```text
K = Terminal_cat
T = chaotic_groth_topology(Terminal_cat)
P = Const_catd(Op(Terminal_cat),Terminal_cat)
R = maximal_sieve(Terminal_obj).
```

This consumer is operationally nonvacuous. It constructs the literal maximal
sieve element `((Terminal_obj,id),tt)`, consumes the actual chaotic-topology
cover witness, packages anchored descent, projects both retained fields, and
checks that the canonical cell at that element reduces to
`Obj_func(id_func(Terminal_cat))`.

It is intentionally assumption-explicit. `ProbeTerminalMaximal_comparison`
and `ProbeTerminalMaximal_agreement` are named constants because
`Prof_imply_cov` is opaque and the active library has no theorem asserting
that the terminal Cat-valued diagram has the required terminal-weighted
comparison. This is a useful nonempty API/usability consumer: it verifies all
indices, coverhood, packaging, projection, and canonical computation. It is
not a derived model of the sheaf condition and therefore does not, by itself,
authorize source promotion.

The ignored research probe is
`tmp/probes/psss05_sieve_descent_boundary.lp`. Its current final quiet log is
`logs/probes/psss05_sieve_descent_boundary-20260801-085224.log`; the final
warning-enabled log is
`logs/probes/psss05_sieve_descent_boundary-20260801-085308.log`. The latter
inherits exactly `1179 = 1020 unjoinable critical pairs + 159 replaceable
pattern variables`. The strict inferred-slot audit reports
`0 reconstructible / 0 unreviewed / 0 annotated` clauses. In addition to the
anchoring and terminal consumer above, the probe confirms:

- the two projection functors send a literal nested sieve element `(V,f,r)`
  to `V`, and the diagram value computes to `P[V]`;
- an arbitrary already-packed slice object does not eta-reduce through
  `Sigma_proj1_func`, so no broad Sigma/package eta rule should be added;
- glue/restrict cancellation is inherited in both directions from the generic
  comparison owners;
- an object package and `Sheaf_cat(T)` facade with ordinary presheaf natural
  maps typecheck with only the intended head projections; and
- discrete and genuinely Cat-valued fibres form packages on the empty
  path-category site, but those remain vacuous formation examples.

#### Remaining semantic promotion gate

The canonical-boundary design question is now resolved: the comparison must
be paired with agreement at the identity, and the canonical map can be built
without coercing the Catd section into a literal `Functor_catd`. The remaining
gate is narrower and mathematical. Before promotion, derive one actual
nonempty inhabitant of `AnchoredSieveDescent` from existing or separately
justified owners. The smallest candidate is a terminal-weighted-limit theorem
for a terminal Cat-valued diagram, followed by a proof that its selected pull
is the canonical map above. A different real discrete or Cat-valued sheaf may
serve instead if it derives both fields. Merely postulating a
`ProfComparison`, using an unrelated isomorphism to the same representing
object, or repeating the empty-site elimination does not close this gate.

##### 2026-08-01 rigid-adapter experiment and rejection

A follow-up terminal-presheaf experiment tested whether the missing agreement
could be exposed computationally without first proving the terminal
weighted-limit theorem. It introduced two rigid matching-map observations, a
proof-time comparison between them, and then a root rewrite of the form

```text
weighted_sieve_matching_map(d)
  -> weighted_limit_cov_pull(d,Prof_func_hom(candidate)).
```

A second terminal-specific rigid head reduced to the independently assembled
canonical cone. Explicit equality composition then connected the literal
generic pull to that cone. Focused quiet and warning-enabled probes were green,
the warning inventory remained exactly inherited, and strict LHS audits found
no candidates. Those engineering results do **not** make the design a sound
public boundary.

The re-audit rejects this adapter for promotion:

- `weighted_sieve_matching_map` has no semantics independent of the generic
  pull, so it is a transparent alias in mathematical intent; making it rigid
  only to capture a pre-rewrite unification proof violates the source
  convention that aliases remain definitions and runtime rules expose genuine
  owner computation;
- the result depends on declaration order: reflexivity is captured while two
  heads are rigid and one of those heads is made reducible only afterward;
- the terminal-specific beta encodes precisely the missing agreement theorem
  rather than deriving it from terminality or from the selected comparison;
  and
- moving the rule to the normalized `weighted_limit_cov_pull` body exposes a
  long, brittle `hom_postcomp`/reindexing normal form, while refactoring the
  generic weighted-limit owner would be a much larger kernel normal-form
  migration with no independent consumer justification.

The active kernel does provide the canonical displayed map
`Terminal_funcd(P) : ProfMap(P,Terminal_prof)`, but it has no
functor/displayed-functor extensionality or terminal-map uniqueness owner from
which equality with an arbitrary map can be constructed. The focused ignored
probe
`tmp/probes/psss05a_terminal_map_uniqueness_boundary.lp` checks both the
canonical map's type and the open normal-form non-collapse. Its quiet log is
`logs/probes/psss05a_terminal_map_uniqueness_boundary-20260801-144541.log`.
This is only a judgmental-normal-form result, not a claim that the mathematical
mapping space is noncontractible; it locates the missing theorem boundary.

Accordingly, the attempted maintained `emdash3_2_sheaf_descent.lp`, its
reviewer, its central diagnostics, and its check-registry entries were removed
before checkpointing. The earlier ignored probes remain recovery evidence.
The useful computational content is still validated there: literal canonical
cone components reduce to the presheaf arrow action, and generalized
glue/restrict cancellation reduces through the existing weighted-comparison
push/pull owners. PSSS-05a remains unpromoted until those computations can be
paired with a genuinely derived or independently justified terminal-map/
weighted-limit theorem, without a rigid alias masquerading as an owner.

The concurrent `goal/typescript-elaborator-v3.2` worktree was inspected
read-only because its completed direct `^n/^f/^f` slice is adjacent to this
bridge. Its committed kernel delta projects covariant target-family action
through `Functor_catd_fapp0_func`; that is useful host-elaboration evidence but
does not by itself identify the two Lambdapi family presentations above. No
source or uncommitted work was copied from that worktree.

### Phase PSSS-05b — Sheaf objects and natural-map category

Status: proposed after PSSS-05a closes the canonical-restriction gate and
validates one nonvacuous discrete or Cat-valued site.

- promote the selected descent diagram and its anchored comparison;
- distinguish chosen computational descent structure from a proposition-only
  `IsSheaf` view unless uniqueness is actually proved;
- package `Sheaf_cat(T)` with presheaf natural maps while retaining the chosen
  object evidence;
- keep the forgetful functor and its higher action separately consumer-gated;
  and
- do not assume a sheafification reflector or generated coverage saturation.

### Phase PSSS-06a — Set-carrier commutative-ring objects

Status: green through full integration CI and included in the authorized local
foundation checkpoint.

The selected first algebra tranche is deliberately smaller than
`CommRing_cat`:

```text
CommRingOps(A)
  = (zero, one, add, neg, mul)

IsCommRing(A,ops)
  = AddAssoc x AddComm x AddZero x AddInv
      x MulAssoc x MulComm x MulOne x LeftDistrib

CommRingStructure(A)
  = Sigma(ops : CommRingOps(A), IsCommRing(A,ops))

CommRing
  = Sigma(A : SetU_grpd,
          CommRingStructure(trunc_grpd_carrier(A))).
```

The eight laws are sufficient: commutativity derives the omitted left
additive unit/inverse, right multiplicative unit, and right distributivity.
The zero ring is permitted, as required by standard algebraic geometry. The
carrier is a packaged set, not the historical unstructured `Type`; sethood is
therefore retained and available to later morphism-equality proofs.

The ignored probe `tmp/probes/psss06_comm_ring_boundary.lp` checks transparent
constructors/projections and a concrete one-element zero ring. Its sethood is
derived from `unit_is_contr`/`unit_is_prop` in the independent Nat arithmetic
module. Open Unit variables do not eta-reduce to `tt`; the additive-zero and
multiplicative-one witnesses correctly use the contraction path instead of
false reflexivity. The final quiet log is
`logs/probes/psss06_comm_ring_boundary-20260801-091344.log`; the
warning-enabled log
`logs/probes/psss06_comm_ring_boundary-20260801-090951.log` remains exactly at
the inherited `1179 = 1020 + 159`, and strict LHS audit reports zero clauses
because the tranche adds no rule.

The promoted candidate source is
`../emdash3_2_commutative_algebra.lp` (453 lines, 48 declarations). It imports
only the independent Nat arithmetic extension, adds no rewrite or unification
rule, and exposes operation/law constructors, carrier/structure projections,
all eight readable law projections, element-level operations, and
`zero_comm_ring`. The 77-line reviewer
`../examples/commutative_ring_objects.lp` checks formation, retained carrier
sethood, operation and law projections, the zero-ring equations, open Unit
laws, and a negative package-eta boundary. Central diagnostics exercise the
same public observations. Individual source, central-check, and reviewer logs
are respectively
`logs/probes/emdash3_2_commutative_algebra-20260801-091549.log`,
`logs/probes/emdash3_2_checks-20260801-091646.log`, and
`logs/probes/commutative_ring_objects-20260801-091722.log`; the maintained
focused aggregate and complete reviewer suite are green. The final
warning-enabled owner log is
`logs/probes/emdash3_2_commutative_algebra-20260801-092403.log`; it inherits
exactly `1179 = 1020 + 159`, while strict module audit reports
`0` reconstructible slots across `0` clauses. The regenerated catalog has
`1785 = 1595 + 190` classified checks across `68` areas with zero legacy or
unclassified entries. Health passes all `50` source/example targets in
`289.311s` at source snapshot
`sha256:32360746ed53dcfb3c2d82bdd1db811151449897b68092217e242a40b2b7217f`.
The current authorities, Foundations, canonical notation, report index, and
formal-presentation module map now record the same boundary. Full `make ci`
passes a fresh `50`-target Lambdapi sweep in `255.698s`, followed by `39`
Python tests, `5` document-registry tests, shell/source/header/reference
lints, book evidence/typography/KaTeX/assembly checks, strict kernel audit,
and fresh strict catalog verification.

PSSS-06a does not introduce ring morphisms, a category facade, a carrier
functor, exponentiation, finite sums, localization, or polynomials. It first
measures the object package and its evidence normal forms.

### Phase PSSS-06b — Ring morphisms and `CommRing_cat`

Status: promoted candidate source, reviewer, maintained aggregates,
warning/audit, catalog, health, synchronized authorities, and full integration
CI green atop the PSSS-06a candidate; included in the authorized local
foundation checkpoint.

The selected first-order morphism classifier is:

```text
CommRingHomLaws(R,S,f)
  = PreservesZero(f)
      x PreservesOne(f)
      x PreservesAdd(f)
      x PreservesNeg(f)
      x PreservesMul(f)

CommRingHom(R,S)
  = Sigma(f : |R| -> |S|, CommRingHomLaws(R,S,f)).
```

Negation preservation is retained as an explicit field in this tranche.
Although it is mathematically derivable from the additive-group fragment,
performing that derivation would first require a cancellation theorem library
and would make the first localization/polynomial consumers harder to
construct. The same pragmatic argument applies to the retained zero field.
The package will expose named projections for all five witnesses rather than
requiring consumers to traverse the nested Sigma representation.

Each preservation classifier is proposition-valued because every equation
lives in the set-valued target carrier. Repeated `is_prop_pi` and
`is_trunc_sigma` therefore prove `CommRingHomLaws(R,S,f)` proposition-valued;
`is_trunc_pi` proves the carrier function space set-valued; and one final
`is_trunc_sigma` proves `CommRingHom(R,S)` set-valued. This is the concrete
PSSS-06b consumer which justifies the law-property work deliberately omitted
from PSSS-06a.

The ordinary category boundary is intentionally small:

```text
Obj(CommRing_cat)          -> CommRing
Hom_cat(CommRing_cat,R,S)  -> Path_cat(CommRingHom(R,S)).
```

The two rules must be installed as sequential declarations. An earlier
single `rule ... with ...` experiment attempted to type the hom clause before
the object clause was available and produced misleading endpoint errors. With
the declarations split, the transparent `CommRing` classifier is accepted
directly; no duplicate rigid `CommRingObject_grpd` facade is necessary.
Sethood of `CommRingHom` then gives the checked
`IsNCat(cat_succ cat_zero, CommRing_cat)` witness.

Whole identity and composition arrows remain the generic `id` and
`comp_fapp0` owners. The readable `comm_ring_hom_id` and
`comm_ring_hom_comp` names are transparent aliases only; PSSS-06b does not
rebuild their entire Sigma packages. Such reconstruction would compete with
the generic category unit rules because an arbitrary retained proof field has
no judgmental package eta. The transparent `comm_ring_hom_function`
projection remains the genuine first Sigma projection and computes for
explicit `comm_ring_hom_intro` constructors, including the concrete checked
zero-ring endomorphism. It deliberately does not claim that projecting an
opaque generic category identity or composite computes pointwise.

This boundary is measured rather than merely stylistic. Rules headed by the
broad outer eliminator `sigma_Fst` around `id`/`comp_fapp0` made the full probe
exceed the 60-second bound
(`logs/probes/psss06b_comm_ring_morphisms-20260801-095100.log`), while deleting
those two clauses left the complete morphism/sethood/category package green in
about eight seconds
(`logs/probes/psss06b_comm_ring_morphisms-20260801-095340.log`). A proposed
transparent named `comm_ring_hom_apply` wrapper could not own specialized
rules at all: Lambdapi correctly rejects rewrite clauses on a symbol already
defined with `≔`
(`logs/probes/psss06b_comm_ring_morphisms-20260801-095720.log`). The final
minimal probe, with direct `CommRing` objects and no projection/cut
interception, passes in 3.1 seconds
(`logs/probes/psss06b_comm_ring_morphisms-20260801-095942.log`). Its
warning-enabled run inherits exactly `1179 = 1020 + 159` warnings
(`logs/probes/psss06b_comm_ring_morphisms-20260801-100002.log`), and strict LHS
audit reports zero reconstructible slots across its two rule clauses.

The completed public-surface probe adds the five named law projections, a
transparent non-owning `comm_ring_hom_apply` alias, constructor computations,
and the negative generic-identity observation; it passes at
`logs/probes/psss06b_comm_ring_morphisms-20260801-100522.log`. The promoted
candidate source is `../emdash3_2_commutative_algebra_category.lp` (394 lines,
29 declarations, two rules, no unification rule), and the focused owner check
passes at
`logs/probes/emdash3_2_commutative_algebra_category-20260801-100647.log`.
The 134-line reviewer `../examples/commutative_ring_morphisms.lp` defines a
concrete zero-ring endomorphism through the public constructors and contains
18 checks covering formation, property/sethood, category projections,
`OneCat`, all five preservation observations, generic whole-arrow units, and
the two negative non-eta/non-pointwise-identity boundaries; its focused log is
`logs/probes/commutative_ring_morphisms-20260801-100748.log`. Eleven central
diagnostics pass at
`logs/probes/emdash3_2_checks-20260801-100853.log`; maintained `make check` and
the complete `make examples` suite are green.

The final warning-enabled owner log
`logs/probes/emdash3_2_commutative_algebra_category-20260801-100906.log`
inherits exactly `1179 = 1020 + 159`. Module and full strict LHS audits report
zero unreviewed candidates; the inherited full-kernel annotation inventory
remains 52 slots across 32 clauses. The regenerated catalog has
`1796 = 1604 + 192` checks across 69 areas with zero legacy or unclassified
entries. Health passes all 52 source/example targets in 281.632 seconds at
source snapshot
`sha256:81a135d9add2e80359523e36507998daf854b65cdae37c29dfa2a9728c548bec`.
Full `make ci` passes all 52 Lambdapi targets in 241.466 seconds, followed by
39 Python tests, 5 document-registry tests, shell/source/header/reference
lints, book evidence/typography/KaTeX/assembly checks, strict kernel audit,
and fresh strict catalog verification.

A full carrier functor is not part of this first promotion. `Grpd_cat` keeps
whole identity/composition functions at a proof-time comparison boundary and
computes only at stable point owners. A direct ring-carrier `fapp1` fold would
therefore introduce a competing presentation precisely at the generic
functoriality rules. Revisit a carrier functor only with the first ring-valued
presheaf consumer and a selected stable action owner; do not make PSSS-06b
depend on it.

### Phase PSSS-07 — Localization and polynomial consumers

Status: `PSSS-07a` through `PSSS-07c` are green through full integration CI
and included in the authorized local foundation checkpoint; `PSSS-07d` is
promoted through maintained aggregates, synchronized authorities, strict
catalog, 61-target health, and full integration CI and is included in the same
checkpoint. Later PSSS-07 subtranches remain separately consumer-gated.

#### PSSS-07a — One-element localization by universal property

The selected boundary does not expose fractions, numerator/exponent syntax,
or a quotient implementation. It first defines explicit invertibility
evidence

```text
CommRingUnitEvidence(R,x)
  = Sigma inverse : |R|, x * inverse = 1
```

and proves that this classifier is proposition-valued. For two witnesses with
inverses `y` and `z`, the proof uses the ordinary commutative-monoid chain

```text
y = y*1 = y*(x*z) = (y*x)*z = (x*y)*z = 1*z = z.
```

Carrier sethood then makes the inverse path contractible; the multiplication
law fibre is an equality in the same set-valued carrier, so its dependent
`PathOver` is contractible as well. This gives a checked
`comm_ring_unit_evidence_is_prop(R,x)` theorem rather than merely promising
that later semantic invertibility sieves will be proposition-valued.

For a proposed structure map `iota : R -> L` and target map `h : R -> S`, a
factor is

```text
CommRingLocalizationFactor(iota,h)
  = Sigma k : L -> S,
      Pi x : |R|, k(iota(x)) = h(x).
```

The triangle is deliberately pointwise. PSSS-06b established that projecting
an opaque generic `CommRing_cat` identity or composite does not compute on
carrier elements, and broad `sigma_Fst`/category-cut bridges time out. A
pointwise triangle states exactly the universal-property observation needed
by consumers without reopening that rejected normal-form boundary.

The property and chosen package are:

```text
IsCommRingLocalizationAt(R,f,L,iota)
  = UnitEvidence_L(iota(f))
      x Pi S : CommRing,
        Pi h : CommRingHom(R,S),
          UnitEvidence_S(h(f)) ->
            IsContr(LocalizationFactor(iota,h))

CommRingLocalizationAt(R,f)
  = Sigma L : CommRing,
      Sigma iota : CommRingHom(R,L),
        IsCommRingLocalizationAt(R,f,L,iota).
```

The promoted module supplies named constructors and projections for the unit,
factor, property, target, structure map, and universal data. It also proves
factor-agreement proposition-valued and supplies the dependent-transport
lemma used to assemble paths between factor packages. No rewrite or
unification rule is added, and opaque localization packages deliberately do
not eta-reduce to their named observations.

The first real localization consumer also justifies
`CommRingHomPointwisePath` and `comm_ring_hom_ext` in the upstream ring-map
module. Pointwise equality gives a path between carrier functions through
`PiFunext`; proposition-valued morphism-law fibres give the dependent Sigma
path. This is theorem-level package extensionality, not a runtime package-eta
rule.

The semantic gate is genuinely nonempty. The reviewer constructs the unique
explicit endomorphism of `zero_comm_ring`, proves its unique element maps to a
unit, and shows that localizing at that element yields the zero ring itself.
For every target ring and every structured map `h` out of the zero ring, the
chosen factor is `h`. Unit contractibility supplies its triangle. A competing
factor's triangle plus the Unit contraction gives pointwise equality with
`h`; ring-map extensionality gives equality of structured maps; and the
property-valued triangle fibre completes the Sigma path. Hence the complete
factorization space is contractible.

The initial all-in-one research probe is green at
`logs/probes/psss07a_localization_universal_property-20260801-104328.log`, and
its warning-enabled run at
`logs/probes/psss07a_localization_universal_property-20260801-104441.log`
inherits exactly `1179 = 1020 + 159` warnings. The separate unit-property
derivation is green at
`logs/probes/psss07a_unit_evidence_property-20260801-105634.log`. The promoted
candidate is `../emdash3_2_commutative_algebra_localization.lp` (626 lines,
31 declarations, no rules or unification rules), with focused warning-enabled
source log
`logs/probes/emdash3_2_commutative_algebra_localization-20260801-105911.log`;
it inherits the same warning inventory and its strict module audit reports
zero candidates across zero clauses. The 324-line reviewer
`../examples/commutative_ring_localization.lp` contains 15 checks and is green
at `logs/probes/commutative_ring_localization-20260801-105911.log`; central
diagnostics are green at
`logs/probes/emdash3_2_checks-20260801-105911.log`.

Maintained `make check` and the complete reviewer suite are green. Twelve new
central diagnostics raise the generated catalog to
`1808 = 1615 + 193` checks across 70 areas with zero legacy or unclassified
entries. Health passes all 54 source/example targets in 260.697 seconds at
source snapshot
`sha256:7344886d649c97bd34312ee60a11632a9502149c860d6093d4a855a9471ed880`.
The module map, Foundations, canonical notation, current-status/SOP, report
index, README, repository guidance, and formal-presentation appendix now state
the same boundary. Full `make ci` passes all 54 Lambdapi targets in 245.809
seconds, followed by 39 Python tests, 5 document-registry tests,
shell/source/header/reference lints, book evidence/typography/KaTeX/assembly
checks, strict kernel audit, and fresh strict catalog verification.

The historical Cartier source remains useful negative evidence here. Its
explicit numerators, natural-number exponents, eliminator, and fraction
computation select one concrete localization implementation. PSSS-07a instead
owns the representation-independent universal property. A future concrete
fraction implementation may prove that it inhabits this interface, but may
not redefine the interface around its syntax.

#### PSSS-07b — Iterated-localization comparison

Status: promoted candidate source, reviewer, central diagnostics, focused
warning/audit, maintained `make check`, complete reviewer suite, catalog,
health, synchronized authority texts, and full integration CI green; included
in the authorized local foundation checkpoint.

The first concrete overlap consumer is the comparison between a chosen
localization at `f*g` and the two-stage construction which first localizes at
`f` and then localizes at the image of `g`. This exposed a real boundary left
open by PSSS-06b. To form the two-stage structure map and state its pointwise
triangle, consumers need carrier application of structured-map composition;
the generic `CommRing_cat` composite intentionally does not expose that
projection as a runtime reduction.

The selected repair is narrow. The ring-map module now contains the rigid
stable comparison target

```text
comm_ring_hom_comp_pointwise(g,f) : CommRingHom(R,T)
```

whose first Sigma projection computes to `x |-> g(f(x))`. One proof-time
unification rule compares it with generic `comp_fapp0(CommRing_cat,g,f)`, and
`comm_ring_hom_comp_pointwise_path` exposes that comparison as a named path.
Generic category composition remains the whole-arrow runtime owner. In
particular, application of the generic composite still does not reduce
pointwise. The only new rewrite is the constructor-specific
`sigma_Fst(comm_ring_hom_comp_pointwise(...))` beta; no broad
`sigma_Fst(comp_fapp0(...))` interception is restored.

The research probe also tested an analogous stable identity head. That wider
pair was green and warning-neutral, but PSSS-07b does not need identity to
construct comparison data, so identity was not promoted. Likewise, a carrier
functor remains consumer-gated: this tranche selects a single structured-map
composition observation, not a functor-action normal form over arbitrary ring
maps.

The rule-free downstream module
`../emdash3_2_commutative_algebra_localization_comparison.lp` first derives
the unit algebra required by the comparison:

- unit evidence transports in both directions along element paths;
- structured ring maps preserve explicit unit evidence;
- products of units are units; and
- if `x*y` is a unit, then both `x` and `y` are units.

It then packages a chosen two-stage localization as

```text
CommRingIteratedLocalizationAt(R,f,g)
  = Sigma Lf : CommRingLocalizationAt(R,f),
      CommRingLocalizationAt(
        target(Lf),
        map(Lf)(g)).
```

Named observations expose the first stage, intermediate ring, first map,
second stage, final target, second map, and stable composite structure map.
The image of `f` stays a unit under the second-stage map, the second stage
directly inverts the image of `g`, their product is a unit, and the structured
map multiplication law transports this evidence to the image of `f*g`.

For a chosen `product_localization : CommRingLocalizationAt(R,f*g)`, the
forward map is the centre of its contractible factorization space applied to
the two-stage structure map. The reverse map is constructed in two universal-
property stages:

1. the unit evidence for the image of `f*g` is transported across the
   product-preservation law and split into unit evidence for the images of
   `f` and `g`;
2. the product-localization map factors through localization at `f`;
3. the first factor triangle transports unit evidence for the image of `g`
   to the intermediate factor map; and
4. that intermediate map factors through the second localization.

The two staged triangles compose pointwise over `R`. The public
`CommRingIteratedLocalizationComparison` package therefore retains a forward
factor and a reverse factor, with named forward/reverse maps and agreement
projections. This is selected comparison data, not a global equality of
chosen localization packages. It also deliberately does not yet claim that
the two maps are inverse. Such inverse laws can be derived later by nested
factor uniqueness if a basic-open equivalence consumer needs them; promoting
them now would additionally justify a stable identity comparison and more
pointwise composition bookkeeping without changing the first overlap data.

The owner-position research probe is green at
`logs/probes/psss07b_comm_ring_action_owner-20260801-114219.log`; the complete
comparison probe is green at
`logs/probes/psss07b_explicit_ring_map_composition-20260801-114219.log`, and
its warning-enabled run at
`logs/probes/psss07b_explicit_ring_map_composition-20260801-114247.log`
inherits exactly `1179 = 1020 + 159` warnings. The promoted category owner is
543 lines with 34 symbols, three rules, and one unification rule. The promoted
comparison module is 1,201 lines with 38 symbols and no rule or unification
rule; focused green logs are
`logs/probes/emdash3_2_commutative_algebra_localization_comparison-20260801-114638.log`
and the warning-enabled
`logs/probes/emdash3_2_commutative_algebra_localization_comparison-20260801-114944.log`.
The warning inventory remains exactly inherited, and strict module audits
report zero unreviewed candidates.

The 197-line reviewer
`../examples/commutative_ring_localization_comparison.lp` contains 16
positive checks and one negative generic-composite application check; it is
green at
`logs/probes/commutative_ring_localization_comparison-20260801-114934.log`.
Eleven positive and one negative central diagnostics are green at
`logs/probes/emdash3_2_checks-20260801-114934.log`. Maintained `make check` and
the complete reviewer suite are green. PSSS-07a's constructive zero-ring
localization remains the nonempty model for the input classifiers; PSSS-07b's
construction is uniform over all chosen input localizations and adds no new
existence axiom.

The regenerated catalog has `1820 = 1626 + 194` checks across 71 areas with
zero legacy or unclassified entries. Health passes all 56 source/example
targets in 342.143 seconds at source snapshot
`sha256:ca42854edb4bdbfb75fb2c1efde198708a9fb5099b3e1f70627777a1518004c1`.
Repository guidance, README, Foundations, canonical notation, current
status/SOP, report index, this plan, and the formal-presentation module map
now describe the same pointwise-composition and comparison boundary.
Full `make ci` passes all 56 Lambdapi targets in 331.672 seconds, followed by
39 Python tests, 5 document-registry tests, shell/source/header/reference
lints, book evidence/typography/KaTeX/assembly checks, strict kernel audit,
and fresh strict catalog verification.

#### PSSS-07c — Finite/unimodular families and finite sums

Status: green through full integration CI and included in the authorized local
foundation checkpoint. The selected formulas and the first algebraic
Zariski-cover consumer are promoted into two candidate source modules with a
focused reviewer and central diagnostics.

The finite-family prerequisite is deliberately not a new ordinary inductive
declaration. It is the Nat-indexed right-associated record

```text
FiniteFamily(A,0)       = Unit
FiniteFamily(A,succ n)  = Sigma(x : A, FiniteFamily(A,n)).
```

`nat_elim` eliminates into the existing `Obj(Grpd_cat)` universe, so visible
zero and successor lengths compute through the existing Nat and Sigma owners.
The promoted small generic surface has `nil`, `cons`, `head`, `tail`,
`singleton`, `pair`, pointwise `map`, and a proof that finite families of
elements of a set remain set-valued. It intentionally has no `Fin`, lookup,
permutation quotient, list append, recursion/positivity interface, or generic
inductive-declaration macro. An arbitrary zero-length Unit value also need not
eta-reduce to the named `nil`; no package eta is proposed.

The initial probe used the rigid `Product_grpd(A,tail)` presentation for the
successor case. Formation and recursion were green, but the generic
`is_trunc_sigma` theorem correctly did not change its conclusion head from a
constant Sigma to `Product_grpd`; the failed check exposed a repeated direct
head comparison obligation. No product/Sigma unifier is justified by this
consumer. The probe therefore selects the literal constant-family Sigma,
which has the same decoded pair carrier and projections and lets sethood use
the existing theorem directly. This also reduced the complete probe from
about nine seconds to about three seconds.

For a commutative ring `R`, the algebra layer then defines by the same length
recursion

```text
finite_sum_R([])          = 0
finite_sum_R(x :: xs)     = x + finite_sum_R(xs)

finite_dot_R([],[])       = 0
finite_dot_R(a::as,f::fs) = a*f + finite_dot_R(as,fs).
```

The fold order is part of the selected presentation. Associativity can later
compare other parenthesizations, but PSSS-07c does not add a quotient by
permutations or a second computation owner. Two theorem-level Nat inductions
prove that a structured ring map preserves the selected finite sum and finite
dot product; no runtime rule or unification rule is needed.

The mathematically relevant cover input is retained coefficient data

```text
CommRingUnimodularPresentation(R,n,f)
  = Sigma(a : FiniteFamily(|R|,n)),
      finite_dot_R(a,f) = 1.
```

This is deliberately called a **presentation**, not a proposition. Different
coefficient choices need not be equal, and the active kernel has no selected
propositional-truncation reflector with which to express mere existence. The
package is nevertheless set-valued: coefficient families are sets and its
equation fibre is a proposition by carrier sethood. A structured map
`h : R -> S` sends both generators and coefficients pointwise; finite-dot
preservation, action on the retained equation, and `h(1)=1` construct the
mapped presentation.

The first Zariski consumer is the algebraic generating datum

```text
CommRingZariskiCoverPresentation(R)
  = Sigma(n : Nat),
      Sigma(f : FiniteFamily(|R|,n)),
        CommRingUnimodularPresentation(R,n,f).
```

It is set-valued and stable under structured base change. The generic
singleton `[1]` is a derived nonempty model, and a binary helper packages the
familiar hypothesis `a*f + b*g = 1`. This is exactly the finite unit-ideal
condition for the basic opens `D(f_i)` to cover `Spec(R)`, and it corrects the
historical source's simplified `f+g` shortcut.

The name remains presentation-level: PSSS-07c does not yet declare `Spec`,
basic-open objects, localizations indexed by every tuple entry, a sieve
coverage, or a Grothendieck topology. Those belong to PSSS-08/PSSS-09, where
this data will be interpreted as localization-generated cover maps. Likewise,
a finite cover of a relative basic open `D(s)` requires a radical witness
`s^N = sum_i a_i f_i`; powers and that relative interface remain separately
consumer-gated rather than being smuggled into the whole-affine cover datum.

The promoted implementation split is:

- `emdash3_2_finite_families.lp`, importing only Nat arithmetic, for the
  generic Nat/Sigma representation, observations, map, and sethood; and
- `emdash3_2_commutative_algebra_finite.lp`, importing the finite-family and
  structured-ring modules, for sums, dot products, map-preservation theorems,
  unimodular presentations, Zariski-cover presentations, and the singleton/
  binary consumers.

The ignored research probe is
`tmp/probes/psss07c_finite_unimodular_boundary.lp`. Its final quiet log at this
stage is
`logs/probes/psss07c_finite_unimodular_boundary-20260801-123355.log`; the
warning-enabled log
`logs/probes/psss07c_finite_unimodular_boundary-20260801-123039.log` inherits
exactly `1179 = 1020 unjoinable critical pairs + 159 replaceable pattern
variables`. The probe adds no rule or unification rule.

Promotion now consists of the 107-line, 9-symbol
`emdash3_2_finite_families.lp` and the 735-line, 21-symbol
`emdash3_2_commutative_algebra_finite.lp`; both have zero explicit rules and
zero unification rules. The 201-line reviewer has 20 positive and two negative
checks, and the central suite has the same 22 diagnostics in one mapped area.
Focused source/reviewer/central checks, maintained `make check`, the complete
example suite, warning-enabled comparison, zero-clause strict audits, and the
strict catalog of 1,842 checks across 72 areas are green. Health passes all 59
source/example targets in 202.751 seconds at source snapshot
`sha256:4127068d1fa2e3dd43f22c8ca1f607d07bb8645ba1467ee22c96425c23ee5f76`.
Full integration CI passes all 59 Lambdapi targets in 216.912 seconds,
followed by 39 Python tests, 5 document-registry tests, shell/source/header/
reference lints, book evidence/typography/KaTeX/assembly checks, strict kernel
audit, and fresh strict catalog verification. PSSS-07c is included in the
authorized local foundation checkpoint; relative radical/basic-open data and
the geometric interpretation remain downstream consumer gates.

#### PSSS-07d — Polynomial algebras by universal property

Status: promoted candidate green through full integration CI and included in
the authorized local foundation checkpoint.

The historical Cartier algebra fragment supplies useful negative evidence but
no polynomial-algebra interface. Its localization layer selects explicit
numerator/exponent syntax and even asks whether it should instead move directly
to universal algebra. PSSS-07d follows that unanswered suggestion without
copying monomial, coefficient-family, quotient, or inductive syntax.

The selected classifier is the free commutative `R`-algebra on an independent
variable classifier `X`. Candidate data consist of

```text
P         : CommRing
base_map  : CommRingHom(R,P)
variables : X -> |P|.
```

For a target base map `h : R -> S` and valuation `v : X -> |S|`, a factor is

```text
Sigma k : CommRingHom(P,S),
  (Pi r : |R|, k(base_map(r)) = h(r))
  x
  (Pi x : X, k(variables(x)) = v(x)).
```

`IsCommRingPolynomialAlgebra(R,X,P,base_map,variables)` requires this factor
classifier to be contractible for every `S`, `h`, and `v`. The chosen
`CommRingPolynomialAlgebra(R,X)` package retains the target ring, base map,
variable map, and universal property with named transparent observations.
Both agreement fields are proposition-valued because their equations live in
the set-valued target carrier; their Sigma package is therefore also a
property. A theorem-level dependent transport helper is sufficient to turn a
path between factor maps into a path between complete factor packages. No
runtime rule, unification rule, or package eta belongs to the polynomial
module.

`X` is not tied to the PSSS-07c finite-family representation. This is a
deliberate ownership separation: finite families encode retained tuples and
finite sums for cover presentations, whereas a free algebra is naturally
parameterized by its variable classifier. Valuations land in set-valued ring
carriers, so any higher path structure in `X` is respected automatically; no
new `Fin`, list, monomial, or ordinary-inductive interface is required. A
later convenience facade may specialize `X` once a genuine finite-variable
consumer selects an index presentation.

The first executable model is the generic zero-variable equation
`R[Empty] = R`. It uses `P = R`, an empty variable map, and a stable pointwise
structured identity as the base map. For every `h : R -> S`, the centre factor
is `h`; the base triangle is reflexive and the variable triangle follows by
empty elimination. A competing factor's base triangle identifies its map
pointwise with `h`; `comm_ring_hom_ext` and proposition-valued agreement
transport then prove the complete factor space contractible. This is a real
model for every base ring, but it is intentionally only the zero-variable
case. A concrete positive-variable polynomial representation remains a
separate consumer gate and may later prove that it inhabits this interface.

That model is the first consumer which justifies promoting the stable identity
head previously measured and deferred in PSSS-07b. The proposed owner is

```text
comm_ring_hom_id_pointwise(R) : CommRingHom(R,R),
```

with one constructor-specific `sigma_Fst` beta exposing `x |-> x` and one
proof-time comparison with generic `id(CommRing_cat,R)`. Generic category
identity remains the whole-arrow runtime owner, and applying the generic
identity remains a checked negative boundary. This matches the already
promoted pointwise-composition architecture rather than adding a broad
projection/cut rule or a carrier functor.

The bounded probe is
`tmp/probes/psss07d_polynomial_universal_property.lp`. Its quiet run is green
at
`logs/probes/psss07d_polynomial_universal_property-20260801-130950.log`; the
warning-enabled run at
`logs/probes/psss07d_polynomial_universal_property-20260801-131007.log`
inherits exactly `1179 = 1020 unjoinable critical pairs + 159 replaceable
pattern variables`. Strict probe audit reports zero candidates across zero
unreviewed clauses.

Promotion adds `comm_ring_hom_id_pointwise` at the structured ring-category
owner with one narrow first-projection beta and one proof-time comparison to
generic category identity. The category module is consequently 573 lines with
36 symbols, four explicit rules, and two unification rules. The separate
`emdash3_2_commutative_algebra_polynomial.lp` source is 432 lines with 24
symbols and no rewrite or unification rule; the 429-line
`examples/commutative_ring_polynomial_algebra.lp` reviewer has 16 positive and
two negative checks, and the central suite maps the same 18 diagnostics to one
area. Focused source/reviewer/central checks, maintained `make check`, the
complete example suite, exact inherited warning comparison, zero-candidate
strict audits, synchronized authority texts, and the strict catalog of 1,860
checks across 73 areas are green. Health passes all 61 source/example targets
in 314.231 seconds at source snapshot
`sha256:35a1d735feeea679e12e62b3bc14690783758c0da59ed1e8f20522f898f075df`.
Full integration CI passes all 61 Lambdapi targets in 389.345 seconds,
followed by 39 Python tests, 5 document-registry tests, shell/source/header/
reference lints, book evidence/typography/KaTeX/assembly checks, strict kernel
audit, and fresh strict catalog verification. The candidate is included in
the authorized local foundation checkpoint.

Concrete fractions, powers, monomials, quotient syntax, positive-variable
polynomial representations, and a general inductive declaration remain
outside this tranche.

### Phase PSSS-08 — Ringed sites and invertibility sieves

Status: proposed after PSSS-05b through PSSS-07.

- ring-valued presheaf/sheaf;
- semantic `InvSieve`;
- selected `D` comparison;
- localization-over-`D(f)` descent comparison.

### Phase PSSS-09 — Zariski coverage

Status: proposed after PSSS-08.

- localization-generated cover family;
- pullback stability;
- subcanonicity/representable sheaf diagnostic at the selected scope;
- polynomial-algebra examples remain consumers, not topology owners.

### Phase PSSS-10 — Slice sites and affine charts

Status: proposed after PSSS-09.

- induced slice topology and ringed pullback;
- `Spec(R)/D(f)` versus `Spec(R[1/f])` computational comparison;
- one overlap/iterated-localization example.

### Phase PSSS-11 — Scheme atlases

Status: proposed after PSSS-10.

- affine-cover record;
- selected chart comparisons and overlap coherence;
- evaluate whether an optimized coinductive slice interface has a genuine
  remaining consumer.

### Phase PSSS-12 — Functor-of-points comparison

Status: later research boundary.

- derive variance through existing hom/profunctor owners;
- formulate the qcqs/spectral comparison at the correct subcategory;
- only then assess a Zeuner-style adjoint equivalence.

## 16. Validation Contract

For each Lambdapi implementation phase:

1. inspect all worktrees and exact staged/unstaged state;
2. work in a dedicated authorized branch/worktree from a green common
   checkpoint;
3. locate owners with `rg` and write the mathematical normal form first;
4. probe in a temporary full-import file at a 60-second cap;
5. add typed `eq_refl` for every proof-time comparison and ordinary
   conversion assertions only for actual rewrites;
6. run the focused module check and warning comparison;
7. run `python3 scripts/audit_rule_lhs.py --strict` for rule changes;
8. update checks, catalog, health, Foundations/SOP/syntax, and this ledger in
   the same bounded tranche as required by the nested SOP; and
9. run full `make ci` at a promoted integration boundary before any authorized
   checkpoint.

Do not add a second unification rule because an equivalent opposite equation
looks convenient. Add a direct represented-rung comparison only after a typed
consumer demonstrates that nontransitive unification requires it.

## 17. Risks And Guards

- **Terminology drift:** ordinary sieves are subterminal; higher sieves are
  not silently called ordinary subobjects.
- **Unification trust:** `Psh_cat` comparisons remain rigid-headed and narrow;
  no broad opposite eta rule is installed.
- **Strict versus weak descent:** Cat-valued descent is not advertised as a
  complete infinity-stack implementation without a coherence audit.
- **Topology/modality conflation:** a site does not automatically provide a
  computational sheafification adjunction.
- **Algebra leakage:** polynomial syntax and finite-sum implementation do not
  become topology owners.
- **Rewrite duplication:** Yoneda, restriction, Sigma totalization, `DefIso`,
  adjunction, and profunctor laws remain with existing generic owners.
- **Historical over-porting:** old `mod`, `smod`, `ascheme`, and fraction rules
  are requirements evidence, not names to restore.
- **Macro authority inversion:** the TypeScript structure macro does not make
  generated TypeScript the active mathematical authority.
- **Concurrency:** no uncommitted file is copied from the elaborator worktree.

## 18. Decision Ledger

- **PSSS-D-001:** use a separate standard-library module; do not initially edit
  `emdash3_2.lp`.
- **PSSS-D-002:** select a rigid Cat-valued `Psh_cat(K)` facade over
  `Catd_cat(Op_cat K)` for the first tranche.
- **PSSS-D-003:** install one `Psh_cat`/`Catd_cat` unification comparison with
  endpoint recovery, not two mirror comparisons.
- **PSSS-D-004:** derive presheaf reindexing from `Pullback_catd_func(Op_func
  F)`.
- **PSSS-D-005:** derive Yoneda, arrow-into totals, slices, and the higher-sieve
  classifier from active hom/Sigma/Catd owners.
- **PSSS-D-006:** distinguish higher sieves from ordinary subterminal sieves
  and reserve `Omega` until the truncation boundary is implemented.
- **PSSS-D-007:** treat coverage, Grothendieck topology, and sheafification
  modality as distinct layers.
- **PSSS-D-008:** express glue through `DefIso`/weighted descent comparison,
  not a global ad hoc cancellation rule.
- **PSSS-D-009:** treat Zeuner's compact-open support as a valid restricted
  presentation and the sieve-valued support as a generalization with a future
  representability comparison.
- **PSSS-D-010:** build commutative algebra and localization by universal
  properties before concrete polynomial/fraction representations.
- **PSSS-D-011:** prefer a computational affine atlas using selected
  equivalences; keep the historical coinductive affine-slice interface
  consumer-gated.
- **PSSS-D-012:** postpone TypeScript transfer/code generation and parser work.
- **PSSS-D-013:** keep restriction map action at the generic functor owner.
  The measured Psh-headed point-component projection remains consumer-gated;
  do not add a facade bridge or broaden the Catd rule in PSSS-01.
- **PSSS-D-014:** promote Yoneda, restriction-oriented arrow totals,
  conventional slices, and the Cat-valued higher-sieve classifier only as
  transparent PSSS-02 names over `hom_con_int`, `Sigma_func`, `Catd_catd_con`,
  and `Terminal_catd`; add no local action rules.
- **PSSS-D-015:** compare `HigherSieve_cat(U)` and
  `Psh_cat(Slice_cat(U))` through the stable common presentation
  `Catd_cat(Into_restr_cat(U))`. Preserve their direct runtime non-collapse;
  do not add a second unifier merely because experimental unification is not
  transitive.
- **PSSS-D-016:** the PSSS-02 pointwise consumer confirms rather than relaxes
  PSSS-D-013. Yoneda components compute through the represented-hom owner and
  higher-sieve restriction through the Catd owner, so the generic
  Psh-pullback component bridge remains deferred until a different real
  consumer cannot use either canonical presentation.
- **PSSS-D-017:** select
  `IsSubterminalCat(C) := Sigma(IsPropGrpd(Obj(C)), IsGroupoidalCat(C))`.
  Object proposition evidence alone is rejected because it does not exclude
  nontrivial directed endomorphisms. The selected native groupoidality field
  derives the existing `IsDiscreteCat` contract and admits
  proposition-valued `Path_cat` as canonical examples.
- **PSSS-D-018:** define an ordinary sieve as the property subtype
  `Sigma(S : HigherSieve(U), IsOrdinarySieve(S))`, where the property is
  pointwise `IsSubterminalCat`. Retain the underlying higher-sieve functor and
  reuse its Catd pullback action; add no parallel action rule.
- **PSSS-D-019:** keep `Omega` unbound until both
  `IsSetGrpd(Sieve(U))` and an owner-aligned contravariant family assembly are
  proved. A warning-neutral primitive candidate that fails identity/package
  eta is diagnostic evidence, not a classifier implementation.
- **PSSS-D-020 (refined by PSSS-04a):** PSSS-03a deferred the maximal ordinary
  sieve rather than importing arithmetic solely for a convenience
  constructor. The concrete topology consumer now justifies constructing it
  in `emdash3_2_sites.lp` as the constant `Path_cat(Unit_grpd)` family, using
  the reusable `unit_is_prop` witness. Do not replace this with an unproved
  `Terminal_cat = Path_cat(Unit_grpd)` category-head identification.
- **PSSS-D-021:** allow coverage/topology work to proceed objectwise from
  `Sieve(U)` and `sieve_pullback` after PSSS-03a is green; do not make the
  optional `Omega` family facade a false prerequisite for indexed topology
  axioms.
- **PSSS-D-022:** represent a direct sieve coverage as an object-indexed
  function `Sieve(U) -> PropU_grpd`; decode coverhood with the existing
  truncated-universe carrier/evidence projections. This makes coverhood
  proposition-valued without requiring `Sieve(U)` itself to be a set.
- **PSSS-D-023:** select exactly maximality, pullback stability, and local
  character as `IsGrothTopology` fields. Local character quantifies objects
  `(V,f)` of `Into_restr_cat(U)`, uses the proposition-valued object classifier
  of the sieve value as membership, and reuses `sieve_pullback(f,S)`.
- **PSSS-D-024:** use the generic chaotic topology, instantiated on
  `Terminal_cat`, as the first direct combinatorial model. Its trivial proofs
  still exercise every law's typing and projection route; a nontrivial finite
  coverage remains a separate consumer gate.
- **PSSS-D-025:** keep end-user cover-family presentations and generated/free
  saturation separate from the direct topology package. Concrete future
  coverages may supply their topology witness; generic saturation remains
  postponed with quotient/higher-inductive infrastructure.
- **PSSS-D-026:** select the Sigma total of the underlying ordinary-sieve
  family as the restriction-oriented descent index. Its two canonical Sigma
  projections land in `K^op`, so composing the presheaf gives the matching
  diagram without a new variance or action rule.
- **PSSS-D-027:** express computational matching through the existing
  terminal-weight `IsWeightedLimit_cov_comp`. Expose glue/restrict as aliases
  of its generic push/pull operations; do not duplicate their cancellation
  rules in a sheaf module.
- **PSSS-D-028:** do not yet equate a selected weighted-limit comparison with
  the sheaf condition. Promotion requires agreement of its restriction map
  with the canonical presheaf-action cone. The empty-site packages prove
  formation only and do not discharge this nonvacuous semantic consumer gate.
- **PSSS-D-029:** an evidence-retaining `Sheaf_cat` may project objects to
  presheaves with chosen descent data and homs to ordinary presheaf natural
  maps, parallel to the existing `Psh_cat` facade. Keep the distinction
  between chosen computational structure and proposition-only sheafhood
  explicit, and defer a forgetful-functor action until consumed.
- **PSSS-D-030 (refined by PSSS-D-031):** retain only the component-correct
  section and its probe-local represented-hom bridge as diagnostic evidence.
  The pulled action family does not convert to the literal `Functor_catd`
  family, and the tautological-transformation route retains stable
  pre/postcomposition endpoints. Remove the ineffective normal-form unifier
  and disconnected abstract-section/Eval scaffolding; do not import the
  concurrent TypeScript tranche or add a broad family or endpoint eta rule.
- **PSSS-D-031:** define the canonical restriction boundary natively as a
  profunctor cell with component `Obj_func(P[f])`. Compose it after left
  co-Yoneda and curry with `Prof_lambda_cov_map`. Anchor a selected weighted
  comparison by equating this canonical matching map with
  `weighted_limit_cov_pull` applied to the candidate identity
  `Prof_func_hom`. A sheaf descent datum retains the Sigma pair of comparison
  and agreement; bare representability is insufficient.
- **PSSS-D-032:** distinguish a nonempty interface consumer from a derived
  semantic model. The terminal-site/maximal-sieve probe exercises a real
  cover, sieve element, canonical component, constructor, and projections,
  but its comparison and agreement are named assumptions because the opaque
  implication calculus has no terminal-diagram weighted-limit theorem. Keep
  promotion gated until one nonempty consumer derives both fields.
- **PSSS-D-033:** anchor at the candidate's identity-shaped
  `Prof_func_hom`, not by postulating equality of whole inverse profunctor
  maps. The latter requires a currently absent natural composition map from
  `Hom_prof(L) tensor Hom_prof_along(L,F)` to `Hom_prof(F)` and would reopen
  deferred coend/Yoneda semantics. Reassess only when that owner is justified
  independently of sheaves.
- **PSSS-D-034:** replace the historical `ring : Type -> TYPE` boundary with
  a `SetU_grpd` carrier package. Retain carrier sethood explicitly and allow
  the zero ring; do not assume `zero != one`.
- **PSSS-D-035:** separate ring operations from law evidence. Select zero,
  one, addition, negation, and multiplication plus the eight sufficient
  commutative-ring laws: additive associativity/commutativity/right-unit/
  right-inverse, multiplicative associativity/commutativity/right-unit, and
  left distributivity. Derived mirror laws remain theorem work rather than
  redundant stored fields unless a consumer proves the redundancy unusable.
- **PSSS-D-036:** split algebra implementation into PSSS-06a object formation
  and PSSS-06b morphisms/category/carrier action. Do not let category-law or
  morphism-extensionality questions destabilize the first carrier package.
- **PSSS-D-037:** reuse the independent Nat arithmetic module for Unit
  contraction/proposition evidence and later powers. The one-element ring's
  open unit laws use the contraction path; no open-variable Unit eta rule or
  algebra-local truncation axiom is added.
- **PSSS-D-038:** promote PSSS-06a as a separate rule-free one-way module
  whose public usability comes from transparent Sigma constructors and named
  carrier/operation/law projections. Do not hide package structure behind an
  eta rule, and do not require law-evidence proposition theorems until the
  PSSS-06b morphism/category consumer demonstrates which such theorem is
  actually needed.
- **PSSS-D-039:** represent a ring morphism as a carrier function plus five
  proposition-valued preservation fields, and derive morphism sethood from the
  target carrier's retained sethood. Let `CommRing_cat` project directly to
  `CommRing` objects and `Path_cat(CommRingHom)` homs through two sequential
  rules. Keep generic category identity/composition as whole-arrow owners;
  expose the transparent first projection only on explicit packages, reject
  broad `sigma_Fst`/cut interception, and defer the carrier functor until a
  ring-valued-presheaf consumer selects its stable action normal form.
- **PSSS-D-040:** define localization at one element by explicit unit evidence
  plus contractible pointwise factorization. Keep factor agreement on carrier
  applications so the universal property does not depend on projected
  generic-category identity/composition computation. Package chosen target,
  map, and property with named transparent observations; add no fraction
  syntax, rule, unification rule, or package eta.
- **PSSS-D-041:** let the first localization uniqueness proof justify
  theorem-level `CommRingHom` extensionality in the upstream morphism module.
  Prove unit evidence proposition-valued from inverse uniqueness and carrier
  sethood so later invertibility sieves receive a checked property classifier.
  Use the zero-ring localization as the required nonempty semantic model.
- **PSSS-D-042:** let the first iterated-localization overlap consumer select
  one rigid pointwise structured-map composition head. Give only its canonical
  first-projection beta and a proof-time comparison with generic
  `CommRing_cat` composition. Retain the generic whole-arrow runtime owner,
  preserve the negative generic-application boundary, and do not promote the
  separately probed stable identity head or a carrier functor before a
  consumer needs them.
- **PSSS-D-043:** compare localization at `f*g` with localization first at `f`
  and then at the image of `g` through universal properties alone. Derive unit
  transport, preservation, multiplication, and factor extraction; package the
  canonical forward factor and the staged reverse factor with pointwise
  triangles. Do not add fractions, a global equality of chosen localization
  packages, or inverse laws until a basic-open equivalence consumer requires
  the extra identity/composition boundary.
- **PSSS-D-044:** represent a length-`n` finite family as Nat recursion into a
  right-associated constant-family Sigma ending in Unit. Use the existing
  Nat/Sigma computation and truncation owners; do not revive the retired Sum
  former, introduce `Fin`/list/inductive infrastructure, or add a
  `Product_grpd`/Sigma comparison merely to obtain sethood.
- **PSSS-D-045:** retain explicit coefficients witnessing
  `sum_i a_i*f_i=1` as a set-valued unimodular **presentation**, not as a
  falsely proposition-valued existence claim. Let structured-map preservation
  of finite dot products own base change, and package these data as the
  algebraic input to a future Zariski coverage. Defer `Spec`, localization-
  indexed cover maps, relative radical/basic-open witnesses, and topology to
  their named downstream consumers.
- **PSSS-D-046:** define polynomial algebras as free commutative `R`-algebras
  on an independent variable classifier `X`, through contractible structured
  extensions of every base map and valuation. Keep pointwise base/variable
  agreements as proposition-valued evidence; do not select monomials,
  coefficient syntax, quotients, `Fin`, lists, or an inductive implementation.
  Keep finite-family cover presentations independently owned by PSSS-07c.
- **PSSS-D-047:** let the generic executable model `R[Empty] = R` justify the
  previously probed stable pointwise structured identity at the ring-category
  owner. Expose only its carrier-projection beta and a proof-time comparison
  with generic category identity; retain generic identity as runtime owner and
  preserve its negative pointwise-application boundary. Treat a concrete
  positive-variable model as a later implementation of the universal
  interface, not as a prerequisite for that interface.
- **PSSS-D-048:** reject the warning-neutral PSSS-05a rigid-adapter
  experiment. A name whose sole content is
  `weighted_limit_cov_pull(...)` must remain a transparent alias; it may not
  be made rigid solely to capture an order-sensitive unification proof before
  a later rewrite. The terminal-specific beta also states, rather than
  derives, the missing canonical-agreement theorem. Keep PSSS-05a at the
  research boundary until terminal-map uniqueness/contractibility or another
  genuine nonempty semantic model supplies the proof.
- **PSSS-D-049:** retain the historical Cartier objective of computational
  schemes as a phase-wide acceptance criterion. A package that only forms or
  typechecks is useful staging evidence, not by itself the intended geometric
  result. Future invertibility-sieve, Zariski, slice-chart, overlap, and scheme
  tranches must identify concrete observations that normalize through active
  owners—for example restriction of a section, membership in an invertibility
  sieve, localization comparison on carrier elements, or chart-overlap
  composition—and must keep theorem-level equalities explicit where runtime
  computation is neither owned nor justified.

## 19. Side-Task Ledger

| ID | Task | Status | Gate |
|---|---|---|---|
| PSSS-00 | Active-owner, historical-consumer, and Zeuner review plus bounded formula probe | Complete | This report |
| PSSS-01 | Rigid presheaf facade and reindexing | Green; locally checkpointed | PSSS-02 consumer gate closed |
| PSSS-02 | Yoneda, slice, higher-sieve classifier, maximal sieve | Green; locally checkpointed | PSSS-03a consumer gate closed |
| PSSS-03a | Native subterminal categories, ordinary-sieve package, and pullback | Green; locally checkpointed | PSSS-03b and PSSS-04a remain separately gated |
| PSSS-03b | Set-valued `Omega` family facade | Research gate | Sieve setness plus owner-aligned family assembly |
| PSSS-04a | Direct ordinary-sieve Grothendieck topology and chaotic model | Green; locally checkpointed | PSSS-05a consumer gate |
| PSSS-04b | Cover-family presentations and generated topology | Proposed | Nontrivial finite/combinatorial or algebraic coverage consumer; higher-inductive gate for generic saturation |
| PSSS-05a | Canonical sieve-descent diagram and anchored restriction agreement | Research probes green; rigid-adapter promotion trial rejected and removed | Terminal-map uniqueness/contractibility or another derived nonempty semantic consumer, then source/SOP gate |
| PSSS-05b | Sheaf object package and natural-map category | Proposed | PSSS-05a semantic and SOP gate |
| PSSS-06a | Set-carrier commutative-ring operations, laws, package, and zero-ring model | Green through full integration CI; locally checkpointed | PSSS-06b consumer gate closed |
| PSSS-06b | Ring morphisms, `CommRing_cat`, and transparent explicit-map carrier observation | Green through full integration CI; locally checkpointed | Carrier functor separately consumer-gated |
| PSSS-07a | One-element localization universal property and zero-ring model | Green through full integration CI; locally checkpointed | Later PSSS-07 consumers remain gated |
| PSSS-07b | Iterated-localization comparison | Green through full integration CI; locally checkpointed | Inverse laws remain consumer-gated |
| PSSS-07c | Finite/unimodular families and finite sums | Green through full integration CI; locally checkpointed | Relative radical/basic-open and geometric consumers remain gated |
| PSSS-07d | Polynomial algebra universal property | Green through full integration CI; locally checkpointed | Positive-variable representation remains consumer-gated |
| PSSS-08 | Ringed sites and invertibility sieve | Proposed | PSSS-05b and PSSS-07 |
| PSSS-09 | Zariski coverage | Proposed | PSSS-08 |
| PSSS-10 | Slice sites and affine-basic-open comparison | Proposed | PSSS-09 |
| PSSS-11 | Scheme atlas | Proposed | PSSS-10 |
| PSSS-12 | Functor-of-points/qcqs comparison | Research boundary | PSSS-11 and representability audit |

## 20. Success Criteria For The Foundation Tranches

PSSS-01/PSSS-02 are successful when:

1. `Psh_cat(K)` remains a visible runtime facade and compares directly with
   `Catd_cat(Op_cat K)` only at proof time;
2. `Obj` and `Hom_cat` expose the existing Catd hierarchy;
3. presheaf pullback computes through `Pullback_catd_func(Op_func F)`;
4. the Yoneda presheaf computes pointwise to `Hom_K(V,U)`;
5. the slice is built from the opposite Sigma total of the representable;
6. the higher-sieve classifier computes pointwise to Cat-valued presheaves on
   that slice;
7. maximal higher sieves reuse `Terminal_catd`;
8. no generic functoriality, naturality, Sigma, or opposite rule is duplicated;
9. ordinary sieves remain outside those two modules rather than being
   conflated with higher sieves; topology, sheafification, rings, and schemes
   remain absent rather than being represented by placeholders; and
10. focused checks, warning comparison, audit, synchronized documentation, and
    the required integration gate are green before any authorized checkpoint.

PSSS-03a is successful when:

1. `IsSubterminalCat` rules out both multiple objects and non-equality
   directed cells while deriving `IsDiscreteCat`;
2. its witness and the pointwise ordinary-sieve witness are each proved
   proposition-valued;
3. `Sieve(U)` retains an underlying `HigherSieve(U)` and only property
   evidence;
4. pullback uses the existing classifier/Catd action and preserves the
   property by witness selection;
5. no local rewrite or unification rule duplicates generic action;
6. identity/package eta remains an explicit negative rather than being
   asserted as computation;
7. neither `Omega` nor setness of `Sieve(U)` is claimed prematurely; and
8. focused checks, reviewer example, warning comparison, strict audits,
   catalog, health, synchronized prose, and full integration CI are green
   before any separately authorized checkpoint.

PSSS-04a is successful when:

1. membership is the object classifier of an ordinary sieve value and is
   proved proposition-valued;
2. the canonical maximal ordinary sieve is pointwise true, pulls back
   computationally, and does not force a `Terminal_cat`/`Path_cat(Unit)` head
   identification;
3. an arbitrary cover predicate returns a packaged proposition and exposes
   its proposition evidence;
4. the topology package has exactly maximality, pullback stability, and local
   character, with named projections for practical consumers;
5. local character uses real restriction-total arrows, membership, and
   `sieve_pullback` rather than an ad hoc Boolean relation;
6. a generic chaotic topology and its `Terminal_cat` instance exercise all
   three laws;
7. `Omega`, generated coverage saturation, sheafification, and descent remain
   absent; and
8. focused checks, reviewer example, warning comparison, strict audits,
   catalog, health, synchronized prose, and full integration CI are green
   before any separately authorized checkpoint.

PSSS-05a may be promoted only when:

1. the restriction-oriented category of sieve elements and its projection to
   `K^op` reuse the existing Sigma owners;
2. the presheaf descent diagram computes on literal nested elements without a
   broad package-eta rule;
3. the terminal weight and `P[U]` candidate use the existing profunctor and
   weighted-limit owners;
4. glue/restrict cancellation remains inherited from generic comparison
   push/pull rather than duplicated locally;
5. the public datum retains a proof that its selected restriction of the
   candidate identity agrees with the independently assembled canonical
   presheaf-action cell, not merely some isomorphism to a representing object;
6. one nonvacuous discrete or Cat-valued topology/presheaf consumer derives
   both the comparison and that agreement; an example which assumes those two
   exact fields counts as an API test but not as this semantic promotion gate;
7. chosen computational descent structure is not mislabeled as a
   proposition-only `IsSheaf` theorem without a uniqueness proof; and
8. only then are the sheaf package/category, reviewer checks, warning/audit
   comparison, catalog, health, synchronized prose, and full integration CI
   eligible for promotion and a separately authorized checkpoint.

PSSS-06a is successful when:

1. a ring carrier is an explicit `SetU_grpd` package and exposes its retained
   sethood evidence;
2. operations and law evidence are separate, with readable constructors,
   projections, and element-level operations;
3. the selected eight laws are sufficient for a commutative unital ring and
   do not impose `zero != one`;
4. the one-element zero ring is constructed from existing Unit contraction
   evidence, and its open unit laws use actual paths rather than a false Unit
   eta reduction;
5. ring morphisms, `CommRing_cat`, localization representations, finite
   families, powers, and polynomial syntax remain outside this tranche;
6. no rewrite or unification rule is added merely to hide Sigma/package
   structure; and
7. focused source checks, a reviewer example, warning comparison, strict
   audit, catalog/health synchronization, current-authority prose, and full
   integration CI are green before any separately authorized checkpoint.

PSSS-06b is successful when:

1. a ring morphism exposes one carrier function plus readable zero, one,
   addition, negation, and multiplication preservation evidence;
2. each law classifier and their combined package are proved
   proposition-valued from target-carrier sethood, and the whole morphism
   classifier is proved set-valued;
3. `CommRing_cat` uses `CommRing` directly as its object classifier and
   `Path_cat(CommRingHom(R,S))` as its hom category, with a checked `OneCat`
   truncation witness;
4. explicit constructors project to their supplied function and evidence,
   including one concrete zero-ring endomorphism consumer;
5. whole identity and composition retain the generic category owners, no
   package eta or broad outer-projection/inner-cut rule is added, and a
   negative check records that the generic identity projection is not falsely
   advertised as pointwise computation;
6. the carrier functor remains outside the tranche unless a ring-valued
   presheaf consumer supplies a stable action normal form; and
7. focused source and reviewer checks, warning comparison, strict audit,
   catalog/health synchronization, current-authority prose, and full
   integration CI are green before any separately authorized checkpoint.
