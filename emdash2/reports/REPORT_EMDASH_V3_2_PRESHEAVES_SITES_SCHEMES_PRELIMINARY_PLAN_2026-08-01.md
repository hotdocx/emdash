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

Status: active living implementation architecture; `PSSS-00` review and
bounded type probe complete; `PSSS-01` is the authorized next tranche

Branch: `goal/record-structure-usability-v3.2`

Worktree: `/home/user1/emdash1-record-structure-usability`

Parent checkpoint: `6ac4a2b459ecbe9af6d1821dd2dbc6a11d71a3e4`
(`feat: add outer LF structure declarations`)

Git authorization: the parent record/structure tranche was explicitly
authorized and locally checkpointed. On 2026-08-01 the user explicitly
authorized checkpointing this reviewed documentation baseline, creating a
dedicated implementation branch/worktree, starting implementation, and
starting a corresponding persistent goal. That authorization does not include
push, merge, publication, history rewrite, cleanup, or an automatic future
implementation checkpoint; those remain separately gated.

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

The authorized implementation line begins with only the `PSSS-01` presheaf
facade. The slice/higher-sieve formulas remain the separately gated
`PSSS-02` tranche even though their bounded probe is already green. Everything
involving topology axioms, descent, algebra, or schemes remains behind a later
gate.

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
2. `../AGENTS.md` and the current-status/SOP report for the Lambdapi workflow;
3. `../emdash3_2_checks.lp` for durable diagnostics;
4. `EMDASH_FOUNDATIONS.md` and the canonical-syntax report;
5. this plan for the selected standard-library staging;
6. `../../docs/RECORD_STRUCTURE_USABILITY_V3_2_PLAN.md` only for the
   TypeScript outer-LF record API boundary; and
7. the explicitly authorized ignored Cartier sources and local Zeuner review
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

### 6.4 Probe evidence

An ephemeral full-import Lambdapi probe checked all of the following against
the unchanged active kernel:

- the proposed `Psh_cat` `Obj`/`Hom_cat` projections and single unification
  comparison;
- `Psh_pullback_func(F) = Pullback_catd_func(Op_func(F))` at object action;
- `y_K(U)[V] = Hom_K(V,U)`;
- the `ArrowInto_catd` Sigma fibre;
- the `HigherSieveClassifier` point fibre; and
- the terminal/maximal higher sieve.

The bounded check completed successfully in approximately ten seconds. The
probe is diagnostic evidence only and is not retained as source.

### 6.5 Ordinary sieves

Reserve `Sieve` and `Omega` for the subterminal specialization. A first
ordinary-sieve package should contain:

- an underlying object of the higher-sieve category;
- pointwise subterminal/proposition-valued evidence; and
- only the extra coherence not already supplied by functoriality.

The exact `IsSubterminalCat` boundary needs a focused truncation audit. It may
live in a one-way module importing the equality/groupoidality extension rather
than forcing that dependency into the basic higher-presheaf module.

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
emdash3_2_sites.lp
emdash3_2_commutative_algebra.lp
emdash3_2_ringed_sites.lp
emdash3_2_schemes.lp
```

The dependency direction is one way:

```text
kernel
  -> presheaves
  -> sites

kernel + algebra
  -> ringed sites
  -> schemes
```

The exact split may be reduced if the first declarations are too small, but a
single giant `emdash3_2_adjunctions`-style or `schemes` file should not mix
foundational presheaf variance with algebra and atlas rules.

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

Status: proposed first implementation tranche.

- add the one-way presheaf module;
- promote only `Psh_cat`, `Psh`, the two runtime projections, the single
  direct `Catd_cat` comparison, and `Psh_pullback_func`;
- add typed `eq_refl`, object/hom, abstract/opposite/nested-opposite, and
  reindexing diagnostics;
- compare warnings and prove no duplicate generic action owner was added.

### Phase PSSS-02 — Yoneda, slice, and higher-sieve classifier

Status: proposed after PSSS-01.

- promote the transparent formulas proven by the probe;
- name the restriction-oriented total and conventional slice clearly;
- expose point and pullback diagnostics;
- add maximal higher sieve; defer intersection/sub-sieve until consumed.

### Phase PSSS-03 — Ordinary sieve/truncation boundary

Status: research/design gate.

- define and validate `IsSubterminalCat` or the selected equivalent;
- package ordinary sieves as the subterminal specialization;
- reserve `Omega` for this classifier;
- keep higher sieves available under an explicit higher name.

### Phase PSSS-04 — Coverage and topology

Status: proposed after a concrete coverage consumer is selected.

- implement cover-family presentation and base change;
- implement topology evidence on ordinary sieves;
- test one direct combinatorial site before algebraic generation;
- do not implement generic free saturation.

### Phase PSSS-05 — Descent and sheaves

Status: proposed after PSSS-04.

- select a cover/descent shape;
- express the sheaf condition by `DefIso` or weighted-limit comparison;
- package `Sheaf_cat` without assuming sheafification;
- validate both a discrete and a Cat-valued example.

### Phase PSSS-06 — Commutative-ring category

Status: separate prerequisite.

- select the ring carrier/category/record boundary;
- define ring morphisms and the carrier functor;
- use explicit laws and no quotient-specific rewrite rules.

### Phase PSSS-07 — Localization and polynomial consumers

Status: separate prerequisite after PSSS-06.

- localization universal property and iterated comparison;
- finite/unimodular family interface;
- polynomial algebra universal property and one executable example.

### Phase PSSS-08 — Ringed sites and invertibility sieves

Status: proposed after PSSS-05 through PSSS-07.

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

## 19. Side-Task Ledger

| ID | Task | Status | Gate |
|---|---|---|---|
| PSSS-00 | Active-owner, historical-consumer, and Zeuner review plus bounded formula probe | Complete | This report |
| PSSS-01 | Rigid presheaf facade and reindexing | Proposed | Authorized implementation worktree |
| PSSS-02 | Yoneda, slice, higher-sieve classifier, maximal sieve | Proposed | PSSS-01 green |
| PSSS-03 | Ordinary subterminal sieve and `Omega` | Research gate | Truncation design |
| PSSS-04 | Coverage and Grothendieck topology | Proposed | Concrete combinatorial consumer |
| PSSS-05 | Descent and sheaf category | Proposed | PSSS-04 plus selected descent shape |
| PSSS-06 | Commutative-ring category | Separate prerequisite | Algebra design |
| PSSS-07 | Localization, finite families, polynomial consumers | Separate prerequisite | PSSS-06 |
| PSSS-08 | Ringed sites and invertibility sieve | Proposed | PSSS-05 and PSSS-07 |
| PSSS-09 | Zariski coverage | Proposed | PSSS-08 |
| PSSS-10 | Slice sites and affine-basic-open comparison | Proposed | PSSS-09 |
| PSSS-11 | Scheme atlas | Proposed | PSSS-10 |
| PSSS-12 | Functor-of-points/qcqs comparison | Research boundary | PSSS-11 and representability audit |

## 20. Success Criteria For The First Tranche

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
9. ordinary sieves, topology, sheafification, rings, and schemes remain absent
   from the tranche rather than being represented by placeholders; and
10. focused checks, warning comparison, audit, synchronized documentation, and
    the required integration gate are green before any authorized checkpoint.
