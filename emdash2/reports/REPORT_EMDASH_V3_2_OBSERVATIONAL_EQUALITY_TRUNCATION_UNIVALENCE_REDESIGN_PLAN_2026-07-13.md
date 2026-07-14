# EMDASH v3.2 Observational Equality, Truncation, And Univalence Redesign Plan

Date: 2026-07-13
Last reviewed: 2026-07-13
Plan-ID: EMDASH-V3-2-OBSERVATIONAL-EQUALITY-TRUNCATION-UNIVALENCE-REDESIGN-2026-07-13
Depends-On: EMDASH-V3-2-GROUPOID-COMPUTATIONAL-UNIVALENCE-2026-06-23; REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26
Supersedes: no whole report yet; proposes the successor architecture for the active groupoid/computational-univalence track after review and staged approval
Side-Task-Ledger: #side-task-ledger
Infinity-Codex-Origin: current-session-analysis-2026-07-13
Infinity-Codex-Decision-Responses: current-session-user-direction-2026-07-13; infinity-codex:019f5d75-e60e-7e50-8ebc-b3586081b672:019f5d7c-3fd0-7932-a38e-48985ba4bda0
Status: proposed integrated redesign; no kernel migration is promoted by this report, and the current implementation remains the active draft until individual slices are refined, probed, and accepted

## Goal

Replace the current first-draft groupoid/univalence architecture with a staged
program whose eventual target is full observational equality and computational
univalence, while introducing the truncation and finite-dimensional structure
needed to state the mathematics correctly.

The program must integrate four concerns that should no longer be developed in
isolation:

1. observational equality for functions, dependent pairs, records, universes,
   and later inductive/coinductive structures;
2. HoTT truncation levels and the universes of propositions, sets, and
   `n`-groupoids;
3. directed `n`-categories, especially an ordinary/univalent `OneCat` layer;
4. one coherent computational-univalence interface at the groupoid and
   categorical levels.

The near-term objective is not to implement this whole program at once. It is
to settle the dependency structure, select canonical owners, identify small
feasible slices, and prevent the current draft rules from becoming accidental
permanent foundations.

## Decisions Accepted For This Proposal

This proposal incorporates the following project directions.

1. **Full observational equality is the eventual target.** The current hybrid
   of direct Sigma/Pi equality views and a uniform J eliminator is not the
   intended final design.
2. **Truncation is an immediate architecture prerequisite.** `Prop`, `Set`,
   ordinary groupoids, `OneCat`, and general finite-dimensional variants must
   be designed together with univalence, even if their first implementation
   slice is only formation and projection computation.
3. **Every active `C : Cat` remains globally univalent for now.** The kernel may
   retain `cat_univalence(C)` and its decoder-oriented companion as explicit
   operational assumptions.
4. **No `PreCat`/`UnivCat` split is required in the near term.** If non-univalent
   structures are needed later, they may receive a separate classifier; the
   current `Cat` interface itself is interpreted as univalent.
5. **Universe stratification and a model of `Cat_cat : Cat` remain deferred.**
   The code and reports must label the current policy as an unstratified
   operational specification, not as a consistency or model-existence result.
6. **Ordinary isomorphism univalence is dimension-specific.** The global
   omega-level principle compares equality with `OmegaEquiv`; the
   `IsoEvidence` comparison belongs to `OneCat` or an explicit ordinary-category
   truncation hypothesis.
7. **Finite dependent structures should not default to deeply nested Sigma
   projections.** A one-constructor dependent inductive record convention is
   the preferred explicit encoding; small existential/property packages may
   continue to use Sigma.

## Current Baseline And Review Findings

At creation of this proposal:

```text
tracked working tree                         clean
EMDASH_TYPECHECK_TIMEOUT=60s make check      pass
active implementation                        emdash3_2.lp
active diagnostics                           emdash3_2_checks.lp
```

The existing architecture contains valuable first slices:

- `PathOver`, `eq_apd`, Sigma/Pi path views, and contractible-fibre
  `TypeEquiv`;
- explicit `idtoequiv_grpd`, `idtoiso_cat`, and `idtoequiv_cat` directions;
- explicit reverse decoder heads;
- a recursive `OmegaEquiv` observation interface;
- constructor-specific Product experiments;
- a global categorical-univalence policy stated visibly rather than hidden in
  conversion.

The review nevertheless found four blocking design boundaries.

1. `Path_cat` inherits strict generic category identity rules that do not join
   the current one-sided J definition of `eq_trans`.
2. `Op_cat(Path_cat(A)) -> Path_cat(A)` identifies a self-opposite equivalence
   with definitional equality and erases the endpoint reversal.
3. Sigma/Pi equality has begun reducing observationally, while `eq_refl` and J
   still follow the older uniform-inductive identity architecture.
4. Capability-selected inverse maps and operational decoder heads coexist
   without named agreement, and Product reflexive collapse competes with
   structured decoder normal forms.

These are not reasons to abandon the current concepts. They show that the
next work must be an architecture migration, not additional constructor-local
rules on the existing hybrid.

## Four Distinct Notions That Must Remain Separate

### Truncation property

`IsTruncGrpd(n,A)` states that `A` is already `n`-truncated. It does not change
the elements of `A` and should be computational only through recursion on the
level and projection of its evidence.

### Truncation reflector

`Trunc_grpd(n,A)`, written mathematically as `||A||_n`, freely turns an
arbitrary type into an `n`-type. It requires higher-inductive/path
constructors and a restricted dependent eliminator. It is not supplied merely
by an inhabitant of `IsTruncGrpd(n,A)`.

### Groupoidal truncation level

An `n`-groupoid is represented homotopy-type-theoretically by an `n`-type.
Thus propositions, sets, ordinary groupoids, and higher groupoids are levels
of the ambient type/groupoid universe.

### Directed categorical dimension

An `n`-category is not merely a category whose object classifier is an
`n`-type. It is a directed structure whose iterated hom-categories become
discrete above dimension `n`. This requires a separate recursive predicate
over `Hom_cat`.

The kernel names must distinguish these axes. In particular,
`IsObjTruncCat(n,C)` and `IsNCat(n,C)` must not be aliases.

## Ambient Type/Groupoid Naming

The current kernel name:

```text
Grpd : TYPE
```

classifies general type-like objects with iterated identity structure. It does
not currently impose 1-truncation and therefore behaves more like an ambient
universe of types or infinity-groupoids than a universe of ordinary
groupoids.

The near-term migration should not rename `Grpd`, because it is pervasive.
Instead:

- document `Grpd` as the legacy kernel name for the ambient type/infinity-
  groupoid classifier;
- reserve `GroupoidU_grpd` or an agreed successor name for the universe of
  1-truncated objects;
- permit the future surface language to print the ambient classifier as
  `Type`, `Space`, or another reviewed notation;
- avoid claiming that every `A : Grpd` is an ordinary 1-groupoid.

## Truncation-Level Architecture

### Level codes

Use an explicit native level datatype beginning at `-2`, rather than an
undocumented shift of ordinary natural numbers:

```lambdapi
inductive TruncLevel : TYPE ≔
| trunc_minus_two : TruncLevel
| trunc_succ : TruncLevel -> TruncLevel;
```

Derived readable levels are:

```text
trunc_minus_one = trunc_succ(trunc_minus_two)
trunc_zero      = trunc_succ(trunc_minus_one)
trunc_one       = trunc_succ(trunc_zero)
```

This encoding makes the recursion equations direct and prevents confusion
between homotopy dimension and the internal natural-number representation.

### Recursive truncation predicate

The intended computational equations are:

```text
IsTruncGrpd(-2,A)
  = IsContr(A)

IsTruncGrpd(n+1,A)
  = Pi x y : A, IsTruncGrpd(n,x = y).
```

A candidate Lambdapi surface is:

```lambdapi
symbol IsTruncGrpd (n : TruncLevel) (A : Grpd) : Grpd;

rule IsTruncGrpd trunc_minus_two $A
  ↪ IsContr $A
with IsTruncGrpd (trunc_succ $n) $A
  ↪ @Pi_grpd $A
      (λ x : τ $A,
        @Pi_grpd $A
          (λ y : τ $A, IsTruncGrpd $n (x = y)));
```

This is a candidate for a future owner-position probe, not promoted code.

Named properties should be transparent views:

```text
IsPropGrpd(A)     := IsTruncGrpd(-1,A)
IsSetGrpd(A)      := IsTruncGrpd(0,A)
IsGroupoidGrpd(A) := IsTruncGrpd(1,A).
```

`IsContr` already exists and remains the semantic base case.

### Universes of truncated objects

The universe of `n`-types should package an ambient classifier with truncation
evidence:

```text
TruncGrpdU(n) = { A : Grpd | IsTruncGrpd(n,A) }.
```

The preferred implementation representation is the record convention below,
not a public chain of anonymous `sigma_Fst(sigma_Snd(...))` projections.

Canonical aliases are:

```text
PropU_grpd      := TruncGrpdU(-1)
SetU_grpd       := TruncGrpdU(0)
GroupoidU_grpd  := TruncGrpdU(1).
```

The future surface may print these as `Prop`, `Set`, and `Gpd`/`Groupoid`.
The active Lambdapi builtin already maps the kernel builtin name `Prop` to
`Grpd`, so the kernel must not immediately reuse the literal symbol `Prop` for
the internal proposition universe.

The universe record needs at least:

```text
trunc_grpd_carrier   : TruncGrpdU(n) -> Grpd
trunc_grpd_evidence  : Pi X : TruncGrpdU(n),
                         IsTruncGrpd(n,trunc_grpd_carrier(X)).
```

Carrier projection and decoding should compute. Truncation evidence is a
proof capability and must not acquire broad proof-erasing runtime rules.

### Evidence irrelevance

For paths in `TruncGrpdU(n)` to be controlled by paths/equivalences of the
carrier, the theory eventually needs:

```text
IsPropGrpd(IsTruncGrpd(n,A)).
```

This should be derived from the recursive definition. It must not be replaced
by a global proof-irrelevance rewrite. Until the derivation is available,
univalence of the truncated universes remains incomplete.

### Truncation reflectors

The desired later interface is:

```text
Trunc_grpd(n,A)       : Grpd
trunc_intro(n,A)      : A -> Trunc_grpd(n,A)
trunc_is_truncated    : IsTruncGrpd(n,Trunc_grpd(n,A))
trunc_elim            : elimination into n-truncated families.
```

This is a higher-inductive construction. It is deferred until the
observational equality and higher-constructor elimination architecture is
settled. No opaque `Trunc_grpd` plus unrestricted eliminator should be promoted
as a shortcut, because that would provide neither the desired computation nor
the required universal property.

## Finite Dependent Record Convention

### Assessment of the proposed manual pattern

The proposed pattern of a carrier type, one constructor, named projections,
and constructor projection rules is fundamentally sound. It is preferable to
nested Sigma when:

- the structure has many named fields;
- later fields depend on earlier fields;
- field names are part of the mathematical API;
- observational equality should follow the field telescope;
- a stable constructor head is useful to computation.

For ordinary finite data structures, the carrier should normally be declared
with Lambdapi's parametrized `inductive` command rather than as an unrelated
opaque `constant`. Lambdapi then generates the dependent eliminator and its
constructor beta rule. Named record projections still have to be declared
manually.

### Canonical schematic encoding

For a parameter telescope `P` and dependent fields, use the following pattern:

```lambdapi
(P : Parameters) inductive RData : TYPE ≔
| Struct_R [P]
    (field0 : Field0 P)
    (field1 : Field1 P field0)
    (field2 : Field2 P field0 field1)
    : RData P;

constant symbol R_grpd (P : Parameters) : Grpd;
rule τ (R_grpd $P) ↪ RData $P;

symbol r_field0 [P] (r : RData P) : Field0 P;
rule r_field0 (@Struct_R $P $f0 $f1 $f2) ↪ $f0;

symbol r_field1 [P] (r : RData P) : Field1 P (r_field0 r);
rule r_field1 (@Struct_R $P $f0 $f1 $f2) ↪ $f1;
```

The exact implicit slots require an owner-position probe. The example states
the convention, not a mechanical rule about explicit arguments.

For the covering-sieve example, the user's `Struct_cov_sieve` idea therefore
has the right semantic shape. The recommended refinements are:

1. use a one-constructor dependent inductive carrier if the structure is
   ordinary finite data;
2. expose `cov_sieve_cat`, `cov_sieve_func`, and `cov_sieve_hom` as named
   projections with constructor beta rules;
3. use current `Cat`/functor/hom names in promoted v3.2 code rather than
   obsolete lowercase spellings;
4. add an explicit eliminator wrapper only when the generated eliminator has
   an inconvenient parameter/motive surface;
5. do not install runtime record eta by default.

### When not to use an inductive record

Use an opaque stable facade with destructors instead when the object is
intentionally abstract, coinductive, or operationally specified only through
observations. Current examples include `OmegaEquiv` and the computational
`DefIso` facade.

Use nested Sigma when the package is small and genuinely existential, for
example a map together with one property. `TypeEquiv` may retain a Sigma
semantic presentation if its path algebra remains manageable. Named
projections should hide nesting from consumers.

### Observational equality of records

For a record with fields `f0`, `f1`, and `f2`, equality is a dependent path
telescope:

```text
RPath(r,s)
  = Sigma p0 : f0(r) = f0(s),
      PathOver(Field1,p0,f1(r),f1(s))
      ... followed by the transported path for f2.
```

In the final observational design this should be a dedicated record identity
classifier with named fields, not definitionally an ordinary nested Sigma.
Later path fields depend on all earlier path fields.

The minimum generated/manual package for an observational record is expected
to contain:

- the data carrier and constructor;
- named data projections and beta rules;
- the dedicated path-record carrier;
- named path projections;
- structural reflexivity observations;
- structural action/substitution observations;
- an eliminator or extensionality theorem;
- diagnostics for constructor-first and projection-first reduction.

### Optional external generator

The repeated boilerplate is suitable for a future deterministic repository
tool, for example `scripts/gen_record.py`, driven by a small field-telescope
schema. A generator may emit checked Lambdapi declarations, projection rules,
path-record skeletons, and diagnostic templates.

The generator must not become a second semantic authority. Generated output
must follow the same owner rules, remain reviewable, and be validated by
Lambdapi. This tooling is optional and should follow one or two successful
manual record implementations.

## Groupoidal Truncation Versus Directed `n`-Categories

### `n`-groupoids

Use the HoTT identification:

```text
NGroupoid(n) = TruncGrpdU(n).
```

Thus:

```text
(-1)-groupoids = propositions
0-groupoids    = sets
1-groupoids    = ordinary groupoids
n-groupoids    = n-types.
```

This is a property/universe hierarchy inside the ambient `Grpd` classifier.

### Object truncation of a category

Define the independent property:

```text
IsObjTruncCat(n,C)
  := IsTruncGrpd(n,Obj(C)).
```

This says nothing by itself about non-invertible arrows or higher directed
cells.

### Directed categorical dimension

Introduce a nonnegative native dimension code:

```lambdapi
inductive CatDim : TYPE ≔
| cat_zero : CatDim
| cat_succ : CatDim -> CatDim;
```

The proposed recursive directed-dimension property is:

```text
IsNCat(0,C)     := IsDiscreteCat(C)
IsNCat(n+1,C)   := Pi x y : Obj(C), IsNCat(n,Hom_cat(C,x,y)).
```

The base `IsDiscreteCat` is a real prerequisite. It should express that `C`
has no directed information beyond the equality/groupoidal structure of a
set of objects. A likely semantic formulation is:

```text
IsSetGrpd(Obj(C))
and Core_incl_func(C) is an equivalence of categories.
```

The exact category-equivalence classifier required by that formula is not yet
present. An equivalent intrinsic formulation may be selected after the
`Path_cat` and functor-equivalence layers are repaired. Therefore
`IsDiscreteCat` must be designed before `IsNCat` is promoted.

The recursive definition matches the iterated-hom architecture: an ordinary
1-category has discrete hom-categories; a 2-category has ordinary
hom-categories; and so on.

This is the project's strict/iterated-hom notion of finite categorical
dimension. It is distinct from an `(n,1)`-category presented as a complete
semi-Segal type. Connections with Segal/Rezk presentations are future
comparison theorems, not definitional equalities.

### Packaged finite-dimensional categories

Once `IsNCat` is stable, define record packages:

```text
NCat(n) = { C : Cat | IsNCat(n,C) }
ZeroCat = NCat(0)
OneCat  = NCat(1).
```

Because the current policy makes every `C : Cat` globally univalent, these
packages need not carry an additional `CatUnivalence(C)` field. Their extra
data is finite-dimensionality evidence.

Carrier projections should compute:

```text
ncat_carrier(Struct_ncat(C,h)) -> C.
```

No runtime eta or proof-field erasure should be installed initially.

### `OneCat` and ordinary isomorphism univalence

The current global symbol:

```text
cat_iso_univalence(C) : CatIsoUnivalence(C)
```

should eventually be replaced or quarantined by a dimension-correct
interface:

```text
onecat_iso_univalence
  : Pi C : OneCat,
      CatIsoUnivalence(onecat_carrier(C)).
```

The preferred final result is to derive this from:

- global `CatUnivalence` into `OmegaEquiv`;
- the discreteness/truncation of all hom-categories of a `OneCat`;
- a comparison between `OmegaEquiv` and `IsoEvidence` at that level.

A scoped operational axiom is acceptable before the derivation, but the
unscoped global `CatIsoUnivalence` claim should remain labelled temporary.

### Universes of `n`-categories

Later interfaces may include:

```text
NCat_grpd(n) : Grpd
NCat_cat(n)  : Cat
OneCat_grpd  : Grpd
OneCat_cat   : Cat.
```

`NCat_cat(n)` should be the full category of `n`-categories and ordinary
functors between their carriers. Its univalence and equality must account for
the fact that `IsNCat(n,C)` is property-valued. This depends on evidence
irrelevance and the repaired category-univalence decoder, and is not an early
slice.

## Full Observational Equality Target

### Selected end state

Equality should compute according to the classifier of its endpoints:

- record equality is a dependent record of field paths;
- Sigma equality is a base path plus a fibre path over it;
- Pi/function equality relates values at related inputs;
- universe equality is equivalence;
- reflexivity and action/substitution compute structurally;
- later inductive/coinductive equality follows the corresponding structural
  observation scheme.

The identity classifier for a record or inductive structure should normally
be a dedicated identity structure. It may be definitionally isomorphic to a
Sigma encoding without being literally the same public record.

### Uniform J is not the final computational owner

The active `ind_eqr`/`ind_eq` interface can remain as a compatibility and
semantic reference during migration, but a full observational implementation
cannot rely on one beta rule that only recognizes the literal `eq_refl` head.

The final computation owner should be type-directed higher-dimensional
substitution/action. At minimum the design must specify:

- structural reflexivity/degeneracy;
- symmetry and higher degeneracies in canonical form;
- action of open terms on structured paths;
- transport through dependent fields;
- readback or rewrite normal forms for higher composites.

No further wholesale `eq_refl` rewrite should be promoted before that contract
exists.

### Open-world classifier protocol

The current `Grpd` universe is an open collection of stable classifier heads,
not an inductive-recursive closed universe of codes. The near-term
observational design should therefore use an explicit registration protocol:

1. each supported type former owns one equality classifier rule;
2. it owns the corresponding structural reflexivity observations;
3. it owns structural action/substitution projections;
4. it supplies focused critical-pair tests against generic consumers;
5. unsupported classifiers remain opaque rather than receiving guessed
   equations.

A later closed inductive-recursive universe of type codes might permit a more
uniform normalization proof, but it would be a major migration and would make
extensibility harder. This proposal does not choose that migration now.

### Isolated prototype before migration

Before changing the active `=`/`eq_refl`/J owners again, introduce an isolated
prototype surface in an owner-position full-file probe, for example:

```text
ObsEq(A,x,y)
ObsRefl(A,x)
ObsSubst(...)
```

The prototype should cover one nondependent record, one dependent record,
Sigma, and Pi. It must demonstrate:

- structural record path formation;
- reflexivity projections;
- related-input function equality;
- dependent field transport;
- both orders of every projection/refl reduction;
- a credible migration path for current `=` consumers.

Only after that probe should a slice migrate the public equality owner.

## Global `Cat` Univalence Policy

The selected near-term policy is:

```text
for every C : Cat,
  cat_univalence(C)            : CatUnivalence(C)
  cat_univalence_by_decoder(C) : CatUnivalenceByDecoder(C).
```

This is an explicit global operational axiom. Under this policy,
non-univalent `Cat` values are not part of the intended semantics, even though
the primitive `Cat` declaration does not syntactically store a univalence
field.

Reports should remove or correct the claim that non-univalent intermediate
categories remain semantically expressible while the global instance applies
to every `C`.

The policy includes `Cat_cat`. The following remain deferred and must be
listed as such:

- a stratified hierarchy `Cat_i : Cat_(i+1)`;
- an impredicative or self-universe model;
- consistency/canonicity of the unstratified global axiom;
- constructor-specific computation for category-universe univalence.

The operational axiom is permitted to remain while these questions are open.
No report may infer a model-existence result merely because Lambdapi accepts
the signature.

## One Operational Inverse Per Univalence Layer

The decoder-oriented interfaces are selected as the eventual operational
owners:

```text
grpd_equiv_path
iso_evidence_path       // OneCat-scoped in the final design
omega_equiv_path.
```

Capability-oriented names should be derived aliases or connected by named
agreement paths:

```text
ua_grpd(U,e)             = grpd_equiv_path(e)
isotoid_cat(U,i)         = iso_evidence_path(i)
equivtoid_cat(U,e)       = omega_equiv_path(e).
```

The equalities begin propositionally. Runtime orientation is added only when
one side is selected as a genuine evaluator normal form and both reduction
orders have been measured.

The coherence API must eventually include:

```text
coe_grpd(p,a)
  = type_equiv_to(idtoequiv_grpd(p),a)

iso_evidence_to(idtoiso_cat(p))
  = path_to_hom(p)

omega_equiv_to(idtoequiv_cat(p))
  = path_to_hom(p)

path_to_hom(omega_equiv_path(e))
  = omega_equiv_to(e)
```

Both round trips from each `EquivByInverse` capability need named projections
and diagnostics. Their existence inside a nested Product package is not an
adequate public coherence API.

## `Path_cat` Repair Is A Prerequisite

The path-category redesign must precede `IsDiscreteCat`, `IsNCat`, and
`OneCat`.

Required decisions:

1. remove the runtime collapse `Op_cat(Path_cat(A)) -> Path_cat(A)`;
2. represent self-oppositeness by a functor/equivalence whose arrow action is
   path symmetry;
3. select a path-composition owner whose interaction with both strict category
   units is measured;
4. decide whether `Path_cat` is a strict category by computation or a weak
   category with propositional coherence during the observational migration;
5. test associativity and both unit diamonds at arbitrary paths;
6. reconnect `Core_incl_func` and `path_to_hom` only after the selected path
   composition normal form is stable.

Do not add a second specialized `Core_incl_func` composition owner merely to
hide a failure in `Path_cat` itself.

## Product Reflexivity Policy

Product constructor provenance should be preserved until observational
reflexivity has one canonical structured normal form.

The initial candidate migration is to remove reflexive-collapse rules of the
form:

```text
omega_equiv_product(refl,refl) -> omega_equiv_refl
iso_evidence_product(refl,refl) -> iso_evidence_refl.
```

The Product constructors and decoders can then reduce componentwise without a
competing generic evidence head. This candidate requires an owner-position
probe and warning comparison; the report does not promote the deletion.

## Computational Policy

“As computational as feasible” means:

- data constructors and named projections have beta rules;
- truncation-level recursion computes on level constructors;
- carrier projections from `Prop`/`Set`/`n`-groupoid and `n`-category packages
  compute;
- structural equality observations compute at supported type-former heads;
- transport through univalence computes through the selected equivalence map;
- proof fields remain propositions/evidence rather than arbitrary runtime
  erasure rules;
- equivalences that do not select a canonical runtime normal form remain
  propositional or proof-time;
- truncation reflectors do not pretend to compute until their higher-inductive
  eliminators exist.

Computational ambition does not justify broad collapse rules, duplicate
semantic owners, or hidden proof-irrelevance axioms.

## Proposed Implementation Phases

### Phase 0: Documentation And Freeze

1. Refine and approve this proposal.
2. Mark the June 23 univalence report as the active historical implementation
   ledger and this report as its proposed successor architecture.
3. Add no new direct equality, Product decoder, or global
   `CatIsoUnivalence` computation during the redesign.
4. Preserve the passing active baseline.

### Phase 1: Finite Record Convention Probe

1. Implement one small dependent one-constructor record in a temporary
   owner-position probe.
2. Validate the generated eliminator, named projections, dependent projection
   types, and constructor beta rules.
3. Compare its source/readability and warning behavior with a nested-Sigma
   encoding.
4. Record the final convention in the SOP or a dedicated decision section.
5. Do not yet generate observational record equality globally.

This phase is independently feasible and informs all later packaged
universes.

### Phase 2: Truncation Properties

1. Add/probe `TruncLevel` and readable level aliases.
2. Add/probe the recursive `IsTruncGrpd` equations.
3. Add `IsPropGrpd`, `IsSetGrpd`, and `IsGroupoidGrpd` views.
4. Add focused formation and reduction checks.
5. Do not add truncation reflectors.

This is the leading candidate for the first promoted mathematical slice.

### Phase 3: Packaged Truncated Universes

1. Add the one-constructor `TruncGrpdU(n)` record/classifier.
2. Add computing carrier/evidence projections.
3. Add `PropU_grpd`, `SetU_grpd`, and `GroupoidU_grpd` aliases.
4. Derive or explicitly defer property-valuedness of truncation evidence.
5. Do not claim univalence of these subuniverses before proof-field paths are
   controlled.

### Phase 4: `Path_cat` Coherence Repair

1. Remove/probe removal of definitional self-oppositeness.
2. Introduce/probe the path-symmetry opposite functor/equivalence.
3. Settle unit/associativity ownership.
4. Add both-order diagnostic diamonds.
5. Revalidate `Core_incl_func`, `path_to_hom`, `DefIso`, opposite, and Product
   consumers.

### Phase 5: Directed Dimension And `OneCat`

1. Select and implement `IsDiscreteCat`.
2. Add `CatDim` and recursive `IsNCat`.
3. Add `NCat(n)`, `ZeroCat`, and `OneCat` record packages.
4. Add `IsObjTruncCat` separately.
5. Scope ordinary `CatIsoUnivalence` to `OneCat`.
6. Prove or defer the `OmegaEquiv`/`IsoEvidence` comparison for `OneCat`.

### Phase 6: Observational Equality Prototype

1. Specify `ObsEq`, structural reflexivity, and higher substitution.
2. Cover a nondependent record, a dependent record, Sigma, and Pi.
3. Test canonical higher-dimensional normal forms and projection diamonds.
4. Decide the open-world classifier registration protocol.
5. Produce a migration audit for every active `=`/`eq_refl`/`ind_eq` consumer.

### Phase 7: Public Equality Migration

1. Migrate one type former at a time from the prototype to public equality.
2. Replace old encode/decode implementations that became identity coercions.
3. Retain compatibility aliases only when they have real consumers.
4. Eliminate the two-reflexivity-normal-form Product boundary.
5. Keep bounded checks and warning comparisons for every owner migration.

This phase must not be combined with a module split or broad code
reorganization.

### Phase 8: Univalence Coherence

1. Select the reverse decoder owner at each level.
2. Connect capability-selected inverses.
3. Expose both round trips.
4. Add the path-to-arrow/transport coherence squares.
5. Derive TypeEquiv and OmegaEquiv symmetry/composition.
6. Add constructor closure only after the generic squares are stable.

### Phase 9: Truncation Reflectors And Higher Constructors

1. Design propositional and set truncation as higher-inductive structures.
2. Specify their restricted dependent eliminators and beta rules.
3. Generalize to `n`-truncation only after the low levels are computationally
   credible.
4. Integrate truncated higher-inductive structures rather than assuming that
   post-hoc truncation always preserves desired computation.

### Phase 10: Deferred Universe Metatheory

Compare:

- the current unstratified operational specification;
- a stratified type/category universe hierarchy;
- a deliberate impredicative/self-universe model.

This phase owns consistency/model claims. No earlier implementation phase
depends on resolving it.

## Immediately Feasible Candidate Slices

The following are intentionally small enough for later refinement into the
next concrete task.

### Candidate A: record convention only

```text
one dependent record probe;
constructor and projection beta;
generated eliminator audit;
no active equality or univalence change.
```

Risk: low.

### Candidate B: truncation property kernel

```text
TruncLevel;
IsTruncGrpd recursion;
IsPropGrpd / IsSetGrpd / IsGroupoidGrpd;
formation and reduction checks;
no packaged universes and no reflector.
```

Risk: low to medium, principally interaction with direct Pi equality and
recursive evidence types.

### Candidate C: `Path_cat` focused repair

```text
remove self-opposite collapse in a full-file probe;
classify warning delta and downstream type failures;
probe symmetry functor;
test both path-category units.
```

Risk: medium to high, but this is a prerequisite for `OneCat`.

Candidates A and B can be investigated before C. No candidate should include
the public observational equality migration.

## Explicitly Deferred Work

- a complete normalization or canonicity proof for observational equality;
- a closed inductive-recursive universe of all groupoid/type codes;
- general record-schema metaprogramming before the manual convention is
  validated;
- runtime record eta;
- proof-irrelevance rewrites;
- propositional, set, and general `n`-truncation reflectors;
- `NCat_cat(n)` universe univalence;
- complete `OmegaEquiv` corecursion/productivity semantics;
- comparison with complete semi-Segal/Rezk presentations;
- universe stratification, impredicativity, and self-universe models;
- consistency of the global categorical-univalence policy;
- simultaneous source module splitting.

## Required Diagnostics

### Record diagnostics

- constructor projection beta for every field;
- dependent later-field projection typing;
- generated eliminator beta;
- no unintended record eta;
- path-record projection order once observational equality is introduced.

### Truncation diagnostics

- `IsTruncGrpd(-2,A) = IsContr(A)`;
- successor recursion unfolds exactly one level;
- proposition/set/groupoid aliases select the intended indices;
- carrier projection of each packaged universe;
- no runtime elimination of evidence fields.

### Path-category diagnostics

- both identity units at an arbitrary path;
- both associativity reduction orders;
- opposite hom endpoints remain reversed;
- the symmetry functor maps identity and composition correctly;
- `Core_incl_func` retains generic functorial ownership.

### Univalence diagnostics

- both decoder/encoder round trips propositionally;
- `coe_grpd` agrees with `idtoequiv_grpd` action;
- `path_to_hom` agrees with `idtoiso_cat`/`idtoequiv_cat` forward arrows;
- Product reflexive constructor/decoder diamonds;
- `OneCat` ordinary-iso comparison is not available for arbitrary `Cat`.

## Risk Register

### Direct observational equality remains the highest-risk migration

Adding open-world rules to `=` and structural reflexivity can multiply
critical pairs across every dependent consumer. The isolated prototype and
per-former registry are mandatory.

### Native inductive records interact with the current `Prop`/`P` builtins

Lambdapi generates induction principles using the configured proposition
classifier. The active mapping `Prop := Grpd`, `P := τ` is useful but means the
generated motive and existing encoded groupoid universe must be inspected in
every record probe.

### `IsDiscreteCat` may expose missing category-equivalence infrastructure

Do not weaken discreteness to object-set truncation merely to make `OneCat`
easy to declare. Record the prerequisite instead.

### Property fields affect universe equality

`TruncGrpdU(n)` and `NCat(n)` are structures with evidence. Their paths reduce
to carrier paths only after property-valuedness is established. Broad
proof-irrelevance is not an acceptable shortcut.

### Global `Cat` univalence remains semantically strong

The policy is accepted operationally but may fail in a future model or under a
constructor not closed by univalence. Such failures are architecture evidence,
not reasons to add arbitrary closure axioms silently.

## Side-Task Ledger

| ID | Status | Depends on | Resume trigger | Next action |
| --- | --- | --- | --- | --- |
| `OETU-RECORD-CONVENTION` | proposed | current inductive/Sigma infrastructure | first concrete slice selected | Probe one dependent one-constructor record, projections, and generated eliminator; compare with nested Sigma. |
| `OETU-RECORD-GENERATOR` | deferred/optional | `OETU-RECORD-CONVENTION` | two manual records show repeated stable boilerplate | Specify a deterministic external schema generator; generated code remains reviewable Lambdapi source. |
| `OETU-TRUNC-LEVEL` | proposed early slice | existing `IsContr`, `Pi_grpd`, equality | truncation slice selected | Probe `TruncLevel`, recursive `IsTruncGrpd`, and named low-level aliases. |
| `OETU-TRUNC-EVIDENCE-PROP` | deferred proof | `OETU-TRUNC-LEVEL`, stable observational paths | packaged-universe equality is consumed | Derive `IsPropGrpd(IsTruncGrpd(n,A))`; do not postulate global proof irrelevance. |
| `OETU-TRUNC-UNIVERSE` | proposed follow-up | `OETU-RECORD-CONVENTION`, `OETU-TRUNC-LEVEL` | low-level predicates pass | Add `TruncGrpdU`, `PropU_grpd`, `SetU_grpd`, and `GroupoidU_grpd` carrier/evidence projections. |
| `OETU-TRUNC-REFLECTOR` | deferred | observational equality and HIT elimination | a theorem needs `||A||_n`, not merely `IsTruncGrpd(n,A)` | Design propositional truncation first with restricted dependent elimination. |
| `OETU-PATH-CAT` | proposed prerequisite repair | current path algebra | `OneCat` or observational category equality begins | Remove/probe self-opposite collapse, settle strict unit ownership, and add symmetry functor/equivalence. |
| `OETU-DISCRETE-CAT` | blocked by design prerequisite | `OETU-PATH-CAT`, category-equivalence classifier | directed dimension slice begins | Select an intrinsic or core-equivalence definition that excludes higher directed data. |
| `OETU-NCAT` | proposed architecture, implementation deferred | `OETU-DISCRETE-CAT`, `OETU-TRUNC-LEVEL`, record convention | `IsDiscreteCat` is stable | Add `CatDim`, recursive `IsNCat`, and packaged `NCat`. |
| `OETU-ONECAT-ISO` | proposed replacement | `OETU-NCAT`, global Cat univalence | `OneCat` exists | Scope/derive `CatIsoUnivalence` for `OneCat`; retire the unscoped claim. |
| `OETU-OBS-SPEC` | proposed | record convention and truncation terminology | equality work resumes | Specify structural identity, reflexivity, substitution, and open-world former registration. |
| `OETU-OBS-PROBE` | deferred until specification | `OETU-OBS-SPEC` | specification reviewed | Probe records, Sigma, and Pi through isolated `ObsEq`/higher-substitution heads. |
| `OETU-OBS-MIGRATE` | deferred high-risk migration | successful `OETU-OBS-PROBE` | prototype has canonical joins and consumer audit | Migrate public equality one former at a time; do not combine with reorganization. |
| `OETU-UNIV-DECODER` | proposed coherence repair | stable equality owner | round trips or constructor univalence are consumed | Select decoder heads, add named capability agreement and coherence squares. |
| `OETU-PRODUCT-DIAMOND` | proposed focused cleanup | stable equality/reflexivity policy | Product decoder migration begins | Probe preserving Product evidence provenance by removing reflexive collapse. |
| `OETU-CAT-GLOBAL` | accepted operational policy | none | any report/kernel text suggests non-univalent `Cat` semantics | Keep every `C : Cat` globally univalent and label the policy axiomatic/unstratified. |
| `OETU-CAT-SELF` | deferred metatheory | `OETU-CAT-GLOBAL` | model or universe computation is claimed | Compare stratified, impredicative, and operational self-universe readings. |
| `OETU-METATHEORY` | deferred research | mature observational kernel | consistency/canonicity claim is needed | Develop normalization/model evidence; Lambdapi typechecking alone is not sufficient. |

## Acceptance Criteria For Refining This Proposal

Before this report becomes the active replacement plan:

1. agree on kernel names for `TruncLevel`, `IsTruncGrpd`, truncated universes,
   `CatDim`, and `IsNCat`;
2. agree on the definition boundary for `IsDiscreteCat`;
3. agree that the one-constructor inductive record convention is the default
   for finite named structures;
4. decide whether Candidate A, B, or C is the first implementation slice;
5. specify the minimal `ObsEq` prototype interface without changing public
   equality;
6. add a migration statement to the June 23 plan when this proposal is
   formally adopted.

## Long-Term Completion Criteria

The redesign program is complete only when:

```text
truncation properties and packaged Prop/Set/n-groupoid universes are active;
Path_cat is coherent with strict category computation or explicitly weak;
OneCat is defined through directed hom truncation/discreteness;
ordinary IsoEvidence univalence is OneCat-scoped;
public equality computes observationally for records, Sigma, Pi, and universes;
structural reflexivity and higher substitution have one canonical owner;
univalence forward/reverse maps have named round trips and action coherence;
Product constructor/reflexivity/decoder reductions join;
global Cat univalence remains explicitly axiomatic until a model is supplied;
all promoted slices pass focused probes, make check, relevant examples,
warning classification, catalog checks, health refresh, and make ci.
```

## References And Design Context

- The active code, diagnostics, SOP, Foundations, and canonical syntax remain
  authoritative over this proposal.
- The recursive `n`-type convention follows the standard HoTT truncation-level
  hierarchy in the [HoTT Book](https://homotopytypetheory.org/book/).
- The distinction between a truncation property and its higher-inductive
  reflector follows the same source.
- The observational target and dedicated identity records are informed by
  Michael Shulman's [Towards an Implementation of Higher Observational Type
  Theory](https://home.sandiego.edu/~shulman/papers/running-hott.pdf) and the
  [Narya documentation](https://narya.readthedocs.io/en/latest/).
- The need to connect identity of structures with a local univalence condition
  is consistent with [A Higher Structure Identity
  Principle](https://arxiv.org/abs/2004.06572).
- Complete semi-Segal/Rezk approaches to univalent `(n,1)`-categories provide
  comparison context, not the project's recursive strict/iterated-hom
  definition; see [Univalent Higher Categories via Complete Semi-Segal
  Types](https://arxiv.org/abs/1707.03693) and [A Type Theory for Synthetic
  Infinity-Categories](https://arxiv.org/abs/1705.07442).
- Lambdapi's generated induction principles and parametrized dependent
  inductives are documented in `docs/lambdapi_docs_commands.rst`; the active
  `τΣ_` implementation is the local reference example.
