# EMDASH v3.2 Observational Equality, Truncation, And Univalence Redesign Plan

Date: 2026-07-13
Last reviewed: 2026-07-14
Plan-ID: EMDASH-V3-2-OBSERVATIONAL-EQUALITY-TRUNCATION-UNIVALENCE-REDESIGN-2026-07-13
Depends-On: EMDASH-V3-2-GROUPOID-COMPUTATIONAL-UNIVALENCE-2026-06-23; REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26
Supersedes: no whole report yet; proposes the successor architecture for the active groupoid/computational-univalence track after review and staged approval
Side-Task-Ledger: #side-task-ledger
Infinity-Codex-Origin: current-session-analysis-2026-07-13
Infinity-Codex-Decision-Responses: current-session-user-direction-2026-07-13-and-2026-07-14; infinity-codex:019f5d75-e60e-7e50-8ebc-b3586081b672:019f5d7c-3fd0-7932-a38e-48985ba4bda0; infinity-codex:019f5d75-e60e-7e50-8ebc-b3586081b672:019f618e-041a-77d2-ad93-31d04d584fa2
Status: revised proposed integrated redesign; review and feasibility-probe findings are incorporated, but no kernel migration is promoted by this report and the current implementation remains the active draft until individual slices are refined, probed, and accepted

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
permanent foundations. A second objective is to maintain an executable
foundational-adequacy benchmark: the minimal introductory HoTT kernel and its
immediate category/omega-category analogues must remain expressible, with
explicit prerequisites where the active file does not yet contain the needed
classifier, constructor, action, or eliminator.

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
8. **The equality redesign has two cooperating tracks.** A conservative
   classifier-and-observer MVP may be promoted without waiting for arbitrary
   structured-path elimination, while shaped `eq_refl`, structural
   action/substitution, and shaped `J` remain available for immediate design
   and implementation as soon as an owner-position probe meets the promotion
   criteria below.
9. **Earlier failed encodings are evidence, not vetoes.** In particular, the
   earlier failure of a raw `eq_refl ->` path-record-constructor rewrite does
   not prohibit a stable shaped-reflexivity head, a different action owner, or
   another now-feasible architecture.
10. **Missing infrastructure is an ordinary prerequisite, not a reason to
    weaken the target.** A slice may first add a classifier, stable facade,
    record convention, equality action, or equivalence certificate that is not
    yet in `emdash3_2.lp`; existing first-draft owners may also be redesigned or
    corrected after focused migration probes.
11. **Foundational adequacy is a design test.** The plan must account for the
    minimal HoTT-style notions listed below and their immediate directed
    categorical/omega analogues, including at least one iteration through the
    next hom level. Passing Lambdapi formation alone is not sufficient; the
    matrix records expected computation and missing prerequisites.
12. **A property over an already-named map needs a computational facade.** A
    Sigma fibre such as `Sigma e, omega_equiv_to(e) = F` is a valid semantic
    specification, but it is not by itself the selected runtime interface for
    declaring that a concrete functor is an equivalence. Stable fixed-map
    certificates and optional declaration tooling are designed below.

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

The 2026-07-14 full-file feasibility probe
`tmp/probes/oetu_architecture_feasibility_probe.lp` additionally established
the following implementation evidence. The probe is ignored scratch evidence,
not promoted source.

- a parametrized one-constructor dependent record, its generated eliminator,
  named projections, `TruncLevel`, recursive `IsTruncGrpd`, and a packaged
  truncated universe all typecheck against the active file;
- conservative observational classifiers for nondependent and dependent
  records, direct reflexivity observations, generic literal-reflexivity `J`, a
  strict path-algebra head, and recursive `IsNCat` formation are mechanically
  feasible as isolated skeletons;
- rewriting record reflexivity directly to the raw path-record constructor
  reproduced local critical-pair failures;
- replacing that raw constructor normal form by a stable former-specific
  shaped-reflexivity head, letting its projections own the component
  reflexivities, and adding a specialized reflexive `ind_eqr` rule is viable;
- generic operations that discriminate on literal `eq_refl` must register a
  narrow rule for the shaped head at the generic owner's position. After the
  probe registered strict path composition and symmetry this way, the
  warning-enabled probe passed with no probe-local warning;
- the semantic fixed-functor fibre for category equivalence typechecks, but
  this does not resolve the computational declaration/usability question.

This evidence raises shaped reflexivity and reflexive shaped `J` from a blanket
future deferral to an immediate candidate slice. It does **not** yet establish
arbitrary structured-path substitution, nested-former scalability, public
equality migration safety, or metatheoretic normalization.

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

### Directed categorical dimension axis

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

This recursion has been mechanically validated in the isolated 2026-07-14
probe. It remains candidate architecture rather than promoted code until its
active owner position, warnings, and diagnostics are reviewed.

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

The package itself must not silently be assigned the carrier's truncation
level. Under univalence, the expected universe of `n`-types is generally an
`(n+1)`-type: for example, the universe of propositions is set-like and the
universe of sets is groupoid-like. The first package slice may leave its own
truncation theorem open, but its comments and types must not claim
`IsTruncGrpd(n,TruncGrpdU(n))` without a proof.

### Evidence irrelevance

For paths in `TruncGrpdU(n)` to be controlled by paths/equivalences of the
carrier, the theory eventually needs:

```text
IsPropGrpd(IsTruncGrpd(n,A)).
```

This should be derived from the recursive definition. It must not be replaced
by a global proof-irrelevance rewrite. Until the derivation is available,
univalence of the truncated universes remains incomplete.

### Closure and invariance ledger

The property kernel is only the beginning of usable truncation support. Each
following item needs an explicit status (`active`, `probed`, `prerequisite`, or
`deferred`) rather than an assumed closure axiom:

- equality lowers truncation by one recursive step;
- truncation is invariant under `TypeEquiv`;
- dependent products preserve an appropriate fixed truncation level;
- dependent sums use the truncation of both base and fibres with the standard
  level bound rather than an unconditional same-level rule;
- contractibility, proposition, set, and 1-groupoid evidence is itself
  property-valued at the required level;
- carrier/evidence paths in `TruncGrpdU(n)` are controlled by carrier paths;
- univalence for `TruncGrpdU(n)` agrees with ambient univalence restricted to
  equivalences preserving the packaged property.

Only the first recursion equations are required for the earliest MVP. The
remaining entries are prerequisites for claiming that the truncated universes
are closed, univalent, or convenient foundations for later HoTT examples.

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
| Struct_R
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
the convention, not a mechanical rule about explicit arguments. Prefix
parameters of a parametrized inductive are already in scope for its
constructors and must not be duplicated in the constructor binder. Generated
constructor applications will still expose those parameters in their
elaborated form. Projection LHSs should infer non-discriminating parameters as
`_` wherever the subject-reduction and warning audit permits.

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

### Recursive directed categorical dimension

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
and IsOmegaEquivFunctor(Core_incl_func(C)).
```

Here `IsOmegaEquivFunctor(F)` means equivalence structure on the **already
selected** functor `F`. There are two legitimate but operationally different
ways to present it.

The semantic/reference presentation is the homotopy fibre:

```text
OmegaEquivFibre(F)
  := Sigma e : OmegaEquiv(Cat_cat,A,B),
       omega_equiv_to(e) = F.
```

The equality in this formula is ordinary HoTT practice: it says that the
forward map selected by an equivalence package is the fixed map under study.
It is useful for specifications and comparison theorems. It is not the best
public computational interface when consumers immediately need the forward
projection to normalize to `F`, because that recovery otherwise travels
through an equality proof.

The preferred public facade is therefore a fixed-map certificate, provisionally
named `OmegaEquivAlong(F)` or `IsOmegaEquivFunctor(F)`. Its telescope stores
the inverse and recursively required hom-equivalence/coherence data while the
forward functor is a parameter, not a projected field. A stable introduction
bridge into the existing first-class package should have a beta rule of the
following shape:

```text
omega_equiv_from_along
  : OmegaEquivAlong(F) -> OmegaEquiv(Cat_cat,A,B)

omega_equiv_to(omega_equiv_from_along(u)) -> F.
```

The certificate is intended to be property-like, but that must be established
from its recursive coherence or from an equivalence with the semantic fibre;
it is not licensed by the name `IsOmegaEquivFunctor`. Until then, paths of
`IsDiscreteCat`/`NCat` packages still contain an evidence-field obligation.

This outline requires a genuine introduction/corecursion design for
`OmegaEquiv`; the active file currently exposes observations and reflexivity,
not an unrestricted general constructor. That missing bridge is a prerequisite
to implement and probe, not a reason to weaken discreteness to object
truncation. An equivalent intrinsic definition may still be selected after
`Path_cat` and the functor-equivalence layer are repaired.

The same usability convention applies to structures such as adjunctions. For
concrete named data the desired manual expansion is conceptually:

```text
myF       : Functor(A,B)
myWitness : OmegaEquivAlong(myF)
myEquiv   := omega_equiv_from_along(myWitness)

assert omega_equiv_to(myEquiv) ≡ myF.
myEquiv_forward_path
  : omega_equiv_to(myEquiv) = myF
  := eq_refl(myF).
```

The conversion assertion checks the runtime beta rule; the typed reflexive
path makes the same selected projection available as an ordinary equality
fact. If a concrete adjunction must similarly be declared over named `F` and
`G`, an `AdjunctionAlong(F,G)` facade with computing left/right projections is
preferable to making two per-instance unification rules the only connection.
The analogous outline is:

```text
AdjunctionAlong(F,G) : Grpd
adjunction_from_along
  : AdjunctionAlong(F,G) -> Adjunction(A,B)

left_adj_func(adjunction_from_along(j))  -> F
right_adj_func(adjunction_from_along(j)) -> G.
```

A concrete `myAdj` can then be a transparent definition through
`adjunction_from_along(myAdjWitness)`, so all instances share the same generic
projection rules. The active opaque first-class `Adjunction` observations do
not yet provide this introduction bridge; as with `OmegaEquiv`, the bridge's
field/coherence telescope is a prerequisite to design rather than boilerplate
that can be assumed away.

A future `declare_equivalence` or `declare_adjunction` source generator may
emit the stable package, projection assertions, and—only where conversion is
intentionally proof-time—a narrow typed `unif_rule`. Per-instance unification
rules are experimental, do not supply runtime normalization, and scale poorly;
they may be convenience bridges but must not be the sole semantic authority.
When the projection is needed by computation, a constructor/facade beta rule
is preferred. The current first-class `Adjunction` design is therefore not
rejected, but the previously deferred parameterized "along named functors"
bridge is reopened as an explicit usability task.

Consequently, `IsDiscreteCat` must be designed before `IsNCat` is promoted,
and the blocker is specifically fixed-functor omega-equivalence
infrastructure—not an unspecified need for every possible notion of category
equivalence.

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

### `J`, shaped reflexivity, and structural action

The active `ind_eqr`/`ind_eq` interface remains a useful compatibility and
semantic reference. A full observational implementation cannot, however,
depend solely on one beta rule that recognizes only the literal `eq_refl`
head. The redesign therefore separates three achievements that were previously
too easily conflated:

1. a conservative classifier MVP: equality exposes a record/Sigma/Pi path
   view; projections of literal reflexivity compute; generic `J` computes on
   literal reflexivity;
2. shaped reflexivity and reflexive shaped `J`: a supported former selects a
   stable reflexivity head whose path projections compute structurally, and
   `ind_eqr` recognizes that head at the reflexive endpoint;
3. arbitrary structured-path elimination: open terms and dependent motives
   act on non-reflexive structured paths through an explicit structural
   action/substitution architecture.

The conservative MVP does not require (3), but (2) and (3) are **not deferred
by policy**. They are immediate design/implementation tracks and may overtake
or simplify the conservative route as soon as their probes are globally
credible.

The 2026-07-14 probe gives a concrete candidate for (2):

```text
PairPathRefl(r) : PairPath(r,r)

eq_refl(PairGrpd(A,B),r) -> PairPathRefl(r)
pair_path_first(PairPathRefl(r)) -> eq_refl(first(r))
pair_path_second(PairPathRefl(r)) -> eq_refl(second(r))
ind_eqr(...,r,PairPathRefl(r)) -> branch.
```

The stable head is essential: rewriting directly to a raw nested path-record
constructor produced competing reductions. It is also not sufficient in
isolation. Every generic consumer whose beta rule discriminates on literal
`eq_refl`—the probe exercised strict composition, symmetry, and `ind_eqr`—must
register a narrow rule for the shaped head at that consumer's owning position.
With those bridges, the warning-enabled probe added no local critical-pair
warning.

The successful rule order is also part of the evidence. The shaped former head
was declared before the fresh generic consumers, and its bridges were placed
at those consumers before their literal-`eq_refl` rules. A late append-only
bridge may make final terms reduce while still hiding the critical pair from
the owner's sequential warning check. For the open-world architecture, the
active migration must therefore choose one of these scalable arrangements:

- declare the initially supported former/reflexivity heads before a centralized
  generic-consumer registry;
- refactor direct literal-reflexivity consumers through the selected structural
  action/`J` owner so that fewer former-specific bridges are required; or
- retain literal `eq_refl` as the runtime head for a former and expose a shaped
  constructor/proof-time comparison until a safe ordering migration exists.

The first shaped slice may use a closed, explicitly listed set of supported
formers. It must not claim that a successful late extension proves an
indefinitely open registration mechanism.

This candidate may be implemented immediately after it passes the full
promotion protocol for a nondependent and a dependent record. Promotion
requires all of the following:

- candidate rules inserted at their intended owner positions in a full-file
  copy, not merely appended after all consumers;
- declaration and registration order is feasible in the active source without
  forward-reference tricks or duplicating a generic semantic owner;
- constructor-first and projection-first joins for the supported former;
- generic literal-`eq_refl` `J` remains unchanged for unsupported classifiers;
- all current generic consumers of literal reflexivity are inventoried and
  either remain parametric or receive a narrow former registration;
- Sigma, Pi, one dependent path telescope, and one nested supported former are
  tested before claiming a reusable protocol;
- subject reduction, warning delta, both reduction orders, bounded full check,
  and focused typed `eq_refl` diagnostics pass.

Achievement (3) is stronger. An arbitrary path-record value cannot soundly be
eliminated by returning the reflexive branch for an arbitrary motive. It needs
a real owner for action of open terms, dependent transport through field
telescopes, and higher coherence. Immediate candidate architectures include a
former-specific structural-action facade, an `ObsSubst` protocol from which
compatible `J` is derived, or another stable higher-dimensional action head.
The design must eventually specify:

- structural reflexivity/degeneracy;
- symmetry and higher degeneracies in canonical form;
- action of open terms on structured paths;
- transport through dependent fields;
- readback or rewrite normal forms for higher composites.

Earlier reports constrain known-bad encodings but do not veto a new solution
that passes these criteria.

### Open-world classifier protocol

The current `Grpd` universe is an open collection of stable classifier heads,
not an inductive-recursive closed universe of codes. The near-term
observational design should therefore use an explicit registration protocol:

1. each supported type former owns one equality classifier rule;
2. it selects either conservative reflexivity observations or one stable
   shaped-reflexivity head, never competing runtime normal forms;
3. each generic literal-reflexivity consumer states whether and how a shaped
   former registers with it;
4. it owns or explicitly marks pending structural action/substitution
   projections;
5. it supplies focused critical-pair tests against generic consumers;
6. unsupported classifiers remain opaque rather than receiving guessed
   equations.

A later closed inductive-recursive universe of type codes might permit a more
uniform normalization proof, but it would be a major migration and would make
extensibility harder. This proposal does not choose that migration now.

### Prototype and public-owner probes before migration

Before changing the active `=`/`eq_refl`/J owners again, continue with two
complementary owner-position full-file probes. A specification-only surface may
use heads such as:

```text
ObsEq(A,x,y)
ObsRefl(A,x)
ObsSubst(...)
```

In addition, the viable shaped-reflexivity candidate must be tested on fresh
public-like equality heads at the exact positions where the real owners and
generic consumers would live. `ObsEq` alone can miss migration interactions.
Together the probes should cover one nondependent record, one dependent
record, Sigma, and Pi. They must demonstrate:

- structural record path formation;
- reflexivity projections;
- related-input function equality;
- dependent field transport;
- both orders of every projection/refl reduction;
- shaped-head registration with `ind_eqr`, composition, symmetry, transport,
  and every other inventoried generic literal-reflexivity consumer;
- either arbitrary structured-path action or an explicit, accurately named
  boundary at reflexive shaped `J`;
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

This owner selection belongs near the beginning of the migration, before
constructor-specific univalence closure and before paths of packaged truncated
universes are claimed. Otherwise new code will continue to accumulate against
two unrelated inverse choices.

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

For an arbitrary supplied capability `U`, agreement with the global selected
decoder is additional coherence data; it does not follow merely because both
terms have inverse-like types, and experimental unification rules are not a
substitute for the missing path. The interface must either store/expose that
agreement, restrict to the canonical capability, or label the comparison as an
axiom/theorem prerequisite.

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
4. make `Path_cat` a strict category by the computation required by its
   declared type `Path_cat(A) : Cat`; if the weak route is selected instead,
   reclassify it outside the current strict `Cat` interface rather than leaving
   weak laws inside a supposedly strict category;
5. test associativity and both unit diamonds at arbitrary paths;
6. reconnect `Core_incl_func` and `path_to_hom` only after the selected path
   composition normal form is stable.

Do not add a second specialized `Core_incl_func` composition owner merely to
hide a failure in `Path_cat` itself.

The feasibility probe shows that a fresh strict composition/symmetry interface
with explicit endpoint guards can satisfy its local equations. It does not yet
show that replacing the active `eq_trans`/`eq_sym` owners preserves every
consumer. The repair slice therefore remains a migration audit, not merely the
addition of the fresh probe heads.

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
- a promoted shaped-reflexivity former has exactly one selected shaped head and
  registers with generic literal-reflexivity consumers;
- a fixed-map structure facade makes its selected projection compute to the
  already-named map without transporting through an equality witness;
- transport through univalence computes through the selected equivalence map;
- proof fields remain propositions/evidence rather than arbitrary runtime
  erasure rules;
- equivalences that do not select a canonical runtime normal form remain
  propositional or proof-time;
- truncation reflectors do not pretend to compute until their higher-inductive
  eliminators exist.

Computational ambition does not justify broad collapse rules, duplicate
semantic owners, or hidden proof-irrelevance axioms.

## Foundational Adequacy And Minimal HoTT/Omega Validation Matrix

This matrix is a test of the architecture, not a claim that every row is
already active and not a gate that prevents the first small slice. Every row
must carry one of four statuses in the implementation ledger:

```text
active       present in emdash3_2.lp with diagnostics;
probed       mechanically feasible in an owner-position/full-file probe;
prerequisite missing infrastructure to implement before the consumer;
deferred     deliberately beyond the MVP, with the boundary stated.
```

If an introductory construction cannot be expressed without a brittle global
rewrite, that is evidence that the infrastructure needs redesign. It is not a
reason to declare the construction out of scope.

### Minimal type/groupoid-side benchmark

The first adequacy pass should inventory and exercise:

- basic classifiers and decoding for unit, empty, booleans or binary sums,
  natural numbers, dependent products, dependent sums, and at least one named
  dependent record; absent elementary inductive classifiers are recorded as
  prerequisites rather than simulated by opaque inhabitants;
- equality formation, `eq_refl`, `ind_eqr`/`ind_eq` (`J`), transport,
  `eq_ap`, `eq_apd`, `PathOver`, symmetry, and composition;
- contractibility, fibres, `IsEquivMap`, `TypeEquiv`, selected inverse data,
  and their identity/composition/symmetry behavior;
- function/Pi extensionality in the selected observational reading;
- groupoid-universe univalence, `idtoequiv_grpd`, the selected reverse decoder,
  transport/action beta, and named round trips;
- `IsTruncGrpd`, `PropU_grpd`, `SetU_grpd`, `GroupoidU_grpd`, the closure and
  invariance ledger, and the correct truncation level of packaged universes;
- observational identity of one nondependent and one dependent record,
  including conservative observations and the immediate shaped
  reflexivity/`J` fast track;
- explicit status for higher-inductive truncation reflectors. Their absence
  prevents a claim of full HoTT completeness but does not prevent a useful
  foundational skeleton.

The benchmark distinguishes `J` on literal reflexivity, reflexive shaped `J`,
and elimination/action on an arbitrary structured path. A passing result must
not report the first or second as if it had implemented the third.

### Immediate category and omega-category benchmark

For each relevant type/groupoid notion, the plan should exercise the immediate
directed analogue already suggested by the iterated-hom architecture:

- `Cat`, `Obj`, `Hom`, identities, composition, opposites, `Path_cat`, and
  `Core_cat`/`Core_incl_func`;
- functors, object/arrow action, identity/composition laws, transfors, and
  naturality through the global generic owners;
- first-class and fixed-map/"along" forms of omega-equivalence, including
  usable declaration of a concrete named equivalence;
- `idtoequiv_cat`, the selected category decoder, path-to-arrow coherence, and
  the ordinary-isomorphism comparison only at the appropriate dimension;
- strict path-category composition/opposite coherence;
- `IsObjTruncCat`, `IsDiscreteCat`, recursive `IsNCat`, and packaged `OneCat`;
- the corresponding structure one hom level higher: an object-level example
  is repeated for a hom-category or transfor hom-action so that a capped point
  rule cannot accidentally erase the data needed by omega iteration.

This is not a demand to encode every HoTT construction as a directed category.
It tests the obvious structural correspondences: identity groupoids versus
path categories, maps versus functors, homotopies versus transfors,
equivalences versus omega-equivalences, and truncation versus eventual
discreteness of iterated homs.

### Initial 2026-07-14 status snapshot

This initial inventory prevents the general benchmark from obscuring what is
already known. `Active` here means that symbols exist and current diagnostics
pass; it does not upgrade a documented first-draft coherence boundary.

| Benchmark row | Status | Current evidence or prerequisite |
| --- | --- | --- |
| Unit, natural numbers, Pi, Sigma, decoding | active | Present in `emdash3_2.lp`; Sigma/Pi equality is already partly observational. |
| Empty type and a reviewed binary coproduct/boolean classifier | prerequisite | No canonical active row was found in the reviewed foundational surface; add only when selected by a concrete adequacy example. |
| Equality, literal `eq_refl`, generic `J`, transport, `ap`, `apd`, `PathOver` | active | Present, but the equality architecture is hybrid and not the final global owner. |
| Record identity classifier and reflexivity observers | probed | Nondependent and dependent conservative skeletons pass in the full-file probe. |
| Stable shaped record reflexivity and reflexive shaped `J` | probed | Nondependent stable-head skeleton passes with owner-position consumer registrations and no local warning. |
| Dependent/nested shaped reflexivity and arbitrary structured action | prerequisite | Immediate Phase 4 track; must not be inferred from the nondependent reflexive probe. |
| Contractibility, fibres, `IsEquivMap`, `TypeEquiv` | active | Contractible-fibre presentation and selected map/inverse observations are active. |
| Groupoid univalence and operational reverse decoder | active | First-draft capabilities exist; decoder agreement and action coherence remain Phase 5 work. |
| Truncation properties and low-level aliases | probed | `TruncLevel`/`IsTruncGrpd` skeleton passes; no active promotion yet. |
| Packaged `PropU_grpd`/`SetU_grpd`/`GroupoidU_grpd` | probed | Carrier/evidence record skeleton passes; property paths, closure, and universe-level truncation remain open. |
| Truncation reflectors | deferred | Require the higher-constructor/restricted-elimination architecture. |
| `Cat`, functors, transfors, iterated hom actions | active | Broad generic infrastructure exists and remains the owner of ordinary functoriality/naturality. |
| Strict coherent `Path_cat` and opposite action | prerequisite | Current first draft has unit/self-opposite coherence defects; a fresh strict local algebra is only probe evidence. |
| First-class `OmegaEquiv` observations | active | Recursive observation/reflexivity interface exists; unrestricted introduction/corecursion is absent. |
| Fixed-map `OmegaEquivAlong(F)` and concrete declaration | prerequisite | Semantic Sigma fibre is probed; computational facade/bridge and property-valuedness remain to design. |
| `IsObjTruncCat` | probed | Formation is mechanically small once `IsTruncGrpd` exists. |
| `IsDiscreteCat` | prerequisite | Needs repaired `Path_cat` and fixed-map omega-equivalence of `Core_incl_func`. |
| Recursive `IsNCat` | probed | Recursion skeleton passes with an opaque stand-in for the discrete base. |
| Packaged `OneCat` and scoped ordinary-iso univalence | prerequisite | Depends on the real discrete base, evidence paths, and the omega/ordinary comparison. |
| One-next-hom end-to-end adequacy example | prerequisite | Generic machinery exists, but the redesigned equality/truncation/univalence stack has not yet passed this integrated test. |

### Per-former computational checklist

Every former admitted to the adequacy matrix is evaluated in the following
columns:

| Column | Required question |
| --- | --- |
| formation/decoding | Does the classifier decode to the intended Lambdapi carrier? |
| introduction | Is there a constructor or stable introduction facade with the right endpoints? |
| observations/elimination | Do named projections and the intended eliminator beta rules compute? |
| equality classifier | Is endpoint equality direct, encoded, or still opaque, and is that status honest? |
| reflexivity | Do conservative observations and any selected shaped head have one joining normal form? |
| action/transport | Can open and dependent terms act on the supported paths, or is this a recorded prerequisite? |
| equivalence/univalence | Are closure and decoder round trips present at the relevant universe/dimension? |
| omega iteration | Does the construction retain the owner needed at the next hom level? |
| diagnostics/performance | Do typed assertions, both reduction orders, warnings, and bounded checks remain credible? |

The first promoted skeleton may leave cells marked `prerequisite` or
`deferred`; it fails the benchmark only if it silently claims those cells,
chooses an interface that makes them implausible, or cannot state the missing
work precisely.

## Proposed Implementation Phases

The phase numbers express dependency and migration order for promoted code;
they are not a prohibition on parallel design probes. In particular, the
shaped lane of Phase 4 and the fixed-map facade of Phase 7 are available for
immediate investigation while the low-risk record/truncation slices are being
refined.

### Phase 0: Documentation And Freeze

1. Refine and approve this proposal.
2. Mark the June 23 univalence report as the active historical implementation
   ledger and this report as its proposed successor architecture.
3. Add no unrelated direct equality, Product decoder, or global
   `CatIsoUnivalence` computation during the redesign. Focused equality rules
   explicitly belonging to the shaped fast track are allowed after their
   promotion probe; this freeze is not a veto on that track.
4. Preserve the passing active baseline.

### Phase 1: Finite Record Convention Probe

1. Refine the already-passing small dependent one-constructor record in a
   temporary owner-position probe.
2. Validate the generated eliminator, named projections, dependent projection
   types, and constructor beta rules.
3. Compare its source/readability and warning behavior with a nested-Sigma
   encoding.
4. Record the final convention in the SOP or a dedicated decision section.
5. Do not yet generate observational record equality globally.

This phase is independently feasible and informs all later packaged
universes.

### Phase 2: Truncation Properties

1. Promote or refine the passing `TruncLevel` and readable-level probe.
2. Promote or refine the passing recursive `IsTruncGrpd` equations.
3. Add `IsPropGrpd`, `IsSetGrpd`, and `IsGroupoidGrpd` views.
4. Add focused formation and reduction checks.
5. Open the closure/invariance ledger without pretending that all entries are
   required for the property-kernel slice.
6. Do not add truncation reflectors.

This is the leading candidate for the first promoted mathematical slice.

### Phase 3: Packaged Truncated Universes

1. Add the one-constructor `TruncGrpdU(n)` record/classifier.
2. Add computing carrier/evidence projections.
3. Add `PropU_grpd`, `SetU_grpd`, and `GroupoidU_grpd` aliases.
4. Derive or explicitly defer property-valuedness of truncation evidence.
5. Do not claim univalence of these subuniverses before proof-field paths are
   controlled.
6. State the expected `(n+1)` truncation level of the universe separately from
   the `n`-truncation evidence carried by its elements.

### Phase 4: Equality MVP And Immediate Shaped Fast Track

This phase has two cooperating lanes. Either may produce the first useful
equality slice; neither lane may misstate what it has implemented.

Conservative lane:

1. retain direct record/Sigma/Pi equality classifiers and projection observers
   where both reduction orders join;
2. keep generic `J` computation on literal `eq_refl`;
3. use the lane as a fallback MVP and as a control for warning/performance
   comparisons.

Shaped lane:

1. refine the stable former-specific shaped-reflexivity head demonstrated by
   the 2026-07-14 probe;
2. cover a nondependent record and a genuinely dependent path telescope;
3. register the shaped head with `ind_eqr`, composition, symmetry, transport,
   and every inventoried generic literal-reflexivity consumer at the correct
   owner positions;
4. test Sigma, Pi, a nested former, and both reduction orders;
5. probe a structural action/substitution owner for arbitrary path-record
   values; promote reflexive shaped `J` independently if it passes before the
   arbitrary-action design does;
6. write an exact consumer/migration audit before changing an existing public
   former.

### Phase 5: Univalence Decoder Interface Normalization

1. Select the reverse decoder owner at the groupoid and categorical layers.
2. Connect capability-selected inverses by named coherence data or restrict to
   the canonical capability.
3. Expose both round trips and the path-to-arrow/transport squares.
4. Keep constructor closure propositional until the generic squares are
   stable.
5. Do not use arbitrary-capability `unif_rule`s as a replacement for missing
   coherence.

### Phase 6: `Path_cat` Coherence Repair

1. Remove/probe removal of definitional self-oppositeness.
2. Introduce/probe the path-symmetry opposite functor/equivalence.
3. Settle strict unit/associativity ownership required by `Path_cat : Cat`.
4. Add both-order diagnostic diamonds.
5. Revalidate `Core_incl_func`, `path_to_hom`, `DefIso`, opposite, and Product
   consumers.

### Phase 7: Fixed-Map Equivalence, Directed Dimension, And `OneCat`

1. Specify `OmegaEquivAlong(F)`/`IsOmegaEquivFunctor(F)` as a fixed-map
   certificate and compare it propositionally with `OmegaEquivFibre(F)`.
2. Design/probe the stable introduction or corecursion bridge into
   `OmegaEquiv` so its forward projection computes to `F`.
3. Validate one concrete named equivalence declaration without relying only on
   a per-instance unification rule.
4. Select and implement `IsDiscreteCat` from the fixed-map certificate.
5. Add `CatDim`, recursive `IsNCat`, `NCat(n)`, `ZeroCat`, and `OneCat`.
6. Add `IsObjTruncCat` separately.
7. Scope ordinary `CatIsoUnivalence` to `OneCat` and prove or defer the
   `OmegaEquiv`/`IsoEvidence` comparison there.

### Phase 8: Public Equality And Structural-Action Migration

1. Migrate one type former at a time from the prototype to public equality.
2. Replace old encode/decode implementations that became identity coercions.
3. Retain compatibility aliases only when they have real consumers.
4. Eliminate the two-reflexivity-normal-form Product boundary.
5. Promote arbitrary structured-path `J` only through the selected
   action/substitution architecture; do not identify it with the already
   feasible reflexive shaped beta rule.
6. Keep bounded checks and warning comparisons for every owner migration.

This phase must not be combined with a module split or broad code
reorganization.

### Phase 9: Foundational Adequacy And Closure Completion

1. Populate every row of the minimal HoTT/omega matrix with an honest status.
2. Implement missing elementary prerequisites needed by the selected
   validation examples.
3. Complete the truncation closure/invariance facts needed by active packaged
   universes.
4. Run at least one record/equality/equivalence example through the next hom
   level.
5. Derive TypeEquiv and OmegaEquiv symmetry/composition and add constructor
   closure only after the generic univalence squares are stable.

### Phase 10: Truncation Reflectors And Higher Constructors

1. Design propositional and set truncation as higher-inductive structures.
2. Specify their restricted dependent eliminators and beta rules.
3. Generalize to `n`-truncation only after the low levels are computationally
   credible.
4. Integrate truncated higher-inductive structures rather than assuming that
   post-hoc truncation always preserves desired computation.

### Phase 11: Deferred Universe Metatheory

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

Feasibility status: the isolated full-file probe passes; the remaining work is
owner-position refinement, naming, diagnostics, and promotion review.

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

Feasibility status: the recursion and package skeleton pass in the isolated
probe; active-source placement and closure-ledger boundaries remain to audit.

### Candidate C: shaped record reflexivity and reflexive `J`

```text
one stable former-specific shaped-reflexivity head;
path projection beta rules;
specialized reflexive ind_eqr beta;
registration with generic composition and symmetry;
dependent-record and nested-former extension probe;
no claim yet of arbitrary structured-path action.
```

Risk: medium to high. The nondependent stable-head skeleton passes with
warnings enabled and no local warning after owner-position registrations. The
dependent/nested and complete-consumer audits remain promotion gates.

This candidate is immediately available; it is not deferred behind completion
of the conservative observational MVP.

### Candidate D: fixed-map structure usability facade

```text
OmegaEquivFibre(F) as semantic reference;
OmegaEquivAlong(F) field telescope;
stable introduction bridge with omega_equiv_to beta;
one concrete named equivalence declaration;
optional typed proof-time comparison, not unif-only semantics.
```

Risk: medium. The fibre formulation typechecks, but the active `OmegaEquiv`
introduction/corecursion boundary is deliberately incomplete and must be
designed first.

### Candidate E: `Path_cat` focused repair

```text
remove self-opposite collapse in a full-file probe;
classify warning delta and downstream type failures;
probe symmetry functor;
test both path-category units.
```

Risk: medium to high, but this is a prerequisite for `OneCat`.

Candidates A, B, and C can be refined independently; C may become a narrow
public equality slice only after its stated promotion gates pass. Candidate D
may proceed far enough to settle the facade even before the entire directed
dimension layer is implemented. Candidate E remains the prerequisite for
`IsDiscreteCat` and `OneCat`.

## Explicitly Deferred Work

Shaped `eq_refl`, structural action/substitution, reflexive shaped `J`, and a
sound arbitrary structured-path `J` are intentionally **not** blanket entries
in this deferred list. They are immediate tracks. A particular attempted
encoding may fail or an unresolved subpart may remain a prerequisite for a
later slice, but earlier reports do not defer the subject itself.

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
- shaped-reflexivity projection order against the raw path constructor;
- specialized reflexive `ind_eqr` beta without changing unsupported formers;
- dependent path-telescope and one nested-former case;
- registrations for every generic consumer that matches literal `eq_refl`.

### Truncation diagnostics

- `IsTruncGrpd(-2,A) = IsContr(A)`;
- successor recursion unfolds exactly one level;
- proposition/set/groupoid aliases select the intended indices;
- carrier projection of each packaged universe;
- no runtime elimination of evidence fields.
- no false claim that `TruncGrpdU(n)` is itself `n`-truncated;
- focused checks for each promoted closure/invariance fact.

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
- `omega_equiv_to(omega_equiv_from_along(u)) ≡ F` by runtime computation;
- comparison of `OmegaEquivAlong(F)` with `OmegaEquivFibre(F)` propositionally;
- a concrete named equivalence/adjunction-style declaration whose selected
  projection is usable by downstream computation;
- no semantic dependency on an untyped or unvalidated per-instance
  `unif_rule`.

### Foundational adequacy diagnostics

- every matrix row has an `active`, `probed`, `prerequisite`, or `deferred`
  status and at least one owning file/symbol or missing-prerequisite entry;
- equality, transport, equivalence, univalence, and truncation examples compose
  rather than merely typecheck independently;
- literal-reflexivity `J`, reflexive shaped `J`, and arbitrary structured-path
  action are tested and reported separately;
- one selected construction remains iterable through a hom-category/transfor
  action instead of terminating at a pointwise object rule;
- bounded timing and warning deltas are recorded for every promoted equality
  or univalence owner.

## Risk Register

### Direct observational equality remains the highest-risk migration

Adding open-world rules to `=` and structural reflexivity can multiply
critical pairs across every dependent consumer. The isolated prototype and
per-former registry are mandatory.

### Shaped reflexivity creates a generic-consumer registration obligation

The stable-head probe is locally successful, but any generic operation whose
rewrite LHS recognizes literal `eq_refl` can otherwise lose its beta rule after
the inner reflexivity rewrites. The registry must be auditable and its bridges
must live at the generic owner's position. An append-only successful assertion
is insufficient evidence. Because Lambdapi declarations are ordered, a former
introduced after an early generic owner cannot simply be referenced in that
owner's earlier rule block. The migration may need forward declaration and
section reordering, a centralized closed registry for initially supported
formers, or a generic-consumer refactor through structural action. This source
ordering change is part of Candidate C's risk, not mere formatting.

### Native inductive records interact with the current `Prop`/`P` builtins

Lambdapi generates induction principles using the configured proposition
classifier. The active mapping `Prop := Grpd`, `P := τ` is useful but means the
generated motive and existing encoded groupoid universe must be inspected in
every record probe.

### `IsDiscreteCat` may expose missing category-equivalence infrastructure

Do not weaken discreteness to object-set truncation merely to make `OneCat`
easy to declare. The concrete prerequisite is a fixed-functor
`OmegaEquivAlong(Core_incl_func(C))` facade and its bridge to the recursive
`OmegaEquiv` observations; record it rather than postulating an opaque generic
category-equivalence property.

### Declaration convenience can accidentally become semantic authority

A generated or handwritten per-instance `unif_rule` is attractive for making
`left_adj_func(myAdj)` or `omega_equiv_to(myEquiv)` elaborate as an already
named map. Lambdapi unification rules are experimental and proof-time only.
The semantic package and runtime projection beta must remain meaningful when
that convenience rule is removed.

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
| `OETU-RECORD-CONVENTION` | proposed early slice; skeleton probed | current inductive/Sigma infrastructure | first concrete slice selected | Refine the passing dependent one-constructor record, projections, generated eliminator, parameter syntax, and inferred-slot audit; compare with nested Sigma. |
| `OETU-RECORD-GENERATOR` | deferred/optional | `OETU-RECORD-CONVENTION` | two manual records show repeated stable boilerplate | Specify a deterministic external schema generator; generated code remains reviewable Lambdapi source. |
| `OETU-TRUNC-LEVEL` | proposed early slice; skeleton probed | existing `IsContr`, `Pi_grpd`, equality | truncation slice selected | Promote/refine `TruncLevel`, recursive `IsTruncGrpd`, and named low-level aliases with owner-position diagnostics. |
| `OETU-TRUNC-CLOSURE` | proposed staged ledger | `OETU-TRUNC-LEVEL`, equality/equivalence | a closure fact receives a concrete consumer | Prove one fact at a time: equality lowering, equivalence invariance, Pi/Sigma bounds, and package-universe truncation. |
| `OETU-TRUNC-EVIDENCE-PROP` | deferred proof | `OETU-TRUNC-LEVEL`, stable observational paths | packaged-universe equality is consumed | Derive `IsPropGrpd(IsTruncGrpd(n,A))`; do not postulate global proof irrelevance. |
| `OETU-TRUNC-UNIVERSE` | proposed follow-up; skeleton probed | `OETU-RECORD-CONVENTION`, `OETU-TRUNC-LEVEL` | low-level predicates pass | Add `TruncGrpdU`, low-level aliases, carrier/evidence projections, and an explicit no-false-universe-truncation diagnostic. |
| `OETU-TRUNC-REFLECTOR` | deferred | observational equality and HIT elimination | a theorem needs `||A||_n`, not merely `IsTruncGrpd(n,A)` | Design propositional truncation first with restricted dependent elimination. |
| `OETU-PATH-CAT` | proposed prerequisite repair | current path algebra | `OneCat` or observational category equality begins | Remove/probe self-opposite collapse, settle strict unit ownership, and add symmetry functor/equivalence. |
| `OETU-OMEGA-EQUIV-ALONG` | proposed prerequisite; semantic fibre probed | recursive `OmegaEquiv`, record/facade convention | fixed-functor equivalence or discreteness is consumed | Design the fixed-map certificate and stable bridge whose forward projection computes to the parameter; compare with the semantic Sigma fibre. |
| `OETU-STRUCTURE-DECLARATION` | proposed usability protocol | one successful `Along` facade; current first-class `Adjunction` | a second concrete named structure instance is needed | Validate manual declaration expansion, typed projection assertion, and optional narrow proof-time unification bridge; consider a generator only afterward. |
| `OETU-DISCRETE-CAT` | blocked by explicit prerequisites | `OETU-PATH-CAT`, `OETU-OMEGA-EQUIV-ALONG` | directed dimension slice begins | Define object-set truncation plus `OmegaEquivAlong(Core_incl_func(C))`; do not substitute object truncation alone. |
| `OETU-NCAT` | proposed architecture, implementation deferred | `OETU-DISCRETE-CAT`, `OETU-TRUNC-LEVEL`, record convention | `IsDiscreteCat` is stable | Add `CatDim`, recursive `IsNCat`, and packaged `NCat`. |
| `OETU-ONECAT-ISO` | proposed replacement | `OETU-NCAT`, global Cat univalence | `OneCat` exists | Scope/derive `CatIsoUnivalence` for `OneCat`; retire the unscoped claim. |
| `OETU-OBS-MVP` | proposed conservative lane; skeleton probed | record convention and current equality views | a low-risk equality former is selected | Refine direct classifier, literal-reflexivity observers, and generic `J` control case without claiming arbitrary structured action. |
| `OETU-OBS-SHAPED-REFL` | immediate candidate; nondependent skeleton probed | `OETU-OBS-MVP` classifier shape, consumer inventory | shaped lane selected | Extend the stable shaped head to a dependent record and nested former; register every generic literal-reflexivity consumer at owner position. |
| `OETU-OBS-ACTION` | immediate design/probe track | path telescopes, `PathOver`, shaped registry | any arbitrary structured path must eliminate | Select/probe structural action or `ObsSubst`; account for open terms, dependent fields, composites, and next-dimensional data. |
| `OETU-OBS-SHAPED-J` | split status: reflexive candidate immediate; arbitrary depends on action | `OETU-OBS-SHAPED-REFL`; for arbitrary paths `OETU-OBS-ACTION` | shaped equality slice selected | Promote specialized reflexive `ind_eqr` when it passes; derive arbitrary structured-path `J` only from a sound action architecture. |
| `OETU-OBS-MIGRATE` | deferred high-risk public migration | successful shaped/MVP probe and consumer audit | one former has canonical joins | Migrate public equality one former at a time; do not combine with reorganization. |
| `OETU-FOUNDATIONAL-ADEQUACY` | active validation ledger | all relevant rows above | every slice refinement and milestone | Populate status/owner/computation cells; implement prerequisites needed by a selected end-to-end HoTT/omega example. |
| `OETU-UNIV-DECODER` | proposed early coherence repair | current equality and univalence interfaces | round trips, truncated-universe paths, or constructor univalence are consumed | Select decoder heads, add named capability agreement and coherence squares before further closure rules. |
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
4. agree on the semantic-fibre versus computational fixed-map-facade boundary
   and on the limited role of declaration-generated `unif_rule`s;
5. decide whether Candidate A, B, C, D, or E is the first implementation
   slice, allowing the shaped candidate C to proceed immediately if its
   dependent/nested/consumer gates pass;
6. specify the conservative equality MVP, stable shaped-reflexivity registry,
   and arbitrary structural-action boundary without conflating them;
7. initialize the foundational adequacy matrix with honest statuses and named
   prerequisites;
8. add a migration statement to the June 23 plan when this proposal is
   formally adopted.

## Long-Term Completion Criteria

The redesign program is complete only when:

```text
truncation properties and packaged Prop/Set/n-groupoid universes are active;
their closure, evidence-path, and universe-level truncation claims are explicit;
Path_cat is coherent with strict category computation, or a weak replacement is
classified outside strict Cat;
OneCat is defined through directed hom truncation/discreteness;
fixed-map omega-equivalence structure supports usable named declarations;
ordinary IsoEvidence univalence is OneCat-scoped;
public equality computes observationally for records, Sigma, Pi, and universes;
structural reflexivity and higher substitution have one canonical owner;
reflexive shaped J and arbitrary structured-path action are both implemented
and distinguished by diagnostics;
univalence forward/reverse maps have named round trips and action coherence;
Product constructor/reflexivity/decoder reductions join;
the minimal HoTT/omega adequacy matrix has no unacknowledged missing cell and
at least one construction iterates through the next hom level;
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
- Lambdapi's `unif_rule` documentation in the same local manual describes the
  feature as experimental and proof-time; this is why declaration convenience
  rules are not selected as runtime or semantic owners.
- The 2026-07-14 feasibility findings are supported by the ignored full-file
  probe `tmp/probes/oetu_architecture_feasibility_probe.lp` and its
  warning-enabled log
  `logs/probes/oetu_architecture_feasibility_probe-20260714-135156.log`.
  Neither scratch artifact is promoted kernel source.
