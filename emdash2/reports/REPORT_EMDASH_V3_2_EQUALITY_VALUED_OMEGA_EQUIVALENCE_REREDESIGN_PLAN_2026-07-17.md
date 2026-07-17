# EMDASH v3.2 Equality-Valued Omega-Equivalence And Groupoidal-J Re-Redesign Proposal

Date: 2026-07-17
Last reviewed: 2026-07-17
Plan-ID: EMDASH-V3-2-EQUALITY-VALUED-OMEGA-EQUIVALENCE-REREDESIGN-2026-07-17
Status: proposed successor/overlay plan; not yet adopted as the active implementation master plan
Review baseline: `772411011ac721c84d143a2967f4e5c31e94bc70`
Primary predecessor: `REPORT_EMDASH_V3_2_OBSERVATIONAL_EQUALITY_TRUNCATION_UNIVALENCE_REDESIGN_PLAN_2026-07-13.md`
Depends on: `emdash3_2.lp`; `emdash3_2_checks.lp`; `REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`; `EMDASH_FOUNDATIONS.md`
Provenance: independent peer review and user clarification sequence archived in Infinity Codex session `019f6bd3-8405-7d31-8ced-8a6b127c1499`, especially responses `0003` through `0005`
Proposed side-task ledger: [Side-Task Ledger](#side-task-ledger)
Proposed implementation entry point: [Recommended First Implementation Slice](#recommended-first-implementation-slice)

## Status And Authority

This document is a comprehensive proposed re-redesign of the equality,
omega-equivalence, univalence, groupoidality, and structured path-induction
parts of the July 13 living master plan. It exists beside that plan so that
the current implementation and its synchronized evidence remain available for
comparison while this simpler architecture is reviewed, probed, corrected,
and either adopted or rejected.

Until an explicit adoption decision is recorded:

1. `emdash3_2.lp` remains the active kernel authority;
2. `emdash3_2_checks.lp` remains the executable diagnostic authority;
3. the current SOP and Foundations report retain their ordinary authority;
4. the July 13 plan remains the active implementation master plan and ledger;
5. this report is a proposed successor/overlay and does not authorize deletion
   or migration merely by existing.

If this proposal is adopted, it should supersede the July 13 plan only for the
specific architecture tracks named below. The July 13 plan should remain a
historical and implementation-evidence record for all promoted slices. Its H0
formation/elimination work, truncation hierarchy, `CatDim`/`IsNCat` packages,
directed kernel, `PathOut` infrastructure, and validated examples must not be
discarded merely because their surrounding univalence interpretation changes.

The review baseline commit records the repository state from which this plan
was written. It is not a frozen boundary and must never be used as an implied
authorization to reset, restore, or overwrite later work.

Earlier checkpoints named by the predecessor implementation handoff are
`07a24e6f07c0cd7ecd8147f1fe6158e3af73707d` (pre-implementation comparison),
`7dc149294d554315bf79113420c572f1076a207b` (temporary progress), and the
current review baseline `772411011ac721c84d143a2967f4e5c31e94bc70`.
All three are historical comparison points only. None authorizes a reset or
limits ordinary forward editing.

## Executive Summary

The proposed redesign is based on one simplifying observation:

> Fixed-arrow omega-equivalence should store separate left and right inverse
> arrows whose cancellation witnesses are ordinary equalities in the
> appropriate hom-categories. Because every hom-category is again a category
> and every active category is intended to be univalent, those equalities
> already carry the recursive higher-equivalence content.

The current D0 certificate stores recursive `OmegaEquiv` cells and later
decodes them to ordinary hom equalities through categorical univalence. This
proposal reverses that ownership:

```text
current primary fields:
  left_cell  : OmegaEquiv(Hom_cat C x x, l o f, id_x)
  right_cell : OmegaEquiv(Hom_cat C y y, f o r, id_y)

proposed primary fields:
  left_law  : l o f =_{Obj(Hom_cat C x x)} id_x
  right_law : f o r =_{Obj(Hom_cat C y y)} id_y
```

Recursive omega-cells then become views of these equality fields rather than
independently stored data. This should remove the central duplication between
equality, omega-equivalence certificates, encoders, decoders, and recursive
cell observers.

The proposed MVP has seven principal parts:

1. retain `OmegaEquivAlong(C,f)` as the semantic owner for a named arrow;
2. replace its recursive cell fields with equality-valued cancellation laws;
3. initially retain `OmegaEquiv(C,x,y) := Sigma f, OmegaEquivAlong(C,f)`, while
   probing a primitive two-field facade only if stable observer/rule ownership
   requires it;
4. identify `x =_{Obj C} y` directly with `OmegaEquiv(C,x,y)` through a
   carefully classified rewrite/unification architecture rather than a
   decoder tower;
5. add the shaped `Path_cat` join and the term observers needed when an
   equality proof is used directly as equivalence data;
6. define general internal groupoidality by equivalence of `Core_cat(C)` with
   `C`, and use the existing `PathOut`/directed-family action as the structured
   groupoidal form of `J`;
7. demote unrelated former-specific action experiments, especially the
   current Sum action bases, from the foundational univalence MVP.

This is not a proposal to copy Book HoTT, cubical type theory, observational
type theory, or Narya. Those systems remain mathematical sanity checks and
sources of examples only. The implementation must be rediscovered in the
local Kosta--Dosen/Emdash cut-elimination architecture and in Lambdapi's
separation between runtime rewriting and proof-time unification.

## Original Goal And Revised Design Intent

The original wanted endpoint remains a small computational foundation on
which an end user can build genuine type-theoretic and categorical standard
libraries. The foundation should feel like a natural extension of the
existing omega-categorical kernel, not a collection of special certificates,
decoder capabilities, and former-specific equations introduced only to make
selected examples pass.

The intended MVP should support:

- primitive ambient `Grpd`, decoding, equality, reflexivity, and raw `J`;
- the existing computational `Cat`/`Obj`/iterated-`Hom`/identity/composition
  kernel;
- functors, transformations, directed families, and higher projections;
- equality as hom in literal path categories;
- internally groupoidal categories not required to be syntactically
  `Path_cat(A)`;
- fixed-map and first-class omega-equivalence with reusable construction and
  observation APIs;
- direct computational/proof-time univalence rather than mandatory
  encoder/decoder round trips;
- structured, functorial motives whose transport is existing categorical
  action;
- truncated universes and finite directed dimensions embedded through actual
  functors when a concrete consumer needs them;
- a conservative shaped-computation policy for Product, Sigma, records, sums,
  and later formers.

The MVP does not require:

- copying an external cubical or observational syntax;
- automatically turning every raw meta-level family into a structured motive;
- a new general `J` beyond primitive `ind_eqr` and the existing `PathOut`
  action;
- arbitrary HITs or truncation reflectors;
- a generic full-subcategory construction;
- runtime decomposition of every identity or equivalence constructor;
- a complete model, normalization proof, canonicity theorem, or stratified
  universe hierarchy before any operational work can proceed.

Those stronger goals remain later research or standard-library tracks. They
must not be claimed merely because Lambdapi accepts a rewrite or unification
rule.

## Independent Review Diagnosis

### Foundations that should be retained

The following current components are globally coherent and should be treated
as assets of the redesign:

- the computational category, functor, transfor, and directed-family layer;
- the iterated-hom architecture, which already makes every hom-category a
  category and therefore supports dimension-recursive reasoning;
- `Path_cat(A)`, including `Obj(Path_cat A) -> A`, homs as equality path
  categories, and identity as `eq_refl`;
- `Core_cat(C) := Path_cat(Obj C)` and `Core_incl_func(C)`;
- `PathOut_cat`, its contravariant source action, the canonical `rho` arrow,
  motive transport, `path_ind_sec`, and the `PathInd_*` telescope packaging;
- the ordinary primitive equality/J fallback for unstructured motives;
- decoded H0 formers, elementary eliminators, Sigma/record path interfaces,
  truncation levels, truncated packages, `CatDim`, `IsNCat`, `NCat`, and the
  current evidence-retaining package discipline;
- the runtime/proof-time distinction and existing identity-normal-form policy,
  including the refusal to reduce a Product-category identity globally to a
  pair of identities.

### Architecture that should be reopened

The following current choices should be treated as successful experiments,
not presumed permanent foundations:

- the opaque recursive `OmegaEquivAlong_D0` certificate as the primary
  mathematical representation;
- storing recursive omega-equivalence cells and later decoding them to
  equality-valued laws;
- parallel global capabilities `cat_univalence` and
  `cat_univalence_by_decoder`;
- the first-class decoder/round-trip hierarchy required only because equality
  and equivalence remain separate classifiers;
- contractible-fibre `TypeEquiv` as the primary operational representation of
  equivalence in the groupoid universe;
- finite observation trees as a substitute for a direct, understood
  fixed-arrow representation;
- treating the absence of a traditional fibrancy package as a blocker even
  when the proposed motive is already a structured directed family;
- former-specific observational-action bases whose only foundational consumer
  is a demonstration that generic `eq_ap` can be bridged to a component view;
- the conclusion that direct groupoid universe identity failed in principle,
  when the measured failure concerned a recursively transparent
  contractible-fibre representation.

### Revised interpretation of current achievements

The current Cat-universe classifier rule already demonstrates that direct
univalence can be a finite operational normal form when the equivalence
payload is stable. The `PathOut` section already has substantial component
and motive-specific computation despite being a bodyless primitive symbol.
The current `IsDiscreteCat` already contains the likely groupoidality concept
as its second field. These are not missing ideas; they need to be reorganized
under simpler owners.

## Core Mathematical Hypothesis

Let `C : Cat`, `x y : Obj(C)`, and `f : Hom_C(x,y)`. The proposed fixed-arrow
evidence is bi-invertibility with separate inverse arrows:

```text
OmegaEquivAlongEq(C,x,y,f)

left_inv(u)  : Hom_C(y,x)
right_inv(u) : Hom_C(y,x)

left_law(u) :
  left_inv(u) o f =_{Obj(Hom_cat C x x)} id_x

right_law(u) :
  f o right_inv(u) =_{Obj(Hom_cat C y y)} id_y.
```

The separate inverse choices are deliberate. At the groupoid/type level the
bi-invertible formulation is expected to make fixed-map equivalence evidence
property-valued, unlike raw single-quasi-inverse data. At higher categorical
levels the analogous theorem is an acceptance obligation, not an assumption
that may be inferred from the shape alone.

First-class equivalence initially remains:

```text
OmegaEquivEq(C,x,y)
  := Sigma f : Hom_C(x,y), OmegaEquivAlongEq(C,x,y,f).
```

The intended univalence equation is:

```text
x =_{Obj C} y  ==  OmegaEquivEq(C,x,y).
```

Because `Hom_cat C x x` and `Hom_cat C y y` are themselves categories, the
two equality-valued laws can be observed through the same univalence equation
at the next hom level. The recursion is therefore latent in equality and
revealed only through observations. It need not be materialized as a
transparent infinite Sigma tree.

For finite `NCat` levels, this interpretation descends through the explicit
dimension index. At the omega level, its mathematical reading is the usual
greatest-fixed-point/coinductive notion of recursively invertible cells. That
reading is semantic justification, not a demand to copy an external
coinductive implementation.

## Proposed Kernel Architecture

The declarations below are conceptual signatures. Exact Lambdapi syntax,
modifiers, implicit arguments, owner position, and final names must be selected
by probes. A candidate must not be promoted merely because this pseudocode is
well-typed on paper.

### A. Equality-valued fixed-arrow evidence

Introduce a staging candidate next to the current D0 owner:

```text
constant symbol OmegaEquivAlong_EQ1
  [C : Cat] [x y : Obj C]
  (f : Hom C x y) : Grpd;

symbol omega_equiv_along_left_inv_EQ1  ...;
symbol omega_equiv_along_right_inv_EQ1 ...;

symbol omega_equiv_along_left_law_EQ1
  (u : OmegaEquivAlong_EQ1 f)
  : left_inv(u) o f =_{Hom C x x} id_x;

symbol omega_equiv_along_right_law_EQ1
  (u : OmegaEquivAlong_EQ1 f)
  : f o right_inv(u) =_{Hom C y y} id_y;
```

The candidate needs explicit construction rather than unexplained observers:

```text
omega_equiv_along_intro_EQ1
  (l r : Hom C y x)
  (alpha : l o f = id_x)
  (beta  : f o r = id_y)
  : OmegaEquivAlong_EQ1 f.
```

Projection beta should expose exactly the four supplied fields. Canonical
reflexive evidence should be built through this representation or be a stable
constructor with the same observed fields:

```text
omega_equiv_along_refl_EQ1(C,x)
  : OmegaEquivAlong_EQ1(id_x).
```

No runtime eta or proof erasure is required initially. The candidate must,
however, have an explicit future extensionality/property story; otherwise it
would merely rename the current opaque certificate.

### B. Recursive omega-cells become derived views

Compatibility views corresponding to the current recursive fields should be
defined from the equality laws:

```text
omega_equiv_along_left_cell_EQ1(u)
  : OmegaEquivEq(
      Hom_cat C x x,
      left_inv(u) o f,
      id_x)

omega_equiv_along_right_cell_EQ1(u)
  : OmegaEquivEq(
      Hom_cat C y y,
      f o right_inv(u),
      id_y).
```

If equality and omega-equivalence are directly comparable, each body is an
identity/coercion view of `left_law(u)` or `right_law(u)`. Until the direct
equation is promoted, these compatibility views may temporarily use the
existing encoders. That temporary dependency must be removed before decoder
retirement is declared complete.

The reverse direction already exists conceptually in the current source:
current recursive D0 cells are decoded into `omega_equiv_left_law` and
`omega_equiv_right_law`. This provides an initial migration map from old D0
evidence to the proposed equality-valued evidence.

### C. First-class packaging fork

#### Candidate S: retain the transparent Sigma

The default first experiment is:

```text
OmegaEquiv_EQ1(C,x,y)
  := Sigma f : Hom C x y, OmegaEquivAlong_EQ1(C,x,y,f).
```

Advantages:

- minimal change from the current public API;
- ordinary Sigma introduction and elimination remain available;
- fixed-map evidence remains the sole semantic owner;
- the outer representation is finite because the evidence classifier is a
  stable head;
- existing code that packages a named arrow has a direct migration path.

Risks:

- a path silently accepted as an equivalence is not syntactically a
  `Struct_sigma`, so raw Sigma projections remain stuck;
- a transparent defined head is less convenient for selected runtime join
  rules;
- eagerly defined aliases such as `omega_equiv_to := sigma_Fst` can compete
  with shaped observer rules.

Candidate S therefore requires stable public observer owners even if their
underlying package is a Sigma.

#### Candidate R: primitive two-field first-class facade

Escalate only if Candidate S cannot provide stable joins/observers without
duplicated or nonjoining rules:

```text
constant symbol OmegaEquiv_EQ1(C,x,y) : Grpd;

omega_equiv_pack_EQ1
  (f : Hom C x y)
  (u : OmegaEquivAlong_EQ1 f)
  : OmegaEquiv_EQ1(C,x,y);

omega_equiv_to_EQ1
  (e : OmegaEquiv_EQ1(C,x,y)) : Hom C x y;

omega_equiv_evidence_EQ1
  (e : OmegaEquiv_EQ1(C,x,y))
  : OmegaEquivAlong_EQ1(omega_equiv_to_EQ1(e)).
```

with the two constructor projection betas. Candidate R is mathematically the
same dependent pair; its purpose is only to provide a stable classifier head
and observer boundary. If selected, it must also provide:

- an introduction/elimination story usable by standard-library authors;
- a comparison with the Sigma presentation;
- no unbacked runtime eta;
- computation for equality terms that cross into the record through direct
  univalence.

#### Selection gate

Retain Candidate S unless a measured candidate demonstrates at least one of:

1. the `Path_cat` classifier join cannot be stated or made operationally
   stable with the Sigma head;
2. stable `omega_equiv_to`/evidence projections on coerced paths require a
   competing alias-unfolding normal form;
3. the generic object-equality equation requires a rigid first-class head for
   acceptable performance or confluence;
4. end-user elimination of equivalence packages is materially clearer and
   more stable through Candidate R.

Do not select Candidate R merely because a record looks architecturally
cleaner in prose.

### D. Direct univalence equations

The target generic comparison is:

```text
unif_rule
  @= (Obj $C) $x $y
  == OmegaEquiv_EQ1 $C $x $y.
```

This is proof-time logical authority, not runtime normalization. It must be
classified accordingly: a typed `eq_refl` consumer proves that Lambdapi fired
the rule, not that the rule is mathematically sound.

The target runtime policy is hybrid:

- preserve or restate direct runtime equality for rigid universe owners where
  a finite normal form and joining observers are measured;
- initially use proof-time comparison for variable `C` because a generic
  runtime rule overlaps every category constructor whose `Obj` reduces;
- add shaped joins for `Path_cat` and later Product/Sigma/Functor categories
  only when an actual consumer requires them;
- do not make generic `eq_refl` runtime-reduce to a structured equivalence
  package;
- expose canonical equivalence observations of `eq_refl` through projections
  or narrow proof-time comparisons.

The already-active rigid Cat-universe rule is evidence that this policy can
produce a finite direct normal form. A redesigned Grpd-universe direct rule or
unification equation must be re-probed against the new stable payload; the
earlier transparent contractible-fibre timeout does not decide this case.

### E. Observer table: the real computational-univalence surface

Classifier comparison alone is insufficient. Terms accepted across the
equality/equivalence boundary must interact coherently with equivalence
observers. The MVP observer matrix is:

| Term/presentation | Required computation or comparison |
| --- | --- |
| `omega_equiv_pack(f,u)` | `to` returns `f`; evidence returns `u` |
| `eq_refl x` used as `OmegaEquiv(C,x,x)` | `to` exposes `id_C(x)` |
| same reflexivity | both inverse observers expose `id_C(x)` |
| same reflexivity | both law observers expose canonical reflexive/unit laws |
| `p : x =_A y` used in `Path_cat A` | `to` exposes `p` |
| same path | left/right inverse observers expose `path_sym(p)` or the selected equivalent presentation |
| same path | cancellation laws expose the selected path inverse/unit theorems |
| Product-category identity | compare with component identities proof-time; do not globally reduce generic `id` to a pair |
| equality law used as next-hom equivalence | no decoder; it is accepted directly by the classifier equation |
| non-reflexive arbitrary equivalence used by primitive `J` | typechecks as equality, but `J` need not runtime-reduce |

Every promoted classifier equation must name the observers that make its
consumer behavior meaningful. A bare unification rule with no operational
consumer is not completion.

### F. Exact `Path_cat` join

The type-correct shaped comparison is:

```text
OmegaEquiv_EQ1(Path_cat A,x,y) == (x =_A y).
```

It is not a comparison with `Path_cat(x = y)`, because both sides here are
`Grpd` classifiers. A proposed proof-time owner is:

```text
unif_rule
  OmegaEquiv_EQ1 (Path_cat $A) $x $y
  == @= $A $x $y.
```

If Candidate R supplies a stable first-class head, a runtime orientation from
`OmegaEquiv_EQ1(Path_cat A,x,y)` to `x =_A y` may also be probed. The RHS does
not syntactically reconstruct `Obj(Path_cat A)`, so the obvious direct loop is
absent. It still requires a full owner-position critical-pair audit.

The join resolves the two readings of:

```text
x =_{Obj(Path_cat A)} y:

  Obj(Path_cat A) -> A       gives x =_A y
  object univalence         gives OmegaEquiv(Path_cat A,x,y).
```

Term computation requires a canonical path-equivalence witness:

```text
path_equiv_along_EQ1(p)
  : OmegaEquivAlong_EQ1(Path_cat A,p),
```

derived by primitive path induction from reflexive evidence or supplied as a
stable field owner with a reflexive beta. Required observers include:

```text
omega_equiv_to_EQ1(p)        -> p
omega_equiv_left_inv_EQ1(p)  -> path_sym(p)
omega_equiv_right_inv_EQ1(p) -> path_sym(p).
```

### G. Internal groupoidality

The leading definition is the current `IsDiscreteCat` core-equivalence field
without object-set truncation:

```text
IsGroupoidalCat(C)
  := OmegaEquivAlong_EQ1(
       Cat_cat,
       Core_cat C,
       C,
       Core_incl_func C).
```

This says that the identity-on-objects inclusion from the equality/path core
is an omega-equivalence. Under global univalence it expresses internally that
all directed arrows are recovered from object paths/equivalences. It is not
the same as zero-dimensional discreteness.

The existing boundary should refactor conceptually to:

```text
IsDiscreteCat(C)
  == Product_grpd(IsSetGrpd(Obj C), IsGroupoidalCat(C)),
```

subject to compatibility with the active exact two-field representation.

An alternative pointwise definition,

```text
Pi x y, Pi f : Hom C x y, OmegaEquivAlong_EQ1(C,f),
```

should be compared mathematically and computationally. It may characterize
all arrows as equivalences but does not immediately supply the reusable core
inclusion functor equivalence. The core-inclusion formulation is preferred
unless the pointwise form yields a materially simpler property theorem and a
proved equivalence between the two presentations.

### H. Canonical groupoidality of path categories

Current computation gives:

```text
Core_cat(Path_cat A)
  = Path_cat(Obj(Path_cat A))
  -> Path_cat A.
```

The remaining canonical comparison is:

```text
Core_incl_func(Path_cat A)
  == id Cat_cat (Path_cat A).
```

A narrowly typed proof-time rule is the conservative candidate. A runtime
fold may be selected only if its existing object and hom projections join in
both reduction orders. Once selected, canonical groupoidality is supplied by
reflexive fixed-map evidence for the identity functor:

```text
path_cat_is_groupoidal(A)
  : IsGroupoidalCat(Path_cat A).
```

This is the canonical introduction test for the new concept. The plan should
not claim `IsGroupoidalCat` usable until this witness and at least one
non-literal consumer exist.

### I. Structured motives are the MVP fibrancy boundary

An object `E : Catd(K)` is already a functor `K -> Cat_cat`. It contains the
action, identity/composition computation, iterated hom action, and coherence
required for transport. If `K` is groupoidal, functoriality sends its
invertible arrows to equivalences of fibres. No separate abstract
"transport-exists" or general fibrancy witness is needed for this structured
MVP.

If the fibres themselves must be sets, groupoids, or finite `n`-categories,
the motive should factor through an appropriate core-universe inclusion. This
is evidence about the image objects, not a second transport mechanism.

This boundary is deliberately restrictive:

- a raw function `P : Pi x, Grpd` is not automatically a `Catd` object;
- a raw path-dependent family `P(y,p)` is not automatically functorial on
  `PathOut`;
- the standard library or a later structured-former layer must construct the
  corresponding functor when needed;
- no claim is made that this solves arbitrary HIT fibrancy or all external
  cubical composition structure.

Within this boundary, however, the missing "fibrancy" problem is concrete and
syntactic: supply a functorial motive.

### J. `PathOut` is the structured groupoidal `J`

The current `path_ind_sec` is a primitive eliminator with an operational
specification, not an inert assumption. Its component rules expose action
along the canonical `rho` arrow, and its selected motive rules fold to generic
fibre transport.

For arbitrary directed `Z`, this is a directed initiality/action principle on
the outgoing-arrow category. For groupoidal `Z`, it is the structured
functorial form of identity/path induction. The proposed policy is:

1. keep primitive `ind_eqr` for arbitrary unstructured `Grpd`-valued motives;
2. use existing `path_ind_sec`/`PathInd_*` for structured motives;
3. require `IsGroupoidalCat(Z)` only when a theorem needs symmetric/invertible
   transport or comparison with primitive equality;
4. specialize to literal `Path_cat(A)` for the first comparison with
   `ind_eqr`;
5. use the core-inclusion equivalence to extend that comparison to a general
   internally groupoidal category;
6. do not introduce another general `GroupoidalJ` primitive unless a concrete
   consumer cannot be expressed as a readable alias/specialization of
   `path_ind_sec`.

For a path-dependent motive, the structured source is already:

```text
PathOut_cat(Path_cat A,x),
```

whose objects are `(y,p)` with `p : x =_A y`. A structured motive over this
category is exactly the selected pre-arranged/functorial fragment of ordinary
`J`.

### K. Shaped motive computation

When a motive is built from Product, Sigma, constant, pullback,
representable, or another known categorical constructor, its transport should
compute through the generic `fapp*`/`tapp*` owners of those constructors.

Do not add a separate former-specific `J` calculus. Add only:

- classifier joins;
- identity/reflexivity comparisons;
- constructor projection beta;
- a narrow projection-order bridge when an existing generic owner is erased
  by normalization and a measured consumer cannot reach it;
- theorem-level semantic comparisons where neither side should be a runtime
  normal form.

This policy is the structured replacement for the current broad
`ObsAction`/fibrancy expansion track.

### L. Core-universe inclusion functors

The MVP needs actual functors, not merely carrier functions, when a universe
is used as the codomain of a structured motive. Candidate constructions are:

```text
TruncGrpdCore_cat(n)
  := Path_cat(TruncGrpdU n)

TruncGrpdCore_incl_func(n)
  : TruncGrpdCore_cat(n) -> Cat_cat

TruncGrpdCore_incl_func(n)[X]
  := Path_cat(trunc_grpd_carrier X)
```

and:

```text
NCatCore_cat(n)
  := Path_cat(NCat n)

NCatCore_incl_func(n)
  : NCatCore_cat(n) -> Cat_cat

NCatCore_incl_func(n)[X]
  := ncat_carrier X.
```

A package of general groupoidal categories may later be introduced:

```text
GroupoidalCatData := Sigma C : Cat, IsGroupoidalCat(C)
GroupoidalCatU    : Grpd

GroupoidalCatCore_incl_func
  : Path_cat(GroupoidalCatU) -> Cat_cat.
```

The object projections remain useful as the object actions of these functors.
The functors own action on package paths/equivalences.

These are core/groupoidal inclusions, not full subcategories. A full
subcategory of `Cat_cat` would inherit all functor hom-categories between
selected carriers and would require additional evidence/path bookkeeping.
That construction is not required for groupoidal motives and is deferred.

### M. Sum and other visible formers

The current four binary-Sum equality classifier rules are mathematically
appropriate and should remain in the retained H0/shaped layer:

```text
inl(a) = inl(a') -> a = a'
inr(b) = inr(b') -> b = b'
inl(a) = inr(b)  -> Empty
inr(b) = inl(a)  -> Empty.
```

The canonical proof-time reflexivity comparisons should be probed as general
former owners:

```text
eq_refl(Sum A B,inl a) == eq_refl(A,a)
eq_refl(Sum A B,inr b) == eq_refl(B,b).
```

Generic outer `eq_refl` should remain the runtime proof normal form; no
runtime proof erasure is proposed.

The current `sum_map` action bases and their four action-specific unification
bridges are not prerequisites of direct univalence or structured groupoidal
`J`. Before any retirement:

1. inventory all consumers;
2. show that structured motive/functor action or ordinary library-level
   `eq_ap` covers the intended use;
3. preserve a reviewer example if the action remains useful as a library
   theorem;
4. remove or demote only through a synchronized migration.

The same principle applies to Nat successor action and future former-specific
registrations: preserve completed evidence, but pause expansion of the
registry until the direct univalence/structured-motive architecture is
resolved.

### N. Encoder/decoder retirement

Direct equality/equivalence comparison should make most foundational
encoders and decoders identity facades:

```text
idtoequiv_cat(p) := p
equivtoid_cat(e) := e.
```

The same applies at the groupoid universe once its direct comparison is
selected. This does not mean every current symbol should be deleted at once.
The migration should classify current APIs into four groups:

1. **retained semantic owners**: fixed-arrow equivalence, projections,
   path/core action, `PathOut`, truncation and dimension data;
2. **temporary compatibility wrappers**: current encoders/decoders used while
   old and new evidence coexist;
3. **derived library theorems**: contractible-fibre `TypeEquiv`, explicit
   round trips, transport squares, and comparison theorems useful to external
   HoTT-style consumers;
4. **retirable duplicate capabilities**: global assumptions and decoder
   packages whose only role is to mediate classifiers now identified directly.

`TypeEquiv` should not necessarily disappear from the library. Contractible
fibres remain a standard theorem-level formulation of equivalence for
ordinary functions. It should cease to be the primary operational universe
identity representation.

No decoder is retired until:

- every active consumer is relocated;
- the direct classifier equation is active at the required layer;
- reflexivity and path observers compute/compare as intended;
- old-to-new and new-to-old migration examples pass;
- negative controls ensure no accidental runtime proof erasure;
- reports and examples no longer describe the decoder as foundational.

## Proposed Runtime And Proof-Time Policy

| Equation/behavior | Preferred initial owner | Reason |
| --- | --- | --- |
| `Eq(Obj C,x,y) == OmegaEquiv(C,x,y)` for variable `C` | proof-time `unif_rule` candidate | avoids selecting an infinite or overlap-heavy generic runtime normal form |
| `Eq(Obj Cat_cat,A,B) -> OmegaEquiv(Cat_cat,A,B)` | existing rigid runtime owner, re-probed with new payload | finite direct universe normal form already demonstrated |
| `Eq(Obj Grpd_cat,A,B)` versus groupoid equivalence | proof-time first; runtime candidate second | old timeout used a different transparent payload |
| `OmegaEquiv(Path_cat A,x,y) == Eq(A,x,y)` | proof-time shaped join first | resolves exact type-level diamond without forcing a runtime facade |
| same `Path_cat` join under primitive Candidate R | measured runtime candidate | stable head may permit a terminating orientation |
| `eq_refl` versus canonical equivalence package | observer projection rules and/or narrow proof-time comparison | preserve generic proof provenance |
| `Core_incl_func(Path_cat A)` versus identity functor | narrow proof-time candidate; runtime only after projection audit | canonical groupoidality introduction |
| Product identities versus component pair | proof-time comparison | preserve current identity normal-form policy |
| Sum outer/component reflexivity | two general proof-time comparisons | replace action-specific bridge proliferation |
| equality law used as recursive equivalence | silent type comparison; no decoder | central ownership reversal |

Every unification rule is trusted proof-time authority. Lambdapi performs no
sanity check on user unification rules. Every candidate therefore needs:

- a precise semantic statement;
- a typed firing test;
- a negative non-firing test;
- a runtime non-conversion control;
- an overlap and performance inventory;
- an explicit trust classification in the plan and Foundations report.

## Current-To-Proposed Migration Map

| Current owner/interface | Proposed status |
| --- | --- |
| `OmegaEquivAlong_D0(C,f)` | replace as primary representation with equality-law fixed-map evidence; retain during migration |
| public `OmegaEquivAlong` alias | preserve public role; retarget after evidence migration |
| `omega_equiv_along_left/right_inv_D0` | preserve semantics and names without staging suffix after migration |
| `omega_equiv_along_left/right_cell_D0` | become derived compatibility views of equality laws |
| `omega_equiv_left/right_law` | move from decoder-derived theorem to primary evidence projection |
| public `OmegaEquiv := Sigma f, Along(f)` | retain in Candidate S; replace by equivalent two-field facade only if selection gate fires |
| `omega_equiv_to`/`omega_equiv_evidence` transparent aliases | make stable observer owners if coerced-path computation requires it |
| `CatUnivalence`/`CatUnivalenceByDecoder` | temporary compatibility types; expected foundational retirement |
| `cat_univalence`/`cat_univalence_by_decoder` | expected retirement after direct comparison and consumer migration |
| `idtoequiv_cat`/`omega_equiv_path` | identity/coercion compatibility wrappers, then retire or retain as library aliases |
| `GrpdPathView := TypeEquiv` | replace as primary universe identity with direct omega-equivalence; retain theorem-level comparison |
| groupoid `idtoequiv`/decoder capabilities | migrate like categorical decoders after direct Grpd comparison |
| `TypeEquiv`/`IsEquivMap` | retain as library concepts; remove from primary universe normal form |
| `OmegaEquivAlongObservation_D0` and dimension views | retain as migration/debug evidence until new extensionality/property theorem; then reassess |
| `IsDiscreteCat` | conceptually factor as object-set evidence plus `IsGroupoidalCat`; preserve active compatibility |
| `Core_cat`/`Core_incl_func` | retain; add canonical `Path_cat` identity comparison |
| `path_to_hom` | retain or redefine as the forward-arrow observer of a path used directly as equivalence |
| `path_ind_sec`/`PathInd_*` | retain as primary structured directed/groupoidal induction owner |
| general fibrancy/structured-J prerequisite track | narrow to construction of structured motives and concrete shaped projection joins |
| `ObsAction`/`ObsDAction` | preserve existing evidence; demote from direct-univalence MVP pending consumer inventory |
| Sum/Nat action bases | preserve until migration; no further foundational expansion before redesign decision |
| truncation universes, `CatDim`, `IsNCat`, `NCat` | retain; add core inclusion functors as concrete consumers require |

## Dependency Structure

```text
equality-valued OmegaEquivAlong
        |
        +--> Sigma-vs-record packaging decision
        |          |
        |          +--> stable term observers
        |
        +--> old/new evidence bridges
        |
        +--> Path_cat equivalence witness and classifier join
        |          |
        |          +--> Core_incl(Path_cat) == id
        |                     |
        |                     +--> IsGroupoidalCat(Path_cat)
        |
        +--> generic/rigid direct univalence equations
        |          |
        |          +--> decoder migration/retirement
        |          +--> direct Grpd universe
        |
        +--> fixed-map evidence property/extensionality
                   |
                   +--> unconditional IsNCat object truncation

IsGroupoidalCat + existing PathOut/Catd
        |
        +--> structured groupoidal J comparison
        +--> groupoidal/truncated/NCat core-universe inclusion functors

direct univalence + structured motives
        |
        +--> simplify/demote former-specific ObsAction machinery
        +--> later reassess H2/HIT readiness
```

## Phased Implementation Plan

### Phase 0: Review, adoption, and frozen questions

Before kernel work:

1. review this proposal against the July 13 plan and active source;
2. obtain external or independent feedback on the mathematical fixed-map
   representation, groupoidality definition, and generic unification equation;
3. decide whether this report becomes the active successor, an adopted overlay,
   or a rejected experiment;
4. record the status change in `reports/INDEX.md` and the predecessor plan;
5. identify the exact current implementation slice and decide whether it is
   completed first or paused without deleting work;
6. keep all code untouched until the first owner-position candidate is ready.

Exit criterion: an explicit adoption statement and a selected first candidate
name/owner position.

### Phase 1: Equality-law fixed-arrow candidate

In a temporary full-file owner-position copy:

1. add `OmegaEquivAlong_EQ1` beside the current D0 owner;
2. add separate left/right inverse and equality-law projections;
3. add an explicit four-field introduction constructor;
4. add canonical reflexive evidence and projection computation;
5. define `OmegaEquiv_EQ1` as the outer Sigma;
6. add stable package projections and reflexive package evidence;
7. add positive and negative diagnostic assertions;
8. compare quiet, warning-enabled, subject-reduction, decision-tree, and
   strict-LHS results with baseline;
9. do not yet add generic univalence or remove current D0.

Required positive observations:

- package forward/evidence projections;
- all four evidence fields on an introduced witness;
- all four reflexive observations;
- next-hom equality laws have the exact intended classifier;
- a named fixed functor can carry evidence without first-class repackaging.

Required negatives:

- no evidence eta;
- no equality-proof erasure;
- no collapse of left and right inverse choices;
- no unintended recursive unfolding of an equality-law field;
- no direct comparison with current D0 without an explicit bridge.

Exit criterion: finite, warning-audited, subject-reducing equality-law
representation with explicit construction and observation.

### Phase 2: Packaging and stable-observer decision

Using the Phase-1 candidate:

1. test Candidate S with stable named projections on constructed packages;
2. test `eq_refl` observer behavior through a local direct classifier
   comparison;
3. test an arbitrary path in `Path_cat(A)` used as a first-class equivalence;
4. determine whether public projection aliases can remain transparent;
5. if they compete, make the projections stable before changing the
   classifier representation;
6. prototype Candidate R only if the selection gate is met;
7. compare declaration count, rewrite count, warning inventory, eliminability,
   user-facing construction, and performance.

Exit criterion: a recorded Sigma-versus-record decision with measured
evidence, not preference.

### Phase 3: `Path_cat` join and canonical groupoidality

1. define `path_equiv_along_EQ1(p)`;
2. establish reflexive computation;
3. add the proof-time classifier join
   `OmegaEquiv_EQ1(Path_cat A,x,y) == Eq(A,x,y)`;
4. add forward/inverse/law observer computation for a path used as an
   equivalence;
5. compare `Core_incl_func(Path_cat A)` with the identity functor;
6. define `IsGroupoidalCat_EQ1`;
7. construct `path_cat_is_groupoidal_EQ1(A)`;
8. add at least one nontrivial path consumer and one higher-hom observation;
9. keep runtime alternatives in probes until both reduction orders join.

Exit criterion: literal path categories satisfy internal groupoidality and
their equality/equivalence interface computes through named observers.

### Phase 4: Old/new evidence bridges

Before migration:

1. define old-D0 to equality-law evidence using the existing decoded
   `omega_equiv_left/right_law`;
2. define equality-law to old-D0 using temporary current encoders at the two
   hom-law fields;
3. compare both representations on reflexivity, Product, opposite, and one
   D0b hom-action consumer;
4. state round trips propositionally where current evidence extensionality
   permits;
5. do not assume a round trip that is blocked by current opaque evidence;
6. identify every current consumer that genuinely needs recursive cells
   rather than equality laws.

Exit criterion: a migration table backed by executable examples and an honest
list of any unproved evidence-equality direction.

### Phase 5: Direct univalence equations

1. probe the generic variable-`C` proof-time equation at owner position;
2. test typed firing, non-firing, and runtime non-conversion;
3. enumerate overlaps with `Path_cat`, Product, Sigma, Functor, and universe
   object computation;
4. preserve the shaped `Path_cat` join;
5. re-target the existing rigid Cat-universe runtime rule to the new
   representation and test self-normalization;
6. probe Grpd-universe proof-time direct identity;
7. probe Grpd-universe runtime identity only after the proof-time candidate is
   understood;
8. add the full observer matrix for reflexivity and paths;
9. record the semantic/trust classification in Foundations and the plan.

Exit criterion: one selected generic comparison, selected rigid universe
owners, and no unexplained classifier equation lacking term consumers.

### Phase 6: Decoder migration and direct use

1. change new consumers to use equality directly as `OmegaEquiv` and vice
   versa;
2. reduce `idtoequiv_cat` and `omega_equiv_path` to compatibility aliases or
   remove their foundational use;
3. migrate groupoid universe consumers away from contractible-fibre identity;
4. retain explicit `TypeEquiv` comparison theorems in the library;
5. retire duplicate global decoder capability inhabitants only after consumer
   inventory reaches zero;
6. keep round-trip theorem names only where external compatibility warrants
   them;
7. update examples to demonstrate direct projections from an equality proof.

Exit criterion: direct equality/equivalence is the primary public interface;
no foundational theorem requires an arbitrary decoder capability.

### Phase 7: Evidence extensionality/property and finite dimension

1. formulate `IsPropGrpd(OmegaEquivAlong_EQ1(C,f))`;
2. prove it first for literal path categories/groupoid functions if possible;
3. prove finite-`NCat` cases by dimension recursion using equality-valued laws;
4. compare separate-left/right evidence with current OneCat ordinary-iso
   evidence;
5. determine whether a general omega-level theorem follows from direct
   univalence and structured equality or requires an additional extensionality
   principle;
6. use the theorem to discharge the current conditional `IsNCat` object
   truncation spine where justified;
7. retain an explicit blocker if the omega-level property remains unproved.

Exit criterion: property-valuedness is either proved at the claimed scope or
is an explicit bounded blocker; no global capability is smuggled in.

### Phase 8: General groupoidal categories and structured `J`

1. promote `IsGroupoidalCat` after the `Path_cat` introduction case;
2. compare core-inclusion and pointwise-all-arrows formulations;
3. define a package only when a consumer needs it;
4. specialize `path_ind_sec` to a groupoidal source and structured motive;
5. compare the literal `Path_cat(A)` specialization with primitive `ind_eqr`
   on a pre-arranged Cat-valued motive;
6. show that transport is an equivalence through the source inverse and
   functoriality;
7. add a nonliteral groupoidal category consumer;
8. do not introduce a second eliminator if an alias of `path_ind_sec` suffices.

Exit criterion: the documented groupoidal `J` story is executable and uses
existing directed action rather than a parallel transport calculus.

### Phase 9: Core-universe inclusion functors

1. select the smallest concrete universe consumer;
2. define the corresponding `Path_cat(package universe) -> Cat_cat` functor;
3. make its object action compute to the carrier category;
4. derive arrow action from package equality/direct univalence;
5. demonstrate a structured motive factoring through it;
6. add other truncated/`NCat` core inclusions only when independently used;
7. defer full subcategories and all-functor homs.

Exit criterion: at least one groupoid-valued or finite-dimensional structured
motive uses an actual universe inclusion functor.

### Phase 10: Former-action simplification

1. inventory `ObsAction`, `ObsDAction`, Sum action, and Nat successor action
   consumers;
2. add the two general Sum reflexivity comparisons in a probe;
3. show that structured motive/functor action covers the foundational
   transport use case;
4. preserve useful `sum_map`/`eq_ap` statements as library examples;
5. retire or demote action-specific bases only after all diagnostics migrate;
6. pause new former registrations until a concrete structured-motive consumer
   cannot use generic action.

Exit criterion: the foundational kernel no longer carries action-specific
bridges merely to demonstrate a general observational-action framework.

### Phase 11: Consolidation and next-scope decision

1. remove staging suffixes only after old/new migration is closed;
2. synchronize kernel comments, checks, examples, Foundations, SOP, report
   index, health report, and catalog;
3. record final runtime/proof-time owners and trust classes;
4. re-evaluate H2/HIT readiness without assuming this redesign solves raw
   higher-inductive fibrancy;
5. decide whether the next work is evidence metatheory, standard-library
   construction, finite universes, or a representative HIT;
6. retain explicit consistency/normalization/universe-size deferrals.

Exit criterion: one coherent public equality/equivalence/groupoidal-J API and
no active duplicate foundation.

## Recommended First Implementation Slice

If this proposal is adopted, the first implementation task should be
`EVOGJ-ALONG-EQ-LAWS`, not decoder deletion, generic univalence, or Sum
cleanup.

The implementing agent should:

1. recover the active source/check/report state and inspect all current D0/D1
   consumers;
2. create a temporary owner-position full-file candidate immediately beside
   the current `OmegaEquivAlong_D0` owner;
3. add the equality-law candidate with explicit introduction, four
   projections, reflexive evidence, and the outer Sigma package;
4. add focused positive and negative assertions without changing public
   names;
5. compare warning, subject-reduction, rule-audit, performance, and decision
   tree results;
6. document whether the equality-law fields stay finite when merely typed and
   when individually observed;
7. stop before generic univalence and report the exact representation result;
8. promote only after the owner-position result and proportional full gates
   pass.

The first slice must not:

- delete or retarget current D0;
- add a broad unification rule;
- change public `OmegaEquiv` representation;
- add a decoder assumption;
- claim evidence property or extensionality;
- mix the representation experiment with Sum/ObsAction cleanup;
- reorganize the file.

This bounded slice gives the highest-value architectural evidence with the
smallest migration risk.

## Required Probe Matrix

Every architectural candidate should be evaluated against this matrix.

| Dimension | Required evidence |
| --- | --- |
| Formation | candidate classifiers and fields typecheck at owner position |
| Construction | explicit introduction and reflexive evidence are usable |
| Projection | selected fields compute on introductions/reflexivity |
| Fixed-map use | evidence can be attached to an already-named arrow without repackaging ambiguity |
| First-class use | package forward/evidence observers compute |
| Higher iteration | a law is usable at the next hom level without a duplicated recursive body |
| Path-category join | classifier and term observers agree with ordinary paths |
| Generic univalence | typed direct use works while runtime non-conversion remains classified |
| Rigid universe | self-normalization terminates for the selected representation |
| Subject reduction | proof-dependent consumers retain declared result types |
| Critical pairs | both reduction orders for every shaped join are measured |
| Performance | bounded source/check times remain within SOP thresholds |
| Trust | every unification equation has a semantic statement and negative controls |
| Reusability | an example constructs and consumes equivalence without private staging symbols |
| Migration | old/new representations interoperate on a real current consumer |

## Acceptance Criteria For The Redesigned MVP

The equality-valued omega-equivalence/groupoidal-J MVP is complete only when:

1. fixed-arrow evidence has explicit left/right inverse and equality-law
   fields;
2. evidence construction and reflexive projection computation are public and
   stable;
3. the Sigma-versus-record decision is closed by measured evidence;
4. equality of category objects is directly comparable with first-class
   omega-equivalence at the selected runtime/proof-time boundary;
5. equality laws are usable directly as next-hom equivalences without a
   decoder capability;
6. `Path_cat` has a coherent classifier join and term-observer computation;
7. `IsGroupoidalCat(Path_cat A)` is constructible;
8. at least one nonliteral internally groupoidal category is consumed;
9. structured groupoidal `J` is expressed through existing `PathOut` action;
10. primitive `ind_eqr` remains available for unstructured motives;
11. rigid Cat-universe direct equality remains finite under the new payload;
12. Grpd-universe direct identity has a selected, explicitly trusted owner;
13. foundational encoder/decoder capability duplication has been migrated or
    retired;
14. `TypeEquiv` remains available as a theorem/library formulation rather than
    the primary universe identity normal form;
15. evidence property is proved at every scope claimed by truncation results;
16. old conditional `IsNCat` truncation is discharged only where the property
    theorem supports it;
17. former-specific action bases are either justified by concrete consumers
    or demoted;
18. all changed diagnostics, examples, comments, reports, catalog, health,
    warning, audit, and CI evidence are synchronized;
19. no claim of consistency, stratification, normalization, or canonicity is
    inferred from Lambdapi acceptance alone;
20. an end-user example builds a small library construction using only public
    equality, equivalence, groupoidality, and structured-motive APIs.

## Feasibility Assessment

| Work item | Mathematical feasibility | Lambdapi feasibility | Current confidence |
| --- | --- | --- | --- |
| equality-valued fixed-arrow record | high | high | high |
| outer Sigma packaging | high | high | high |
| primitive two-field facade if needed | high | medium-high | medium-high |
| stable package/path observers | high | medium-high | medium-high |
| `Path_cat` classifier join | high | high as proof-time equation | high |
| runtime `Path_cat` join | high | representation/overlap dependent | medium |
| `Core_incl(Path_cat) == id` | high | high as narrow comparison | high |
| `IsGroupoidalCat` via core inclusion | high under global univalence | high | high |
| structured groupoidal `J` via `PathOut` | high | most machinery already active | high |
| generic variable-`C` univalence | plausible/intentional | broad unification trust and overlap risk | medium |
| rigid Cat direct identity | already operational | re-probe required after payload change | high |
| redesigned Grpd direct identity | high | proof-time high; runtime medium | medium-high |
| evidence property for groupoids/finite levels | high | medium | medium-high |
| evidence property for unrestricted omega level | plausible | may need extensionality principle | medium-low |
| unconditional finite-`NCat` object truncation | high after property theorem | medium | medium |
| core-universe inclusion functors | high | medium-high | high |
| full subcategories of `Cat_cat` | high but unnecessary for MVP | medium/large scope | deferred |
| decoder retirement | high after migration | medium due consumer breadth | medium-high |
| Sum/action simplification | high | high after inventory | high |
| normalization/model/self-universe metatheory | research | outside bounded MVP | deferred |

## Principal Risks And Mitigations

### Risk 1: a broad unification equation silently asserts too much

Mitigation: classify it as trusted logical authority; require typed firing,
negative firing, runtime non-conversion, semantic explanation, and shaped
consumer tests. Prefer rigid runtime rules and narrow joins where feasible.

### Risk 2: generic runtime object univalence overlaps every reducible `Obj`

Mitigation: begin with a generic proof-time equation; enumerate `Path_cat`,
Product, Sigma, Functor, and universe diamonds; add shaped joins only for real
consumers; do not assume one `Path_cat` join solves the whole system.

### Risk 3: the new stable evidence is still merely opaque

Mitigation: require explicit introduction, projection beta, reflexive
construction, old/new bridges, and a property/extensionality plan. An opaque
head is an operational boundary, not permission to omit its semantics.

### Risk 4: a primitive first-class record duplicates Sigma without benefit

Mitigation: Candidate S is default; Candidate R requires a measured selection
gate and an explicit Sigma comparison.

### Risk 5: fixed-arrow evidence is not proposition-valued

Mitigation: use separate left/right inverse data; prove property first at
groupoid and finite levels; do not unblock truncation through an assumed
global capability.

### Risk 6: groupoidality is conflated with discreteness

Mitigation: define `IsGroupoidalCat` independently; make `IsDiscreteCat` the
additional set-object specialization; add non-discrete groupoidal examples.

### Risk 7: structured motives are claimed to solve arbitrary fibrancy

Mitigation: state the restriction explicitly. `Catd` solves transport and
coherence only for motives supplied as functors. Raw families and HITs remain
separate.

### Risk 8: decoder retirement breaks useful theorem-level APIs

Mitigation: distinguish foundational mediators from library comparisons.
Retain `TypeEquiv`, contractible-fibre theorems, and explicit round trips where
users need them; retire only duplicate capabilities.

### Risk 9: identity/proof provenance is erased

Mitigation: preserve generic `eq_refl` and generic `id` runtime forms; use
observers and narrow proof-time comparisons; retain negative runtime controls.

### Risk 10: the redesign expands into a new giant parallel layer

Mitigation: use `_EQ1` only in probes; promote one owner at a time; migrate and
delete compatibility code before beginning unrelated new former/HIT work.

## External/Independent Review Questions

The next review should answer or sharpen these questions before adoption:

1. Is equality-valued bi-invertibility sufficient as the primary omega-level
   equivalence structure in the intended strict/lax Emdash semantics?
2. Does the separate-left/right formulation support the required
   property-valuedness theorem at unrestricted omega level, or is a small
   coherence/extensionality field missing?
3. Is `IsGroupoidalCat(C) := EquivAlong(Core_incl_func C)` exactly the desired
   internal groupoidality notion under global univalence?
4. Should a pointwise "every arrow is an equivalence" formulation be retained
   as a theorem, alternate interface, or primary definition?
5. Is Candidate S sufficient when stable named observers replace raw Sigma
   projection use on coerced paths?
6. What exact evidence would justify Candidate R?
7. Should generic object univalence be one broad proof-time rule, a family of
   rigid/shaped rules, or an explicit `ObjEquiv` facade?
8. Can the direct Grpd-universe equation be a runtime rewrite with the new
   payload, or should it remain proof-time?
9. What is the minimal complete observer interface for a path used as an
   equivalence?
10. Does `Core_incl_func(Path_cat A)` admit a safe runtime fold to identity, or
    should the comparison stay proof-time?
11. Is the existing `path_ind_sec` operational specification sufficient as
    the primitive structured eliminator, or is one missing naturality/eta law
    required by a concrete groupoidal consumer?
12. Which current decoder/round-trip APIs are valuable library theorems after
    they cease to be foundational?
13. Which current `ObsAction` consumers survive once structured motives own
    transport?
14. What finite semantic model or stratified approximation is the best sanity
    check for the generic univalence equation without becoming an
    implementation template?

## Side-Task Ledger

All rows are proposed/unstarted until adoption. Completed predecessor work is
recorded in the July 13 ledger and should not be duplicated here.

| Task ID | Initial status | Purpose | Dependency | Status-changing result |
| --- | --- | --- | --- | --- |
| `EVOGJ-ARCH-REVIEW` | proposed | independent/external review and adoption decision | this report | explicit adopt/revise/reject statement |
| `EVOGJ-ALONG-EQ-LAWS` | proposed first implementation slice | equality-valued fixed-arrow representation | adoption | owner-position candidate passes proportional gates |
| `EVOGJ-PACKAGING-FORK` | blocked on first slice | select Sigma or primitive facade | equality-law candidate | measured selection decision |
| `EVOGJ-STABLE-OBSERVERS` | blocked on packaging | define package/reflexivity/coerced-path observations | packaging candidate | complete observer matrix |
| `EVOGJ-PATH-CAT-JOIN` | blocked on observers | identify path-category equivalence with path equality | equality-law package | typed join and term computation |
| `EVOGJ-PATH-CAT-GROUPOIDAL` | blocked on join | prove `IsGroupoidalCat(Path_cat A)` | path join/core identity | canonical witness and consumer |
| `EVOGJ-OLD-NEW-BRIDGE` | blocked on equality-law candidate | migrate current D0 evidence | candidate plus current decoder | executable bridges and honest round-trip status |
| `EVOGJ-DIRECT-UNIV-GENERIC` | blocked on path join | generic object equality/equivalence comparison | stable package and joins | selected trusted owner |
| `EVOGJ-DIRECT-UNIV-CAT` | blocked on candidate | retarget rigid Cat direct rule | equality-law package | finite self-normalization and observer checks |
| `EVOGJ-DIRECT-UNIV-GRPD` | blocked on candidate | replace finite TypeEquiv view as primary identity | stable package | selected proof-time/runtime owner |
| `EVOGJ-DECODER-MIGRATE` | blocked on direct equations | remove foundational decoder dependency | direct universe and generic owners | zero foundational decoder consumers |
| `EVOGJ-EVIDENCE-PROP` | blocked on representation | prove fixed-map evidence property | equality-law evidence | scoped theorem or blocker |
| `EVOGJ-NCAT-TRUNC` | blocked on property | discharge conditional object truncation | evidence property | unconditional theorem at justified scope |
| `EVOGJ-GROUPOIDAL-CAT` | blocked on path witness | general internal groupoidality | path-category introduction | nonliteral consumer |
| `EVOGJ-GROUP-J` | blocked on groupoidality | structured groupoidal `J` comparison | groupoidal category and PathOut | executable comparison with primitive J |
| `EVOGJ-UNIVERSE-CORE-INCL` | blocked on direct equality/groupoidality | actual package-core functor into `Cat_cat` | selected concrete motive | one used inclusion functor |
| `EVOGJ-SUM-SIMPLIFY` | blocked on direct/structured architecture | replace action-specific bases with general reflexivity joins/library action | consumer inventory | synchronized migration |
| `EVOGJ-OBSACTION-SCOPE` | blocked on structured motive evidence | decide remaining role of action registry | groupoidal J and former consumers | retain/demote decision |
| `EVOGJ-H2-READINESS` | deferred | reassess representative HIT/truncation reflector | consolidated MVP | new bounded plan or continued deferral |
| `EVOGJ-METATHEORY` | deferred research | consistency, normalization, stratification, semantic model | mature architecture | separate research evidence |

## Validation And Synchronization Protocol

Implementation must follow `AGENTS.md` and the current SOP. In particular:

- inspect staged and unstaged changes separately on every continuation;
- relocate symbols with `rg`; never rely on the line numbers in this report;
- probe nontrivial rewrite/unification changes in temporary owner-position
  full-file copies;
- preserve inferred slots unless a measured audit justifies change;
- keep checks bounded to the repository timeout policy;
- classify `unif_rule` as proof-time authority, never runtime computation;
- validate unification-rule firing with typed equality and retain conversion
  negatives;
- test both reduction orders for every shaped join;
- compare warning inventories rather than using raw counts as a semantic veto;
- add focused positive and negative checks for every promoted owner;
- run `make check` for inner-loop promotion, `make examples` for reviewer
  milestones, catalog/health/warning/audit gates after architectural changes,
  and `make ci` before substantive handoff;
- update this ledger, the active master plan status, Foundations, SOP, examples,
  catalog, and health report whenever a conclusion changes;
- do not combine semantic migration with file splitting or unrelated cleanup.

## Completion And Blocker Policy

This proposal is complete as a design document when its review questions,
phases, migration map, trust boundaries, and first slice are explicit. That
does not mean its implementation is complete.

The implemented redesign is complete only when the MVP acceptance criteria
are met and old/new duplicate foundations have been reconciled. A difficult
or slow proof is not a blocker. A blocker must name:

- the exact desired term/rule/theorem;
- the smallest failing owner-position probe;
- whether failure is typing, subject reduction, nontermination, overlap,
  performance, representation, or missing mathematics;
- the prerequisite that would change the result;
- any independent dependency-ready work that remains.

Deferred metatheory is not a blocker to the bounded operational MVP unless a
claim of consistency, normalization, stratification, or canonicity becomes a
required deliverable.

## Future Implementation Handoff Requirements

After the next review/refinement turn, the implementation handoff prompt
should instruct a new coding agent to:

- read this proposal together with the July 13 master plan and active
  authorities;
- treat the new report as the selected re-redesign overlay only if its status
  has been changed to adopted;
- implement rather than merely review;
- begin with the dependency-ready ledger row, normally
  `EVOGJ-ALONG-EQ-LAWS`;
- preserve all committed work and use commit `7724110...` only as review
  provenance;
- keep source, checks, examples, reports, catalog, health, warnings, audit, and
  CI evidence synchronized;
- revise the plan when owner-position evidence invalidates a decision;
- continue safe plan-scoped work until completion or a documented hard
  blocker, without using that persistence instruction to broaden scope.

The exact `/goal` handoff text should be generated only after the next review
has resolved the plan's initial adoption status and any externally identified
corrections.
