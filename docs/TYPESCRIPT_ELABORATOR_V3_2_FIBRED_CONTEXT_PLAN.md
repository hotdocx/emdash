# TypeScript Fibred-Context And Displayed-Product Usability For emdash v3.2 — Living Sub-Plan

Date: 2026-07-27
Plan-ID: TS-ELAB-V3.2-FIBRED-CONTEXT
Depends-On:
[`TYPESCRIPT_ELABORATOR_V3_2_USABILITY_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_USABILITY_PLAN.md),
approved H-01/D-007 dependent-first semantics, approved
H-DTTLF-USABILITY-DEPENDENT/D-DTTLF-USABILITY-003, and completed
USABILITY-DEPENDENT-1A
Status: active implementation sub-plan; the corrected architectural direction
is user-accepted, FIBRED-PLAN-0 and the read-only FIBRED-PRODUCT-0A authority
probe are complete, FIBRED-CONTEXT-0A's dependency-analysis foundation is
complete, FIBRED-CONTEXT-0B's categorical representation adapter is complete,
FIBRED-PRODUCT-0B's three-way owner-position comparison and immutable proposal
are complete, FIBRED-PRODUCT-1A awaits the exact
H-DTTLF-USABILITY-02/D-DTTLF-USABILITY-004 decision,
FIBRED-COMPREHENSION-0A/0B's semantic audit, three-way owner-position
comparison, and immutable proposal are complete,
FIBRED-COMPREHENSION-1A awaits the separate exact
H-DTTLF-USABILITY-02/D-DTTLF-USABILITY-005 decision, and no proposed Lambdapi
owner or rule is active before its corresponding approval
Infinity-Codex-Decision-Responses:
`infinity-codex:019f9243-9fba-7c73-861b-ff4eacf0c56c:019fa4cd-724e-7cc0-8f16-a32c82870ef1`
and
`infinity-codex:019f9243-9fba-7c73-861b-ff4eacf0c56c:019fa4fb-cd38-7ac1-87dc-829f004f77f5`
Human-Decision-Record: on 2026-07-27 the user accepted the consolidated
displayed-binder and corrected fibred-sibling analyses, requested this
dedicated plan and continued implementation, and separately cautioned that a
generic total-category pullback must not be assumed
FIBRED-CONTEXT-0A implementation checkpoint:
`d25ddb349e97dc0629cd6bc1aa941e1cc200066e`
FIBRED-CONTEXT-0B implementation checkpoint:
`569ebac0c8eaaeaaec63f93bde02fd91f50864f9`
FIBRED-PRODUCT-0B proposal checkpoint:
`ec5d87f2b3cfe298fd5272456740f35428f65925`

## Purpose And Exact Outcome

This sub-plan closes the next end-user-usability architecture question left
open by the completed first-order categorical frontend:

- general ordered dependent telescopes must remain expressible;
- variables that are independent siblings over a common dependent base must
  receive a complete fibrewise-cartesian structural treatment;
- convenient displayed functor and displayed transfor binders must elaborate
  through active directed-DTT semantics rather than pointwise TypeScript-only
  shortcuts; and
- the frontend must retain enough dependency information to choose, compare,
  and transport sequential Sigma and grouped fibrewise-product
  presentations.

The plan does **not** assume that ordinary and displayed lowering use either
one implementation function or two. It selects the natural,
authority-correct, scalable/generalizable solution and allows shared generic
dependency machinery plus authority-specific lowerers wherever the evidence
requires them.

This is an implementation continuation, not a request to redesign the
outer dependent LF, the backend-neutral explicit Core, or the completed
ordinary bracket compiler. It also does not resume bulk Lambdapi acquisition,
select a string parser, promote a browser profile, or complete the deferred
groupoidal-DTT specialization.

## Consolidated Correction: Dependency Edges Versus Fibred Siblings

The decisive distinction is between exchange across a genuine dependency
edge and exchange of sibling variables sharing a dependency base.

Let:

```text
Δ := Γ, a : A
B, C : Catd Δ.
```

The dependency graph for:

```text
Γ, a : A, b : B(a), c : C(a)
```

is:

```text
    a
   / \
  b   c
```

The sequential context is more precisely:

```text
Δ.B.(πB* C),
```

because the family `C` over `Δ` is pulled back along the projection
`πB : Δ.B -> Δ` before introducing `c`. It should be related to a grouped
presentation:

```text
Δ.(B ×Δ C),
```

where the desired displayed product has fibres:

```text
(B ×Δ C)[a] = B[a] × C[a].
```

For this sibling case, weakening, pairing, symmetry, diagonal, associativity,
and terminal-unit structure are meaningful fibrewise operations:

- either sibling can be discarded by a displayed projection;
- two sibling terms can be paired;
- the siblings can be exchanged by fibrewise symmetry;
- a single sibling can be duplicated by a fibrewise diagonal when the
  classifiers agree after reindexing; and
- a larger independent sibling block can be grouped by iterated products.

By contrast, in:

```text
Γ, a : A, b : B(a), c : C(a,b),
```

the graph contains `a -> b -> c`. The family `C` is not a family over
`Γ.A` alone. There is no general `B × C` over that prefix and no blanket
exchange of `b` and `c`.

The corrected structural rule is therefore:

> Arbitrary dependent telescope entries are not freely permutable. Variables
> with no dependency path between them can be exchanged with the required
> classifier and suffix transport, and variables that are siblings over a
> common dependent base admit a coherent fibrewise-cartesian structural
> package.

This distinction is inherited from ordinary dependent type theory. The
categorical setting adds explicit object/arrow/higher-cell action and
therefore needs owner-backed directed computations, but it does not require a
second, incompatible notion of dependency.

## Two Complementary Foundations

The displayed contextual frontend needs both of these structures.

### Comprehension/Sigma structure for genuine dependency

For `A : Catd Γ`:

```text
Γ.A  := Sigma_cat A
wk_A := Sigma_proj1_func A.
```

The general dependent-telescope path uses:

- `Sigma_cat` for context extension;
- `Sigma_proj1_func` for weakening/projection;
- `Pullback_catd` and `Pullback_catd_func` for family substitution;
- `section_pullback_func` for section substitution;
- a qualified contextual-pairing map
  `⟨σ,t⟩ : Δ -> Sigma_cat A`; and
- dependency-sensitive exchange and contraction only where the relevant
  reindexing makes them well typed.

The active kernel does not yet package the complete general
comprehension-pairing and Sigma-introduction arrow-action story. The audit of
that gap remains a required later row; the frontend must not manufacture it.

### Cartesian structure in each fibre for independent siblings

For `B,C : Catd K`, the provisional package is:

```text
Product_catd B C : Catd K
```

with intended computations:

```text
Fibre_cat (Product_catd B C) k
  ↦ Product_cat (Fibre_cat B k) (Fibre_cat C k)

catd_transport_func (Product_catd B C) p
  ↦ Product_map_func
      (catd_transport_func B p)
      (catd_transport_func C p).
```

Its structural maps should be genuine displayed functors:

```text
projL : Functord (Product_catd B C) B
projR : Functord (Product_catd B C) C

pair  : Functord E B
      → Functord E C
      → Functord E (Product_catd B C)

swap  : Functord
          (Product_catd B C)
          (Product_catd C B)

diag  : Functord B (Product_catd B B).
```

The terminal displayed family:

```text
Const_catd K Terminal_cat
```

supplies the fibrewise unit and a terminal presentation of weakening.
Reindexing should preserve the package in the exact runtime or proof-time
orientation selected by an owner-position audit:

```text
σ*(Product_catd B C)
  ≡ Product_catd (σ*B) (σ*C).
```

No separate unrelated `weakd`, `symd`, and `diagd` theory should be invented.
If stable names are needed, they form one product/comprehension package whose
higher behavior is inherited from generic categorical action wherever the
active authority supports it.

## `Product_catd`, Product Normalization, And The Stable-Head Question

The active v3.2 kernel has no declaration named `Product_catd` or
`Productd_catd`. It does contain:

- `Product_cat`, its projections, pairing, swap, identities, and
  componentwise hom action;
- the ordinary codomain normalization:

  ```text
  Functor_cat X (Product_cat A B)
    ↦ Product_cat (Functor_cat X A) (Functor_cat X B);
  ```

- paired product-valued functors;
- `Product_map_func(F,G)` with object, full-hom, and capped-arrow action;
- the internalized `Product_cat_func`; and
- curry/uncurry plus generic composition.

The user's proposed analogy is meaningful, but its displayed-level spelling
must be type correct. `Product_catd B C` is a family `K -> Cat`, not itself a
category. The direct fibre consequence is:

```text
Functor_cat X (Fibre_cat (Product_catd B C) k)
  ↦ Product_cat
      (Functor_cat X (Fibre_cat B k))
      (Functor_cat X (Fibre_cat C k)).
```

The corresponding family-level classifier comparison is provisionally:

```text
Functord_cat E (Product_catd B C)
  ≡ Product_cat
      (Functord_cat E B)
      (Functord_cat E C).
```

That comparison is desirable because it makes displayed projection and
pairing structure visible to elaboration, but this plan does not yet choose
runtime rewriting, proof-time comparison, or derivation. The owner audit must
check subject reduction, projection iteration, higher hom action,
reindexing, and critical pairs before selecting an orientation.

### FIBRED-PRODUCT-0A probe result

A bounded ignored Lambdapi probe constructed the obvious transparent
candidate:

```text
Product_catd_probe(B,C)
  := uncurry(Product_cat_func) ∘ ⟨B,C⟩.
```

The probe established:

```text
Fibre_cat (Product_catd_probe B C) k
  ≡ Product_cat (Fibre_cat B k) (Fibre_cat C k)
```

by ordinary runtime conversion.

It also established the required negative:

```text
catd_transport_func (Product_catd_probe B C) p
  ≢ Product_map_func
      (catd_transport_func B p)
      (catd_transport_func C p)
```

under the current active reductions. The reason agrees with the kernel's
existing boundary: the transfor/hom action of semantic uncurry depends on a
higher arrow action of `Product_cat_func` that is deliberately deferred.

The successful probe is:

```text
emdash2/tmp/probes/typescript_usability_fibred_product_0a.lp
```

and its successful local log is
`emdash2/logs/probes/typescript_usability_fibred_product_0a-20260727-163429.log`.
Both paths are ignored experiment evidence; the result is durably recorded
here rather than making ignored files an authority.

This rules out claiming that the transparent alias already supplies the
required directed product. It leaves two principled implementation routes:

1. complete the generic higher action needed by `Product_cat_func` and
   semantic uncurry, then retain a transparent `Product_catd` facade if all
   computations and critical pairs join; or
2. add a narrow stable `Product_catd` semantic head with owned fibre and
   base-arrow projections, deriving its projections/pair/swap/diagonal from
   existing generic structure where possible.

A hybrid semantic definition plus one narrow stable transport facade is also
admissible if the owner-position probe demonstrates that it is the smallest
coherent boundary. The next product row must compare these routes. It may not
choose a primitive merely for notation, and it may not force the general
uncurry action solely to make one demo pass.

### FIBRED-PRODUCT-0B owner-position comparison result

The bounded full-file comparison has now resolved the first consumer more
narrowly than either original endpoint. All three candidates use or reproduce
the same intended family:

```text
P(B,C)
  := uncurry(Product_cat_func) ∘ Struct_sigma(B,C)
  : Catd K.
```

The required first two computations are:

```text
Fibre_cat (P(B,C)) k
  ≡ Product_cat (Fibre_cat B k) (Fibre_cat C k)

catd_transport_func (P(B,C)) p
  ≡ Product_map_func
      (catd_transport_func B p)
      (catd_transport_func C p).
```

The owner-position measurements are:

| Candidate | Kernel presentation | New declarations/rules | Result | Warning inventory |
| --- | --- | --- | --- | --- |
| broad generic product off-diagonal | transparent semantic composite plus unrestricted `(F * 1)[G] -> Product_map_func(F,G)` | 0 declarations, 2 runtime rules | fibre and transport pass, but the broad action meets three unjoined naturality/higher-action cuts | `1013/159`, delta `+3/0` |
| stable `Product_catd` head | new injective family head with direct fibre and transport projections | 1 declaration, 2 runtime rules | fibre and transport pass, but semantics are duplicated and reindexing/full base-two-cell action are still absent | `1015/159`, delta `+5/0` |
| narrow shared-base existing-owner projection | transparent semantic composite plus a generic Cat-valued postcomposition action and a product fold requiring two actions over the same base arrow | 0 declarations, 2 runtime rules | fibre and componentwise transport pass with the smallest tested boundary | `1010/159`, delta `0/0` |

The five extra stable-head critical pairs comprise two fibre-projection
overlaps, an identity-transport overlap between `Product_map_func(id,id)` and
`id_func`, and two naturality transport overlaps. The three broad-rule
critical pairs are the unrestricted product off-diagonal action meeting
existing naturality and still-deferred higher action. These are not treated
as mere warning-count objections: they identify semantic closure that the
first grouped-sibling consumer does not require and that this tranche cannot
yet join.

The selected candidate retains the transparent semantic family and proposes
exactly these existing-owner runtime projections:

```text
// Cat-valued represented postcomposition, at hom_postcomp_fapp0:
(E[p] ∘ G)[q]
  ↦ E[p][G[q]]

// Product action, at Product_cat_fapp1_fapp0_functord:
(B[p] * 1)[C[p]]
  ↦ Product_map_func(B[p],C[p])
```

The second left-hand side is deliberately restricted to
`B[p]` and `C[p]` arising as `fapp1_fapp0` actions of two Cat-valued families
over the same `K`, endpoints, and base arrow `p`. It is not the unrestricted
`(F * 1)[G]` fold. The first rule supplies the capped action needed while
semantic uncurry traverses represented postcomposition; the second exposes
the already stable componentwise `Product_map_func` transport.

This result changes the provisional `Product_catd` recommendation:

- no active `Product_catd` primitive or injective head is needed for the
  first consumer;
- no notation-only Lambdapi alias is needed;
- a readable TypeScript displayed-product surface operation may lower
  directly to the explicit transparent composite;
- the returned `Product_map_func` already has active object, full-hom, and
  capped-arrow action, so downstream consumers can iterate that stable head;
  and
- the full base-two-cell action of the *family*, arbitrary off-diagonal
  product action, and their naturality closure remain separately
  unqualified.

The bounded negative corpus is equally important:

```text
opaque E
  ≢ P(B,C)

Functord_cat E (P(B,C))
  ≢ Product_cat (Functord_cat E B) (Functord_cat E C)

Pullback_catd (P(B,C)) F
  ≢ P(Pullback_catd B F, Pullback_catd C F).
```

The first two negatives prevent a global family or classifier collapse. The
`Functord_cat` product comparison should be derived later from qualified
displayed projections and pairing functors, not installed as a global
runtime conversion. The pullback comparison did not convert at runtime, and
an explicit proof-time reflexivity attempt also failed: existing unification
does not currently establish it. Reindexing stability therefore remains a
separate owner-or-proof-time audit rather than an inferred side effect.

The final narrow probe passes quietly and with warnings enabled. Its strict
LHS audit reports zero unreviewed reconstructible slots and retains the
active 45 annotated slots across 27 intentional clauses. The warning-enabled
inventory is exactly the active `1010` unjoinable critical pairs plus `159`
replaceable-pattern warnings. The relevant ignored evidence is:

```text
emdash2/tmp/probes/
  typescript_usability_fibred_product_0b_generic_projection.lp
  typescript_usability_fibred_product_0b_stable_head.lp
  typescript_usability_fibred_product_0b_narrow_projection.lp

emdash2/logs/probes/
  typescript_usability_fibred_product_0b_narrow_projection-20260727-174145.log
  typescript_usability_fibred_product_0b_narrow_projection-20260727-174148.log
```

These ignored files remain experimental evidence, not authority. The durable,
deep-frozen, non-authorizing proposal is
`src/v3_2/categorical_fibred_product_proposal.ts`; its five focused tests are
in `tests/v3_2_categorical_fibred_product_proposal_tests.ts`.

The selection is now exact but not active: adding the two Lambdapi rules,
transferring their minimal closure, and lowering the first grouped-sibling
transport are FIBRED-PRODUCT-1A and require
H-DTTLF-USABILITY-02/D-DTTLF-USABILITY-004 approval.

## Comprehension And Contextual Pairing Owner Audit

FIBRED-COMPREHENSION-0A/0B has now isolated the missing computational
boundary for a genuinely dependent context extension. For:

```text
F : Functor A K
E : Catd K
s : Obj(Pi_cat(Pullback_catd E F)),
```

the desired contextual substitution is:

```text
⟨F,s⟩ : Functor A (Sigma_cat E)
⟨F,s⟩[a] = (F[a],s[a])
⟨F,s⟩[p] = (F[p],s[p]).
```

This is the categorical comprehension map needed to substitute both objects
and arrows into a further family:

```text
D : Catd (Sigma_cat E)
Pullback_catd D ⟨F,s⟩ : Catd A.
```

### Active ingredients and the exact missing boundary

The active kernel already provides:

- `Pullback_catd E F`, the asymmetric reindexing of a family;
- `Pullback_catd_func F`, its family-level functor;
- `sigma_map_func η`, the total map of a displayed functor over one fixed
  base;
- `Sigma_cat E` and `Sigma_proj1_func E`;
- `section_pullback_func F E`; and
- `sigma_intro_transf E`, the fibrewise inclusion into the constant total
  category.

Those ingredients establish the semantic shape, but they do not provide the
base-changing total map:

```text
Sigma_cat(Pullback_catd D F) -> Sigma_cat D.
```

That map is the Grothendieck totalization of the already-active asymmetric
family pullback. It is **not** a pullback of arbitrary total-category
functors and does not introduce a generic categorical pullback.

### FIBRED-COMPREHENSION-0A semantic route

A zero-owner route can be typed using the pullback of
`sigma_intro_transf E` and the section `s`. It is useful semantic evidence:

```text
pullback_F(sigma_intro_transf E) ∘ s
  : Functor A (Sigma_cat E).
```

Under the current reductions, however, its ordinary consumers remain stuck:

- object evaluation does not expose `(F[a],s[a])`;
- arrow evaluation does not expose `(F[p],s[p])`;
- an explicit constant-family displayed component folds back to the same
  stuck ordinary evaluation; and
- first projection does not expose `F`.

It therefore cannot serve as the computational elaboration target for the
first end-user dependent chain without adding a broader commuting-conversion
closure.

### FIBRED-COMPREHENSION-0B three-way comparison

The full-file owner-position comparison measured:

| Candidate | New declarations/rules | Consumer result | Warning inventory |
| --- | --- | --- | --- |
| semantic Sigma-introduction composite | 0 declarations, 0 rules | type correct, but object, arrow, substitution, and projection consumers remain stuck | `1010/159`, delta `0/0` |
| direct specialized `sigma_pair_func(F,E,s)` | 1 declaration, 3 runtime rules | object, arrow, substitution, and whole first projection compute | `1012/159`, delta `+2/0` |
| asymmetric pullback-total owner | 1 declaration, 2 runtime rules | object, arrow, pointwise projection, and object/arrow substitution compute through a transparent contextual-pair composite | `1010/159`, delta `0/0` |

The direct pair's arbitrary-arrow rule intersects the generic identity action
in two unjoined cuts. More importantly, a dedicated pair owner packages one
special consumer instead of exposing the reusable base-change operation that
also applies to later substitutions and displayed constructions.

The selected prospective owner is:

```text
injective symbol sigma_pullback_total_func [A K : Cat]
  (F : Functor A K)
  (D : Catd K)
  : Functor
      (Sigma_cat (Pullback_catd D F))
      (Sigma_cat D).
```

It requests exactly two runtime projections:

```text
sigma_pullback_total_func(F,D)[(a,u)]
  -> (F[a],u)

sigma_pullback_total_func(F,D)[(p,alpha)]
  -> (F[p],alpha).
```

The object rule owns total-object evaluation near the Sigma-map package. The
structured-arrow rule is placed after the active capped
`Pullback_catd` transport rule; placing it before that cut failed subject
reduction because the source endpoint was not yet computationally visible.
Its left-hand side is restricted to a structured Sigma arrow, so it does not
compete with arbitrary ordinary arrows.

### Transparent contextual pairing

No dedicated contextual-pair owner is required. Define the pair as the
following explicit three-factor composite:

```text
A
  -> Sigma_cat(Const_catd A Terminal_cat)
  -> Sigma_cat(Pullback_catd E F)
  -> Sigma_cat E.
```

The factors are:

```text
terminal_total_A
  := Struct_sigma
       (id_func A)
       (Const_func A Terminal_cat Terminal_obj)

sigma_map_func(s)

sigma_pullback_total_func(F,E).
```

This reuses `sigma_map_func` for the section's same-base lax displayed action
and uses the new owner only for base change. The resulting composite computes:

```text
⟨F,s⟩[a] = (F[a],s[a])
⟨F,s⟩[p] = sigma_arrow(E,F[p],s[p]).
```

For every further `D : Catd(Sigma_cat E)`, both selected substitution
consumers compute:

```text
(Pullback_catd D ⟨F,s⟩)[a]
  = D[(F[a],s[a])]

(Pullback_catd D ⟨F,s⟩)[p]
  = D[(F[p],s[p])].
```

First projection computes pointwise. The whole-functor equation:

```text
Sigma_proj1_func(E) ∘ ⟨F,s⟩ = F
```

is deliberately **not** added as a runtime beta in this tranche. An opaque
total functor also does not collapse to the proposed owner.

### Sigma-introduction arrow action remains separate

The deferred direct component action:

```text
sigma_intro_tapp0_func(E,k)[alpha]
  -> sigma_arrow(E,id_k,alpha)
```

is not needed by the selected contextual-pair factorization. A separate
full-file subexperiment made that rule compute but changed the inventory from
`1010/159` to `1020/160`: ten new critical pairs and one replaceable pattern.
The overlaps cover generic identity action, off-diagonal naturality,
precomposition, postcomposition, and composition/higher action.

That evidence does not say the mathematical action is invalid. It says its
runtime closure is substantially broader than the first comprehension
consumer and must be qualified separately. It is not bundled into
D-DTTLF-USABILITY-005.

### Architectural consequence and remaining boundary

This result is stronger than a one-off demo:

- the frontend dependency graph supplies the general telescope shape;
- active `Pullback_catd` supplies substitution of families;
- active `sigma_map_func` supplies fixed-base totalization;
- the proposed pullback-total owner supplies the one missing base-change
  boundary; and
- contextual pairing remains a backend-neutral explicit Core composite.

The design is therefore mechanically reusable for arbitrary first-order
genuine dependent chains at the object/base-arrow level. It does not yet
graduate all displayed binding: displayed product structural maps,
full higher-cell action, direct `:^fd`/`:^nd` abstraction, the deferred
Sigma-introduction action, and groupoidal closure remain later rows.
FIBRED-PRODUCT's D-004 decision remains independent; after both approved
implementations, grouped siblings and sequential comprehension can compose
without assuming a total-category pullback.

The final selected quiet and warning-enabled probes pass with strict LHS
audit `0/45/27`. The relevant ignored evidence is:

```text
emdash2/tmp/probes/
  typescript_usability_fibred_comprehension_0a.lp
  typescript_usability_fibred_comprehension_0b_direct_pair.lp
  typescript_usability_fibred_comprehension_0b_base_change.lp

emdash2/logs/probes/
  typescript_usability_fibred_comprehension_0b_direct_pair-20260727-181305.log
  typescript_usability_fibred_comprehension_0b_direct_pair-20260727-181314.log
  typescript_usability_fibred_comprehension_0b_base_change-20260727-181402.log
  typescript_usability_fibred_comprehension_0b_base_change-20260727-181411.log
```

These ignored files are experiment evidence, not authority. The durable,
deep-frozen, non-authorizing proposal is
`src/v3_2/categorical_comprehension_proposal.ts`; its focused tests are in
`tests/v3_2_categorical_comprehension_proposal_tests.ts`.

The selection is exact but not active. FIBRED-COMPREHENSION-1A requires
H-DTTLF-USABILITY-02/D-DTTLF-USABILITY-005 approval.

## Total-Category Comparison Is A Theorem Boundary, Not An Assumed Rewrite

The semantic slogan:

```text
Sigma_cat (Product_catd B C)
  ≃ Sigma_cat B ×K Sigma_cat C
```

explains the relationship between grouped and sequential contexts, but the
right-hand `×K` is **not** currently a generic active computational owner.

In particular, active `Pullback_catd E F` is asymmetric: it reindexes a
Cat-valued family `E` along a functor `F`. Its computational behavior relies
on the family/fibration presentation. It is not a symmetric pullback
constructor for arbitrary functors
`Sigma_cat B -> K <- Sigma_cat C`.

Therefore this plan:

- does not postulate a generic categorical pullback or a rewrite using
  notation `×K`;
- first compares sequential and grouped contexts through the explicit
  Sigma projections, family pullbacks, displayed product projections, and
  contextual pairing maps;
- treats any total-category equivalence as a later theorem/conformance row;
  and
- requires a separate Lambdapi owner-position design if a computational
  total pullback/comma construction becomes a concrete consumer.

This boundary does not weaken the fibrewise-product architecture. The
frontend can elaborate sibling grouping and structural maps directly at the
displayed-family level without first internalizing a generic total-category
pullback.

## Displayed Binder Taxonomy And Semantic Lowering

Binder spelling does not map one-to-one to kernel owners. The frontend tracks
at least these orthogonal axes:

- outer-LF versus categorical abstraction layer;
- plicity;
- variation capability (`object-only`, functorial, natural, or a later
  qualified capability);
- covariance/contravariance;
- cell level; and
- ordinary versus displayed dependency.

Consequently:

- outer LF `λ x : A. t` is checked against an LF `Π` and lowers to
  `KernelLambda`;
- ordinary `λ a :^f A. t` is convenient functorial categorical abstraction;
- `k :^n K` means natural/indexed variation and is not specifically a binder
  for `Transf_cat`; and
- provisional `:^fd` and `:^nd` are useful surface constraints/sugar, not new
  primitive Core binder kinds.

A displayed-functor abstraction:

```text
λ a :^fd E. body
```

semantically hides a telescope like:

```text
λ (k :^n K; a :^f E[k]). body[k,a].
```

It must produce fibre-arrow and base-arrow coherence, not merely a pointwise
object function. The active Sigma/Pi comparison gives the principled route:

```text
Pi_cat
  (Sigma_cat E)
  (Sigma_proj1_pullback_catd E D)
≡ Functord_cat E D
```

at proof time. The corresponding next-hom comparison reaches
`Transfd_cat`. Thus direct:

```text
λ a :^fd E. ...
```

and nested:

```text
λ k :^n K. λ a :^f E[k]. ...
```

may check against compatible stable classifier presentations. The frontend
must preserve which classifier it elaborated and let explicit Core
conversion/proof-time unification establish the comparison. It must never
turn a proof-time comparison into an unreviewed runtime rewrite.

The exact notation remains provisional. `:^nd` should mean construction of a
coherent displayed transfor at the expected `Transfd_cat` cell level, not
simply binding an object of an arbitrary displayed category.

## Dependency-Aware Contextual IR

The current categorical contextual IR records ordered slot uses and the
ordinary/displayed distinction, but not a general dependency graph. The
next foundation records, for every stored contextual slot:

```text
slot identity and ordered position
classifier
direct dependencies
transitive dependency closure
least ordered dependency prefix
source provenance
```

The reusable analysis must:

- recover dependencies structurally from locally nameless Core classifiers,
  including occurrences beneath internal binders;
- distinguish a genuine dependency edge from independent slots;
- identify siblings with the same minimal dependency base;
- identify independent slots that become siblings only after weakening to a
  common base;
- permit adjacent exchange exactly when no dependency path is crossed and
  enumerate the dependent suffix that must be transported;
- plan discard, single use, and repeated use as weakening/projection,
  identity, and diagonal/contraction respectively; and
- reject malformed, escaping, or dependency-crossing requests with exact
  provenance.

The generic outer-LF Core telescope already implements scoped weakening,
dependency-sensitive adjacent exchange, and contraction using explicit
ambient-index maps. This plan extends that evidence with an inspectable
dependency graph rather than building a second independent dependency
language. The categorical contextual builder can then adapt the same
analysis while emitting its additional Sigma/pullback/product/action owners.

Sequential and grouped surface presentations remain two views of this one
model:

```text
λ a. λ b : B(a). λ c : C(a). t

λ a. λ (b,c) : Product_catd(B,C)(a). t.
```

The compiler may retain the sequential Sigma telescope, choose a grouped
displayed product, or compare both, according to the expected classifier and
available active owners. It may not erase dependency evidence before
checking.

## Qualification Corpus

The architecture is not considered mechanically settled for general
displayed binding until the following bounded cases are executable:

1. direct displayed-functor identity, composition, and eta through a
   provisional typed `displayedFunctorLambda`/`:^fd` API;
2. displayed weakening: pull a section back to `Sigma_cat E`, then check the
   Sigma-section presentation against `Functord_cat E D`;
3. substitution stability: abstract before versus after reindexing along
   `σ`, using `Pullback_catd_func`;
4. a genuinely fibre-dependent target `B[k,a]`, using
   `Sigma_catd_functord_catd` and the internal/pullback-Pi package;
5. direct displayed-transfor abstraction plus `tdapp0_fapp0` and one
   `tdapp1_int_cell` consumer;
6. sibling product projections, pairing, swap, and diagonal over one
   dependent base;
7. positive exchange of independent siblings and required rejection across
   a genuine dependency edge;
8. sequential-versus-grouped context conformance without assuming a generic
   total-category pullback;
9. reindexing stability of the displayed product; and
10. an explicit audit of comprehension pairing and the deferred
    Sigma-introduction arrow action.

The already completed representation-only scale slices are reusable evidence:

- SCALE-STRESS-2A: Sigma/Pi telescope uncurrying;
- SCALE-STRESS-2B1/2B2: internal/pullback Pi plus base-arrow action; and
- SCALE-STRESS-2B3: Sigma-total displayed-transfor uncurrying.

They do not by themselves promote those comparisons into the active
usability profile.

## Implementation Ledger

| Slice | Status | Depends on | Exact bounded result |
| --- | --- | --- | --- |
| FIBRED-PLAN-0 | complete | accepted consolidated review | This dedicated plan records the dependency-edge/sibling correction, the two-foundation architecture, displayed-binder semantics, product and total-category boundaries, qualification corpus, gates, and persistent launch prompt |
| FIBRED-PRODUCT-0A | complete; ignored read-only probe | active v3.2 product, uncurry, Catd, and composition owners | The transparent `uncurry(Product_cat_func) ∘ ⟨B,C⟩` candidate computes to pointwise product fibres but deliberately does not compute its base-arrow transport to `Product_map_func`; no active source, owner, rule, or catalog changed |
| FIBRED-CONTEXT-0A | complete | FIBRED-PLAN-0 | Added backend-neutral dependency-graph inspection for persistent Core telescopes: dependencies are recovered beneath internal binders; direct/closure/prefix data, shared-base versus weakened siblings, genuine edges, exchange suffix transport, owner-neutral usage planning, exact provenance, fail-closed errors, immutability, and six focused tests are green |
| FIBRED-CONTEXT-0B | complete | FIBRED-CONTEXT-0A | Adapted the generic graph to categorical contextual slots through explicit locally nameless classifier references; represents genuine edges/chains, direct versus pullback-then-Sigma sequential extension, shared-base versus weakened sibling groups, grouped displayed-product structural intent, exact errors/provenance, and a zero-owner boundary without changing completed ordinary or D-003 behavior |
| FIBRED-PRODUCT-0B | complete; immutable proposal awaits D-DTTLF-USABILITY-004 | FIBRED-PRODUCT-0A, concrete first categorical consumer | Compared broad generic, stable-head, and narrow shared-base existing-owner routes in full-file probes. Selected the zero-warning-delta transparent semantic family plus exactly two existing-owner runtime projections; froze positive/negative conversions, higher-action limits, no-owner/no-total-pullback boundary, and the exact human decision |
| FIBRED-PRODUCT-1A | blocked pending H-DTTLF-USABILITY-02/D-DTTLF-USABILITY-004 | FIBRED-PRODUCT-0B and exact human approval | If approved, promote only the Cat-valued postcomposition capped action and shared-base product-action projection, run the full Lambdapi SOP, transfer exactly that closure through generic TypeScript mechanisms, and lower the first grouped-sibling transport while preserving frozen profiles |
| FIBRED-COMPREHENSION-0A | complete; ignored semantic probe | FIBRED-CONTEXT-0B and active Sigma/pullback/section owners | Constructed the zero-owner semantic contextual pair through pulled-back `sigma_intro_transf`; its type is correct, but ordinary object, arrow, substitution, and projection consumers remain computationally stuck |
| FIBRED-COMPREHENSION-0B | complete; immutable proposal awaits D-DTTLF-USABILITY-005 | FIBRED-COMPREHENSION-0A and concrete object/arrow substitution consumers | Compared the semantic composite, a direct specialized pair owner (`+2/0` warnings), and a general asymmetric pullback-total owner (`+0/0`). Selected one new owner with two structured runtime projections, a transparent three-factor contextual pair, object/base-arrow substitution evidence, strict `0/45/27` audit, exact non-collapse boundaries, and separate Sigma-introduction action deferral |
| FIBRED-COMPREHENSION-1A | blocked pending H-DTTLF-USABILITY-02/D-DTTLF-USABILITY-005 | FIBRED-COMPREHENSION-0B and exact human approval | If approved, promote only `sigma_pullback_total_func` with its object and structured-arrow projections, run the full Lambdapi SOP, transfer that one-owner/two-rule closure, and lower one genuine dependent-chain contextual substitution |
| FIBRED-SIGMA-INTRO-ACTION-1 | deferred separate closure | concrete consumer beyond contextual pairing | Reassess direct `sigma_intro_tapp0_func` arrow action only with a closure that joins the measured `+10/+1` identity, naturality, composition, and higher-action interactions |
| FIBRED-STRUCTURE-1 | pending | FIBRED-CONTEXT-0B, FIBRED-PRODUCT-1A or a proved existing-owner derivation | Lower displayed projection, pairing, swap, diagonal, and reindexing stability for independent siblings with positive, negative, and higher-action evidence |
| FIBRED-BINDER-1 | pending | FIBRED-STRUCTURE-1 and existing Sigma/Pi comparisons | Implement the first direct `:^fd`-equivalent typed API and show direct/nested classifier compatibility without collapsing proof-time and runtime equality |
| FIBRED-TRANSFD-1 | pending | FIBRED-BINDER-1 and transferred exact `Transfd` application closure | Implement one coherent displayed-transfor abstraction and component/higher-cell consumer |
| FIBRED-GROUPED-SEQUENTIAL-1 | pending | FIBRED-STRUCTURE-1, FIBRED-COMPREHENSION-1A | Demonstrate sequential and grouped sibling syntax through one dependency-aware model and explicit owner-backed Core |
| FIBRED-TOTAL-COMPARE-1 | deferred theorem/owner boundary | concrete need after grouped/sequential success | State or implement the total-category comparison only with an exact active pullback/comma/equivalence construction; never treat notation `×K` as an existing generic computational owner |
| FIBRED-GRADUATE-1 | pending | complete qualification corpus | Freeze the exact supported envelope, residual owner/action gaps, mechanical-reuse assessment, TypeScript/Lambdapi conformance, and a separate human graduation decision |

## FIBRED-CONTEXT-0A Completion Record

The first implementation slice extends the existing generic locally nameless
Core rather than creating a categorical-only dependency language:

- `kernelAmbientDependencies` traverses arbitrary stored Core, distinguishes
  internal Pi/lambda binders from ambient telescope variables, and retains
  every dependency occurrence's provenance;
- `coreContextDependencyGraph` derives direct dependencies, transitive
  closure, and the least outermost-first dependency prefix from each
  persistent `CoreContext` binding type;
- adjacent exchange analysis distinguishes a genuine dependency edge from
  independent slots, classifies shared-minimal-base siblings versus siblings
  needing weakening, and names every later classifier whose dependency
  evidence must be transported;
- contiguous sibling-block analysis records common dependencies, required
  weakening, sequential pullback positions, and projection/pairing/exchange/
  diagonal intent without claiming a displayed implementation owner; and
- slot-use analysis maps zero, one, and repeated occurrences to
  projection/weakening, identity, and iterated diagonal/contraction intent.

The focused corpus covers:

```text
Γ, a : A, b : B(a), c : C(a), d : D(b,c)
```

including a dependency occurrence beneath an internal Core binder. It
accepts and classifies the `b,c` sibling block, records that exchanging it
requires transport of `d`, rejects the `c,d` dependency edge at the exact
stored occurrence, and separately detects a constant sibling that must be
weakened to the common base.

Implementation:
`src/v3_2/kernel.ts`,
`src/v3_2/context_dependencies.ts`, and
`tests/v3_2_context_dependency_tests.ts`.

Validation:

```text
./scripts/pnpmw run typecheck
  passed

node --require ts-node/register --test \
  tests/v3_2_context_dependency_tests.ts
  6 passed, 0 failed

./scripts/pnpmw run check:ts
  687 tests, 645 passed, 42 opt-in skipped, 0 failed

./scripts/pnpmw run check:all
  root gate passed
  19 mandatory live TypeScript/Lambdapi differential tests passed
  41 active Lambdapi kernel/example files passed
  39 formal infrastructure and 5 print registry tests passed
  warning/LHS/catalog/health/book/reference gates passed
```

This slice emits no categorical owner, changes no runtime/profile semantics,
and does not claim that the categorical surface already stores the new graph.
That adaptation is exactly FIBRED-CONTEXT-0B.

## FIBRED-CONTEXT-0B Completion Record

The categorical adapter now turns first-order contextual classifier syntax
into the same generic dependency graph used by persistent outer-LF Core:

- categorical classifier references are nearest-first locally nameless
  indices with source provenance, not caller-maintained dependency flags;
- the generic graph constructor validates that every occurrence points
  strictly backward, merges repeated evidence, and derives direct
  dependencies, transitive closure, and the least ordered dependency prefix;
- closed slots and displayed-family applications are retained as distinct
  classifiers, while the already implemented one-index
  `indexed-object` classifier has an explicit compatibility adapter;
- sequential planning distinguishes direct Sigma extension from a family
  that must first be pulled back past intervening independent slots;
- grouping distinguishes siblings with the same minimal dependency base from
  independent factors needing weakening to a common base, and retains
  projection, pairing, exchange, and diagonal intent; and
- every grouped product remains explicitly
  `representation-only-owner-unqualified`: its semantic candidate name is
  `Product_catd`, but `selectedCoreOwner` is `null`, emitted-owner count is
  zero, and generic total-category pullback is false.

The executable corpus uses:

```text
Γ, a : A, b : B(a), c : C(a), d : D(b,c).
```

It records the sequential pullback of `C` past `b`, recognizes `b,c` as
shared-base siblings, records the grouped pointwise-product and
componentwise-base-arrow obligations, and rejects grouping `c,d` at the
exact occurrence where `D` depends on `c`. A second case recognizes a
constant displayed factor as independent only after weakening. Escaping
indices and incompatible base categories fail closed.

Implementation:
`src/v3_2/context_dependencies.ts`,
`src/v3_2/categorical_context_dependencies.ts`, and
`tests/v3_2_categorical_context_dependency_tests.ts`.

Validation:

```text
./scripts/pnpmw run typecheck
  passed

./scripts/pnpmw run lint
  passed

node --require ts-node/register --test \
  tests/v3_2_context_dependency_tests.ts \
  tests/v3_2_categorical_context_dependency_tests.ts
  13 passed, 0 failed

./scripts/pnpmw run check:ts
  694 tests, 652 passed, 42 opt-in skipped, 0 failed

./scripts/pnpmw run check:all
  passed, including 19 mandatory live differential tests,
  41 active Lambdapi kernel/example files, warning/LHS/catalog/health,
  print, book, and reference gates
```

This is an inspectable planning boundary, not a new surface elaboration
claim. The completed ordinary bracket and D-003 `FF[k](s[k])` lowerers are
unchanged. Concrete displayed product and contextual Sigma owners are
selected only by the subsequent authority-qualified rows.

## Human Review Gates

### Existing H-DTTLF-USABILITY-02 — New Mathematical Owner Or Rule

FIBRED-PRODUCT-0B has triggered the existing usability rule gate without
requesting a new mathematical owner. The immutable decision is:

**D-DTTLF-USABILITY-004 — pending human decision.** Keep the fibrewise product
as the transparent existing-owner composite. Add only:

1. the probed Cat-valued postcomposition capped-action rule at
   `hom_postcomp_fapp0`; and
2. the same-base product projection
   `(B[p] * 1)[C[p]] -> Product_map_func(B[p],C[p])` at
   `Product_cat_fapp1_fapp0_functord`.

After the active Lambdapi package passes the full nested SOP, transfer only
that two-rule closure through the generic TypeScript runtime and lower the
first grouped-sibling transport to backend-neutral explicit Core.

This decision does **not** authorize:

- a `Product_catd` primitive, injective head, or notation-only kernel alias;
- the broad arbitrary `(F * 1)[G]` off-diagonal rule;
- full base-two-cell action or its naturality closure;
- global `Functord_cat`-product conversion;
- pullback/reindexing stability;
- displayed projection, pairing, swap, or diagonal;
- a generic total-category pullback or equivalence;
- browser/frozen-profile promotion; or
- parsing, acquisition, or bulk transfer.

The exact question is:

> Approve H-DTTLF-USABILITY-02/D-DTTLF-USABILITY-004 as proposed: keep the
> fibrewise product as the transparent existing-owner composite; add only the
> probed Cat-valued postcomposition capped-action rule and the shared-base
> product projection `(B[p] * 1)[C[p]] ->
> Product_map_func(B[p],C[p])`; transfer only that two-rule closure and first
> grouped-sibling transport to TypeScript; and retain the broad off-diagonal
> action, a primitive `Product_catd` head, base two-cell action, `Functord`
> product comparison, pullback stability, structural maps, total pullback,
> and profile promotion as separate unapproved work?

FIBRED-COMPREHENSION-0B has now independently triggered the same gate with one
new mathematical owner. Its immutable decision is:

**D-DTTLF-USABILITY-005 — pending human decision.** Add:

```text
sigma_pullback_total_func(F,D)
  : Functor
      (Sigma_cat(Pullback_catd D F))
      (Sigma_cat D)
```

with only:

```text
(a,u) -> (F[a],u)
(p,alpha) -> (F[p],alpha).
```

Derive contextual pairing transparently from the terminal-total map,
`sigma_map_func(s)`, and this pullback-total map. After the active Lambdapi
package passes the full nested SOP, transfer only that one-owner/two-rule
closure through the generic TypeScript engines and lower one genuine
dependent-chain object/arrow substitution consumer.

This decision does **not** authorize:

- a dedicated `sigma_pair_func` owner;
- the direct `sigma_intro_tapp0_func` arrow rule or its measured
  identity/naturality/composition closure;
- a whole-functor first-projection runtime beta;
- a pullback of arbitrary total functors or generic total-category pullback;
- D-DTTLF-USABILITY-004 or any product structural map;
- browser/frozen-profile promotion; or
- parsing, acquisition, bulk transfer, or general displayed graduation.

The exact question is:

> Approve H-DTTLF-USABILITY-02/D-DTTLF-USABILITY-005 as proposed: add
> `sigma_pullback_total_func` as the asymmetric family-pullback total map with
> only object `(a,u) -> (F[a],u)` and structured-arrow
> `(p,alpha) -> (F[p],alpha)` runtime projections; derive contextual pairing
> as the transparent terminal-total, `sigma_map_func`, and pullback-total
> composite; transfer only that one-owner/two-rule closure and one genuine
> dependent-chain consumer to TypeScript; and retain a dedicated pair owner,
> the direct Sigma-introduction arrow rule, whole first-projection beta,
> generic total pullback, D-004 product work, and profile promotion as
> separate unapproved work?

### Future FIBRED-GRADUATE-1 — General Displayed Usability

Completing individual product or binder examples does not by itself settle
the general architecture. Graduation requires the executable corpus above,
an explicit unsupported-action table, and separate statements about:

- frontend dependency/binder scalability;
- mathematical displayed-owner coverage;
- bulk library transfer throughput;
- optional acquisition/parsing;
- groupoidal closure; and
- product/browser promotion.

## Acceptance And Validation Policy

FIBRED-CONTEXT-0A and FIBRED-CONTEXT-0B are complete only when:

1. dependencies are derived from stored locally nameless Core rather than
   user-maintained duplicate flags;
2. the sibling graph and genuine chain examples receive different,
   deterministic classifications;
3. independent exchange names the later dependent suffix needing transport;
4. use counts select projection/identity/diagonal intent without emitting an
   unqualified categorical owner;
5. invalid positions/counts fail closed;
6. all public records and arrays are immutable; and
7. the categorical adapter retains sequential pullback and grouped-product
   obligations while emitting no unapproved owner; and
8. focused tests plus `./scripts/pnpmw run check:ts` pass.

FIBRED-PRODUCT-0B is complete only when:

1. broad generic, stable-head, and narrow shared-base candidates are tested
   at their intended full-file owner positions;
2. both pointwise fibre and componentwise base-arrow transport compute for
   every candidate;
3. warning deltas and critical-pair families are measured, not inferred;
4. opaque-family, family-level classifier-collapse, and pullback-stability
   negatives are retained;
5. the selected candidate introduces no unrecorded owner, alias, proof-time
   rule, full two-cell action, or total pullback;
6. the proposal is executable, deeply frozen, self-validating, and names the
   exact human gate; and
7. focused tests, TypeScript gates, the final bounded owner-position probe,
   and strict LHS audit pass.

FIBRED-COMPREHENSION-0B is complete only when:

1. the zero-owner semantic, direct-pair, and general base-change candidates
   are tested at their intended full-file owner positions;
2. contextual-pair object and arrow action plus further-family object and
   base-arrow substitution are exercised;
3. the chosen owner is the asymmetric total map of family pullback and cannot
   be mistaken for a pullback of arbitrary total functors;
4. direct-pair identity overlaps and direct Sigma-introduction action
   overlaps are measured and retained as separate evidence;
5. whole first projection and opaque-owner non-collapse boundaries are
   explicit;
6. the proposal is executable, deeply frozen, self-validating, and names the
   separate exact human gate; and
7. focused tests, TypeScript gates, the final quiet/warning probes, and strict
   LHS audit pass.

Any active Lambdapi edit follows `emdash2/AGENTS.md` and the current v3.2 SOP:
intended-owner full-file probe, positive and negative consumers, bounded
checks, warning comparison, strict LHS audit, catalog and health
synchronization, examples where affected, and full local CI before a
checkpoint. Every Lambdapi process remains bounded to at most 60 seconds.

This sub-plan inherits
[`PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`](./PERSISTENT_GOAL_GIT_EXPERIMENTATION.md).
The user's existing authorization permits local checkpoint commits only on
the existing `goal/typescript-elaborator-v3.2` branch/worktree after a bounded
coherent tranche is green, all linked ledgers/navigation are synchronized,
the exact staged diff excludes unrelated work, and
`git diff --cached --check` passes.

No push, merge, PR, publication, release, new branch/worktree, amend, rebase,
reset, history rewrite, cleanup, branch deletion, or worktree removal is
authorized.

## Persistent `/goal` Launch Prompt

```text
Kick off or continue implementing
docs/TYPESCRIPT_ELABORATOR_V3_2_FIBRED_CONTEXT_PLAN.md.

Treat its Persistent /goal Launch Prompt as part of the objective. Recover
actual state from active code and tests, this sub-plan and its ledger, the
linked usability/scale/DTT-LF/master plans, all Git worktrees and
staged/unstaged diffs, and the active authority order. Follow root AGENTS.md
and, for every emdash2 action, emdash2/AGENTS.md and the current v3.2 SOP.
Resume an in-progress row or select the next dependency-ready bounded
implementation slice. Produce executable evidence and synchronize all
affected living documents.

Preserve the exact frozen emdash-v3.2-mvp-1 profile, the reviewed root-only
emdash-v3.2-dttlf-directed-1 continuation, the outer dependent LF,
backend-neutral locally nameless explicit Core, generic checker/evaluator and
transfer engines, completed ordinary categorical bracket, completed indexed
section eta, and completed D-003 non-eta `FF[k](s[k])` composition witness.
Preserve H-01/D-007 dependent-first semantics. It requires contexts as
categories, types as displayed families, terms as sections, substitution as
functorial pullback, and only authority-classified ordinary constant-family
bridges. It requires neither one shared nor deliberately separate
ordinary/displayed TypeScript algorithm.

Implement both general dependent telescopes and fibrewise-cartesian structure
for independent siblings as two presentations in one dependency-aware
contextual architecture. Distinguish a genuine dependency edge from sibling
variables over a common dependent base. Reuse the generic locally nameless
Core telescope's dependency, weakening, exchange, contraction, scope, and
provenance mechanisms where sound; add categorical Sigma/pullback/product and
higher-action lowering only through active authority-backed owners.

Preserve FIBRED-PRODUCT-0A's exact result: the transparent
`uncurry(Product_cat_func) ∘ ⟨B,C⟩` candidate computes pointwise fibres but
does not currently compute base-arrow transport to `Product_map_func`.
Preserve FIBRED-PRODUCT-0B's measured correction: the broad generic action
works but adds three unjoined critical pairs; a new stable `Product_catd`
head works but duplicates semantics and adds five; the narrow shared-base
existing-owner route works with zero warning delta. Its exact proposal keeps
the transparent family and requests only the Cat-valued postcomposition
capped action plus the same-base
`(B[p] * 1)[C[p]] -> Product_map_func(B[p],C[p])` projection. Do not promote
either rule until H-DTTLF-USABILITY-02/D-DTTLF-USABILITY-004 is explicitly
approved. If approved, implement only FIBRED-PRODUCT-1A's frozen two-rule
closure and first grouped-sibling transport; if not yet approved, continue
only a genuinely independent dependency-ready audit and do not guess the
decision.

Preserve FIBRED-COMPREHENSION-0A/0B's exact result. A contextual-pair
expression built only by pulling back `sigma_intro_transf` is type correct but
computationally stuck. A dedicated direct pair owner computes but adds two
generic identity-action critical pairs and duplicates the more reusable
base-change construction. The selected proposal adds exactly one asymmetric
family-pullback totalization owner,
`sigma_pullback_total_func(F,D)`, with only structured object
`(a,u) -> (F[a],u)` and arrow `(p,alpha) -> (F[p],alpha)` projections.
Contextual pairing stays a transparent terminal-total/`sigma_map_func`/
pullback-total composite; further-family object and base-arrow substitution
compute with zero warning delta. Do not promote the owner or either rule
until H-DTTLF-USABILITY-02/D-DTTLF-USABILITY-005 is explicitly approved. If
approved, implement only FIBRED-COMPREHENSION-1A's frozen one-owner/two-rule
closure and first genuine dependent-chain consumer. Keep the direct
Sigma-introduction arrow action separate: its measured `+10/+1` interaction
closure is not needed for contextual pairing.

Treat the ordinary `Functor_cat X (Product_cat A B)` rule as useful evidence,
not as an automatically valid family-level rule. The first owner-position
comparison has rejected global runtime collapse of
`Functord_cat E P(B,C)` to a product. Derive that comparison later from
qualified displayed projection and pairing functors unless new typed evidence
selects a proof-time owner. Pullback stability and full base-two-cell action
also remain separate audits. Preserve stable returned heads where higher
projections require them; never add a primitive merely for notation.

Do not assume a generic computational total-category pullback
`Sigma_cat B ×K Sigma_cat C`. Active `Pullback_catd E F` is asymmetric
family reindexing. First implement grouped/sequential sibling behavior through
explicit displayed products, Sigma projections, pullbacks, contextual
pairing, and structural maps. Defer any total-category equivalence until an
exact pullback/comma/equivalence owner or theorem is separately qualified.

Treat provisional `:^fd` and `:^nd` as ergonomic combinations of abstraction
layer, plicity, variation, polarity, cell level, and displayed dependency,
not primitive Core binder modes or one-to-one owner names. A displayed
functor binder must supply fibre-arrow and base-arrow coherence. Use the
active Sigma/Pi uncurrying comparison to relate total-context sections to
`Functord_cat`, and the next-hom comparison to reach `Transfd_cat`; preserve
direct and nested classifier presentations and never turn proof-time
comparisons into runtime rewrites.

Keep canonical Lambdapi term/declaration parsing deferred and optional.
Direct typed TypeScript construction remains the default. Do not resume the
70-root/83-extension transfer closure, promote a browser/product profile,
claim complete groupoidal DTT, or broaden metatheory as a side effect of this
usability tranche.

Recover the actual descendant HEAD. Named baselines and checkpoints are
comparison/backtracking evidence, never permission to reset or rewrite.
Existing authorization permits local checkpoint commits only on the existing
goal branch after a bounded green tranche, synchronized ledgers/navigation,
exact staged-diff review, and `git diff --cached --check`. It authorizes no
push, merge, PR, publication, release, new branch/worktree, amend, rebase,
reset, cleanup, or deletion.

When a row reaches a human mathematical gate, record the exact evidence and
approval question, continue any independent dependency-ready row, and never
guess the missing rule. Keep every Lambdapi process bounded to at most 60
seconds and run all proportional warning, audit, catalog, health, example,
conformance, and CI obligations.
```

## Change Log

- **2026-07-27 — Dedicated fibred-context plan created.** Integrated the
  accepted displayed-binder analysis and the corrected distinction between
  dependency-chain exchange and fibrewise-cartesian sibling structure.
  Recorded the two complementary comprehension/product foundations,
  provisional `fd`/`nd` semantics, dependency-aware contextual IR, stress
  corpus, product owner gate, and total-category non-assumption.
- **2026-07-27 — Transparent displayed-product derivation measured.** A
  bounded ignored probe showed that
  `uncurry(Product_cat_func) ∘ ⟨B,C⟩` computes the desired pointwise fibre but
  not the desired `Product_map_func` base-arrow transport. The plan therefore
  retains generic higher-action and stable-head alternatives and authorizes
  neither active kernel change without H-DTTLF-USABILITY-02.
- **2026-07-27 — FIBRED-CONTEXT-0A completed.** Added generic locally nameless
  dependency-occurrence inspection and an immutable persistent-context graph
  with sibling/edge, weakening, exchange-suffix, and structural-use analysis.
  Six focused tests distinguish the accepted sibling and rejected chain
  examples without emitting or selecting a displayed product owner.
- **2026-07-27 — FIBRED-CONTEXT-0B completed.** Generalized the dependency
  graph over syntax-specific binding evidence and adapted categorical
  contextual classifiers to it. Seven focused cases now preserve genuine
  chains, sequential pullback intent, shared-base and weakened sibling
  grouping, structural obligations, provenance, immutability, and the
  explicit zero-owner/zero-total-pullback boundary.
- **2026-07-27 — FIBRED-PRODUCT-0B completed and exact rule gate opened.**
  Full-file probes compared the transparent broad-action route
  (`+3` critical pairs), a new stable `Product_catd` head (`+5`), and the
  narrow shared-base existing-owner route (`+0`). The selected proposal adds
  no declaration or alias and freezes exactly two prospective runtime rules,
  positive fibre/transport computation, three non-collapse boundaries, the
  unproved pullback-stability boundary, iterable `Product_map_func` result,
  and all higher-action/non-effect limits. Five executable proposal tests,
  quiet and warning-enabled probes, and the strict `0/45/27` LHS audit pass.
  FIBRED-PRODUCT-1A now awaits
  H-DTTLF-USABILITY-02/D-DTTLF-USABILITY-004.
- **2026-07-27 — FIBRED-COMPREHENSION-0A/0B completed and exact owner gate
  opened.** The zero-owner Sigma-introduction composite is type correct but
  computationally stuck. A direct specialized pair computes with one
  declaration, three rules, and `+2/0` warnings. The selected general
  asymmetric pullback-total owner computes contextual-pair object/arrow
  action plus further-family object/base-arrow substitution with one
  declaration, two structured rules, and `+0/0`. The direct
  Sigma-introduction arrow action was separately measured at `+10/+1` and is
  not bundled. The immutable proposal and five focused tests preserve
  pointwise-only first projection, opaque non-collapse, no generic total
  pullback, product-decision independence, and the exact
  H-DTTLF-USABILITY-02/D-DTTLF-USABILITY-005 gate.
