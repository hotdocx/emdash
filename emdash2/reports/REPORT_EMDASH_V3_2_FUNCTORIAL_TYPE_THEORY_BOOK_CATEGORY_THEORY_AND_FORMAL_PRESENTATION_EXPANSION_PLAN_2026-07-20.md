# Functorial Type Theory Book: Category Theory And Formal Presentation Expansion Plan

Date: 2026-07-20
Last reviewed: 2026-07-20
Plan-ID: EMDASH-V3-2-FTT-BOOK-CATEGORY-THEORY-FORMAL-PRESENTATION-EXPANSION-2026-07-20
Depends-On: EMDASH-V3-2-FUNCTORIAL-TYPE-THEORY-BOOK-ARCHITECTURE-2026-07-20; EMDASH-V3-2-PROFUNCTOR-WEIGHTED-LIMITS-2026-06-17; EMDASH-V3-2-PROFUNCTOR-REPRESENTABILITY-2026-06-19; EMDASH-V3-2-EQUIPMENT-SHADOW-TENSOR-JOIN-REDESIGN-2026-06-28; EMDASH-V3-2-FULL-NATURALITY-2026-06-12; REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26; EMDASH_FOUNDATIONS; REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05
Supersedes: no whole report; refines the post-B6 recommended next action in EMDASH-V3-2-FUNCTORIAL-TYPE-THEORY-BOOK-ARCHITECTURE-2026-07-20
Side-Task-Ledger: #side-task-ledger
Infinity-Codex-Origin: current-session-book-category-theory-formal-presentation-review-2026-07-20
Infinity-Codex-Decision-Responses: none
Status: **COMPLETE - C0 through C7 implemented and release-audited**

## Executive Decision

The completed B0-B6 book is a sound first vertical slice, but it should not
stop after its present chapters on transfors and profunctors. The next edition
should add a coherent second spine in which the category-theory material of
the HoTT Book's Chapter 9, the formal-presentation discipline of its Appendix
A, and emdash's active universal-construction interfaces explain one another.

This is not an invitation to append a catalogue of implemented features. The
new spine should make one mathematical argument:

> Functorial type theory treats categorical substitution as internal
> computation. Single-arrow hom actions, natural-family action, and
> universal-property beta/eta laws are successive forms of cut elimination.
> Representability then organizes Yoneda, adjunctions, weighted limits and
> colimits, while duality and joins exhibit the directed geometry that is
> absent from a purely groupoidal foundation.

The WalkingEnd/Nat calculation remains the opening theorem and the culmination
of the prerequisite spine. The new material begins from that established
example and broadens the foundation rather than displacing it.

Five decisions govern the expansion:

1. Adapt all nine sections of the HoTT Book's category-theory chapter, but do
   not transplant its 1-categorical, set-valued-hom definition as the
   definition of an emdash category.
2. Move Došen-style cut elimination from an implementation aside to a central
   explanatory thread running from represented hom action through weighted
   universal properties.
3. Include adjunctions, tensor/internal hom, weighted limits, weighted
   colimits, duality, and joins in this edition through theorem-led chapters,
   with neighboring free-form mathematics supplied where the checked kernel
   intentionally stops.
4. Adapt the HoTT formal appendix to a categorical-kernel-first architecture:
   the internal categorical calculus is the computational core, the book's
   notation is its mathematical surface, and a conventional end-user syntax
   is a later elaboration layer rather than the source of the theory.
5. Repair and harden mathematical typography before adding more prose. The
   current PDF contains both malformed display mathematics and literal TeX
   commands hidden in Markdown code spans; the existing release gates did not
   detect those semantic notation failures.

This report is a subordinate follow-on to the completed book plan. It does not
reopen or rewrite the B0-B6 implementation history.

## Scope And Non-Scope

This plan covers:

- the global dependency architecture for the next book edition;
- a source-by-source adaptation map for HoTT Chapter 9 and Appendix A;
- the Došen cut-elimination narrative and its exact emdash notation;
- theorem-led chapters for adjunctions, Yoneda, profunctors, weighted
  universals, duality, and join;
- the separation between checked evidence and plausibly implementable
  free-form theory;
- a formal-presentation appendix and its integration into earlier chapters;
- a notation, lint, render, and PDF-verification repair phase;
- a read-only architectural assessment of the parent TypeScript prototype as
  evidence for a possible future elaborator.

It does not authorize:

- semantic changes to `emdash3_2.lp` or its dependent modules merely to make
  prose look cleaner;
- a physical Lambdapi module split;
- implementation work in the parent `/home/user1/emdash1` TypeScript
  prototype;
- presentation of a general coend, end, collage, Rezk completion, structure
  identity principle, or dependent adjunction as checked when only a shaped
  or symbolic interface is active;
- conflation of HoTT's use of “strict category” with emdash's strict
  computation or strict transfor terminology;
- replacement of the current print stack;
- copying Došen or HoTT prose without source, license, and adaptation
  provenance.

The book remains allowed to develop mathematics beyond the current code. Such
material must use the existing four-way status contract: **checked**, **formal
consequence**, **mathematical development**, or **research boundary**.

## Review Baseline

This follow-on review was performed against repository commit `91fc9bf`.
Before this report was edited:

- the staged and unstaged worktrees were empty;
- `EMDASH_TYPECHECK_TIMEOUT=60s make check` passed;
- the current SOP, Foundations, canonical syntax, report index, completed book
  plan, relevant profunctor/weighted-limit and equipment/join plans, active
  Lambdapi owners, current book sources, and book manifest were reviewed;
- the Infinity Codex archive verified 447 completed responses, with no linked
  decision response required for this task;
- the HoTT Book source was reviewed from the temporary sibling checkout
  `/home/user1/emdash1/.hott-book-review-20260720` at pinned revision
  `578b85cc8d586b1677ec4335148adeb443057d24`;
- `categories.tex` sections 9.1-9.9 and `formal.tex` sections A.1-A.4 were read
  as source, not reconstructed from the rendered table of contents;
- the parent `/home/user1/emdash1` README, contributor guidance, parser,
  elaboration data structures, and focused functor/transfor tests were
  inspected read-only;
- the 103-page PDF
  `output/pdf/functorial-type-theory-0.1.0-dev.pdf` was text-extracted and
  selected affected pages were rendered for visual inspection.

The temporary HoTT checkout is review input only and is not a build dependency
or a vendored book source.

## Review Findings

### 1. The current edition establishes the first theorem, not the whole foundation

Chapters 1-8 now give a coherent route from judgments, iterated homs, directed
families, arrow induction, and categorical height to the WalkingEnd/Nat
encode-decode theorem. Chapters 9 and 10 then introduce strict/lax transfors
and profunctor representability through central computations.

That is an effective first spiral. It is not yet a globally complete account
of the title *Functorial Type Theory: Univalent Foundations for Mathematics*.
In particular, a reader currently reaches profunctors before receiving a
systematic account of:

- the distinct category/precategory/strict-category ideas inherited from
  univalent category theory;
- adjunctions and their several notions of equivalence;
- the full Yoneda-to-representability argument;
- the structure identity principle and saturation/Rezk completion;
- weighted limits and colimits as universal representability statements;
- duality and join as directed constructions;
- the formal presentation and metatheoretic boundary of the calculus.

The remedy is another spiral, not an encyclopedic appendix. Basic categories
and functors remain introduced early in Chapter 2 for the WalkingEnd proof;
the later part revisits them at the level needed for categorical univalence,
universal constructions, and formal architecture.

### 2. HoTT Chapter 9 is a rhetorical and dependency spine, not a drop-in foundation

The HoTT chapter assumes a 1-categorical setting:

- a precategory has a type of objects and set-valued homs;
- a category is a precategory whose object equality is equivalent to
  isomorphism;
- a strict category additionally has a set of objects;
- natural transformations use proposition-level equality for naturality;
- the Rezk completion saturates a precategory into a category.

Emdash starts elsewhere. `Cat` has iterated hom-categories and supports
genuinely directed higher cells. Finite `NCat` evidence, equality-local
groupoids, object equality, ordinary isomorphism, omega-equivalence evidence,
strict runtime computation, and strict/lax transfors are related but distinct
layers.

Consequently, the HoTT definitions must be accompanied by an explicit
translation matrix. The book may present ordinary univalent 1-category theory
as an important truncation/specialization, but it must not silently identify
that specialization with the native definition of `Cat`.

### 3. The two represented-hom actions settle the associativity architecture

The active kernel has two separate runtime owners:

| Mathematical action | Emdash owner | Pointwise reading |
| --- | --- | --- |
| postcomposition by `u` | `hom_postcomp_*` | `u_*(g) = u ∘ g` |
| precomposition by `u` | `hom_precomp_along_*` | `u^*(g) = g ∘ u` |

This fixes an important naming ambiguity in the motivating discussion. The
formula `f^*(g) = g ∘ f` is precomposition and belongs to
`hom_precomp_along_*`, even if one informally thinks of the resulting
composite as “putting `f` in front.” With an additional functor `H`, the same
formula becomes `(Hf)^*(g) = g ∘ Hf`.

The owners accumulate adjacent cuts rather than requiring a broad global
associativity rewrite. They are the single-arrow flavor of the Došen
architecture.

The second flavor is `tapp1_func`/`tapp1_fapp0`. For a transfor
`eta : F => G`, its off-diagonal action sends an arrow `f : x -> y` to
`eta[f] : F(x) -> G(y)`. The two strict naturality reductions have the forms

```text
G[g] ∘ eta[f]  ->  eta[g ∘ f]
eta[f] ∘ F[h]  ->  eta[f ∘ h].
```

Here the arrow is not isolated data: `eta` supplies a natural family of
arrows. These two flavors are complementary:

- `hom_precomp_*` and `hom_postcomp_*` internalize a selected arrow as an
  action on a represented hom;
- `tapp1*` internalizes an entire transfor and accumulates naturality cuts;
- universal-property comparison maps then extend the same pattern to
  beta/eta normalization.

This distinction should be introduced once, used consistently, and included
in the notation appendix and glossary.

### 4. The product-projection example is the right benchmark, but not yet a checked theorem

Let

```text
h : A' -> A
k : B' -> B
g : A -> C.
```

Writing `pi1 : A x B -> A` and `pi1' : A' x B' -> A'`, the typed Došen
benchmark is

```text
pi1^*(g) ∘ (h x k)  ->  (pi1')^*(g ∘ h).
```

The overloaded informal formula
`pi1^*(g) ∘ (h x k) -> pi1^*(g ∘ h)` suppresses the change of product and
therefore uses two different projections under one name. The book may use the
overload after stating the fully typed version.

The active kernel already has `Product_projL_func`, `Product_map_func`, the
projection/product-map computation, generic functoriality, and represented
hom actions. That makes the example plausibly derivable through existing
owners. This review did not establish that the exact displayed composite is a
present checked normal form. Before it is labeled **checked**, a focused typed
probe must test both reduction paths and either cite the existing composite
normalization or add a narrowly justified theorem/check in a separately
authorized implementation phase.

### 5. Active universal-construction interfaces already form a theorem chain

The current code is strong enough to support a coherent later-book arc:

```text
represented hom actions
  -> transfors and naturality cuts
  -> representables and profunctors
  -> shaped tensor/co-Yoneda beta
  -> internal hom and representability
  -> adjunction mate comparison
  -> weighted limits
  -> right adjoints preserve weighted limits
  -> opposite duality
  -> left adjoints preserve weighted colimits
  -> directed join and its cross-cell recursor.
```

Important active interfaces include:

- `Adjunction`, with selected unit/counit data and triangle computation;
- `Prof_tensor` and its shaped co-Yoneda beta/fusion surface;
- `Prof_imply_cov` and `Prof_imply_con`, with fixed-endpoint eval/lambda
  computation;
- `WeightedCone_prof`, `WeightedLimit_cov`, and representability comparison;
- `right_adjoint_preserves_weighted_limit_cov_comp`;
- `WeightedColimit_con` defined through opposite duality;
- `left_adjoint_preserves_weighted_colimit_con`;
- `Join_cat`, its inclusions and internally natural cross cell, and
  `join_elim_func` with nondependent beta rules.

These interfaces do not amount to a complete bicategory/equipment of
profunctors, semantic coends/ends, a general collage construction, or a
dependent join eliminator. The book should use the checked theorem chain as
its backbone and develop those neighboring notions with the appropriate
free-form or research status.

### 6. HoTT Appendix A suggests a discipline, not the correct layer order for emdash

The HoTT appendix distinguishes:

- an informal first presentation based on raw expressions and
  type-independent convertibility;
- a second presentation using explicit judgments, contexts, and inference
  rules;
- the extra constants/rules of homotopy type theory;
- basic metatheory such as subject reduction, confluence, normalization,
  canonicity, consistency, and decidability, with careful limits on what is
  established for extensions.

It also organizes each type former by formation, introduction, elimination,
computation, and optional uniqueness rules. This architecture is worth
adapting throughout the emdash book.

The layer order must change, however. In functorial type theory, the
computational categorical presentation is not merely a denotational semantics
added after a conventional syntax. It is the main calculus. A user-friendly
syntax can later elaborate into it because functorial action, transfors,
directed families, and cuts are already internalized.

The book should therefore distinguish:

1. the **computational categorical kernel**, currently encoded in Lambdapi;
2. the **canonical mathematical surface**, used in prose and examples;
3. an optional future **elaborator/compiler**, which inserts implicit
   categorical structure and compiles end-user syntax into the kernel;
4. external semantic models, which remain valuable but are not what makes the
   core calculus computational.

The first three are presentations of one intended formalism. The fourth is a
semantic and metatheoretic validation layer.

### 7. The parent TypeScript prototype is feasibility evidence, not an authority

The parent repository contains a bespoke term AST, parser, bidirectional
elaboration/unification/reduction machinery, binder modes such as
`Functorial`, `Natural`, and `ObjectOnly`, and explicit terms for
`TApp1FApp0`, displayed functor action, and displayed transfor action. Focused
tests exercise off-diagonal transfor typing and both naturality accumulation
directions.

This makes a later surface-to-kernel compiler plausible. It does not yet
provide a finalized syntax, a compiler to the current Lambdapi v3.2 API, or an
authority equal to the active `.lp` files. Its categories and rules mirror
only portions of the current formalization and are explicitly outdated.

The parent code should be cited in the architecture appendix as a prototype
and left unchanged during this plan. A future elaborator RFC must start from a
fresh symbol/normal-form mapping against the then-current kernel.

### 8. The current PDF has semantic typography defects

Visual and extracted-text review found two distinct defect families.

First, some display-math commands lost their leading backslash in source and
render as italic strings of variables. Confirmed examples include:

- `book/chapters/01-judgments-and-computation.md`: bare `mathsf`, `qquad`,
  and `quad` on PDF pages 12-13;
- `book/chapters/02-categories-functors-and-families.md`: bare
  `longrightarrow` on page 18;
- `book/chapters/04-equivalence-and-univalence.md`: bare `qquad` on page 29;
- `book/chapters/07-truncation-and-categorical-height.md`: bare `mathsf` on
  page 47;
- `book/chapters/09-transfors-strictness-and-laxity.md`: bare
  `longrightarrow` on page 62.

The first Chapter 1 example also appears to contain a punctuation typo:
`A;mathsf{classifier}` should be reviewed as mathematics, not repaired by a
mechanical backslash insertion alone.

Second, at least 52 source lines put TeX commands inside Markdown code spans.
The renderer correctly treats those spans as literal code, so the PDF prints
expressions such as `g\circ f`, `* \to x`, and
`E:K\to\mathsf{Cat}` verbatim. This affects prose across the prologue,
Chapters 5-10, and Appendix C, including page 50 near the start of Chapter 8.

The existing syntax, browser, PDF-structure, and contact-sheet gates did not
detect either problem. A rendered page can be structurally valid, accessible,
and overflow-free while its mathematical notation is wrong. The next edition
therefore needs a semantic typography gate.

## Global Mathematical Architecture

### The second spiral

The book should preserve the first eight chapters and organize the expanded
narrative as follows. Chapter numbers after 8 are provisional until Phase C1
ratifies the manifest migration.

| Part | Provisional chapters | Central question |
| --- | --- | --- |
| I. The functorial language | 1-4 | What are the judgments, iterated homs, actions, equality layers, and equivalences? |
| II. Directed induction | 5-8 | How does an opaque directed generator compute to Nat? |
| III. Categorical computation | 9-13 | How do cuts, transfors, categories, adjunctions, equivalences, Yoneda, and representability compute? |
| IV. Univalent categorical structure | 14-15 | Which structures respect equality, and how are unsaturated structures completed? |
| V. Weighted and directed universals | 16-17 | How do weights, duality, and joins organize general universal constructions? |
| Appendices | A-G initially | What is the notation, evidence, provenance, formal calculus, status, and metatheoretic boundary? |

The dependency flow is:

```text
judgments and equality-local structure
  -> iterated homs and functor action
  -> single-arrow cuts and transfor cuts
  -> directed families and induction
  -> WalkingEnd/Nat encode-decode
  -> categories, equivalences, and categorical identity
  -> Yoneda and representability
  -> adjunctions and mates
  -> weighted limits/colimits
  -> duality and directed join

categorical identity
  -> structure identity principle
  -> saturation / Rezk completion

all chapters
  -> formal presentation and metatheoretic status appendix.
```

The order in prose may braid the last three branches. The dependency claims
must remain explicit even if the final chapter order changes.

### Provisional chapter sequence

#### Chapter 9. Transfors And The Calculus Of Cuts

Refactor the current Chapter 9 around the distinction between:

- ordinary functor action `F[f]`;
- single-arrow lower-star and upper-star hom actions;
- off-diagonal transfor action `eta[f]`;
- strict naturality as cut accumulation;
- lax directed comparison cells;
- higher iteration through `fapp*` and `tapp*`.

Its central result is the two-sided strict naturality computation. Its central
worked benchmark is the fully typed product/projection cut. Adjunction and
co-Yoneda should appear here only as previews of the same normalization
pattern.

#### Chapter 10. Categories, Precategories, And Categorical Identity

Revisit the Chapter 2 notion of category at the univalent 1-categorical
specialization. Introduce HoTT precategories, categories, and strict
categories, then compare them with:

- native `Cat` and iterated homs;
- `NCat`/`OneCat` evidence;
- equality-local categories;
- ordinary isomorphism and the one-way active lift into native
  omega-equivalence evidence;
- the presently absent full equality/isomorphism equivalence for arbitrary
  native categories.

The chapter's theorem should be a carefully scoped categorical identity
result that is actually supported. A general emdash category-univalence
theorem remains a research boundary unless separately implemented.

#### Chapter 11. Functors, Transfors, And Functor Categories

Adapt HoTT 9.2 while using the native iterated-hom architecture. Explain
identity, composition, whiskering, vertical composition, and interchange
through the generic owners rather than constructor-specific rules.

The central computation remains off-diagonal naturality. A theorem about
functor categories being categories may be stated in its ordinary
univalent-1-category form as mathematical development unless the exact native
package is checked.

#### Chapter 12. Adjunctions And Equivalences

Adapt HoTT 9.3-9.4 and distinguish:

- selected unit/counit adjunction data;
- triangle computation;
- hom/profunctor representability comparisons;
- ordinary categorical equivalence;
- fully faithful plus essentially surjective functors;
- strict isomorphism of categories;
- carrier/type equivalence and native omega-equivalence evidence.

The central checked theorem is triangle cut elimination. The central
mathematical theorem is the relationship between adjunction and
representability. Proof-relevance and the proposition-like status of chosen
adjoint structure must be stated at the level actually supported.

#### Chapter 13. Yoneda, Representability, And Profunctors

Fold the strongest prose from the current Chapter 10 into an adaptation of
HoTT 9.5. Progress from covariant/contravariant representables to the unit hom
profunctor, companions/conjoints, endpoint reindexing, representability, and
the shaped co-Yoneda beta.

The central checked computation is the shaped-element co-Yoneda cut. The full
Cat-valued Yoneda lemma, full faithfulness of the Yoneda embedding, semantic
coends, and a complete profunctor bicategory must retain their current
mathematical-development or research-boundary labels.

#### Chapter 14. Strictness, Dagger Structure, And Duality

Adapt HoTT 9.6-9.7 while preventing terminology collisions:

- HoTT strict category: its object type is a set;
- emdash strict computation: selected equations are runtime normal forms;
- strict transfor: both naturality directions compute;
- dagger category: a contravariant involution with a selected unitary notion
  of object equality;
- emdash opposite duality: active `Op_*` owners and their currently checked
  involutive/computational surface.

The dagger-category development is initially free-form unless an active
native dagger interface is identified. It should motivate, but not be
identified with, opposite-category duality.

#### Chapter 15. Structure Identity And Saturation

Adapt HoTT 9.8-9.9. Present the structure identity principle as the systematic
answer to “when does equality of carriers plus compatible structure coincide
with structured equivalence?” Relate it to the current evidence-property and
finite-truncation results without claiming they already implement the general
principle.

Present Rezk completion by its universal property first. Then compare the two
HoTT constructions:

- the image of the Yoneda embedding;
- a higher-inductive saturation construction.

The latter is pedagogically valuable because its proof again uses
encode-decode. The book should draw that structural analogy to Chapter 8 while
making clear that no general native Rezk completion is currently implemented.

#### Chapter 16. Weighted Universal Constructions

Develop the neighboring theory needed to make the active weighted interfaces
mathematically intelligible:

- weights as Cat-valued profunctors;
- weighted cones as maps into a represented profunctor;
- weighted limits as representability;
- tensors and internal hom as the calculus surrounding weighted
  representability;
- ordinary limits as suitable special cases;
- Kan-extension and end/coend readings as free-form extensions where needed;
- mate correspondence under an adjunction;
- preservation of weighted limits by right adjoints.

The chapter's central checked theorem is
`right_adjoint_preserves_weighted_limit_cov_comp`. The theorem should be
proved in book notation, with implementation names and formal status placed
after the mathematical argument.

#### Chapter 17. Weighted Colimits, Opposite Duality, And Join

Derive the colimit side through opposite duality and make
`left_adjoint_preserves_weighted_colimit_con` the central preservation
theorem. Then introduce join as a directed universal construction:

- two inclusions;
- a generating cross arrow/cell from the left part to the right part;
- internal naturality of the cross cell;
- nondependent recursion and beta laws;
- the expected collage interpretation as a research boundary;
- the missing dependent eliminator and hom decomposition.

The chapter should close by relating join back to directed HITs and explaining
why the construction is not merely a sum of groupoidal types.

### Adaptation matrix for HoTT Chapter 9

| HoTT source | Proposed destination | Emdash adaptation | Initial status |
| --- | --- | --- | --- |
| 9.1 Categories and precategories | Chapter 10 | Treat as the univalent 1-category specialization; compare with iterated `Cat`, finite height, and equality-local structure | mixed checked comparison / mathematical development |
| 9.2 Functors and transformations | Chapters 9 and 11 | Replace pointwise-only naturality with `tapp1` off-diagonal action and higher iteration | checked core, broader packaging mixed |
| 9.3 Adjunctions | Chapter 12 | Lead with unit/counit triangle cuts, then hom/profunctor representability | checked selected interface |
| 9.4 Equivalences | Chapters 10 and 12 | Separate carrier equivalence, ordinary iso, categorical equivalence, and native omega-equivalence evidence | mixed; full native object equality/iso equivalence deferred |
| 9.5 Yoneda | Chapter 13 | Use representables, unit profunctor, and shaped co-Yoneda beta; state full Cat-valued Yoneda boundary | checked slice plus mathematical development |
| 9.6 Strict categories | Chapter 14 | Keep object-set strictness distinct from rewrite strictness and strict transfors | mathematical development with checked truncation interfaces |
| 9.7 Dagger categories | Chapter 14 | Develop dagger/unitary structure free-form; compare, but do not conflate, with active opposite duality | mathematical development |
| 9.8 Structure identity principle | Chapter 15 | Use a structure-over-carrier schema and connect to evidence-property results | mathematical development / research boundary |
| 9.9 Rezk completion | Chapter 15 | State saturation universal property; compare Yoneda-image and HIT/encode-decode routes | research boundary |

Every adapted passage must be entered in
`book/references/third-party-sources.json` with the pinned revision, source
file, source label, adaptation type, and destination anchor before prose is
considered complete.

## The Došen Computational Spine

### Canonical notation contract

The book should ratify the following notation before Phase C2 prose is merged:

| Notation | Type pattern | Kernel reading |
| --- | --- | --- |
| `F[f]` | `F(x) -> F(y)` | functor action through `fapp*` |
| `u_*(g)` | if `g : w -> x`, `u : x -> y`, then `w -> y` | postcomposition, `u ∘ g`, through `hom_postcomp_*` |
| `u^*(g)` | if `u : x -> y`, `g : y -> z`, then `x -> z` | precomposition, `g ∘ u`, through `hom_precomp_along_*` |
| `eta[f]` | if `eta : F => G` and `f : x -> y`, then `F(x) -> G(y)` | off-diagonal action through `tapp1*` |

Simple inline mathematics should generally use Unicode (`->` in source only
when intentionally code-like; rendered prose may use `→`, `×`, `∘`, `⇒`, and
`≃`) or a real math span. Kernel identifiers alone belong in Markdown code
spans. TeX commands do not.

### Four levels of cuts

The exposition should distinguish four levels rather than presenting a flat
list of rewrite rules.

1. **Arrow cuts.** Precomposition and postcomposition turn one selected arrow
   into a functor on a represented hom. Their accumulation laws control local
   associativity.
2. **Family cuts.** `tapp1` packages an internally varying arrow family, and
   strict naturality absorbs cuts on either side.
3. **Structural cuts.** Products, projections, Sigma/Pi operations, curry,
   and displayed totals reduce eliminations applied to introductions or
   transport structured data through canonical maps.
4. **Universal cuts.** Adjunction triangles, representability comparisons,
   co-Yoneda beta, and weighted-limit beta/eta normalize maps through chosen
   universal objects.

The common theme is controlled reassociation at the semantic owner. The book
must not imply that emdash installs unrestricted associativity as a global
rewrite.

### Required worked examples

The chapter sequence should develop at least these examples in increasing
strength:

1. postcomposition accumulation;
2. precomposition accumulation and contravariant order;
3. both `tapp1` naturality cuts;
4. the typed product/projection benchmark;
5. a Sigma or product beta rule in Došen form;
6. the two adjunction triangle cuts;
7. the shaped co-Yoneda beta/fusion computation;
8. weighted-limit representability beta/eta;
9. preservation of a weighted limit by a right adjoint;
10. its weighted-colimit dual.

For every example, prose must identify:

- its mathematical source and target;
- the selected normal form;
- the generic or specialized owner;
- whether the equality is runtime reduction, proof-time comparison, checked
  propositional equality, or free-form mathematics;
- which higher action remains available after normalization.

## Formal Presentation Architecture

### Integration throughout the book

HoTT Appendix A's rule discipline should not be confined to a final appendix.
The following small conventions should appear throughout:

- new formers are explained by formation, introduction, elimination,
  computation, and optional uniqueness/universal principles;
- every chapter distinguishes external judgments from internal classifiers;
- runtime conversion, proof-time unification, equality evidence, and
  equivalence are never written as one undifferentiated equality;
- implicit arguments and readable notation are explicitly described as
  elaboration conveniences;
- each major eliminator is paired with its computation behavior and current
  uniqueness/universal-property status.

Chapter 1 should receive a concise forward pointer to the full appendix.
Chapters 5-8 should use the rule schema for arrow induction and the walking
HIT. Chapters 9-17 should use it for transfors and universal constructions.

### New Appendix G: Formal Presentation Of Functorial Type Theory

Appendix letters A-F are already occupied. Add a new Appendix G with the
following provisional structure.

#### G.1 Judgments, contexts, and classifiers

State the core judgments used in the book and explain the distinction between
the Lambdapi meta-level and internal `Cat`, `Obj`, `Hom`, `Functor`, and
`Transf` classifiers.

#### G.2 The mathematical categorical presentation

Give a compact first presentation in book notation: iterated homs, functors,
transfors, directed families, and their application operations. This is the
human-readable signature, not an untyped parser specification.

#### G.3 The checked Lambdapi presentation

Explain declarations, definitions, injective/opaque heads, rewrite rules,
proof-time unification rules, assertions, modules, and the selected
normal-form policy. Use small faithful excerpts and link each to active
owners; do not reproduce the whole kernel.

#### G.4 Formation, introduction, elimination, and computation

Apply the standard rule schema to representative structures:

- ordinary categories/functors/transfors;
- equality-local categories;
- Sigma/Pi or product structure;
- the WalkingEnd directed HIT;
- adjunctions and a weighted universal property.

This section should show both how the schema survives and how categorical
action adds an extra functorial/naturality layer absent from a pointwise
presentation.

#### G.5 Elaboration and canonical surface syntax

Describe implicit argument recovery, binder modes, notation desugaring, and
compilation into explicit categorical owners as a future interface. Mention
the parent TypeScript prototype only as historical/prototypical feasibility
evidence. State that no current book theorem depends on it.

#### G.6 Directed higher inductive signatures

Explain constructor, eliminator, coherence, beta, and height data using the
walking endomorphism as the fully worked case. Separate the selected HIT from
a not-yet-implemented general directed-HIT schema.

#### G.7 Basic metatheory and its boundary

Use a status table rather than importing the HoTT appendix's metatheorems as
claims about this rewrite system.

| Property | What the book may currently say |
| --- | --- |
| Typing of active sources | checked by bounded Lambdapi runs |
| Subject-reduction obligations of promoted rules | checked by the tool's ordinary rule acceptance; not a separately formalized global metatheorem in this project |
| Selected computation | witnessed by active rules and focused assertions/checks |
| Evidence traceability | checked syntactically by the book evidence tooling |
| Global confluence | not established for the whole emdash rewrite/unification theory |
| Strong normalization | not established for the whole theory |
| Canonicity | not established globally; only selected canonical computations are tested |
| Decidable conversion/type checking as a project theorem | not claimed beyond behavior of the current implementation/toolchain |
| Consistency and semantic soundness | model evidence and future metatheory, not a theorem silently inferred from successful compilation |

The appendix should explain why warning counts, critical-pair probes, and
normal-form discipline are engineering evidence rather than substitutes for a
global metatheory.

### Adaptation matrix for HoTT Appendix A

| HoTT source | Emdash destination | Adaptation |
| --- | --- | --- |
| A.1 The first presentation | G.2 plus Chapter 1 | Replace the raw type-term emphasis with a readable categorical signature and explicit distinction from end-user parsing |
| A.2 The second presentation | G.1, G.3, G.4 | Present judgments/rules through the actual Lambdapi encoding and categorical rule families |
| A.3 Homotopy type theory | G.6 plus Chapters 4, 6, 8 | Replace the circle-only extension story with equality/univalence layers and the selected directed WalkingEnd HIT |
| A.4 Basic metatheory | G.7 and Appendix E | Preserve the taxonomy of metatheoretic properties while weakening claims to the current evidence |

## Free-Form Theory Contract

The broader category theory is not filler. It should be written as serious
mathematics with an implementation route.

Each free-form definition or theorem must include, in its section status note:

1. the mathematical statement independent of kernel names;
2. the closest active interfaces;
3. the missing formal owner or construction;
4. the expected variance and higher-action obligations;
5. the likely validation benchmark;
6. the reason the result is pedagogically required now.

The principal neighboring developments are:

| Topic | Active foothold | Missing general theory |
| --- | --- | --- |
| Full Cat-valued Yoneda | representables, `Unit_prof`, shaped co-Yoneda | fully faithful Yoneda functor/package and all higher naturality |
| Coends and ends | symbolic `Prof_tensor`, shaped beta, profunctor implication | semantic quotient/coinserter or end/coend owner and coherence |
| Kan extensions | weighted representability and adjunction comparison | general pointwise Kan-extension package |
| Dependent adjunctions | Sigma/Pi and selected adjunction infrastructure | general `Sigma_F -| F^* -| Pi_F` theory with directed action |
| Structure identity | equality/univalence and evidence-property layers | generic structure-over-carrier theorem |
| Rezk completion | Yoneda/representability and selected HIT technology | saturation construction and universal property |
| Dagger categories | opposite-category operations | involutive identity-on-objects dagger and unitary equality package |
| Join as collage | primitive `Join_cat`, cross cell, recursor | semantic collage, hom decomposition, dependent eliminator |

This table should evolve into evidence-register entries only when actual book
sections are written.

## Typography And Rendering Remediation

### Source-mode contract

Every mathematical expression must choose one intentional source mode:

1. **Kernel code:** a real identifier or faithful source fragment in a
   Markdown code span/fence, with no expectation of mathematical rendering.
2. **Simple prose mathematics:** Unicode notation such as `→`, `×`, `∘`,
   `⇒`, or `≃` where it is clear and accessible.
3. **Structured mathematics:** a genuine inline or display math span parsed by
   KaTeX.

Do not put TeX commands in a code span to obtain typography. Do not put a
kernel identifier in math mode merely to make it italic.

### New semantic typography checker

Add a source-aware checker, provisionally
`scripts/check_book_typography.py`, during Phase C0. It should:

- reject TeX control sequences inside prose code spans unless an explicit,
  narrowly documented literal-code exception applies;
- parse Markdown fences and avoid treating real Lambdapi/shell examples as
  prose code spans;
- inspect math spans for suspicious bare control words such as `qquad`,
  `quad`, `longrightarrow`, `mathsf`, `operatorname`, `mathrm`, and `text`;
- use the renderer's KaTeX parser in strict/error mode for genuine math
  expressions where feasible;
- report source file, line, span kind, and a suggested mode change;
- carry regression fixtures for both currently observed defect families.

The generated-PDF gate should additionally scan extracted text for literal
`\to`, `\circ`, `\mathsf`, and bare TeX control names that should not
survive rendering. Because text extraction can produce false positives, this
is a review gate with a small explicit allowlist, not a replacement for source
parsing.

### Repair protocol

1. Inventory every affected source line before editing.
2. Repair malformed displays by reviewing the intended formula, not by a
   blind backslash substitution.
3. Convert code-span pseudo-math either to Unicode prose or real math spans.
4. Run source, evidence, provenance, link, math, and typography checks.
5. Render every affected page and inspect it at readable resolution.
6. Render all pages as contact sheets to catch secondary pagination changes.
7. run `book:release` twice from clean install/build states and compare
   checksums.
8. Change the edition version and recorded release checksum; do not continue
   presenting the old checksum as the repaired artifact.

The current PDF remains useful as the audit baseline, but it is not the
typographic acceptance baseline for the expanded edition.

## Implementation Phases

### Phase C0 - Repair notation and add semantic typography gates

State: **COMPLETE (2026-07-20).**

Deliverables:

- complete inventory of malformed displays and code-span pseudo-math;
- source repairs across the current 24-source edition;
- the semantic typography checker and regression fixtures;
- extracted-PDF sentinel checks;
- updated style and release guidance;
- a new deterministic PDF checksum under an incremented development version.

Gate:

- zero unexplained TeX commands in prose code spans;
- zero suspicious bare control names in parsed math;
- affected-page visual review and all-page contact-sheet review pass;
- all existing book checks and deterministic release checks pass;
- no content expansion is mixed into the typography patch except corrections
  necessary to make a malformed sentence mathematically meaningful.

Checkpoint:

- the audited 24-source edition had 52 TeX-bearing inline-code lines across
  eleven sources plus malformed display tokens in Chapters 1, 2, 4, 7, and 9;
  each expression was reviewed and moved to genuine math rather than repaired
  by blind substitution;
- `scripts/check_book_typography.py`, five regression tests/fixtures, and
  `print/scripts/check_book_katex.mjs` now distinguish fences, inline code,
  prose, and math, reject both observed defect families, and strict-parse all
  296 math spans in the repaired source;
- extracted-PDF sentinels, style/release/SOP guidance, root/print scripts, and
  CI wiring are active;
- development version `0.1.1-dev` rendered as a 103-page tagged US-Letter PDF
  with 14 embedded fonts; affected-page review and six all-page contact sheets
  passed, and two independent offline clean-install release cycles produced
  identical SHA-256
  `e581f84e140db1d0972ed95a5b1a1761ac5f9b6fb94f14c76bcaa95a58fd09af`;
- no Lambdapi definition, rule, check, or module boundary changed.

### Phase C1 - Ratify the global outline and translation contracts

State: **COMPLETE (2026-07-20).**

Deliverables:

- final chapter numbering and manifest migration plan;
- HoTT Chapter 9 adaptation ledger entries for all nine sections;
- HoTT Appendix A adaptation ledger entries for all four sections;
- category/precategory/strict-category/native-`Cat` comparison table;
- terminology decisions for strict, lax, equivalence, isomorphism,
  univalence, saturation, dagger, opposite, and duality;
- central theorem and formal-status target for every new chapter;
- evidence and research-boundary map before long prose is written.

Gate:

- no two chapters claim the same conceptual owner without an explicit spiral
  relationship;
- no proposed checked theorem lacks an active symbol/check route;
- every free-form theorem names its missing infrastructure;
- current Chapter 9/10 links can be migrated deterministically if those files
  are renumbered or split.

Checkpoint:

- `book/book.json` now assembles the contiguous Chapter 1-17 sequence and
  Appendix G. The former Chapter 9 source was renamed around the cut calculus;
  the former Chapter 10 was moved, renumbered, and re-anchored as Chapter 13,
  with affected glossary links migrated explicitly;
- `book/expansion.json` is the machine-readable C1 contract for conceptual
  ownership, spiral dependencies, central theorem/status targets, research
  boundaries, the native/HoTT category translation, the ten required
  terminology decisions, four formal-presentation layers, and the two source
  migrations. `check_book.mjs` validates the contract against the manifest,
  evidence register, chapter headings, and provenance ledger;
- Chapters 10-12 and 14-17 plus Appendix G have bounded theorem-led skeletons.
  The existing profunctor prose is now Chapter 13. Five newly cited checked
  routes cover adjunction triangles, opposite duality, weighted-limit and
  weighted-colimit preservation, and the join recursor; the evidence register
  contains 77 cited claims;
- `categories.tex` and `formal.tex` are pinned in the source map. Thirteen new
  adaptation records cover HoTT 9.1-9.9 and A.1-A.4 by exact upstream labels;
- the expanded source line is version `0.2.0-dev`. Its 32-source assembly,
  310-span typography/KaTeX gates, evidence/provenance/architecture checks,
  schema validation, and bounded browser render all pass.

### Phase C2 - Write the Došen vertical slice

State: **COMPLETE (2026-07-20).**

Deliverables:

- revised Chapter 9 organized around the four cut levels;
- canonical lower-star/upper-star/`tapp1` notation in Appendix A and the
  glossary;
- the ten-example progression, with at least the first six fully drafted;
- a focused typed probe and status decision for the product/projection
  benchmark;
- a short explanation of why controlled cut accumulation replaces a broad
  associativity rewrite.

Gate:

- the precomposition/postcomposition naming ambiguity is absent;
- every displayed reduction is typed and its equality mode is stated;
- no specialized rule is attributed to the kernel when computation is owned
  by generic `fapp*`/`tapp*` machinery;
- the chapter reads as a mathematical calculus, not a rule inventory.

Checkpoint:

- Chapter 9 is now a theorem-led calculus of arrow, family, structural, and
  universal cuts. It fully develops the first six examples and supplies the
  required source/target, normal form, owner, equality mode, and surviving
  higher action for all ten examples through co-Yoneda, weighted-limit
  beta/eta, right-adjoint preservation, and its colimit dual;
- the lower-star postcomposition, upper-star precomposition, and off-diagonal
  `tapp1` conventions are ratified in Appendix A and the glossary. The chapter
  explains why stable semantic owners and controlled accumulation replace a
  broad runtime associativity rewrite;
- the product/projection benchmark is stated at its intended generality: in a
  category `K` with chosen binary products, `A`, `B`, and their variants are
  objects of `K`, while `g`, `h`, and `k` are arrows. This general theorem is
  mathematical development pending an iterable internal chosen-product
  interface. The active formal probe is explicitly only the specialization
  `K = Cat_cat`, where category objects and functor arrows use `Product_cat`;
- focused probe `tmp/probes/book_product_projection_cut.lp` established that
  the Cat-specialized sides are well typed and that the owner-aligned Sigma
  projection plus nested upper-star cut reduce. Two permanent diagnostics in
  `emdash3_2_checks.lp` retain those facts. The literal raw composite
  `pi1 ∘ (h × k)` does not convert or unify directly with the selected
  `sigma_Fst(h × k)` observation, so `CUT-PRODUCT-PROJECTION` is correctly
  a formal consequence and no broad product eta or new kernel rule was added;
- checked evidence `CAT-HOM-CUTS`, `CAT-PRODUCT-CALCULUS`, and
  `PROF-COMPARISON-BETA-ETA`, plus the formal-consequence product claim, bring
  the register to 81 fully cited claims. The executable catalog includes the
  new owner-aligned product/projection diagnostics;
- Došen's 1999 *Cut Elimination in Categories* is recorded by DOI and as an
  all-rights-reserved, reference-only conceptual source. The locally supplied
  278-page PDF was consulted only to confirm its general cartesian-category
  setting and terminology; Chapter 9 is freshly written and copies no prose;
- the 32-source source/evidence/architecture/typography gates pass with 451
  strict-KaTeX math spans. Full `make ci` passes. The `0.2.0-dev` release is a
  122-page PDF with 14 embedded fonts and SHA-256
  `ec3764236a3c39f70d7895962e8dff5248f8fbbf59d3b4ebc35af9bafa44247b`;
  Chapter 9 pages 63-73 passed contact-sheet and focused page visual review.

### Phase C3 - Adapt categories through Yoneda

State: **COMPLETE (2026-07-20).**

Deliverables:

- Chapters 10-13 or their ratified equivalents;
- complete adaptations of HoTT 9.1-9.5;
- native-versus-univalent-1-category translation sidebars;
- theorem-led treatments of adjunction triangles, equivalence notions, and
  shaped co-Yoneda;
- revised current profunctor prose integrated into the Yoneda arc;
- provenance and evidence entries for every theorem-like claim.

Gate:

- the book never defines native `Cat` merely as a HoTT precategory;
- adjunction data, categorical equivalence, carrier equivalence, isomorphism,
  and omega-equivalence evidence are not conflated;
- full Yoneda statements beyond the current checked slice are visibly
  status-labeled;
- copied/adapted material passes the existing license/provenance gate.

Checkpoint:

- Chapters 10-13 now form the coherent HoTT 9.1-9.5 adaptation. Chapter 10
  distinguishes native iterable `Cat` from ordinary precategories, univalent
  categories, and strict categories, and separates object paths,
  path-generated arrows, ordinary isomorphisms, carrier equivalences, and
  omega-equivalence evidence. Chapter 11 develops ordinary natural
  transformations beside native off-diagonal transfors and their higher
  action. Chapter 12 organizes adjunctions, hom transposition,
  representability, and the full ladder of equivalence notions. Chapter 13
  proves ordinary Yoneda by encode-decode and then passes to the native
  representable/profunctor interfaces and shaped co-Yoneda computation;
- central checked routes are `EQUIV-ORDINARY-ISO-LIFT`,
  `TRANSF-STRICT-NATURALITY`, `TRANSF-HORIZONTAL-CALCULUS`,
  `ADJ-TRIANGLE-CUTS`, `ADJ-HOM-PROF-COMPARISON`, and `PROF-COYONEDA`.
  Ordinary univalent category and Yoneda theorems are explicitly
  **mathematical development**. Full Cat-valued Yoneda/full faithfulness
  remains the `YONEDA-FULLY-FAITHFUL` research boundary under `FTTX-S6`; the
  chapter does not promote the shaped theorem into a general coend result;
- nine additional evidence entries bring the register to 90 fully cited
  claims. All 32 sources, 681 strict-KaTeX math spans, pinned HoTT provenance,
  the expansion contract, evidence coverage, and the complete local CI gate
  pass; CI checked 39 Lambdapi files/examples and all 21 infrastructure tests;
- the `0.2.0-dev` release is now a 140-page PDF with 15 embedded fonts and
  SHA-256
  `f505c67069c0720795b0f29e9eac21dd1bcee88f68546aa5dfb8c41ad25fb7e0`.
  Every page of Chapters 10-13 (pages 74-100) passed contact-sheet review,
  with focused inspection of tables and displayed calculations. The review
  found and repaired one Chapter 11 orphan and one Chapter 12 status-note page
  split before the final release;
- no Lambdapi definition, rewrite, unification rule, check, or module boundary
  changed during C3.

### Phase C4 - Adapt strictness, dagger structure, SIP, and Rezk completion

State: **COMPLETE (2026-07-20).**

Deliverables:

- Chapters 14-15 or their ratified equivalents;
- complete adaptations of HoTT 9.6-9.9;
- a terminology box separating all meanings of strictness;
- a free-form dagger/unitary development connected carefully to opposite
  duality;
- a structure-identity schema with current evidence-property interfaces
  identified;
- a universal-property-first Rezk completion treatment and comparison of its
  Yoneda-image and HIT/encode-decode constructions.

Gate:

- no general SIP or Rezk completion is labeled checked without new evidence;
- the encode-decode analogy is explained without suggesting that WalkingEnd
  itself is a Rezk completion;
- dagger structure is not reduced to `Op_cat` alone;
- any implementation prerequisites are entered in the side-task ledger rather
  than improvised in book code.

Checkpoint:

- Chapter 10 and `book/expansion.json` now state the exact HoTT definition:
  a strict category is a precategory whose object type is a set and need not
  be univalent. Chapter 14 separates that object-set condition from native
  `IsNCat` height, strict `tapp1` naturality cuts, and runtime reduction;
  develops ordinary strict/gaunt and dagger/unitary categories; and uses the
  checked `Op_cat`, `Op_func`, `Op_transf`, and `Op_adjunction`
  calculus as its central duality theorem;
- Chapter 15 gives the ordinary structure-over-carrier schema and proof of the
  structure identity principle, identifies the checked evidence-property,
  truncated-universe, ordinary-isomorphism-lift, and finite-height footholds,
  and specifies the additional directed structure/equivalence action a native
  theorem would require. It presents Rezk completion by its functor-category
  mapping property, develops both the Yoneda-image and 1-truncated HIT
  constructions, and records the converse characterization of saturated
  categories by inversion of weak equivalences;
- the HIT discussion compares proof architectures without conflating
  constructions: Rezk adds invertible object paths for old isomorphisms,
  whereas WalkingEnd has a checked noninvertible directed generator and
  computes its based hom as Nat. The native SIP, dagger, and Rezk interfaces
  are explicit research specifications under `FTTX-S9` and `FTTX-S12`,
  not invented checked owners;
- seven new mathematical-development/research-boundary entries bring the
  evidence register to 97 fully cited claims. All 32 sources, 818
  strict-KaTeX spans, pinned HoTT provenance, expansion contracts, and full CI
  pass. CI checked 39 Lambdapi files/examples in 202.814 seconds and all 21
  infrastructure tests;
- the `0.2.0-dev` release is a 152-page tagged PDF with 15 embedded fonts
  and SHA-256
  `efdc7ca43aa9578e3121561092532dfac0ce07e4cd05158b4068a75f3ad5faee`.
  Every page of Chapters 14-15 (pages 101-113) passed contact-sheet review
  and focused inspection. The review found and repaired one orphaned
  Yoneda-image heading before the final release;
- no Lambdapi definition, rewrite, unification rule, check, or module boundary
  changed during C4.

### Phase C5 - Write weighted universals, duality, and join

State: **COMPLETE (2026-07-20).**

Deliverables:

- Chapters 16-17 or their ratified equivalents;
- mathematical development of weights, cones, representability, tensor,
  internal hom, mates, and relevant Kan/coend context;
- a complete theorem-led proof narrative for right-adjoint preservation of
  weighted limits;
- its opposite-dual weighted-colimit theorem;
- a join chapter centered on the cross-cell recursor and its directed-HIT
  reading;
- explicit semantic boundaries for coends, bicategorical coherence, collage,
  and dependent join elimination.

Gate:

- weighted limits and colimits appear as consequences of representability and
  adjunction, not independent features;
- duality is used as a proof method, with variance checked at every step;
- join is connected to the preceding profunctor/universal theory but not
  falsely claimed to be an implemented collage;
- every checked central theorem cites its active owner and diagnostic.

Checkpoint:

- Chapter 16 now develops parameterized weights, the cone profunctor, the
  selected tensor and its two residuals, computational representability,
  universal push/pull beta and eta, conical limits, conjoint-weighted right
  Kan extensions, adjunction mates, and the complete three-comparison proof
  that right adjoints preserve selected weighted limits. Chapter 17 derives
  the opposite-dual cocone and colimit theory, companion-weighted left Kan
  extensions, and left-adjoint preservation before developing join through
  its internally natural cross cell and nondependent recursor;
- side task `FTTX-S14` is complete. Four permanent diagnostics establish the
  exact variance-correct classifier instances: terminal weights
  `1 prof J` and `J prof 1` for conical limits and colimits, the conjoint
  `J' prof J` for right Kan, and the companion `J prof J'` for left Kan.
  The book separates those formal-consequence substitutions from the standard
  cone/cocone and pointwise Kan formulas, which remain mathematical
  development until semantic end/coend owners exist;
- the join recursor is connected globally to the universal-construction
  spine: `1 star J` supplies cone-shaped cross data and `J star 1` supplies
  cocone-shaped cross data, while the general collage mapping property is
  specified as the `FTTX-S13` research boundary. The chapter does not claim
  an object/hom decomposition, mapping-category equivalence, opposite
  comparison, or dependent eliminator for the primitive join;
- seven new checked/formal-consequence/mathematical-development/research-
  boundary entries bring the evidence register to 104 fully cited claims.
  The permanent specialization assertions regenerate the reviewer catalog;
  no Lambdapi definition, rewrite, unification rule, or module boundary
  changed;
- growth to 170 pages exposed a fixed 30-second PDF-pagination cap. The
  console and export gates now honor each document's existing registry-owned
  `timeoutMs`, documented in `print/README.md`, and the release completes
  without weakening its bounded execution or browser gates;
- all 32 sources, 1,038 strict-KaTeX spans, pinned provenance, expansion
  contracts, and full CI pass. CI checked 39 Lambdapi files/examples in
  216.771 seconds and all 21 infrastructure tests. The tagged `0.2.0-dev`
  PDF has 170 US-Letter pages, 15 embedded fonts, and SHA-256
  `ec6e4a5379bf00fe32e309273d1256e7c4199c0bac936e583b66f66eb54d2e7d`;
  every page of Chapters 16-17 (pages 114-131) passed visual inspection.

### Phase C6 - Add the formal-presentation appendix and elaboration boundary

State: **COMPLETE (2026-07-20).**

Deliverables:

- Appendix G in the structure above;
- concise rule-schema integrations in Chapters 1, 5, 6, 8, 9, and 16;
- a kernel/surface/elaborator/model architecture diagram or table;
- a conservative metatheory status matrix;
- a read-only parent-prototype note with no build dependency;
- complete HoTT Appendix A adaptation provenance.

Gate:

- the categorical kernel is presented as the computational core, not as a
  post-hoc semantics of an unspecified traditional syntax;
- no global confluence, normalization, canonicity, consistency, or
  decidability theorem is claimed without evidence;
- mathematical surface notation and literal Lambdapi syntax are visibly
  distinct;
- the parent TypeScript repository remains unchanged.

Checkpoint:

- Appendix G now supplies the complete seven-part formal presentation. It
  orders the computational categorical kernel before the canonical
  mathematical surface and optional future elaborator, while keeping external
  semantic models as a distinct fourth layer. It adapts all four pinned HoTT
  Appendix A units without treating native `Cat` as a post-hoc semantics for
  an unspecified traditional syntax;
- the appendix separates external judgments from decoded classifiers and
  distinguishes definitional reduction, proof-time unification, internal
  equality, directed cells, carrier equivalence, and categorical equivalence.
  Its rule ledger applies formation/introduction/elimination/computation/
  uniqueness/action to equality, categories, transfors, Sigma/Pi,
  WalkingEnd, adjunctions, and weighted representability;
- concise schema links in Chapters 1, 5, 6, 8, 9, and 16 connect the formal
  presentation to the prose without turning those chapters into a source-code
  catalogue. The Došen product/projection sentence is explicitly stated in an
  arbitrary category with chosen products; the Cat specialization remains
  implementation evidence only;
- three new evidence records bring the register to 107 fully cited claims.
  All 32 sources and 1,177 strict-KaTeX spans pass the source, typography,
  provenance, architecture, and evidence gates. The `0.2.0-dev` C6 snapshot
  is a tagged 188-page US-Letter PDF with 16 embedded fonts and SHA-256
  `759095f474819a063741a4be6424b873ad6cff867001e496224acc476f4d46d5`;
  every Appendix G page and all six affected chapter pages passed visual
  review;
- the parent TypeScript parser/elaboration prototype remains unchanged,
  read-only, non-authoritative, and absent from the build graph. No Lambdapi
  definition, rewrite, unification rule, check, or module boundary changed in
  C6.

### Phase C7 - Global editorial integration and expanded-edition release

State: **COMPLETE (2026-07-20).**

Deliverables:

- dependency and forward-reference edit across all chapters;
- terminology, notation, glossary, concept-index, and bibliography pass;
- central-theorem and status-note audit for every chapter;
- prose-quality and repetition edit across both spirals;
- updated contents, manifest, evidence appendix, credits, and source map;
- clean deterministic expanded-edition PDF and checksum.

Gate:

- a reader can follow either a type-theory, category-theory, or implementation
  reading path without encountering an undefined essential notion;
- all HoTT and other adapted sources have exact provenance;
- all checked claims resolve, all free-form claims expose their boundary, and
  no research boundary is hidden in ordinary theorem prose;
- source checks, typography checks, book checks, bounded render checks, and
  two clean release builds pass;
- page-level visual QA samples every new chapter and every page affected by
  pagination changes.

Checkpoint:

- the preface, prologue, and reading guide now describe both mathematical
  spirals and give explicit type-theory, category-theory, and implementation
  paths. The contents, chapter transitions, title-cased headings, notation
  appendix, glossary/concept index, status matrix, bibliography, credits, and
  license were edited as one navigation and terminology system;
- every numbered chapter has a formal-status note and a cited central theorem.
  The source checker validates the retained Chapter 1-8 spine as well as the
  Chapter 9-17 expansion against `book/expansion.json`, while all 107 checked
  claims resolve through the evidence register. All HoTT adaptations retain
  exact labels and the pinned revision
  `578b85cc8d586b1677ec4335148adeb443057d24`; Došen remains a cited,
  reference-only conceptual source;
- all 32 sources, 1,274 strict-KaTeX spans, manifest/schema checks, provenance
  checks, source links, bounded page rendering, browser console/request
  checks, and extracted-PDF sentinels pass. A fresh
  `npm --prefix print ci --offline` installed the locked dependency graph with
  zero reported vulnerabilities;
- visual QA reviewed all 192 pages by contact sheet, every new chapter and
  appendix opening at readable resolution, and every locally repaginated
  front-matter/glossary page. The pass repaired a dropped preface fragment and
  two stranded run-in/punctuation cases before the sources were frozen;
- full repository CI passed all 39 measured Lambdapi files and examples in
  267.587 seconds, all 21 infrastructure tests, the 86-heading source TOC,
  active-reference and report-header lints, the zero-unreviewed strict-LHS
  audit with 45 annotated slots across 27 clauses, and the fresh strict check
  catalog;
- two independent frozen-source release builds produced the same tagged
  192-page US-Letter PDF with 16 embedded fonts and SHA-256
  `fbaeb7ea8438a4842c2ea15e7a3671473f6485a1c4b663c2b3b55964c189ef47`.
  C7 changed no Lambdapi semantics, and the parent TypeScript prototype
  remains unchanged, non-authoritative, and outside the build graph.

## Phase Ordering And Change Discipline

The recommended order is `C0 -> C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7`.
Limited drafting for C1/C2 may proceed while C0 is being diagnosed, but no
large prose merge should land on top of known broken notation because it would
expand the audit surface.

Each phase should prefer editorial and evidence changes over kernel changes.
When a book example exposes a missing formal owner:

1. state the mathematics and current status accurately;
2. add or resume a side task;
3. design a focused formalization plan;
4. implement only under separate authorization;
5. return to the book after checks establish the intended interface.

Do not combine chapter renumbering, broad prose import, renderer migration,
and kernel normal-form changes in one patch.

## Acceptance Criteria For The Expanded Architecture

The architecture is successful when:

1. WalkingEnd/Nat remains the memorable opening computation.
2. Došen cut elimination supplies a continuous explanatory line from ordinary
   composition through universal properties.
3. All HoTT Chapter 9 topics occur in a mathematically coherent order, with
   native directed/higher distinctions rather than superficial renaming.
4. Adjunctions, weighted limits, colimits, duality, and joins are central
   theorem chapters rather than an implementation inventory.
5. HoTT Appendix A's formal discipline is adapted to a
   categorical-kernel-first presentation.
6. The book makes clear that a later convenient syntax elaborates into the
   computational categorical core; it does not precede or define that core.
7. Free-form category theory is rigorous, status-labeled, and paired with a
   plausible emdash implementation route.
8. The parent TypeScript prototype remains deferred and non-authoritative.
9. The PDF contains no known raw TeX commands, missing-control-sequence words,
   or source-mode confusion.
10. Every theorem-like statement satisfies the evidence/provenance contract
    and every released artifact is reproducible.

## Risks And Mitigations

### Treating ordinary univalent categories as the native omega architecture

Mitigation: require the category-translation matrix in C1 and repeat the
specialization boundary at the start of Chapters 10 and 15.

### Colliding meanings of strictness

Mitigation: reserve qualified phrases - strict category, strict transfor,
strict/runtime computation - and never use bare “strict” where two meanings
are possible.

### Reversing precomposition and postcomposition

Mitigation: ratify the typed star-notation table, type every first use, and
make the product/projection benchmark a regression example.

### Turning a theorem chain into a feature catalogue

Mitigation: give every chapter one central theorem, one motivating question,
and one explicit dependency on the preceding chapter.

### Overstating checked support for free-form mathematics

Mitigation: require an owner/missing-owner/status block for every unimplemented
definition or theorem and keep the evidence checker strict about “checked.”

### Importing HoTT prose without adapting its truncation assumptions

Mitigation: adapt by labeled source unit, rederive each statement in the
iterated-hom setting, and preserve the source revision/license ledger.

### Making the obsolete elaborator an accidental dependency

Mitigation: keep the parent review read-only, prohibit imports/build steps from
it, and defer any compiler work to a fresh RFC.

### Mistaking successful rendering for correct mathematics

Mitigation: add source-mode lint and extracted-text sentinels, then combine
them with page-level visual inspection.

### Claiming global metatheory from local checks

Mitigation: use the conservative G.7 matrix and distinguish tool acceptance,
regression evidence, and mathematical metatheorems.

## Proposed Decisions

1. **Expansion:** begin a C-series follow-on rather than reopening completed
   B phases.
2. **Scope:** include all HoTT Chapter 9 topics in the expanded edition.
3. **Universal constructions:** include weighted limits, weighted colimits,
   adjunctions, duality, and joins through central theorems.
4. **Computational thesis:** use Došen cut elimination as the bridge between
   functorial substitution and universal properties.
5. **Notation:** `u_*(g) = u ∘ g` is postcomposition;
   `u^*(g) = g ∘ u` is precomposition.
6. **Category boundary:** treat HoTT precategories/categories as an important
   1-categorical specialization, not the definition of native `Cat`.
7. **Formal presentation:** add Appendix G and integrate its rule discipline
   throughout the main text.
8. **Layering:** categorical kernel first, mathematical surface second,
   optional elaborator third, external models as a separate semantic layer.
9. **Parent prototype:** review-only and deferred; no TypeScript work in this
   plan.
10. **Typography:** C0 blocks the expanded prose merge until semantic notation
    lint and the current-source repair pass.
11. **Free-form theory:** admit it wherever needed for coherence, with explicit
    owners, missing prerequisites, and formal status.
12. **Module boundaries:** retain the present Lambdapi organization unless a
    separately authorized formal task demonstrates a concrete need.

## Side Task Ledger

| ID | Task | State | Blocking condition or promotion trigger |
| --- | --- | --- | --- |
| `FTTX-S1` | Implement semantic book-typography lint and PDF sentinels | complete, C0 | repaired `0.1.1-dev` release baseline recorded above |
| `FTTX-S2` | Complete the HoTT Chapter 9 adaptation/concordance ledger | complete, C1 | all nine sections have pinned labels and manifest targets |
| `FTTX-S3` | Complete the HoTT Appendix A adaptation/concordance ledger | complete, C6 | all four pinned sections are adapted in Appendix G with exact provenance |
| `FTTX-S4` | Probe and package the fully typed product/projection Došen benchmark | complete, C2; general `K` mathematical development, Cat-specialized formal consequence | owner-aligned legs are permanent diagnostics; literal raw projection bridge remains unpromoted |
| `FTTX-S5` | Ratify native `Cat` versus precategory/category/strict-category translation | complete, C1 | enforced in `book/expansion.json` and stated in Chapter 10 |
| `FTTX-S6` | Package a full Cat-valued Yoneda/full-faithfulness theorem | deferred formal extension; not required by C3 | shaped co-Yoneda is sufficient for the current chapter; promote only for a concrete stronger checked consumer |
| `FTTX-S7` | Develop semantic coend/end and tensor coherence | deferred research task; C5 semantic specification complete | promote for a general rather than shaped co-Yoneda theorem |
| `FTTX-S8` | Develop general dependent adjunctions `Sigma_F -| F^* -| Pi_F` | deferred research task; C5 book boundary complete | promote for a checked dependent Kan/limit consumer |
| `FTTX-S9` | Design generic structure identity and Rezk completion interfaces | deferred research task; C4 book specification complete | Chapter 15 states the prospective signature, equivalence choice, saturation predicate, unit, local action, and higher mapping property; implementation requires a separately authorized formal task |
| `FTTX-S10` | Write a future surface-to-Lambdapi elaborator RFC | deferred; C6 boundary complete and parent repository out of scope | only after the canonical surface and kernel mapping stabilize |
| `FTTX-S11` | Verify Došen bibliography, quotation limits, and adaptation/license provenance | complete, C2; reference-only use | DOI and all-rights-reserved no-copy policy recorded in bibliography, credits, and provenance |
| `FTTX-S12` | Design a native dagger/unitary category interface | deferred research task; C4 book specification complete | Chapter 14 states the functor, object, involution, higher-action, unitary, and univalence requirements; checked promotion requires a concrete consumer and separately authorized formal task |
| `FTTX-S13` | Develop join-as-collage semantics and dependent elimination | deferred research task; C5 target universal property specified | promote under separate authorization for hom decomposition, mapping equivalence, and dependent elimination |
| `FTTX-S14` | Audit ordinary limits and Kan extensions as special cases of the selected weighted interface | complete, C5; interface substitutions formal consequence, semantic formulas mathematical development | four permanent variance diagnostics cover terminal, conjoint, and companion weights without claiming missing end/coend semantics |

## Recommended Next Action

Treat the completed `0.2.0-dev` artifact as the expanded development-edition
baseline and seek mathematical and editorial review of the whole book. Any
promotion of the deferred Yoneda, coend, dependent-adjunction, native
SIP/Rezk, dagger, or join-as-collage boundaries should begin as a separately
authorized formal task with a concrete consumer; it should not reopen C0-C7
or make the historical parent elaborator an implicit dependency.
