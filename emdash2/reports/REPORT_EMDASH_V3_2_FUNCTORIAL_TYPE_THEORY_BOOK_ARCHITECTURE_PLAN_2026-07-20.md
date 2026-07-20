# Functorial Type Theory: Book Architecture And Implementation Plan

Date: 2026-07-20
Last reviewed: 2026-07-20
Plan-ID: EMDASH-V3-2-FUNCTORIAL-TYPE-THEORY-BOOK-ARCHITECTURE-2026-07-20
Depends-On: REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26; EMDASH_FOUNDATIONS; REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05; REPORT_EMDASH_V3_2_WALKING_ENDOMORPHISM_DIRECTED_HIT_PLAN_2026-07-17; REPORT_EMDASH_V3_2_REORGANIZATION_PLAN_2026-06-16; REPORT_EMDASH_V3_2_RESEARCH_ARTICLE_ARCHITECTURE_2026-06-05; REPORT_EMDASH_V3_2_INDEX_3_2_READABILITY_IMPLEMENTATION_PLAN_2026-06-06
Supersedes: none
Side-Task-Ledger: #side-task-ledger
Infinity-Codex-Origin: current-session-functorial-type-theory-book-review-2026-07-20
Infinity-Codex-Decision-Responses: none
Status: **COMPLETE — Phases B0–B6 completed on 2026-07-20; optional Phase B7 was not triggered and remains deferred**

## Executive Decision

Create a new first-class book, provisionally displayed as
*Functorial Type Theory: Univalent Foundations for Mathematics*. It is a new
artifact, not a rename or incremental extension of
`print/public/index_3_2.md`.

The initial book should use a spiral exposition:

1. open with the walking-endomorphism/Nat theorem and explain why it matters;
2. develop only the prerequisites needed to understand it;
3. return in Chapter 8 to the complete directed encode-decode argument;
4. expand outward to arrow induction, transfors, laxity, higher cells,
   Eckmann--Hilton, profunctors, and the broader functorial-foundations
   programme.

The recognizable HoTT Book spine should be retained deliberately. In
particular, Chapter 8 should contain a section `8.1` whose
subsections parallel “Getting started / classical proof / universal cover /
encode-decode proof.” The mathematical substitution is not merely
`S¹ -> WalkingEnd` and `Z -> Nat`. The groupoidal loop of
the circle is invertible, whereas the walking generator is directed and
provably noninvertible. The new proof must make this contrast its central
idea.

Author the book as chapter-sized source files from the beginning, then
assemble one ASCII-named Markdown render input,
`print/public/emdash-book.md`. The typographic em dash may appear in
the displayed title, but it should not occur in the filename: the current
loader and validators reject it.

Writing should begin before any definition-level split of
`emdash3_2.lp`. The present section organization and already
extracted dependent modules are sufficient evidence for an initial edition.
A physical module split is a later, separately validated migration and must
not be mixed with semantic or notation changes.

## Scope Of This Plan

This plan covers four coordinated workstreams:

- the mathematical and pedagogical architecture of the book;
- traceability from prose claims to checked emdash evidence;
- a maintainable multi-file authoring and deterministic rendering workflow;
- limited documentation and source-organization maintenance needed to keep
  the book honest.

It does not authorize the following work:

- changing the meaning or normal forms of active Lambdapi declarations;
- identifying `WalkingEnd_cat` definitionally with
  `BNat_cat`;
- claiming a full hom-category equivalence or functor-category initiality
  that has not been implemented;
- claiming a complete weak omega-category foundation or a complete
  computational univalence principle;
- copying HoTT Book prose without attribution and ShareAlike compliance;
- replacing the local print renderer wholesale before parity tests exist.

## Review Baseline

The review was performed against the clean `main` worktree at
`4b62daf`. Before documentation edits:

- `git status --short`, the unstaged diff, and the staged diff were
  empty;
- `EMDASH_TYPECHECK_TIMEOUT=60s make check` passed in about 14
  seconds;
- the active implementation, checks, reviewer examples, current SOP,
  Foundations, canonical syntax, report index, reorganization plans, and
  print guidance were inspected;
- the local `/home/user1/arrowgram` repository was clean at
  `ed498a9ec430f3aa6ef5e783cf84228c155e8015`;
- the HoTT Book was cloned only for review to a temporary directory outside
  the emdash Git worktree.

The reviewed HoTT source revision is
`578b85cc8d586b1677ec4335148adeb443057d24`, dated 2026-05-12.
Its README licenses the work under Creative Commons
Attribution-ShareAlike 3.0 Unported. Any copied or adapted text therefore
needs explicit attribution, provenance, and a compatible ShareAlike license
for the book artifact.

The current print schema validation passed for all three existing
`index*.md` papers. A bounded 60-second
`npm run check:render` run completed validation and entered the
production build/browser phase, but exceeded the bound before producing a
final result. The timeout left a preview child process, which was stopped
manually. This is a performance and cleanup observation, not evidence that
the renderer is semantically broken.

## Findings

### 1. The implementation already contains a book-worthy central theorem

The current source is substantially stronger than
`print/public/index_3_2.md`. The active files have the following
roles:

| File | Current role |
| --- | --- |
| `emdash3_2.lp` | 19,201-line active core calculus, organized into sections 0--20 |
| `emdash3_2_eq1_hom_action.lp` | derived equality-valued next-hom action and groupoidality |
| `emdash3_2_eq1_evidence_property.lp` | evidence-property, retract truncation, and finite-category object truncation |
| `emdash3_2_nat_arithmetic.lp` | reusable Nat successor, addition, associativity, proposition evidence, and sethood |
| `emdash3_2_walking_end_hit.lp` | walking directed HIT, Code, encode/decode, Nat comparison, and negative results |
| `emdash3_2_checks.lp` | executable regression suite |

The selected walking object is intentionally opaque:

```
WalkingEnd_cat
walking_base : Obj(WalkingEnd)
walking_loop : Hom_WalkingEnd(base, base)
walking_end_is_one_cat : IsNCat(1, WalkingEnd)
```

Its computation principle is contextual. The primary eliminator
`walking_end_ind_funcd` maps between two displayed families and
accepts a loop-coherence transfor. Ordinary dependent sections and the
nondependent recursor are derived specializations. Both base and loop
observations have checked runtime projection behavior.

The central computation is already implemented in the following order:

1. `walking_Code_catd` is the Cat-valued family with
   `Code(base) = Path(Nat)` and generator action
   `NatSucc_func`.
2. `walking_encode` transports zero along a based arrow.
3. `walking_power` sends zero to the identity and successor to
   generator-prefix composition.
4. The explicit restricted-CoreIncl spiral supplies the coherence needed for
   `walking_directed_decode_funcd`.
5. For every based arrow `p`,
   `walking_directed_normalization_cell` first constructs a directed
   2-cell
   `p -> decode(encode(p))`.
6. Only afterward does one-dimensionality turn that cell into the equality
   `walking_directed_normalization_path`.
7. The hard inverse
   `power(encode(p)) = p` and the Nat-inductive inverse
   `encode(power(n)) = n` form
   `walking_hom_nat_type_equiv`.
8. The same comparison gives sethood and proves that the generator is not the
   identity, has no right inverse, and carries no
   `OmegaEquivAlong` evidence.

The resulting checked statement is an underlying carrier equivalence

```
Hom_WalkingEnd(base, base) ≃ Nat.
```

For readable prose it is reasonable to call this “the endomorphisms of the
walking endomorphism are the natural numbers,” provided a formal-status note
states that the current artifact packages a carrier
`TypeEquiv` and native omega-equivalence facade. It does not yet
package:

- a reverse functor `BNat -> WalkingEnd`;
- a full equivalence of hom-categories;
- preservation of composition/addition as a packaged monoid isomorphism;
- the full initiality or universal mapping property of
  `WalkingEnd_cat`.

These are natural strengthening targets, not facts to silently infer.

### 2. `BNat` is a model and comparison object, not a definition

`BNat_cat` has one object, Nat-valued hom, zero identity, and
recursive composition. It supplies a concrete one-object free-monoid model
and a functor out of `WalkingEnd_cat`. The active examples explicitly
check that:

- `Obj WalkingEnd_cat` is not definitionally
  `Unit_grpd`;
- its based hom is not definitionally `Path_cat Nat_grpd`;
- its identity and composition are not replaced by the concrete
  `BNat` rules.

This separation is pedagogically valuable. The book can first show the
expected classical/free-monoid model and then prove that the opaque HIT has
the same based endomorphism carrier. It must not collapse the two levels.

### 3. The old v3.2 article is an inventory source, not the book draft

The last commit touching `print/public/index_3_2.md` is
`72c59d68a08f0f40eaae4369f27e9d6e05668a53` from 2026-07-01.
Relative to the nearby user-identified
`5b2b4024e13b81b659422d8c370acd9eba5de60f` baseline, the current
active implementation has roughly 15,568 inserted lines across the core,
native equality modules, Nat module, and walking module.

The article still contains useful material:

- coherence as computation;
- the functorial interpretation of functions;
- directed families and Sigma/Pi structure;
- `PathOut` and arrow induction;
- strict/lax transformations;
- profunctors, tensor/co-Yoneda, weighted limits, duality, and join;
- the distinction between rewrite-time and proof-time computation.

It does not contain the WalkingEnd/`BNat` development,
the current native equality-valued module boundary, or the
Eckmann--Hilton slice. Its univalence discussion also predates the current
evidence-property and finite-dimension results. It should therefore be cited
and mined paragraph by paragraph, but not edited into the book or treated as
a current feature inventory.

### 4. The living documentation has clear roles but accumulated history

The current orientation documents are valuable, yet their boundaries have
blurred:

- `EMDASH_FOUNDATIONS.md` combines mathematical explanation,
  present status, retired D0/D1 history, and implementation chronology.
- The current SOP is authoritative but contains a long chronological baseline
  ledger and at least one stale deferred item concerning eventual deletion of
  the already-deleted compatibility module.
- The canonical syntax report is a strong notation authority for categorical
  and directed binders, but does not yet settle book notation for
  WalkingEnd, Code, encode/decode, equality/univalence, or truncation.
- `README.md` duplicates much of the feature inventory that belongs
  in the SOP and Foundations.
- the root `AGENTS.md` is appropriately operational and should
  remain concise;
- `print/AGENTS.md` mixes operational rules, local patch history,
  a diagram-generation prompt, and a long academic-writing prompt.

The right consolidation is a separation of authority, not a merge into one
larger file.

### 5. The print project works, but paper discovery is hard-coded

The current renderer:

- loads Markdown through `print/src/App.tsx`;
- supports KaTeX, Mermaid, Vega-Lite, and Arrowgram blocks;
- sanitizes generated HTML;
- uses Paged.js for the preview;
- auto-validates only filenames matching
  `index(?:_[A-Za-z0-9]+)*.md`;
- allows the browser loader only ASCII filenames matching
  `[A-Za-z0-9_.-]+.md`;
- imports KaTeX print CSS from a CDN during pagination;
- relies on browser “Print / Save PDF” rather than producing a deterministic
  checked PDF artifact.

Consequently, `print/public/emdash—book.md` would neither load by
name nor participate in existing validation. Even
`print/public/emdash-book.md` would load but would not be
auto-discovered by the validators.

The package already imports the local upstream core directly:

```
"@hotdocx/arrowgram": "file:~/arrowgram/packages/arrowgram"
```

`npm ls` confirms this is a symlink to
`/home/user1/arrowgram/packages/arrowgram`. This is convenient for
one workstation but makes `npm ci` and the lockfile
host-dependent. At review time, the npm registry and local manifests agree on
`@hotdocx/arrowgram@1.0.0` and
`@hotdocx/arrowgram-web@1.1.0`.

The local `@hotdocx/arrowgram-web` package is the modern shared
preview pipeline, but the emdash print fork has useful local behavior that
must not be lost: document discovery, paper selection, Markdown table
handling, sanitization hardening, and console checks. The local validator also
duplicates an incomplete Arrowgram Zod schema even though the core package
exports `arrowgram.schema.json`.

### 6. The relevant HoTT spine is smaller and more precise than “copy Chapters 1--8”

The direct source dependencies of HoTT §8.1 through §8.1.4 include:

- functions, dependent families, identity/path induction, transport, and
  transport along composition;
- natural-number and coproduct encode-decode examples;
- equivalences and the total-space/fibre theorem for the classical proof;
- the circle recursor and dependent eliminator;
- dependent paths and computation for a higher constructor;
- integers, sign induction, and powers of a loop;
- sethood/truncation;
- univalence, used to turn successor on the integers into a path in the
  universe.

For the emdash proof, several of these concepts change role. Dependent
families become Cat-valued directed families, path transport becomes functor
action, the circle eliminator becomes a contextual displayed eliminator,
integer induction becomes Nat induction, and path induction in the hard
round-trip is replaced by a directed normalization cell followed by
hom-discreteness.

The revision-pinned source map for adaptation is:

| HoTT source | Material to use |
| --- | --- |
| `introduction.tex` and `preliminaries.tex` | motivation, judgments, functions, families, Sigma/Pi, Nat, identity types, and path induction |
| `basics.tex` | functoriality of transport, families as fibrations, `thm:transport-compose`, and the coproduct/Nat encode-decode pattern |
| `equivalences.tex` | equivalence interfaces and `thm:total-fiber-equiv` for the classical comparison |
| `logic.tex` | contractibility of the based path total space via `thm:contr-paths` |
| `hits.tex` | dependent paths, circle recursion/induction, constructor computation, integers, sign induction, and loop powers |
| `hlevels.tex` | propositions, sets, truncation, and the sethood argument used to discharge higher coherence |
| `homotopy.tex` §§8.1--8.1.4 | the exact “getting started / classical proof / universal cover / encode-decode” rhetorical sequence |

The temporary clone is review evidence only. Do not vendor the upstream Git
repository into emdash; record its commit and license in
`book/references/third-party-sources.json` instead.

## Mathematical Thesis

The first edition should be organized around the following statement.

> A freely generated directed endomorphism can be measured by a Nat-valued
> code. Every based endomorphism admits a directed normalization toward the
> corresponding power of the generator, and one-dimensionality turns that
> normalization into equality. Hence the underlying based endomorphism
> carrier is equivalent to the natural numbers. Unlike the loop of the
> circle, the generator is not invertible.

This is more than a directed imitation of the circle computation. It explains
why functorial type theory needs both groupoidal equality and genuinely
directed arrows:

- equality supplies paths, transport, equivalence, and truncation;
- categories supply noninvertible arrows;
- functors make substitution/action computational;
- directed families express dependent categorical structure;
- transfors and their hom-actions express coherence;
- dimension evidence can turn a directed higher cell into equality at the
  appropriate boundary without making the original arrow invertible.

The natural-number computation should therefore be the reader's first
complete demonstration of the programme, not an appendix after a complete
catalog of syntax.

## The HoTT-To-Emdash Adaptation

The book should state the comparison explicitly.

| HoTT circle proof | Functorial/directed proof | Important difference |
| --- | --- | --- |
| Circle `S¹` with `base` and loop | `WalkingEnd` with `walking_base` and `walking_loop` | The circle loop is an identity path and hence invertible; the walking loop is a directed arrow |
| Loop space `base = base` | Based hom carrier `Hom(base,base)` | The latter is not group-completed |
| Integers `Z` | Naturals `Nat` | Negative powers disappear |
| Universal cover `Code : S¹ -> Type` | Directed family `Code : WalkingEnd -> Cat` | The target action may be a non-equivalence |
| Successor equivalence on `Z`, converted by univalence | Successor functor on `Path(Nat)` | No predecessor or universe path is required |
| `encode(p) = transport Code p 0` | `walking_encode(p) = Code[p](0)` | Transport is functorial directed action |
| Integer-indexed loop powers | Nat-indexed directed powers | Only zero and successor cases |
| Circle-dependent `decode` | Contextual displayed decoder | Coherence is an explicit spiral |
| Hard inverse by path induction | Directed normalization cell, then hom-discreteness | Direction is retained until the last step |
| Easy inverse by circle/integer induction | Nat induction and generator-prefix action | No negative case |
| `Omega(S¹) ≃ Z` as groups | `Hom_W(base,base) ≃ Nat` as carriers | Monoid preservation is expected but not yet packaged |

The prose may reuse the HoTT explanation of encode-decode and the
“generalize from a fixed fibre to all fibres” lesson, with attribution.
It must rewrite every passage whose logic depends on:

- inverse paths;
- predecessor on the code;
- successor being an equivalence;
- univalence turning that equivalence into a universe path;
- cancellation in a group;
- path induction on the based loop as the proof of the hard inverse.

### The role of univalence in the new book

The title's “univalent foundations” should not force univalence artificially
into the WalkingEnd calculation. The contrast is itself instructive:

- in the HoTT proof, univalence is essential to make the integer successor
  equivalence into the circle's universe-valued loop;
- in the directed proof, the Cat-valued family sends the generator directly
  to a successor functor, which need not be invertible;
- elsewhere, emdash has checked groupoid univalence, restricted truncated
  universe univalence, equality-valued omega-equivalence packages, and
  one-way hom action;
- a globally coherent computational univalence theory for all intended
  omega-categorical structures remains a research boundary.

The book should present univalence as a precise layer in the foundation, and
label which uses are checked, derived, or prospective.

## Formal-Status Contract

Every theorem-like claim in the book must belong to one of four statuses.

| Status | Meaning | Required support |
| --- | --- | --- |
| **Checked** | A Lambdapi declaration and regression/reviewer check establish the stated interface | owning file, symbol, and check/example |
| **Formal consequence** | A short mathematical consequence of checked interfaces, not yet packaged under the stated name | cited premises and an explicit note that packaging is absent |
| **Mathematical development** | Free-form category theory designed to be plausibly implementable in emdash | prerequisites, proposed owner, and no “the kernel proves” wording |
| **Research boundary** | Conjectural, underspecified, or known to require new infrastructure | blocking capability and intended experiment |

These labels need not clutter every paragraph. Use a compact margin block or
end-of-section “Formal status” note. The main prose should use mathematical
notation first and kernel names second.

Create a machine-readable evidence register, initially
`book/evidence.json`, with entries such as:

```
{
  "WE-HOM-NAT-CARRIER": {
    "status": "checked",
    "statement": "Hom_W(base,base) is equivalent to Nat as a carrier",
    "owners": [
      "emdash3_2_walking_end_hit.lp:walking_hom_nat_type_equiv"
    ],
    "reviewers": [
      "examples/walking_endomorphism_hit.lp"
    ]
  }
}
```

The checker should verify file and symbol existence, not attempt to parse or
re-prove mathematical prose. Exact line numbers must not be stored because
they drift.

## Proposed Book Architecture

### Front matter

The initial front matter should contain:

- title and edition status;
- authorship/contributor policy;
- licensing and HoTT attribution;
- preface: why directed structure changes univalent foundations;
- “How to read this book” paths for type theorists, category theorists, and
  implementers;
- formal-status legend;
- notation guide and the relation between mathematical and Lambdapi syntax.

### Prologue: The natural number hidden in a directed loop

Lead with a theorem preview requiring only informal category theory:

1. introduce the category freely suggested by one object and one
   endomorphism;
2. show the list `id, loop, loop², ...`;
3. introduce the opaque HIT and the concrete `BNat` model as
   separate objects;
4. state `Hom_W(base,base) ≃ Nat`;
5. preview Code, encode, power, and directed normalization;
6. state the noninvertibility theorem;
7. give a map of Chapters 1--8 showing where every missing notion is built.

This prologue is motivational and must not pretend that the displayed list is
already an exhaustiveness proof.

### Chapters 1--7: the prerequisite spine

The initial contents should adapt the role, not necessarily the exact wording,
of the HoTT Book's first seven chapters.

#### Chapter 1. Judgments, universes, and computation

- terms, types/classifiers, definitional equality, and propositions-as-types;
- the distinction between runtime rewrite, proof-time unification, and
  equality evidence;
- ordinary functions, dependent functions, products, Sigma and Pi;
- Unit, Empty, Bool as needed, and Nat with induction;
- the emdash/Lambdapi reading without exposing raw implementation detail too
  early.

Formal owners: early sections of `emdash3_2.lp` and the ordinary
type-former/equality infrastructure.

#### Chapter 2. Categories, functors, and directed families

- objects, hom-categories, identities, and composition;
- iterated homs and the omega-oriented reading;
- groupoids and `Path_cat` as the equality-local fragment;
- functors as operations acting on every cell;
- transfors and their object/hom projections;
- Cat-valued families, fibres, and reindexing along arrows;
- sections, contextual functors, and representable families;
- dependent Sigma/total categories and dependent Pi;
- hom-indexed families, covariance, contravariance, and mixed variance;
- strict computation versus propositional coherence.

This chapter adapts the HoTT themes “functions are functors” and “families are
fibrations” by making both functorial action and directed transport explicit
rather than deriving them solely from identity types. The full advanced
calculus can be deferred; the first pass needs only the interfaces consumed
by Chapters 5--8.

#### Chapter 3. Logic, propositions, and sets

- propositions-as-types and the basic logical operations;
- proposition and set evidence;
- Unit, Empty, decidability examples, and constructive negation;
- equality of proofs versus evidence that a classifier is a proposition;
- constructive logic and what is not assumed.

The deeper recursive truncation and categorical-dimension layer is postponed
to Chapter 7, matching its role immediately before the Chapter 8
calculation.

#### Chapter 4. Equivalences and univalence

- maps with inverse data, contractible fibres, and
  `TypeEquiv`;
- ordinary isomorphism versus equality;
- groupoid and restricted truncated-universe univalence;
- equality-valued `OmegaEquivAlong` and `OmegaEquiv`;
- one-way next-hom action and the exact boundary of the current API;
- why a directed functor need not be an equivalence.

The chapter should explicitly separate the fully checked native API from
optional full object-equality/ordinary-isomorphism equivalence work.

#### Chapter 5. Induction, arrow induction, and universal properties

- ordinary induction and Nat induction;
- path induction in the equality-local fragment;
- `PathOut` and fixed-source arrow induction;
- contextual elimination as a universal-property interface;
- recursion as a specialization of dependent/contextual elimination;
- homotopy-initiality as a mathematical-development topic, clearly separated
  from what is packaged.

The old article's strongest prose on arrow induction belongs here after being
updated to the current symbol names and formal status.

#### Chapter 6. Directed higher inductive types

- point, arrow, and higher-cell constructors;
- expected recursion and induction data;
- constructor computation rules and their runtime/propositional status;
- the walking-endomorphism signature;
- the contextual algebra
  `D[loop] ∘ u => u ∘ R[loop]`;
- the derived section and recursor views;
- restricted core inclusion, PathLift, and the spiral, at the level needed for
  the decoder;
- limitations of the current single selected HIT.

This chapter adapts the HoTT discussion of the circle's recursion, dependent
paths, and higher-constructor computation, but must not generalize one
implemented HIT into a claimed general directed-HIT schema.

#### Chapter 7. Truncation and categorical height

- recursive truncation levels and their equality-lowering equation;
- propositions, sets, and higher truncation evidence revisited uniformly;
- evidence-property and retract closure;
- packaged truncated universes and their restricted univalence;
- `IsNCat` and homwise categorical height;
- object truncation for finite categorical height;
- how one-dimensionality turns a cell between parallel arrows into equality;
- the exact sethood premise used in the easy encode-decode coherence.

This restores the HoTT spine's “n-types immediately before homotopy theory”
role while translating homotopy level into the combination of native
truncation and categorical height available in emdash.

### Chapter 8. Synthetic directed homotopy theory

Preserve the pedagogical landmark of HoTT Chapter 8 while changing the
mathematics honestly.

#### 8.1 The based endomorphisms of the walking endomorphism

State the goal as the checked carrier equivalence and separately state the
expected monoid-level strengthening.

##### 8.1.1 Getting started

- define Nat-indexed powers of the generator;
- define encode provisionally through Code;
- show the easy computations at zero and successor;
- explain why direct induction on an arbitrary fixed based arrow is
  unavailable;
- motivate generalization over all endpoints/fibres.

##### 8.1.2 The free-monoid model

- introduce the classical free category on one loop;
- define `BNat_cat` concretely;
- show identity as zero and composition as addition;
- present `walking_bnat_model_func`;
- state exactly why this is consistency/model evidence rather than a
  definitional presentation or an already proved equivalence.

This subsection plays the explanatory role of the classical universal-cover
proof without imitating its topology literally.

##### 8.1.3 The directed cover in functorial type theory

- define `Code : WalkingEnd -> Cat`;
- calculate its base fibre and generator action;
- interpret its total/displayed category as a directed helix whose levels are
  naturals and whose motion only goes forward;
- define encode by transporting zero;
- define the representable based-arrow family;
- explain the contextual decoder problem and the spiral coherence.

The “directed helix” may be illustrated, but the diagram must show a boundary
at zero and no downward/predecessor motion.

##### 8.1.4 The encode-decode proof

Present the proof in the implementation's actual dependency order:

1. construct powers and the functor `walking_power_func`;
2. construct the restricted-CoreIncl spiral;
3. invoke the contextual eliminator to obtain
   `walking_directed_decode_funcd`;
4. obtain the fibrewise decoder;
5. for arbitrary endpoint and based arrow, construct the directed
   normalization cell;
6. use hom-discreteness to obtain equality;
7. specialize to prove `power(encode(p)) = p`;
8. prove the generator-prefix encoding formula using generic functoriality;
9. prove `encode(power(n)) = n` by Nat induction;
10. package the carrier equivalence.

The directed normalization cell is the conceptual climax. It must appear
before the equality proof, matching the source rather than compressing the
argument into an ordinary quasi-inverse calculation.

##### 8.1.5 Consequences and the missing negative integers

- sethood by dimension and independently by equivalence;
- loop distinct from identity;
- no right inverse;
- no omega-equivalence evidence;
- expected addition/composition compatibility;
- comparison with `Omega(S¹) ≃ Z`;
- group completion as a future bridge back to the circle.

The absence of negative integers is a theorem-shaped feature, not a defect.

#### 8.2 Higher groupoidal shadows

Use the existing Eckmann--Hilton computation as the first neighboring result:

- two compositions of 2-endomorphisms;
- shared units and interchange;
- commutativity;
- how the result lives in a groupoidal/equality-local shadow even though the
  surrounding theory is directed.

This section is not a prerequisite for §8.1.4 and should not interrupt that
proof.

### Later parts

After the first edition's central spine is stable, expand in this order:

1. representables, Yoneda, and `PathOut`;
2. strict and lax transfors and higher hom-action;
3. dependent homs, fibrations, Sigma/Pi, and adjunctions;
4. profunctors, tensor/co-Yoneda, weighted limits and colimits;
5. duality, joins, and mixed variance;
6. observational equality, truncated universes, and future computational
   univalence;
7. semantics, models, and an implementation metatheory.

These should become later parts of the book, not be forced into the initial
WalkingEnd milestone.

### Appendices

Plan for:

- mathematical notation versus canonical surface syntax;
- Lambdapi source map and evidence register;
- rewrite/unification and normalization methodology;
- the precise HoTT-to-emdash correspondence;
- provenance, bibliography, and licensing;
- an implementation-status matrix;
- deferred theorems and research questions.

## Source And Rendering Architecture

### Source tree

Treat the book as a first-class repository artifact, independent of a
particular renderer:

```
book/
  README.md
  book.json
  STYLE.md
  CREDITS.md
  LICENSE.md
  evidence.json
  frontmatter/
    00-title.md
    01-preface.md
    02-how-to-read.md
  chapters/
    00-prologue.md
    01-judgments-and-computation.md
    02-categories-functors-and-families.md
    03-logic-propositions-and-sets.md
    04-equivalence-and-univalence.md
    05-induction-and-universal-properties.md
    06-directed-hits.md
    07-truncation-and-categorical-height.md
    08-walking-endomorphism.md
  appendices/
    a-notation.md
    b-emdash-evidence.md
    c-hott-correspondence.md
  references/
    bibliography.md
    third-party-sources.json
```

`book.json` is the ordered manifest and owns:

- title, subtitle, edition, authors, license, and canonical slug;
- ordered source files;
- renderer metadata;
- the HoTT source revision used for adaptation;
- output targets.

Do not encode ordering in lexicographic filename discovery alone.

### Generated render input

Add a deterministic assembler under `print/scripts/` that:

1. reads `book/book.json`;
2. rejects duplicate or missing chapter IDs;
3. joins sources with stable chapter-boundary comments;
4. writes `print/public/emdash-book.md`;
5. emits no timestamps or host paths;
6. supports a `--check` mode that detects stale output.

The generated file is a render artifact, not the authoring authority. Decide
once during implementation whether to commit it:

- preferred: do not commit it; run assembly in `predev`,
  `prebuild`, and CI;
- fallback for static hosting: commit it, but require
  `book:assemble --check` in CI.

Never use the Unicode filename `emdash—book.md`. Use the Unicode
punctuation only in displayed text.

### One document registry

Replace the three independent filename regular expressions in the loader,
schema validator, and console checker with a shared document registry. It can
be generated from book/article manifests and should specify:

- slug and source/output filename;
- whether the document participates in quick or full render checks;
- expected layout;
- whether it is generated;
- optional maximum render time.

This allows both legacy `index*.md` articles and the new book to be
validated without broad unsafe path loading.

### Package boundary with Arrowgram

Use two explicit modes:

1. **Reproducible default.** Commit a pinned npm dependency and lockfile.
   Replace `file:~/arrowgram/packages/arrowgram` with the verified
   published version. Avoid a caret for renderer-critical dependencies during
   the first book milestone.
2. **Local upstream development.** Document an opt-in
   `npm link` or `npm install --no-save` workflow against
   `/home/user1/arrowgram`. Never commit that host-specific path.

Do not immediately replace the emdash renderer with
`@hotdocx/arrowgram-web/preview`. First make a parity matrix for:

- Markdown tables;
- math protection and sanitization;
- Mermaid, Vega-Lite, and Arrowgram blocks;
- two-column pagination;
- paper selection and base URLs;
- local/static assets;
- console and request-failure checks.

Generic fixes should move upstream to `arrowgram-web` when feasible.
Book-specific discovery, manifests, evidence links, and styles remain in
emdash. After parity, the local renderer should become a thin adapter around
the pinned upstream preview package.

Replace the hand-maintained validation schema with the core package's exported
`arrowgram.schema.json` or a public parser from that package. One
schema should govern editor, renderer, and CI.

### Deterministic book checks

Introduce:

```
npm run book:assemble
npm run book:check
npm run book:render
```

The combined check should cover:

- manifest and chapter existence;
- generated-output freshness;
- internal anchor and link integrity;
- evidence-register file/symbol existence;
- embedded diagram/schema validation;
- KaTeX errors;
- browser console/page errors and failed requests;
- page generation for the book specifically;
- a deterministic PDF or print snapshot;
- cleanup of preview subprocesses on success, failure, timeout, SIGINT, and
  SIGTERM.

Bundle KaTeX CSS locally so an offline render does not depend on jsDelivr.
Give each document its own bounded render target rather than requiring every
historical article to paginate before the book can be checked.

## Documentation Consolidation

The maintenance pass should assign one durable question to each document.

| Document | Question it answers | Content to move out |
| --- | --- | --- |
| `README.md` | What is emdash, what is the headline theorem, and where do I start? | exhaustive feature and historical inventories |
| root `AGENTS.md` | What rules must an automated contributor obey? | expository book style and renderer tutorials |
| current SOP | What is the current architecture and safe implementation workflow? | chronological completion diaries and retired future tasks |
| `EMDASH_FOUNDATIONS.md` | What mathematics is implemented, and how should it be read? | retired compatibility history and command-level SOP |
| canonical syntax report | How should formulas, comments, and future parser syntax be written? | project status and implementation chronology |
| `book/STYLE.md` | How should book prose, theorem status, terminology, and citations be written? | kernel-development policy |
| `book/README.md` | How is the book assembled, checked, and reviewed? | general repository policy |
| `print/AGENTS.md` | What constraints must changes to the renderer obey? | embedded generation prompts and historical patch narrative |
| dated reports | Why was a design chosen, and what remains open? | nothing; these retain history |

The first consolidation should:

1. fix statements that contradict the current compatibility deletion and
   native unsuffixed API;
2. add the WalkingEnd/Nat result and current limitations to the short
   orientation documents;
3. extend canonical notation for WalkingEnd, Code, encode/decode, powers,
   equivalence status, and directed normalization;
4. move long historical ledgers out of living prose only when their report
   provenance is preserved;
5. reduce `README.md` to an entry point rather than another
   authority;
6. split `print/AGENTS.md` into concise agent constraints and
   human-facing renderer/book instructions.

Do not merge Foundations and canonical syntax. Their separation is useful:
one owns mathematical interpretation, the other owns notation.

## Lambdapi Source Maintenance

### Immediate recommendation

Do not split `emdash3_2.lp` before the first book skeleton. The
file is large, but it already has:

- a stable section 0--20 map;
- a separate executable check file;
- separately owned equality, evidence, Nat, and WalkingEnd extensions;
- passing bounded checks;
- a current reorganization report.

The book needs a reliable evidence map more urgently than it needs smaller
physical files. A premature split would change module-qualified symbol
ownership, rewrite visibility/order, warning interactions, and import
behavior without improving the mathematical argument.

### Conceptual layers to use now

Document the current source under these conceptual tiers without moving it:

1. foundational equality and encoded object/type formers;
2. ordinary category, functor, transfor, product, and adjunction calculus;
3. directed-family, Sigma/Pi, mixed-variance, and representable calculus;
4. displayed hom-action, laxity, and structural bridges;
5. applications: profunctors, `PathOut`, path induction, and
   Eckmann--Hilton;
6. equality-local core/restricted-CoreIncl infrastructure;
7. downstream libraries: native equality action, evidence/truncation, Nat,
   and WalkingEnd.

This gives the book a clean source map even while the physical authority
remains unchanged.

### Later split protocol

Open a separate implementation plan only after at least Chapters 1--8 have an
evidence map. That plan must:

1. generate a declaration/rule dependency inventory from the active source;
2. audit all fully qualified external references;
3. probe whether a proposed `emdash3_2.lp` facade actually
   re-exports/imports symbols in the way downstream Lambdapi clients require;
4. select a mostly linear module chain based on measured dependencies;
5. preserve declaration and rule order initially;
6. move one contiguous layer at a time in a full owner-position probe;
7. change no names, semantics, rewrite orientations, or inferred LHS slots in
   the split;
8. compare symbol/rule inventories, warnings, strict LHS audit, catalog, TOC,
   examples, health, and CI after each layer;
9. update evidence-register owners atomically;
10. retain `emdash3_2.lp` as the user-facing authority/facade only
    if the facade visibility probe succeeds.

Candidate boundaries from the existing reorganization map are
“foundations,” “ordinary,” “directed families,” “representables/dependent
hom,” “displayed action,” “structural bridges,” and “applications.” They are
candidate audit units, not pre-approved filenames.

## Implementation Phases

### Phase B0 — Ratify the book contract

State: **COMPLETE (2026-07-20).**

Deliverables:

- approve the displayed title and provisional scope;
- approve the four formal-status labels;
- approve CC BY-SA 3.0-compatible licensing for the adapted book text;
- record the HoTT source revision and attribution format;
- create `book/book.json` and the empty chapter tree.

Gate:

- no copied/adapted HoTT prose is committed before
  `book/CREDITS.md` and `book/LICENSE.md` exist.

### Phase B1 — Establish traceability and repair current orientation

State: **COMPLETE (2026-07-20).**

Deliverables:

- seed `book/evidence.json` with every Chapter 8 checked claim;
- add a lightweight evidence existence checker;
- consolidate README, SOP, Foundations, canonical syntax, and print guidance
  according to the authority table above;
- correct stale compatibility and deferred-boundary prose;
- add the book workflow to root orientation without embedding the book itself
  in `AGENTS.md`.

Gate:

- documentation changes make no Lambdapi semantic change;
- `make check`, report-header lint, link checks, and
  `git diff --check` pass.

### Phase B2 — Build the book source/render seam

State: **COMPLETE (2026-07-20).**

Deliverables:

- manifest-driven deterministic assembler;
- shared document registry;
- ASCII output `print/public/emdash-book.md`;
- published/pinned Arrowgram core dependency plus documented local override;
- upstream-schema-based diagram validation;
- local KaTeX assets;
- book-specific bounded render check with reliable child cleanup.

Gate:

- a one-page placeholder book assembles and renders from a clean
  `npm ci` without `/home/user1/arrowgram`;
- local-link mode produces the same checked output;
- the existing three papers remain renderable.

#### B0–B2 implementation checkpoint

The completed bounded infrastructure milestone contains:

- `book/book.json`, the chapter-sized source tree, CC BY-SA 3.0 book
  license, HoTT credits, pinned revision/source map, style/status contract,
  and the Chapter 1–8 skeleton;
- nineteen Chapter 8 checked claims in `book/evidence.json`, all cited
  by book sources and verified for owning declarations plus reviewer/check
  evidence by `scripts/check_book_evidence.py`;
- a deterministic assembler with source-boundary comments and stale-output
  mode, plus source/provenance/anchor/link/critical-proof-order checks;
- one explicit `print/documents.json` registry shared by the browser,
  diagram validator, and bounded browser renderer;
- package-owned Arrowgram schema validation, exact published
  `@hotdocx/arrowgram@1.0.0` default, locally bundled KaTeX CSS/fonts,
  and an opt-in `npm link --no-save` workflow documented in
  `print/README.md`;
- per-document render budgets and process-group cleanup on ordinary exit,
  errors, timeouts, `SIGINT`, and `SIGTERM`;
- consolidated root/print orientation, corrected living deferred boundaries,
  and settled WalkingEnd/Code/normalization notation.

The clean published-package workflow passes `book:check` and renders
the skeleton to five pages. The local-link workflow produces the identical
assembled SHA-256
`17010237e7baa8f3d4039b0099dccc90645f93dbaf8c3a20b603c4fbeead5656`,
after which `npm ci` restores the published package. The all-document
render check passes with 27, 19, 32, and 5 pages respectively for
`index.md`, `index_0.md`, `index_3_2.md`, and
`emdash-book.md`. A forced SIGTERM cleanup probe leaves no preview
process. Full `make ci` passes all 39 retained source/example targets
in 88.040 seconds, including the new evidence, assembly, source-integrity,
report-header, active-reference, strict-rule-audit, and catalog gates.

### Phase B3 — Write the vertical slice first

State: **COMPLETE (2026-07-20).**

Deliverables:

- complete front matter and prologue;
- placeholder headings for Chapters 1--7;
- full first prose draft of Chapter 8 §8.1.1--§8.1.5;
- initial HoTT/emdash comparison appendix;
- formal-status notes and evidence links for every Chapter 8 claim.

Writing order inside the phase:

1. theorem statement and limitations;
2. `BNat` model;
3. Code and encode;
4. power and contextual decoder;
5. directed normalization;
6. inverse laws and packaging;
7. negative results;
8. introduction and prologue, rewritten after the proof is stable.

Gate:

- a reader can follow the mathematical proof with a compact prerequisite
  glossary;
- every “checked” statement resolves to an active declaration and reviewer
  example;
- no prose identifies WalkingEnd definitionally with BNat or claims a
  monoid/category equivalence.

#### B3 implementation checkpoint

The vertical slice now contains complete front matter and prologue, a newly
written §8.1.1–§8.1.5 proof, the neighboring Eckmann–Hilton section, and a
revision-pinned HoTT comparison appendix. The proof keeps `BNat` as a
separate concrete model, constructs the directed normalization cell before
extracting equality, states only the checked carrier equivalence, and marks
composition/addition compatibility and group completion at their actual
formal boundaries.

`book/evidence.json` contains 24 claims spanning checked interfaces, a formal
consequence, and research boundaries. All are cited. Appendix B is assembled
deterministically from that register, and the provenance checker now validates
every HoTT adaptation target, source path, source label, type, and description.
The book source/link/math check passes for all 18 assembled sources, and the
bounded browser render passes at 27 pages with no console, page, request, or
render errors.

### Phase B4 — Adapt the prerequisite spine

State: **COMPLETE (2026-07-20).**

Write Chapters 1--7 in dependency order, but revise the chapter order if the
vertical slice exposes a better pedagogical dependency.

For each imported/adapted HoTT passage:

- record source file, section/label, source revision, and adaptation type;
- preserve attribution;
- replace groupoidal-only reasoning where directed action is intended;
- add emdash-native examples;
- mark unimplemented general schemas;
- test every code-facing claim against the evidence register.

Gate:

- Chapter 8 contains no forward reference to an undefined essential notion;
- the prose remains mathematical rather than a line-by-line kernel tour;
- all copied/adapted material passes the licensing/provenance review.

#### B4 implementation checkpoint

Chapters 1–7 now form a complete prerequisite spine rather than scope
markers. They introduce the equality-local foundation, iterated homs,
functors and transfors, directed families, propositions and recursive
truncation evidence, carrier equivalence and the exact native-univalence
boundary, fixed- and varying-source `PathOut` induction, the selected
WalkingEnd contextual eliminator, and finite categorical height. Chapter 7
isolates the precise logical step used by Chapter 8: contextual action first
constructs a directed normalization cell, and discreteness of the based
hom-category only afterward converts it to equality.

The evidence register now contains 57 claims, all cited and resolved to their
declared checked, formal-consequence, mathematical-development, or
research-boundary status. The adaptation ledger records the HoTT source
labels used by each prerequisite chapter. Deterministic assembly and all
source, evidence, provenance, link, anchor, and math checks pass across the 18
sources. The bounded production-browser render passes at 63 pages with no
console, page, request, or render errors.

### Phase B5 — Add the first broader functorial chapters

State: **COMPLETE (2026-07-20).**

Prioritize:

1. `PathOut` and arrow induction;
2. Eckmann--Hilton and the groupoidal shadow;
3. strict/lax transfors;
4. representability and profunctors.

Reuse the old article's best explanations only after updating every claim to
the current native API and formal-status scheme.

Gate:

- each new chapter has one central theorem/example rather than a feature
  catalog;
- free-form developments name their plausible emdash prerequisites and
  intended owners.

#### B5 implementation checkpoint

The first two prioritized topics were already delivered theorem-first:
Chapter 5 develops `PathOut` induction through the composition benchmark,
and §8.2 derives the Eckmann–Hilton commutativity slice. Chapters 9 and 10 now
complete the phase. Chapter 9 organizes ordinary transfors around the
off-diagonal naturality/cut computation, then distinguishes it from the
component-level directed laxity cell of a natural family morphism. Chapter 10
organizes representability and profunctors around the shaped-element
co-Yoneda beta and its naturality fusion.

The chapters explicitly defer a duplicated whole-laxity facade, a fully
faithful Cat-valued Yoneda package, a general coend/coinserter realization of
tensor, and full profunctor-bicategory coherence. The evidence register now
contains 72 fully cited claims. Deterministic 20-source assembly, source and
evidence checks, and the bounded production-browser render pass at 77 pages
with no console, page, request, or render errors.

### Phase B6 — Book-quality production

State: **COMPLETE (2026-07-20).**

Deliverables:

- stable numbering and cross-references;
- bibliography and source attribution;
- glossary and index strategy;
- deterministic PDF;
- print and screen styles;
- accessibility checks for diagrams and color;
- link, math, overflow, orphan/widow, and page-break review;
- a release checklist and versioned edition metadata.

Gate:

- `npm run book:check` passes offline from a clean install;
- the generated PDF has no error boxes, raw Markdown tables, broken links,
  missing glyphs, or network requests;
- source and generated outputs are demonstrably in sync.

#### B6 implementation checkpoint

The initial development edition now has 24 ordered sources: front matter,
prologue, Chapters 1–10, Appendices A–F, bibliography, credits, and license.
`book/book.json` owns version `0.1.0-dev`, publication date, source order,
contents groups, and the ignored release-artifact path. Stable explicit
anchors plus manifest-generated contents are the selected cross-reference
system. Appendix D is a curated glossary/concept index, and the eight-entry
bibliography uses stable reference anchors and primary source links. This
settles `BOOK-S11` without adding an external bibliography engine to the
initial edition.

`BOOK-S12` selects a local, reproducible release pipeline:

1. Paged.js paginates the assembled Markdown in headless Chromium after an
   explicit application-level completion handshake;
2. every manifest source carries a direct Paged.js page-boundary contract,
   and the browser gate verifies all source starts after pagination;
3. `pdf-lib@1.17.1` installs fixed manifest metadata and canonicalizes
   Chromium's process-local tagged-table structure IDs while preserving their
   references;
4. `qpdf` supplies deterministic document IDs and recompression;
5. `qpdf` and Poppler check structure, tagging, metadata, page geometry,
   extracted text, blank pages, embedded fonts, and prohibited features.

The PDF remains an ignored generated artifact under `output/pdf/`; a release
may attach it together with the reported checksum. The release checklist is
`book/RELEASE.md`. Browser validation additionally rejects external requests,
broken internal links, raw Markdown tables, rendered error boxes, horizontal
overflow, inaccessible diagrams/images, low text contrast, color-only links,
missing source page breaks, and incomplete pagination.

A clean `npm --prefix print ci --offline` installs the locked 260-package
dependency graph with zero reported vulnerabilities. `book:release` passes
for all 24 sources and all 72 cited evidence claims. The checked artifact is a
103-page, US-Letter, tagged PDF with 14 embedded font subsets, no JavaScript,
and SHA-256
`c564173cb478e1ca66b90e6c4fa1e78cc7b9a1e684fac78b342e7e3f1792d54f`.
Two independent clean build/export cycles produce that exact checksum. The
all-document matrix passes for the three retained articles and the book at
27, 19, 32, and 103 pages, respectively.

Every PDF page was rendered and inspected in contact sheets, with
high-resolution review of title, contents, the Chapter 8 theorem and directed
normalization argument, notation/evidence/status tables, circle comparison,
glossary, bibliography, credits, and license. The final review found no blank
pages, clipping, overlap, missing glyphs, or unresolved editorial artifacts.
No Lambdapi declaration, rule, normal form, or module boundary changed during
book production. The closing `make ci` passes all 39 retained
source/example targets in 89.516 seconds, all 16 recovery tests, and every
TOC, active-reference, report-header, evidence, assembly, source-integrity,
strict-rule-audit, catalog, and repository-integrity gate.

### Phase B7 — Optional module split

State: **DEFERRED / NOT TRIGGERED (2026-07-20).**

Start only if book evidence mapping or active implementation work demonstrates
a concrete maintenance benefit. Follow the separate split protocol above.

The 72-claim register resolves cleanly against the existing kernel and four
one-way extensions, and book production exposed no declaration-ownership or
import-visibility problem. A physical split would therefore add migration
risk without a demonstrated consumer benefit and is not part of this
completed edition.

Gate:

- no semantic or naming migration is mixed into the split;
- all repository CI and evidence links pass after every promoted boundary.

## Acceptance Criteria For The Initial Book Skeleton

State: **SATISFIED AND SUPERSEDED BY THE B3–B6 SUBSTANTIVE EDITION
CHECKPOINTS (2026-07-20).**

The initial skeleton is complete when:

- the title, subtitle, audience, license, and formal-status legend are present;
- the prologue states the WalkingEnd/Nat result and noninvertibility honestly;
- Chapters 1--7 have paragraph-level scope summaries and prerequisite links;
- Chapter 8 has all five §8.1 subsection headings and theorem placeholders;
- every placeholder identifies whether it is checked, a formal consequence,
  a mathematical development, or a research boundary;
- the HoTT revision and adapted source sections are recorded;
- the source is split by chapter and deterministically assembled;
- `emdash-book.md` is discoverable by the loader and all relevant
  checks;
- the old article remains available as an archival/inventory source;
- no Lambdapi source reorganization is required to preview the book.

The first substantive prose milestone is stricter: §8.1.4 must present the
directed normalization cell before equality extraction and must keep
`BNat` separate from the opaque HIT.

## Risks And Mitigations

### Overclaiming formal support

Risk: polished prose makes free-form category theory sound kernel-checked.

Mitigation: formal-status labels, evidence register, and automated symbol
existence checks.

### Treating WalkingEnd as a renamed circle

Risk: copied HoTT prose accidentally imports inverses, predecessor, or
group-completion.

Mitigation: use the comparison table as an editorial checklist and make
noninvertibility the closing theorem of §8.1.

### License/provenance loss

Risk: near-verbatim adaptation becomes unattributed or incompatible with the
book license.

Mitigation: CC BY-SA-compatible book license, revision-pinned provenance, and
per-chapter source records before prose import.

### A second giant Markdown file

Risk: `emdash-book.md` becomes another unmaintainable monolith.

Mitigation: chapter sources plus one generated renderer input; never hand-edit
the generated file.

### Renderer/upstream divergence

Risk: the emdash fork and `arrowgram-web` continue to accumulate
slightly different fixes.

Mitigation: parity matrix, upstream generic fixes, pinned releases, thin local
adapter, and one shared schema.

### Non-reproducible builds

Risk: a committed `file:~/arrowgram` dependency and CDN assets work
only on the current host.

Mitigation: registry-pinned default, opt-in local link, local assets, clean
`npm ci` gate.

### Premature Lambdapi split

Risk: module-qualified names, rewrite visibility, or import order change while
the book and foundations are also being rewritten.

Mitigation: defer the physical split, create the conceptual source map first,
and require a separate owner-position migration plan.

### Book prose becoming a source-code catalog

Risk: readability regresses to lists of kernel identifiers.

Mitigation: theorem-first prose, short formal-status sidebars, implementation
appendix, and one mathematical example per major construction.

## Proposed Decisions

1. **New artifact:** the book is independent of
   `index_3_2.md`.
2. **Central computation:** WalkingEnd/Nat is the opening and Chapter 8
   theorem.
3. **Faithful analogy:** use the HoTT spine, not a textual
   `S¹/Z` search-and-replace.
4. **Source layout:** split chapter sources immediately; generate one Markdown
   render input.
5. **Filename:** use `emdash-book.md`, not a Unicode em-dash
   filename.
6. **Evidence:** distinguish checked, formal consequence, mathematical
   development, and research boundary.
7. **Licensing:** treat HoTT adaptation as CC BY-SA material from the first
   copied paragraph.
8. **Print dependency:** use pinned published packages by default and a local
   upstream link only as an explicit development mode.
9. **Renderer migration:** compare and upstream before replacing the current
   preview implementation.
10. **Maintenance:** consolidate document roles before deleting useful
    historical evidence.
11. **Kernel organization:** a physical module split is not a book
    prerequisite and requires a separate migration.
12. **Cross-references and bibliography:** use manifest-generated contents,
    stable hand-authored anchors, a curated glossary/concept index, and a
    compact primary-source bibliography for the initial edition.
13. **PDF policy:** generate the ignored release artifact through
    Chromium/Paged.js, fixed `pdf-lib` metadata and structure IDs, and
    deterministic `qpdf` normalization; attach the artifact and checksum at
    release time rather than treating it as source.
14. **Optional split:** the B7 promotion trigger was not met; preserve the
    current Lambdapi module boundaries.

## Side Task Ledger

| ID | Task | State | Blocking condition or promotion trigger |
| --- | --- | --- | --- |
| BOOK-S1 | Verify and adopt a CC BY-SA-compatible license and attribution text | complete (B0, 2026-07-20) | gate remains mandatory for every adapted passage |
| BOOK-S2 | Design `book.json` and evidence-register schemas | complete (B0/B1, 2026-07-20) | evolve compatibly with checked consumers |
| BOOK-S3 | Centralize print document discovery | complete (B2, 2026-07-20) | `print/documents.json` is the selected registry |
| BOOK-S4 | Replace duplicated Arrowgram validation schema | complete (B2, 2026-07-20) | validator imports the package-owned schema |
| BOOK-S5 | Compare emdash print behavior with `arrowgram-web/preview` | deferred | before renderer replacement |
| BOOK-S6 | Add reliable subprocess cleanup and per-document render budgets | complete (B2, 2026-07-20) | success and forced-SIGTERM cleanup verified |
| BOOK-S7 | Package composition/addition compatibility as a monoid isomorphism | deferred mathematical/formal extension | after §8.1 carrier proof prose is stable |
| BOOK-S8 | Construct reverse `BNat` functor/full categorical comparison | deferred research task | requires a separately scoped implementation plan |
| BOOK-S9 | Develop group completion and the precise circle comparison | deferred research task | after directed theorem and monoid structure |
| BOOK-S10 | Generate a declaration dependency graph for module splitting | deferred | only when a concrete split benefit appears |
| BOOK-S11 | Decide bibliography/cross-reference engine | complete (B6, 2026-07-20): stable anchors, generated contents, curated glossary/index and bibliography | reconsider only if a later edition needs automatic citation/page-index generation |
| BOOK-S12 | Decide deterministic PDF implementation and release artifact policy | complete (B6, 2026-07-20): tagged Chromium/Paged.js export, fixed pdf-lib metadata/structure IDs, qpdf normalization, ignored artifact plus release checksum | rerun the release checklist for every versioned edition |

## Recommended Next Action

Phases B0–B6 are complete without moving Lambdapi declarations, and the B7
trigger was not met. The next step is editorial review of the initial
development edition, followed by a versioned release using
`book/RELEASE.md`. Formal extensions such as a monoid isomorphism, reverse
`BNat` functor, full categorical comparison, group completion, or stronger
profunctor packaging remain separately scoped research work. Reconsider B7
only when one of those implementations demonstrates a concrete ownership or
import-visibility benefit.
