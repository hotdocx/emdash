# TypeScript Elaborator v3.2 — Book And Repository Graduation Proposal

Date: 2026-07-30
Proposal-Row: BOOK-NARRATIVE-0B
Review-Gate: H-DTTLF-BOOK-REPOSITORY-01
Decision-ID: D-DTTLF-BOOK-REPOSITORY-001
Parent-Plan:
[`TYPESCRIPT_ELABORATOR_V3_2_BOOK_AND_REPOSITORY_GRADUATION_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_BOOK_AND_REPOSITORY_GRADUATION_PLAN.md)
Capability-Audit:
[`TYPESCRIPT_ELABORATOR_V3_2_BOOK_DELTA_AUDIT.md`](./TYPESCRIPT_ELABORATOR_V3_2_BOOK_DELTA_AUDIT.md)
Status: frozen bounded proposal awaiting separate review; no authored book
source, evidence manifest, TypeScript product, generated artifact, root
README, or mathematical owner changed

## Decision Question

> Approve H-DTTLF-BOOK-REPOSITORY-01 /
> D-DTTLF-BOOK-REPOSITORY-001 as proposed: update the exact authored book,
> structured evidence, one reviewer preset, deterministic public-PDF owner,
> external-review handoff, and root README listed below; preserve the active
> Lambdapi authority, bounded syntax and displayed-context limits, deferred
> whole-library scale programme, proportional validation policy, and local
> checkpoint-only Git boundary?

Approval authorizes only the exact files, claims, examples, artifact route,
and validation stages frozen here. It does not authorize publication, push,
merge, deployment, a release/tag, mathematical-kernel changes, new parser or
checker semantics, evidence-schema expansion, bulk scale work, or unrelated
cleanup.

## Product Thesis

The edited edition should make one argument:

> Functorial type theory treats categorical action as computational
> substitution. The active Lambdapi kernel owns that mathematics; a renewed
> TypeScript outer LF, explicit Core, contextual elaborator, and bounded text
> adapter make a reviewed fragment directly usable without becoming a second
> mathematical authority.

The book remains organized by mathematics, especially the WalkingEnd
calculation and the calculus of cuts. The implementation enters only where it
clarifies:

- the distinction between independent fibred siblings and genuine dependency
  edges;
- the internal ownership of object, arrow, and selected higher action;
- the route from readable bound variables to explicit categorical owners; and
- the precise boundary between implemented product and future generality.

## Frozen Running Examples

### Primary: nested ordinary functorial binding

Assume:

```text
A, B, C : Cat
E : Functor B (Functor_cat A C)
```

The exact text witness is:

```text
λ^f x : A. λ^f y : B. E y x
```

Its mathematical classifier is:

```text
Functor A (Functor_cat B C)
```

The focused implementation probe and existing direct-equality test establish
that the expression lowers to the existing exchange/currying construction. A
compact owner-aligned rendering is:

```text
fapp0
  (Functor_cat B (Functor_cat A C))
  (Functor_cat A (Functor_cat B C))
  exchange-functor-abstraction
  E
```

The exact machine rendering begins with the explicit Core
`functor-object` owner, applies
`emdash.categorical.exchange-functor-abstraction`, and names only the
structural prerequisite `exchange-functor-abstraction`. The book should show
the compact owner-aligned form, not the full provenance-heavy serialized Core.
The full exact serialization remains produced by the reviewer and tests.

This demonstrates:

- `^f` is intrinsic to the binder;
- `: A` and `: B` are checked classifier annotations rather than the source
  of the mode;
- neutral application resolves `E y` and then `(E y) x` through typing;
- the two scoped variables may occur recursively inside the body; and
- the result uses an existing internal categorical construction rather than
  an externally supplied functoriality equation.

### Secondary: genuine dependency plus independent siblings

The exact existing reviewer witness is:

```text
λ^fd (a : A; b : B, c : C; d : D). fibrePair b c
```

Its expected profile is:

```text
kind   = displayed-dependent-context-functor
levels = A; B,C; D
target = Productd(B↑,C↑)
```

The focused product probe accepts it and reports the existing structural
prerequisites:

```text
product-category
product-pair
functor-composition
uncurry-package
```

The exact Core additionally exposes the already reviewed Sigma categories,
Sigma projections, displayed pullbacks, displayed-functor classifier,
constant terminal family, and displayed product pairing. The book should
present the mathematical factorization, not its full serialized Core.

The punctuation has a semantic reading:

- semicolon separates dependency levels;
- comma groups independent siblings over the same prior context;
- `b` and `c` may be exchanged, weakened, contracted, and paired
  fibrewise; and
- no exchange of `a` across a dependent `b : B(a)` is claimed.

Two examples are sufficient. No general syntax catalogue enters the
mathematical chapters.

## Exact Authored Book Edit Set

No source outside this table may be changed under this decision without a
correcting proposal.

| Source | Exact narrative change |
| --- | --- |
| `emdash2/book/book.json` | Advance the draft development snapshot to `editionVersion: 0.3.0-dev`, `publicationDate: 2026-07-30`, and `artifacts.pdf: output/pdf/functorial-type-theory-0.3.0-dev.pdf`; retain `edition: expanded development edition` and `status: draft` intentionally |
| `emdash2/book/frontmatter/01-preface.md` | Replace only the stale “optional future elaborator” architecture phrase with a bounded executable TypeScript bridge that remains subordinate to the checked categorical kernel |
| `emdash2/book/frontmatter/02-how-to-read.md` | Add one executable-review reading path and distinguish the book's broad mathematical notation from the reviewed executable subset; retain the active-Lambdapi authority statement |
| `emdash2/book/chapters/02-categories-functors-and-families.md` | Add two theorem-led subsections inside §2.6: **Fibrewise Contexts** and **Base Change And Evaluation**; do not renumber §§2.7–2.8 |
| `emdash2/book/chapters/09-transfors-and-the-calculus-of-cuts.md` | Add §9.4.4, **Fibred Structural Cuts**, after the existing product-beta example and before universal cuts |
| `emdash2/book/appendices/a-notation.md` | Add the four intrinsic text binder forms and explain that classifier annotations are optional while modes are not; replace the blanket parser sentence with the exact “reviewed subset, not complete book grammar” boundary |
| `emdash2/book/appendices/f-status-and-research.md` | Update the Directed families and Formal presentation status rows and replace the obsolete-parent-only paragraph in F.5 with the renewed bounded product plus remaining complete-surface/scale boundary |
| `emdash2/book/appendices/g-formal-presentation.md` | Correct the opening layer table/flow; rewrite G.5 around the renewed outer LF, explicit Core, same-checker contextual elaboration, four binder modes, two frozen examples, historical prototype distinction, and retained complete-surface boundary |
| `emdash2/book/evidence.json` | Add the three exact checked claims below and rewrite only `FORMAL-ELABORATION-BOUNDARY` as the retained bounded-profile research boundary |
| `emdash2/book/expansion.json` | Replace “optional future elaborator” with “bounded TypeScript elaborator and explicit Core” and synchronize the Appendix G boundary |

The generated contents block remains owned by assembly and needs no authored
edit. Chapter 1 receives no change. No other theorem chapter, bibliography,
credits, license, renderer source, or third-party provenance record changes.

## Frozen Mathematical Narrative

### Chapter 2: fibrewise contexts

For `B,C : K -> Cat`, define the transparent fibrewise family

```text
P(B,C)[k] = B[k] x C[k]
P(B,C)[p] = B[p] x C[p].
```

The prose must distinguish:

```text
k : K, b : B[k], c : C[k]       independent siblings b,c
k : K, a : A[k], b : B[k,a]     genuine dependency a -> b
```

The first context admits fibrewise projections, pairing, exchange, and
contraction among `b,c`. The second does not admit an unqualified exchange of
`a,b`. The active product family remains a transparent composite; the book
must not claim a primitive `Product_catd`.

### Chapter 2: base change and evaluation

For `F : A -> K` and `D : K -> Cat`, the prose introduces:

```text
sigma_pullback_total_func(F,D) : Sigma_A(F*D) -> Sigma_K(D)
(a,u) |-> (F[a],u).
```

Its arrow action maps the base component through `F` and retains the fibre
component. This is the computationally useful asymmetric totalization; the
book must not replace it with an unsupported general pullback equation for
total categories.

For constant domain `A` and `B : K -> Cat`, the prose then introduces:

```text
S(A,B)[k] = Functor(A,B[k])
Eval_funcd(B) : P(S(A,B), Const_K(A)) ->_K B.
```

`Terminal_funcd` supplies weakening to the constant terminal family.
Evaluation, weakening, and pairing therefore reuse internally functorial
owners.

### Chapter 9: displayed introduction/elimination

The new structural-cut example states:

```text
projL_d o pair_d(FF,GG)  -> FF
projR_d o pair_d(FF,GG)  -> GG.
```

It explains that object, base-arrow, and internalized-cell observations
compute componentwise. This is a checked fixed-base displayed-family result,
not a solution of Chapter 9's still-open arbitrary-`K` chosen-object-product
interface.

## Exact Evidence Changes

The evidence checker remains unchanged. The following JSON shapes are frozen;
ordinary formatting/order may follow the neighboring register style.

### `CAT-FIBREWISE-CONTEXT`

Status: `checked`

Statement:

> Fixed-base fibrewise products of displayed families have displayed
> projections and pairing whose fibre, base-arrow, internalized-cell, higher,
> and projection-after-pairing observations compute componentwise; swap and
> diagonal are derived from those owners.

Owners:

```json
[
  {"file": "emdash3_2.lp", "symbol": "Product_projL_funcd"},
  {"file": "emdash3_2.lp", "symbol": "Product_projR_funcd"},
  {"file": "emdash3_2.lp", "symbol": "Product_pair_funcd"}
]
```

Reviewers:

```json
[
  {"file": "emdash3_2_checks.lp", "symbol": "Product_projL_funcd_higher_check"},
  {"file": "emdash3_2_checks.lp", "symbol": "Product_projR_funcd_higher_check"},
  {"file": "emdash3_2_checks.lp", "symbol": "Product_pair_funcd_higher_check"},
  {"file": "emdash3_2_checks.lp", "contains": "The canonical internalized cell of displayed pairing is componentwise."},
  {"file": "emdash3_2_checks.lp", "contains": "Whole displayed universal-property betas."}
]
```

### `CAT-BASE-CHANGE-TOTALIZATION`

Status: `checked`

Statement:

> Pullback totalization sends a base-changed dependent pair `(a,u)` to
> `(F[a],u)` and sends its total arrow by the functorial base action while
> retaining the fibre component.

Owner:

```json
[
  {"file": "emdash3_2.lp", "symbol": "sigma_pullback_total_func"}
]
```

Reviewer:

```json
[
  {"file": "emdash3_2_checks.lp", "contains": "Pullback totalization exposes exactly its base-changed dependent pair."}
]
```

### `CAT-DISPLAYED-EVALUATION`

Status: `checked`

Statement:

> Constant-domain displayed evaluation projects fibrewise to ordinary
> functor evaluation and retains generic base/higher action, while displayed
> terminal weakening projects to the ordinary terminal functor.

Owners:

```json
[
  {"file": "emdash3_2.lp", "symbol": "Eval_funcd"},
  {"file": "emdash3_2.lp", "symbol": "Terminal_funcd"}
]
```

Reviewers:

```json
[
  {"file": "emdash3_2_checks.lp", "contains": "The stable displayed evaluator projects to ordinary product evaluation."},
  {"file": "emdash3_2_checks.lp", "symbol": "Displayed_eval_higher_check"},
  {"file": "emdash3_2_checks.lp", "contains": "Displayed terminal weakening projects to the ordinary unique functor."}
]
```

### Revised `FORMAL-ELABORATION-BOUNDARY`

Status remains `research-boundary`; owners and reviewers remain empty.

Statement:

> The renewed TypeScript product implements a bounded direct-TypeScript and
> categorical-text path through scoped contextual elaboration,
> backend-neutral explicit Core, and a generic checker/evaluator, with
> optional Lambdapi conformance. A complete compiler for the book's canonical
> surface, arbitrary displayed coherence, and whole-library transfer are not
> claimed.

Evidence markers:

- Chapter 2 cites all three new checked claims beside their mathematical
  constructions.
- Chapter 9 cites `CAT-FIBREWISE-CONTEXT`.
- Appendix G retains `FORMAL-ELABORATION-BOUNDARY`.

No TypeScript path is added to the Lambdapi mathematical evidence registry.

## Appendix G Architecture

The corrected architecture has five distinguishable roles:

```text
canonical mathematical surface (broader than implemented text)
               |
               | reviewed direct TypeScript / text subset
               v
scoped contextual elaboration
               |
               v
backend-neutral explicit emdash Core
               |
               v
generic TypeScript LF checker / conversion / bounded runtime
               |
               +---- optional deterministic Lambdapi emission/conformance

active authored Lambdapi v3.2 kernel = mathematical authority
external models                    = separate mathematical work
```

The prose must avoid three false equivalences:

1. the text adapter is not the checker;
2. the TypeScript checker is not the active mathematical authority; and
3. the implemented text subset is not the whole canonical mathematical
   surface.

The stage table records:

| Stage | Implemented bounded profile | Retained boundary |
| --- | --- | --- |
| parse | located `^f`, `^n`, `^fd`, `^nd`, neutral application, reviewed constructors/contexts | not complete book or Lambdapi grammar |
| elaborate | typed expected classifiers route recursively through the existing categorical program | no arbitrary pointwise-to-coherent synthesis |
| select owner | current reviewed operation families lower to internal categorical owners | no whole-library owner acquisition claim |
| check/reduce | generic TypeScript LF checker/runtime for the reviewed profile | no global metatheory |
| conform | optional deterministic Lambdapi emission and bounded oracle | no production Lambdapi dependency |

## Binder Notation Boundary

The executable text forms are:

```text
λ^f  x : A. ...
λ^n  k : K. ...
λ^fd a : E. ...
λ^nd k : K. ...
```

The mode belongs to `λ`; the classifier annotation after the variable may be
omitted when the bidirectional expected classifier supplies it. The book may
continue to write declarations such as `k :^n K` in mathematical telescopes.
Appendix A must map that declaration notation to the executable intrinsic
binder spelling rather than claiming they are character-for-character
identical.

Object-only outer-LF binding remains ordinary dependent LF lambda/application;
the proposal does not invent a categorical `^o` text resolver.

## One Reviewer-Preset Addition

To join the book's primary example to the existing integrated reviewer,
authorize exactly one derived preset:

```text
id: nested-exchange
label: Nested functorial exchange
source: λ^f x : A. λ^f y : B. E y x
expected:
  outer  Functor A (Functor_cat B C)
  inner  Functor B C
assumption:
  E : Functor B (Functor_cat A C)
```

Exact product files:

- `src/v3_2/browser_reviewer.ts`
  - add the preset ID/record and ordinary fixture;
  - supply the existing recursive `bodyExpected` contract;
  - update the reviewer revision and nine-to-ten boundary sentence.
- `tests/v3_2_browser_reviewer_tests.ts`
  - add the direct construction with two existing `program.lambda` calls;
  - assert text/direct explicit-Core equality and the
    `exchange-functor-abstraction` prerequisite;
  - update the exact preset and boundary lists.
- `docs/TYPESCRIPT_ELABORATOR_V3_2_EXTERNAL_REVIEW_DEMO.md`
  - list ten presets and identify the nested example as the book bridge.

`emdash-template/src/App.tsx` already enumerates the exported preset list and
requires no behavior change. No categorical parser, resolver, checker,
runtime, kernel owner, browser barrel, or full report changes.

## Consolidated Reviewer Command

Add one root package script:

```json
"reviewer:dev": "./scripts/pnpmw --dir emdash-template --ignore-workspace exec vite"
```

The README uses:

```bash
./scripts/pnpmw run reviewer:dev
```

The existing lower-level command remains valid. No server backend, GitHub
Pages workflow, deployment, or network dependency is added.

## Deterministic Public-PDF Owner

The existing release owner generates and validates the manifest artifact:

```text
emdash2/output/pdf/functorial-type-theory-0.3.0-dev.pdf
```

No owner currently promotes it to the tracked public paths. Add one root
script:

```text
scripts/promote-book-pdf.mjs
```

Its exact contract is:

1. read `emdash2/book/book.json`;
2. require the manifest artifact to be a regular `.pdf` strictly under
   `emdash2/output/pdf/`;
3. require the artifact to exist and be nontrivially sized;
4. compute its SHA-256;
5. copy through a destination-local temporary file and atomic rename to:
   - `docs/emdash-book.pdf` (canonical public path), and
   - `docs/emdash3_2.pdf` (retained compatibility path);
6. verify both destinations are byte-identical to the source;
7. print the source, destinations, byte size, and checksum; and
8. touch no generated Markdown, ignored output other than reading the
   manifest artifact, or remote state.

Add one root script:

```json
"book:promote": "./scripts/pnpmw run book:pdf:check && node scripts/promote-book-pdf.mjs"
```

`docs/emdash3_2.md` is not regenerated and is removed from the README's
primary artifact list; it remains a legacy tracked snapshot. The new script
does not become a second renderer/exporter.

## Root README Consolidation

Replace the current long mixed status ledger with a concise reader-first
README under these headings:

1. **emdash — Functorial Type Theory**
   - one-paragraph mathematical thesis;
   - current draft/research status.
2. **Read And Review**
   - canonical `docs/emdash-book.pdf`;
   - `reviewer:dev`;
   - terminal `demo:external-review`;
   - direct active Lambdapi source.
3. **What The Reviewer Shows**
   - outer dependent LF;
   - ordinary and displayed categorical binders;
   - explicit Core/checking/computation;
   - book in the same client-side workbench.
4. **Architecture And Authority**
   - active Lambdapi mathematical authority;
   - bounded TypeScript product;
   - optional conformance oracle;
   - no production Lambdapi backend.
5. **Current Boundaries**
   - incomplete canonical surface;
   - bounded displayed contexts;
   - deferred whole-library transfer/groupoidal closure/global metatheory.
6. **Contributor Setup And Focused Commands**
   - bootstrap;
   - bounded TypeScript, kernel, reviewer, and book commands;
   - link to root/nested contributor guidance and handoff.
7. **Related Projects**
   - compact links for Arrowgram/Hotdocx/LastRevision without marketing
     paragraphs unrelated to the emdash review path.
8. **Historical TypeScript Prototype**
   - one paragraph pointing to Git history and the handoff;
   - no stale feature catalogue presented as current v3.2 behavior.

The README does not list plan/decision/checkpoint histories in its opening
sections. Detailed plans remain linked through the handoff.

## Proportional Implementation And Validation

The implementation is split into three bounded checkpoints.

### A. Reviewer bridge

Change only the three reviewer files and root `package.json` command described
above.

Run:

```bash
node --require ts-node/register --test \
  tests/v3_2_browser_reviewer_tests.ts \
  tests/v3_2_categorical_text_nested_ordinary_tests.ts
./scripts/pnpmw run typecheck
./scripts/pnpmw run lint
./scripts/pnpmw --dir emdash-template --ignore-workspace run check
```

The focused test, typecheck, and lint commands may run concurrently where
safe. Do not run the root aggregate, Lambdapi conformance, or book render:
their boundaries are unchanged.

### B. Authored edition

Change only the ten authored/structured book files listed above. Run the
bounded assembly, evidence, typography, source, and paper validation owned by
those files. A single `book:check` may be used after the edition is complete;
do not rerun it after each paragraph.

Because no Lambdapi file changes, retain the recorded kernel checks. The
evidence checker verifies that every new owner/reviewer reference still
exists. Do not rerun kernel CI for unchanged mathematical sources.

### C. Artifact and repository presentation

After the authored edition is stable:

1. use the existing `book:release` once;
2. generate the deterministic PDF a second time as required by the book
   release checklist and compare SHA-256;
3. use the PDF visual-review workflow to inspect the title, contents,
   affected sections, every chapter/appendix first page shifted by pagination,
   evidence tables, bibliography, credits, and license;
4. run `book:promote` and verify source/canonical/compatibility checksums;
5. replace the README and validate its local links/commands; and
6. run only a focused correction gate if any artifact-affecting fix is made.

The two deterministic PDF generations and visual review are strictly
necessary at this final artifact boundary. No third multi-minute aggregate
run is authorized for reassurance about unchanged output.

## Exact Non-Claims

This decision adds none of:

- a new Lambdapi declaration, rewrite, or proof-time unification rule;
- a new TypeScript checker, conversion, runtime, parser-resolver, or
  categorical lowering branch;
- a general parser for Lambdapi or the book's complete mathematical notation;
- inference of binder mode from classifier annotation;
- arbitrary pointwise-to-coherent functor/transfor construction;
- arbitrary displayed telescope depth, variance, or exchange across
  dependency;
- a primitive `Product_catd` or general total-category pullback equation;
- whole-library transfer graduation or a completed WalkingEnd/HIT batch;
- groupoidal closure or global metatheory;
- remote deployment, publication, release, tag, push, or merge; or
- cleanup of unrelated untracked or ignored files.

## Git Boundary

Implementation uses only bounded green local checkpoint commits on
`goal/typescript-elaborator-v3.2` in
`/home/user1/emdash1-elaborator-goal`.

Before every checkpoint:

1. inspect staged and unstaged state;
2. stage only the exact tranche files;
3. run the tranche's proportional gate;
4. run `git diff --cached --check`;
5. review the exact staged diff; and
6. synchronize the living plan/decision ledger.

No push, merge, PR, deployment, publication, tag, amend, rebase, reset,
history rewrite, worktree/branch removal, or unrelated cleanup is authorized.

## Successor Effects

If approved:

- `BOOK-PROSE-1A`, the one reviewer bridge, and the exact structured evidence
  update become implementation-ready;
- `BOOK-ARTIFACT-1B` follows only after the authored edition is source-green;
- `REPO-PRESENT-1C` follows the validated artifact;
- `PRODUCT-BOOK-GRADUATE-1` may then freeze the final checksum, reader path,
  capabilities, and limitations; and
- all remaining bulk scale rows stay deferred to a future explicit goal.

If implementation discovers a false mathematical assumption, missing owner,
unexpected parser/checker requirement, or artifact-owner conflict, stop that
tranche and freeze a correcting proposal. Do not broaden this decision
implicitly.
