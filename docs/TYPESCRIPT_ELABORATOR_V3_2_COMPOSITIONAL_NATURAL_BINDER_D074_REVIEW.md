# TypeScript Elaborator v3.2 — D-074 Compositional Natural Binder Review

Date: 2026-08-02

Review-ID: D-DTTLF-USABILITY-074

Gate: H-DTTLF-USABILITY-COMPOSITIONAL-NATURAL-01

Proposal checkpoint:
`7104ca8cc8c9c46187093ba2051dd80917cc31a3`

Decision: **approved as proposed** under the standing unattended-review
delegation recorded by the living elaborator plans. The approval is limited to
`COMPOSITIONAL-NATURAL-BINDER-1B`; it grants no authority for a compact-`:^nd`
refactor, new kernel semantics, text/browser work, publication, or Git history
mutation beyond rollback-safe local checkpoints.

## Review Method

The review compared the frozen proposal with:

- active `Transf_cat`, `tapp0*`, `tapp1*`, identity, composition,
  precomposition, and postcomposition owners in `emdash2/emdash3_2.lp`;
- the existing rich TypeScript `transfor` Core classifier and generic checker;
- the exact closed/open behavior of `applyOrdinaryTransfor`;
- the integrated `displayedTransforContextLambda` factorer retained as
  rollback evidence;
- the explicit active-kernel statement that mixed transformation sections are
  objects of `Pi_cat(Transf_catd ...)`; and
- the existing fixed `Transf_catd` and `Transfd_cat` action tests.

No behavior file was edited during this review.

## Findings

### 1. The proposed classifier is frontend metadata, not new LF semantics

`ordinary-natural-component` records a locally nameless index and the whole
source/target functors recovered for that index. It is analogous to the
existing construction-only indexed classifiers: it cannot be serialized to
Core and must be eliminated by its owning abstraction. It therefore does not
add a proof object, equality witness, cast, or naturality axiom.

### 2. Every positive branch has an existing internal owner

The proposal's five branches reconstruct only:

- an already coherent `Transf_cat` object;
- generic identity in `Functor_cat`;
- generic vertical composition in `Functor_cat`;
- generic Hom action of fixed precomposition; or
- generic Hom action of fixed postcomposition.

The object expression under the binder is first compiled by the existing
ordinary functorial contextual compiler. Thus the new factorer does not infer
naturality from a pointwise arrow; it recognizes the component syntax of an
internally owned transformation and recovers that transformation.

### 3. Eta exactness gives the correct first compositional witness

The direct body `eta[a]` can return the original `eta` Core term, not a wrapper
or proof-time cast. This establishes the required first equation:

```text
transforLambda(a => eta[a]) == eta.
```

Identity, composition, and whiskering then form a recursive closed body
algebra around that leaf.

### 4. The proposal preserves the classifier distinction

The implementation does not require or claim:

```text
Transfd_cat FF GG = Pi_cat(Transf_catd A B FF GG).
```

Ordinary `Transf_cat`, mixed `Transf_catd` sections, and displayed
`Transfd_cat` remain distinct. Compact `:^nd` retains its current integrated
outer compiler, so no variance-sensitive bridge is introduced implicitly.

### 5. Existing owners are sufficient

The maximal reviewed TypeScript profile already carries the generic action
owners and the transferred fixed pre/postcomposition constructions needed by
the proposal. Using that lineage for the first bounded profile is acceptable.
A later graduation may decouple the ordinary feature into a smaller runtime
profile, but such DevOps/profile minimization is not semantic work and must not
delay the usability slice.

### 6. The fail-closed boundary is reviewable

The proposal rejects an arbitrary point Hom, foreign/escaped tokens, captured
outer contexts, unsupported classifiers, and endpoint mismatches. Callback
evaluation remains exactly once, and no callback or token may enter explicit
Core. Focused tests can observe every one of these boundaries without a new
kernel oracle or long repository aggregate.

## Required Implementation Discipline

The approved implementation must:

1. keep `ordinary-natural-component` construction-only and locally nameless;
2. recover eta exactly before using generic precomposition;
3. use the existing ordinary contextual compiler for object expressions;
4. recursively type-check composition endpoints;
5. express both whiskers as generic Hom actions of existing functors;
6. preserve the current compact `:^nd`, `Transf_catd`, and `Transfd_cat`
   implementations byte-for-byte except for unavoidable shared type plumbing;
7. add focused positive and negative tests before broader validation; and
8. stop and re-open the decision if generic Core checking exposes a genuinely
   missing owner rather than adding a local mirror or cast.

## Validation Boundary

Run the new focused test, nearest existing surface/compact-`:^nd` tests,
typecheck, lint, and exact diff hygiene. Because this changes the shared
frontend and public program, run one root `check:ts` only after the focused
tranche is green. Do not run kernel CI, browser, print, book, or `check:all`.

## Decision

`D-DTTLF-USABILITY-074`: approve
`COMPOSITIONAL-NATURAL-BINDER-1B` exactly as frozen at
`7104ca8cc8c9c46187093ba2051dd80917cc31a3`.
