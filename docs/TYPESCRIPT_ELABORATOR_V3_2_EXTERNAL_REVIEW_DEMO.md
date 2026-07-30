# Emdash v3.2 External-Review Guide

Date: 2026-07-30
Reader profile: `emdash-v3.2-0.3.0-dev`
Inputs: direct typed TypeScript plus bounded categorical text
Production Lambdapi dependency: none
Mathematical authority:
[`emdash2/emdash3_2.lp`](../emdash2/emdash3_2.lp) and its active imports

## Start Here

Read the current development edition of
[*Functorial Type Theory: Univalent Foundations for Mathematics*](./emdash-book.pdf).
The reviewed PDF has 199 pages, 16 embedded fonts, and SHA-256:

```text
b34b7e430deacf4b91ce354c5e5eb3d2674ef08e93d3bcbd4ca7618ea37f41d7
```

From a fresh checkout, start the integrated client-side reviewer:

```bash
./scripts/bootstrap-worktree.sh
./scripts/pnpmw run reviewer:dev
```

Open the URL printed by Vite. A useful first review is:

1. select **Nested functorial exchange**, elaborate it, and inspect the
   generated explicit Core and structural lowering;
2. select **Displayed mixed telescope** and compare semicolon dependency
   levels with the independent comma-separated middle siblings;
3. select **Displayed natural composition** to see a bounded `^nd` coherent
   construction;
4. open **Research evidence**, run the three-panel report, and inspect the
   outer dependent LF, ordinary categorical, and genuine displayed-chain
   witnesses; and
5. open the book from the same workbench and compare its formal-presentation
   appendix with the executable results.

For a noninteractive terminal account of the same architecture:

```bash
./scripts/pnpmw run demo:external-review
```

Neither path starts a Lambdapi process. Lambdapi remains the checked
mathematical authority and an optional development-time conformance oracle.

## What Is Executable

The browser's editable categorical view exposes these ten reviewed presets:

| Preset | Source |
| --- | --- |
| Pointwise application | `λ^f x. (H x) (K x)` |
| Nested functorial exchange | `λ^f x : A. λ^f y : B. E y x` |
| Fixed inner evaluation | `λ^f x. F x y0` |
| Whole Hom action | `G pA` |
| Natural indexed composition | `λ^n k : K. (FF k) (s k)` |
| Displayed functor composition | `λ^fd a : E. GG (FF a)` |
| Displayed weakening | `λ^fd a : E. s (indexOf a)` |
| Displayed sibling pairing | `λ^fd (b : B, c : C). fibrePair (FF b) (GG c)` |
| Displayed mixed telescope | `λ^fd (a : A; b : B, c : C; d : D). fibrePair b c` |
| Displayed natural composition | `λ^nd k : K. composeCells (theta k) (eta k)` |

Each successful request reports readable source, explicit emdash Core,
inferred and expected classifiers, structural prerequisites, and checked
computation. A rejected request reports the exact source span and typed
failure instead of guessing an action or accepting external coherence
equations.

The explicitly started report adds three direct-TypeScript witnesses:

- an outer dependent LF with lambda, Pi, dependent Sigma-telescope data,
  checking/inference, beta reduction, and a wrong-family diagnostic;
- recursively usable ordinary categorical binders lowered through identity,
  composition, pairing/evaluation, diagonal, weakening, and exchange; and
- a genuine displayed dependency chain with object action, internalized-arrow
  action, reindexing, recursive subexpressions, and a wrong-base diagnostic.

The workbench also retains the small editable minimal-Core playground. The
categorical/report implementation is a lazy browser chunk, and the full
report runs only when requested.

## Input Envelope

The current categorical text surface is graduated for an exact bounded
mathematical-expression profile:

- four intrinsic binder modes: `^f`, `^n`, `^fd`, and `^nd`;
- 37 canonical operation heads routed to 47 mathematical construction
  methods;
- classifier-directed neutral application rather than a hard-coded
  `fapp*`/`tapp*` table;
- one independent displayed sibling group, one genuine `[1,1]` dependency
  edge, and the mixed `[1,2,1]` telescope;
- recursively nested ordinary functorial lambdas when their expected
  classifiers are available; and
- category, displayed-family, term, whole-Hom, and selected higher-action
  results through the same typed categorical program.

The remaining 21 public program methods are deliberately host-side
declaration, fixture, inspection, comparison, serialization, and compilation
operations. Text parity is parity with mathematical expressions, not with
arbitrary JavaScript callback control flow.

Binder mode belongs to the lambda:

```text
λ^f  x : A. ...
λ^n  k : K. ...
λ^fd a : E. ...
λ^nd k : K. ...
```

The classifier annotation after the variable is optional only when a
bidirectional expected classifier supplies it. The elaborator never infers
the intrinsic mode from that annotation.

## Two Representative Categorical Examples

Nested ordinary abstraction:

```text
λ^f x : A. λ^f y : B. E y x
```

Given `E : Functor B (Functor_cat A C)`, the occurrence order requires the
existing exchange/currying construction. Text and direct TypeScript produce
the same explicit Core; the parser does not implement exchange as an ad hoc
special case.

Mixed displayed context:

```text
λ^fd (a : A; b : B, c : C; d : D). fibrePair b c
```

Here `A : Catd K`, `B,C : Catd (Sigma_cat A)`, and
`D : Catd (Sigma_cat (Productd B C))`. A semicolon advances to a family over
the preceding total context, while the comma keeps `b` and `c` as
independent siblings over the same prefix. The lowering reuses internalized
fibrewise products, displayed pairing, Sigma projections, and reindexing;
object and base-arrow behavior stay inside those owners.

These examples illustrate the usability goal: bound categorical variables
may occur recursively inside expressions. Explicit brackets are not required
around every occurrence, and the frontend does not supply pointwise
naturality proofs from outside the kernel.

## Pipeline And Authority

```text
categorical text or direct typed TypeScript
  -> scoped recursive contextual elaboration
  -> backend-neutral explicit emdash Core
  -> generic TypeScript dependent-LF checking and reduction
  -> optional deterministic Lambdapi conformance
```

The active Lambdapi v3.2 modules author the categorical declarations,
computation rules, and proof-time comparisons. The TypeScript product
selects those reviewed owners into explicit Core and checks that Core with
one generic dependent logical framework. It does not maintain a second
categorical kernel or require Lambdapi in the browser.

Parsing, typed resolution, and internal categorical factorization are
separate fail-closed phases. A string may be grammatically well formed but
still be rejected when its expected classifier is absent, its family bases
do not align, or no internal owner carries the required object-and-arrow
action.

## Command Matrix

| Command | Purpose | Boundary |
| --- | --- | --- |
| `./scripts/pnpmw run reviewer:dev` | Start the integrated local reviewer | Development server only; no deployment |
| `./scripts/pnpmw run demo:external-review` | Print the curated direct-TypeScript three-panel report | Fixed report, not editable text |
| `./scripts/pnpmw run demo:categorical-text` | Run compact categorical text examples | Uses the same adapter as the browser |
| `./scripts/pnpmw run check:browser-reviewer` | Typecheck, lint, and build the static workbench | Product check; relative client assets |
| `./scripts/pnpmw run check:ts` | Check the root TypeScript workbench | Development validation |
| `./scripts/pnpmw run kernel:check` | Check the active Lambdapi kernel | Requires Lambdapi |

The optional advanced direct-TypeScript higher-action witness is:

```bash
./scripts/pnpmw run demo:categorical-displayed-nd-higher
```

It exercises selected object, whole-Hom, and higher-cell action for displayed
transfors. It is not a claim of arbitrary `^nd` coherence.

## Exact Current Boundary

This reader profile does not claim:

- a parser for all notation in the book or arbitrary Lambdapi source;
- textual outer-LF terms, arbitrary holes, or arbitrary host-language
  callbacks;
- arbitrary displayed telescope depth, variance, exchange across dependency,
  or pointwise-to-coherent synthesis;
- mixed nested `^n`/`^fd`/`^nd` classifiers without an existing reviewed
  direct semantic construction;
- final cross-environment agreement on every historical binder notation;
- systematic transfer of the whole Lambdapi library or a graduated batch
  throughput result;
- groupoidal specialization/closure;
- global normalization, confluence, canonicity, consistency, or semantic
  soundness for the full combined calculus;
- a performance or release SLA; or
- a GitHub Pages workflow, deployment, or remote publication.

The demonstrated operations are nevertheless real: they compile to explicit
owners, typecheck, and compute. The boundaries above identify the next
research and scale work rather than qualifications hidden inside the
successful examples.

## Evidence And Continuation

The detailed implementation evidence is recorded in:

- the
  [`integrated reviewer plan`](./TYPESCRIPT_ELABORATOR_V3_2_INTEGRATED_REVIEWER_PLAN.md);
- the
  [`syntax-parity plan`](./TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md);
- the
  [`book and repository graduation plan`](./TYPESCRIPT_ELABORATOR_V3_2_BOOK_AND_REPOSITORY_GRADUATION_PLAN.md);
  and
- the
  [`v3.2 elaborator handoff`](./TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md).

The manifest-owned book PDF and both tracked public PDF names are
byte-identical at the digest printed above. The final release, deterministic
repeat, 199-page integrity check, and visual review are recorded in the book
graduation plan.

Bulk systematic-transfer qualification remains preserved, not completed.
`SCALE-STRESS-3C`, `SCALE-BATCH-1`, and `SCALE-GRADUATE-1` belong to a future
explicit persistent goal; presenting the current product does not silently
graduate them.
