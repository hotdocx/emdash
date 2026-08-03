# TypeScript Elaborator v3.2 PathOut Standard-Library Plan

Status: deferred future-goal proposal; not part of the completed categorical-
binder usability persistent goal

Authority: `emdash2/emdash3_2.lp`, especially its representable, fibre-
covariance, directed-Sigma, PathOut, PathInd, and transitivity sections;
`emdash2/emdash3_2_checks.lp` supplies the executable regression statements

## Purpose

Expose outgoing paths, fixed-source path induction, its internally varying-
source packaging, and the transitivity benchmark as a TypeScript emdash
standard library and eventual reviewer demonstration.

This is not a proposal for another TypeScript kernel, another binder
architecture, or a Lambdapi-source parser. It is a library/integration plan
over the completed dependent LF, explicit emdash Core, generic declaration and
rewrite compilers, and recursive categorical construction surface.

## Architectural Verdict

The PathOut development separates into two kinds of ingredients.

### Standard-library definitions over existing owners

The following named constructions are transparent compositions in the active
authority and can be authored directly in TypeScript from existing emdash
owners:

- `Rep_catd_func`, `Rep_catd`, and `Rep_transport_func` from `hom_int`, the
  identity functor, and generic action;
- `PathOut_cat`, `PathOut_cat_func`, and `PathOut_transport_func` from
  `Sigma_cat`, `Sigma_func`, and representable action;
- `pathout_obj`, `pathout_refl_obj`, and `pathout_refl_arrow` from
  `Struct_sigma`, ordinary identity, and `sigma_transport_arrow`;
- motive pullbacks, Pi targets, Sigma-total presentations, and section
  pullback from existing `Pullback_catd`, `Pi_*`, `Sigma_*`, and generic
  displayed action;
- the transitivity motive and its ordinary representable precomposition
  normal form from existing mixed-variance and fibre-covariance owners.

These definitions need no new Core node, checker branch, evaluator case,
external naturality equation, curry encoding, or active Lambdapi owner.

### Existing semantic owners to declare in the library

Fixed-source path induction is not definitionally derived from Sigma/Pi alone.
The active kernel already declares `path_ind_sec` and gives it component and
specialized computation rules. Its coherent packages include existing opaque
owners such as `PathOutReflEval_funcd`, `PathInd_func`, and `PathInd_transfd`.
The selected design is to import/transfer those existing owners and rules into
the TypeScript standard library through the explicit declarative LF transfer
machinery. Concretely, that machinery creates checked TypeScript declarations;
"transfer" here records active-authority identity and provenance, not a
runtime Lambdapi dependency or a requirement to parse `.lp` source. The
library must not replace these owners with a new TypeScript primitive or
pretend to synthesize induction from pointwise data.

The generic TypeScript dependent LF already supports checked dependent
declarations, transparent bodies, runtime rewrite rules, proof-time
comparisons, evaluation, and deterministic Lambdapi emission. Consequently,
the remaining question is exact library closure and ergonomic presentation,
not semantic feasibility of the core.

## Current TypeScript Inventory

| Layer | Current evidence | Future work |
| --- | --- | --- |
| Generic dependent LF | checked declarations, Pi/lambda, conversion, runtime and proof rules | no new kernel mechanism expected |
| Categorical prerequisites | `Catd`, fibres, Sigma/Pi, pullback, section evaluation, generic action, `hom_int`, `fib_cov_tapp0_func`, `sigma_transport_arrow`, and higher action occur in reviewed transfer descendants | qualify the smallest exact profile instead of duplicating owners |
| Public typed construction API | categories, objects/arrows, displayed families, fibres, totals, dependent pairs, family transport, Sigma arrows, sections, application, and recursive binders | add thin classifier-checked identity-arrow, representable, canonical Sigma-transport, PathOut, and PathInd facades where useful |
| Named PathOut/PathInd library | absent from `src/v3_2` at this completion boundary | author a dedicated descendant library module |
| Text/browser presentation | no PathOut grammar or preset | add only after direct typed construction and computation are green |

The public `sigmaArrow` operation accepts a general fibre component; the
canonical `sigma_transport_arrow` facade is a distinct useful operation. A
missing facade is not a missing semantic owner. Likewise, a representable
family may compile to the transparent `hom_int(id)` body while retaining the
named library presentation.

## Proposed Future Work Ledger

| Slice | Dependencies | Exact purpose |
| --- | --- | --- |
| `PATHOUT-STDLIB-AUTHORITY-0A` | active source and checks; current transfer profiles | Freeze exact declaration/rule order, distinguish transparent definitions from opaque owners, and measure the smallest descendant profile. No behavior. |
| `PATHOUT-STDLIB-FOUNDATION-1B` | completed 0A | Author representables, fixed-source `PathOut`, source-arrow action, path objects, reflexive object, and canonical reflexive-to-path arrow. Check fibre, object, arrow, and next-action behavior. |
| `PATHOUT-STDLIB-FIXED-INDUCTION-1C` | completed 1B | Import/transfer the existing fixed-source `path_ind_sec` owner and exact component/specialized rules as checked library declarations; expose a typed section constructor and one nontrivial computation. |
| `PATHOUT-STDLIB-INTERNALIZED-1D` | completed 1C | Add motive variation, `PathInd_func`, primary `PathInd_transfd`, and the derived Sigma-total presentation, preserving internally owned source-arrow and higher action. |
| `PATHOUT-STDLIB-TRANSITIVITY-1E` | completed 1D | Add `CompTarget_catd`, `CompMotive_catd`, `path_comp_sec`, and the checked reduction to representable precomposition/composition. |
| `PATHOUT-STDLIB-PRESENTATION-1F` | completed direct typed slices | Add narrow text syntax, CLI/browser reviewer material, and book-facing explanation without adding a second semantic engine. |
| `PATHOUT-STDLIB-GRADUATE-0G` | all selected slices | State the exact library and computation envelope; retain any unimplemented internalized or presentation layers honestly. |

Each behavioral slice requires its own frozen proposal and separate review.
The first executable slice must inventory existing transfer owners before
adding declarations. Transparent aliases should keep transparent bodies;
opaque existing semantic owners should keep opaque interfaces and their exact
active rules. No owner is promoted merely for naming symmetry.

## Required Evidence For A Future Implementation

1. Exact active-source signatures/bodies/rules and owning positions.
2. A compiled TypeScript declaration module over the smallest reviewed
   prerequisite profile, with no duplicate owner.
3. Direct typed examples whose explicit Core agrees with the transparent
   active definitions.
4. Fixed-source point and arrow computation plus at least one internally
   varying-source or higher-action observation before claiming the
   internalized theorem.
5. Strict negative tests for wrong source object, wrong motive base, wrong
   transported endpoint, and foreign scoped terms.
6. A bounded Lambdapi conformance oracle for selected definitions and rules.
7. Text/browser parity only after the typed standard library is green.
8. Proportional validation under root and nested SOP; do not rerun unchanged
   repository aggregates for reassurance.

## Explicit Non-Goals

This future plan does not authorize:

- a generic Lambdapi parser or bulk acquisition redesign;
- a new TypeScript Core/checker/evaluator primitive for path induction;
- external naturality or functoriality equations;
- curry or total-context encodings as binder substitutes;
- arbitrary variance/dependency DAG graduation;
- whole-library transfer graduation;
- groupoidal closure, general normalization, confluence, canonicity, or
  consistency claims;
- push, merge, publication, deployment, or worktree cleanup.

## Deferred Persistent `/goal` Launch Prompt

Use this only when starting the separate future PathOut standard-library goal:

```text
Implement the living TypeScript/emdash v3.2 PathOut standard-library program
rooted at docs/TYPESCRIPT_ELABORATOR_V3_2_PATHOUT_STANDARD_LIBRARY_PLAN.md.
Treat its authority order, work ledger, evidence requirements, and explicit
non-goals as part of the objective. Recover actual Git/worktree state and
active Lambdapi owners on every continuation. Audit and reuse existing generic
TypeScript LF and categorical transfer owners before adding declarations.
Author transparent PathOut definitions as standard-library compositions;
faithfully import/transfer existing opaque PathInd owners and exact rules as
checked library declarations rather than adding Core/checker primitives or
external coherence evidence. For each
bounded slice, freeze and independently review the proposal, implement focused
typed behavior and tests, run proportional validation, synchronize the plan,
and create rollback-safe local checkpoints only where authorized. Do not
resume bulk scale, text/browser presentation, push, merge, publication, or
cleanup unless a later exact gate authorizes it.
```

## Relationship To The Completed Usability Goal

The categorical-binder usability goal establishes the prerequisite
architecture: recursive ordinary and displayed binders, canonical finite
displayed telescopes, internally owned action, direct/text parity for the
reviewed grammar, and an executable reviewer. Deferring this standard-library
program therefore does not reopen or weaken that completion claim. It records
the next research-library integration program for a future persistent goal.
