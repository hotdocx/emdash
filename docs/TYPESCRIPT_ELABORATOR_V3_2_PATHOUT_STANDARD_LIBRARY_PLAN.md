# TypeScript Elaborator v3.2 PathInd Trusted-Profile And PathOut Library Plan

Status: deferred future-goal proposal; not part of the completed categorical-
binder usability persistent goal

Authority: `emdash2/emdash3_2.lp`, especially its representable, fibre-
covariance, directed-Sigma, PathOut, PathInd, and transitivity sections;
`emdash2/emdash3_2_checks.lp` supplies the executable regression statements

## Purpose

Expose outgoing paths, fixed-source path induction, its internally varying-
source packaging, and the transitivity benchmark through two deliberately
separate layers: a sealed, vetted TypeScript emdash v3.2 theory profile for
existing opaque semantic owners and their computation/proof rules, followed
by an end-user standard library of transparent definitions and proof terms.
The eventual reviewer demonstration consumes both layers without hiding their
different trust status.

This is not a proposal for another TypeScript meta-kernel, another binder
architecture, or a Lambdapi-source parser. It is a trusted-profile and
library-integration plan over the completed dependent LF, explicit emdash
Core, generic declaration and rule compilers, and recursive categorical
construction surface. The historical filename is retained so existing plan
links remain stable; "standard library" in that filename does not place the
opaque PathInd rules inside the end-user library.

## Architectural Verdict And Trust Boundary

The PathOut development separates into four layers.

1. The **generic TypeScript meta-kernel** checks dependent declarations,
   transparent definitions, runtime rules, proof-time comparisons, and
   explicit Core. It gains no PathInd-specific Core node, evaluator case, or
   checker branch.
2. A sealed **trusted emdash v3.2 theory profile** faithfully transfers the
   active authority's opaque semantic owners and the exact runtime/proof rules
   that specify their computation. Those declarations are data consumed by
   the generic meta-kernel, but they remain part of the trusted calculus.
3. The **end-user standard library** contains transparent definitions and
   checked proof terms constructed from the trusted profile. Its ordinary
   safe interface does not register new rewrite or unification rules.
4. Thin **typed, text, and reviewer facades** present the resulting library;
   they add no semantic engine.

Exact transcription plus the bounded Lambdapi oracle establishes fidelity to
the vetted active authority. It does not turn opaque owners or conversion
rules into end-user-derived theorems. Conversely, keeping those rules in a
sealed profile need not hard-code PathInd into the generic TypeScript
implementation.

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

### Existing semantic owners to install in the trusted profile

Fixed-source path induction is not definitionally derived from Sigma/Pi alone.
The active kernel already declares `path_ind_sec` and gives it component and
specialized computation rules. Its coherent packages include existing opaque
owners such as `PathOutReflEval_funcd`, `PathInd_func`, and `PathInd_transfd`.
The selected design is to import/transfer those existing owners and rules into
a sealed trusted emdash v3.2 profile through the explicit declarative LF
transfer machinery. Concretely, that machinery creates checked TypeScript
declarations; "transfer" here records active-authority identity and
provenance, not a runtime Lambdapi dependency or a requirement to parse `.lp`
source. The end-user library must neither replace these owners with a new
TypeScript primitive nor pretend to synthesize induction from pointwise data.

`PathInd_funcd` is transparent in the active authority and may therefore live
in the derived library once its opaque dependencies are present. Any related
opaque package enters the trusted profile only when a selected consumer needs
it; opacity is preserved rather than disguised as a library definition.

The generic TypeScript dependent LF already supports checked dependent
declarations, transparent bodies, runtime rewrite rules, proof-time
comparisons, evaluation, and deterministic Lambdapi emission. Consequently,
the remaining questions are exact trusted-profile closure, module sealing and
provenance, derived-library closure, and ergonomic presentation—not semantic
feasibility of the core.

This plan does not authorize an ordinary user API for adding conversion rules.
A future extensible-rewriting mode, if desired, must be separately trust-
labelled and gated by the project's chosen subject-reduction, termination,
confluence, and consistency policy. It is not part of this safe standard-
library program.

## Current TypeScript Inventory

| Layer | Current evidence | Future work |
| --- | --- | --- |
| Generic dependent LF | checked declarations, Pi/lambda, conversion, runtime and proof rules | no new kernel mechanism expected |
| Categorical prerequisites | `Catd`, fibres, Sigma/Pi, pullback, section evaluation, generic action, `hom_int`, `fib_cov_tapp0_func`, `sigma_transport_arrow`, and higher action occur in reviewed transfer descendants | qualify the smallest exact profile instead of duplicating owners |
| Public typed construction API | categories, objects/arrows, displayed families, fibres, totals, dependent pairs, family transport, Sigma arrows, sections, application, and recursive binders | add thin classifier-checked identity-arrow, representable, canonical Sigma-transport, PathOut, and PathInd facades where useful |
| Trusted PathInd profile | generic checked declaration/rule machinery exists; named PathInd package is absent from `src/v3_2` | install the smallest sealed, provenance-pinned opaque-owner/rule closure |
| Derived PathOut/PathInd library | absent from `src/v3_2` at this completion boundary | author transparent definitions and proof terms over the trusted profile |
| Text/browser presentation | no PathOut grammar or preset | add only after direct typed construction and computation are green |

The public `sigmaArrow` operation accepts a general fibre component; the
canonical `sigma_transport_arrow` facade is a distinct useful operation. A
missing facade is not a missing semantic owner. Likewise, a representable
family may compile to the transparent `hom_int(id)` body while retaining the
named library presentation.

## Proposed Future Work Ledger

| Slice | Dependencies | Exact purpose |
| --- | --- | --- |
| `PATHOUT-TRUST-BOUNDARY-0A` | active source and checks; current transfer profiles | Freeze exact declaration/rule order and provenance; distinguish transparent definitions from opaque trusted owners; measure the smallest descendant profile and specify its sealing boundary. No behavior. |
| `PATHOUT-LIBRARY-FOUNDATION-1B` | completed 0A | Author representables, fixed-source `PathOut`, source-arrow action, path objects, reflexive object, and canonical reflexive-to-path arrow as transparent end-user library definitions. Check fibre, object, arrow, and next-action behavior. |
| `PATHIND-TRUSTED-PROFILE-1C` | completed 1B | Import/transfer the existing fixed-source `path_ind_sec` owner and exact component/specialized rules into the sealed trusted profile; expose only a typed library consumer and one nontrivial computation above that boundary. |
| `PATHOUT-LIBRARY-INTERNALIZED-1D` | completed 1C | Add needed opaque `PathInd_func`/`PathInd_transfd` owners to the trusted profile, then derive transparent internalized/Sigma-total library presentations where the authority does. Preserve internally owned source-arrow and higher action. |
| `PATHOUT-LIBRARY-TRANSITIVITY-1E` | completed 1D | Add `CompTarget_catd`, `CompMotive_catd`, `path_comp_sec`, and the checked reduction to representable precomposition/composition, retaining the authority's transparent/opaque classification. |
| `PATHOUT-LIBRARY-PRESENTATION-1F` | completed direct typed slices | Add narrow text syntax, CLI/browser reviewer material, and book-facing explanation without adding a second semantic engine. |
| `PATHOUT-TRUSTED-LIBRARY-GRADUATE-0G` | all selected slices | State the exact trusted profile, derived library, and computation envelope; retain any unimplemented internalized or presentation layers honestly. |

Each behavioral slice requires its own frozen proposal and separate review.
The first executable slice must inventory existing transfer owners before
adding declarations. Transparent aliases should keep transparent bodies;
opaque existing semantic owners should keep opaque interfaces and their exact
active rules inside the sealed profile. No owner is promoted merely for naming
symmetry, and no trusted rule is exposed as an ordinary standard-library
declaration capability.

## Required Evidence For A Future Implementation

1. Exact active-source signatures/bodies/rules and owning positions.
2. A compiled, sealed TypeScript theory-profile module over the smallest
   reviewed prerequisite profile, with authority provenance and no duplicate
   owner.
3. Direct typed examples whose explicit Core agrees with the transparent
   active definitions.
4. Fixed-source point and arrow computation plus at least one internally
   varying-source or higher-action observation before claiming the
   internalized theorem.
5. Strict negative tests for wrong source object, wrong motive base, wrong
   transported endpoint, and foreign scoped terms.
6. A bounded Lambdapi conformance oracle for selected definitions and rules.
7. A negative capability check showing that the ordinary end-user library
   route cannot silently install runtime or proof-time conversion rules.
8. Text/browser parity only after the typed standard library is green.
9. Proportional validation under root and nested SOP; do not rerun unchanged
   repository aggregates for reassurance.

## Explicit Non-Goals

This future plan does not authorize:

- a generic Lambdapi parser or bulk acquisition redesign;
- a new TypeScript Core/checker/evaluator primitive for path induction;
- treating opaque PathInd owners or their conversion rules as end-user-
  authored standard-library definitions;
- an ordinary safe-library API for user rewrite or unification rules;
- external naturality or functoriality equations;
- curry or total-context encodings as binder substitutes;
- arbitrary variance/dependency DAG graduation;
- whole-library transfer graduation;
- groupoidal closure, general normalization, confluence, canonicity, or
  consistency claims;
- push, merge, publication, deployment, or worktree cleanup.

## Deferred Persistent `/goal` Launch Prompt

Use this only when starting the separate future trusted-profile and PathOut-
library goal:

```text
Implement the living TypeScript/emdash v3.2 PathInd trusted-profile and
PathOut derived-library program
rooted at docs/TYPESCRIPT_ELABORATOR_V3_2_PATHOUT_STANDARD_LIBRARY_PLAN.md.
Treat its authority order, work ledger, evidence requirements, and explicit
non-goals as part of the objective. Recover actual Git/worktree state and
active Lambdapi owners on every continuation. Audit and reuse existing generic
TypeScript LF and categorical transfer owners before adding declarations.
Author transparent PathOut definitions and proof terms as end-user standard-
library compositions. Faithfully import/transfer existing opaque PathInd
owners and exact rules only into a sealed, provenance-pinned trusted emdash
v3.2 theory profile—not as end-user library rules and not as Core/checker
primitives or external coherence evidence. Preserve the active authority's
transparent/opaque classification. For each
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
reviewed grammar, and an executable reviewer. Deferring this trusted-profile
and derived-library program therefore does not reopen or weaken that
completion claim. It records the next trusted-theory/library integration
program for a future persistent goal.
