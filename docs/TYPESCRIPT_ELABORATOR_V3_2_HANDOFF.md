# TypeScript Elaborator For Emdash v3.2 — Start Here

Date: 2026-07-23
Status: ELAB-0 implemented; this remains the authority and growth handoff

## Purpose

This document prepares the next fresh conversation to work from the Git root
on a TypeScript elaborator for the active emdash v3.2 Lambdapi kernel. It is a
handoff and design boundary, not a claim that the existing TypeScript category
layer already implements v3.2.

The first checked vertical slice now lives under `../src/v3_2/`, with its
evidence, architecture reassessment, validation record, and human review
points in
[`TYPESCRIPT_ELABORATOR_V3_2_ELAB_0_RFC.md`](./TYPESCRIPT_ELABORATOR_V3_2_ELAB_0_RFC.md).

The intended word *syntax* is broad. Users may construct a typed surface AST
with ordinary TypeScript expressions; a string parser can be added later. The
first architectural problem is elaboration and compilation into explicit
kernel applications, not tokenization.

## Authority Boundary

Read these in order before selecting a semantic target:

1. `../emdash2/emdash3_2.lp` — active definitions and computation;
2. the four active one-way extension modules named in
   `../emdash2/AGENTS.md`;
3. `../emdash2/emdash3_2_checks.lp` — executable regression statements;
4. `../emdash2/reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`;
5. `../emdash2/reports/EMDASH_FOUNDATIONS.md`;
6. `../emdash2/reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`;
7. the active task plan selected through `../emdash2/reports/INDEX.md`.

The root `src/` implementation predates the current kernel. Its generic
elaboration machinery is feasibility evidence, but names such as
`FunctorTypeTerm`, `MkFunctorTerm`, `NatTransTypeTerm`, and the built-in
category rules do not define the v3.2 target. Do not port the active kernel
backward into those nodes piecemeal or recreate retired compatibility names.

## Intended Trust And Compilation Boundary

The preferred initial architecture is:

```text
TypeScript surface AST (string parsing optional)
        ↓ scope, binder-mode, and implicit-argument elaboration
typed surface/core IR with source locations and metavariables
        ↓ owner-directed lowering
explicit v3.2 kernel application IR
        ↓ deterministic Lambdapi serialization
temporary/reviewer .lp consumer
        ↓ lambdapi check
authoritative typing, conversion, and computation result
```

Lambdapi remains the trusted checker. The TypeScript layer may recover omitted
categories, endpoints, variances, binder modes, and implicit arguments, and it
should produce useful constraints and diagnostics. It must not silently invent
functorial action, naturality, a missing higher cell, or a mathematical
equivalence that the active kernel does not provide.

The kernel-target IR should initially be small and mechanical: variables,
binders, applications of named active symbols, explicit implicit arguments,
and source/provenance metadata. Avoid defining a second independent evaluator
for the full categorical calculus before an end-to-end consumer requires it.

## What May Be Reused

Audit before retaining or deleting anything. Likely reusable mechanisms are:

- the generic `Term`/binder representation, or lessons from it;
- bidirectional `infer`/`check` organization;
- holes, constraint collection, occurs checking, and higher-order pattern
  unification;
- rewrite/unification separation as an implementation pattern;
- source-independent proof-state traversal;
- test harness organization and direct TypeScript AST construction.

Likely redesign boundaries are:

- all hard-coded one-category constructors and their implicit-slot tables;
- the old `MkFunctorTerm` proof/coherence contract;
- built-in `Set`, ordinary natural-transformation, and hom-functor reductions;
- any claim that the TypeScript normalizer is the authority for v3.2;
- the parser grammar, until the typed AST and lowering contract stabilize.

The old code should be removed only after an inventory maps each retained test
to a reusable generic invariant or a current v3.2 consumer. A wholesale first
deletion would erase useful executable evidence and make regressions difficult
to classify.

## Implemented First Tranche

The ELAB-0 RFC and isolated `src/v3_2/` implementation now cover this first
vertical slice:

1. define a minimal source-located TypeScript surface AST and a distinct
   explicit kernel-target AST;
2. model explicit, implicit, functorial, natural, and object-only binder modes
   without committing to a string notation;
3. lower one small current family—preferably ordinary `fapp0`,
   `fapp1_fapp0`, and `tapp1_fapp0` applications—using symbol names and types
   relocated from the active kernel;
4. serialize the result into a focused `.lp` probe that imports the active
   owner and is accepted or rejected by Lambdapi as expected;
5. include one positive omission-recovery case and one wrong-endpoint or
   wrong-binder-mode negative case;
6. keep the existing 152-test prototype baseline passing until the RFC selects
   an explicit migration or replacement boundary.

This slice is deliberately end to end. A larger AST taxonomy without a checked
Lambdapi consumer would not yet demonstrate an elaborator.

## Decisions That Need Explicit Review

Record, rather than silently assume, the following choices:

- whether the first implementation lives beside the prototype under a new
  `src/v3_2/` boundary or begins a package split;
- whether successful elaboration returns only kernel AST, serialized Lambdapi,
  or both;
- how Lambdapi diagnostics are mapped back to TypeScript source locations;
- whether TypeScript performs any normalization beyond surface substitution
  and metavariable solving, and how that remains subordinate to Lambdapi;
- which canonical surface constructs are user-facing primitives versus
  derived notation;
- when a string parser becomes valuable enough to stabilize a grammar.

Do not mix these decisions with a physical monorepo split, kernel rewrite
migration, or restoration of the retired D0/D1 compatibility layer.

## Worktree And Validation Workflow

From a fresh worktree rooted anywhere on the same disk:

```bash
./scripts/bootstrap-worktree.sh
./scripts/pnpmw run check:ts
EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
```

The bootstrap creates a local dependency-link graph from the machine-wide pnpm
content-addressable store. It does not share mutable `node_modules` directories
between branches.

During implementation, use focused TypeScript tests first. For every emitted
kernel form, use `emdash2/scripts/probe.sh` with a bounded temporary consumer,
then broaden to `make -C emdash2 check`. Run
`./scripts/pnpmw run check:all` before handing off a substantial cross-layer
change.

## Suggested Fresh-Conversation Prompt

```text
Work from the Git root ~/emdash1 on the TypeScript elaborator for the active
emdash v3.2 kernel. Read AGENTS.md and
docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md, then recover the active Lambdapi
authorities and inspect the clean/dirty Git state. Treat the existing root
category layer as stale feasibility evidence: inventory reusable generic
elaboration machinery, but do not extend or delete it wholesale. Start an
evidence-backed ELAB-0 RFC and implement the smallest end-to-end TypeScript
surface-AST → explicit-v3.2-kernel-AST → checked-Lambdapi probe slice, with
focused positive and negative tests. Keep package/worktree and kernel checks
green and record any mathematical design choice that needs human review.
```
