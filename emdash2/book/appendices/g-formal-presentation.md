<a id="appendix-formal-presentation"></a>

# Appendix G. Formal Presentation Of Functorial Type Theory

This appendix will give the formal presentation underlying the mathematical
chapters. Its governing order is categorical kernel first, mathematical
surface second, optional elaborator third, and external models as a separate
semantic layer. The outline below is already normative even where full prose
is deferred to Phase C6.

## G.1 Judgments, contexts, and classifiers

The full presentation will distinguish the Lambdapi meta-level from the
internal `Cat`, `Obj`, `Hom`, `Functor`, and `Transf` classifiers. External
typing, runtime conversion, proof-time comparison, equality evidence, and
equivalence are different judgments or structures.

## G.2 The mathematical categorical presentation

The book's notation for iterated homs, functors, transfors, directed families,
and their applications is a readable signature. It is not an untyped parser
grammar and does not precede the categorical calculus it presents.

## G.3 The checked Lambdapi presentation

The implementation uses declarations, transparent definitions, stable or
opaque heads, rewrite rules, proof-time unification rules, assertions, and
modules. The eventual prose will explain representative owners without
reprinting the kernel.

## G.4 Formation, introduction, elimination, and computation

Every major former is to be presented by formation, introduction,
elimination, computation, and—where available—uniqueness or a universal
property. Functorial type theory adds an action layer: a pointwise rule is not
complete until its arrow and higher-cell behavior has also been accounted
for.

## G.5 Elaboration and canonical surface syntax

Implicit arguments, binder modes, and readable notation belong to an optional
future elaboration layer that compiles to explicit categorical owners. The
outdated TypeScript prototype in the parent repository is read-only
feasibility evidence, not a dependency or current syntax authority.

## G.6 Directed higher-inductive signatures

WalkingEnd is the worked signature: object and arrow constructors, contextual
elimination, coherence data, computation, and a dimension witness. It does
not by itself implement a general directed-HIT schema.

## G.7 Basic metatheory and its boundary

| Property | Current warranted statement |
| --- | --- |
| typing of active sources | checked by bounded Lambdapi runs |
| selected computation | witnessed by promoted rules and focused assertions |
| evidence traceability | checked syntactically by the book tooling |
| global confluence | not established for the whole rewrite/unification theory |
| strong normalization | not established for the whole theory |
| global canonicity | not established beyond selected computations |
| consistency and semantic soundness | model evidence and future metatheory, not a consequence of successful compilation |

Warning inventories, critical-pair probes, and deterministic builds are
engineering evidence. They are not substitutes for global metatheorems.

> **Formal status — mathematical development.** This appendix is an
> architecture contract. Phase C6 will replace the outline with a complete
> rule presentation while preserving the conservative metatheory boundary.
