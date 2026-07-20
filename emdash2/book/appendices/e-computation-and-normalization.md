<a id="appendix-computation"></a>

# Appendix E. Computation And Normalization

The prose uses equations freely, but the implementation distinguishes three
ways expressions can agree. That distinction is essential whenever a theorem
depends on a particular normal form.

## E.1 Three Forms Of Agreement

**Runtime reduction** selects a computational direction. A rewrite

```text
left  ↪  right
```

makes `right` the intended normal form when the left pattern is
observed. Constructor beta rules, functor projection rules, and selected
cut-elimination rules live here.

**Proof-time comparison** helps elaboration recognize two typed expressions
without making either one compute to the other. Emdash uses narrow
`unif_rule` declarations for this purpose. A typed reflexivity proof is
the relevant diagnostic; mere conversion testing does not exercise the same
interface.

**Internal equality** is mathematical data in a classifier
`x=y`. It can be transported, acted on, inverted, or used in an
equivalence proof. A propositional theorem may compare two stable runtime
presentations without changing either presentation's reduction behavior.

The book's symbol `=` normally denotes internal equality or an ordinary
mathematical equality justified by a formal-status note. It never implies that
the source expressions are definitionally identical.

## E.2 Semantic Owners

A computational operation should have one owner. Generic functoriality is
owned by the `fapp*` calculus; generic naturality by `tapp*`;
displayed hom action by `fdapp*` and `tdapp*`; Sigma and Pi expose
their own structural projections. Readable aliases route through these owners
instead of copying their semantic bodies.

This prevents two kinds of drift:

- competing rewrites can no longer silently choose incompatible normal forms;
- a theorem at the next hom level retains the functor or transfor object it
  needs for further iteration.

The WalkingEnd development illustrates the policy. The contextual eliminator
owns the constructor-specific base and generator observations. It does not
restate generic preservation of identity or composition. The decoder's
normalization cell is the displayed hom-action of one constructed functor; it
is not a custom recursion rule for every arbitrary based arrow.

## E.3 Direction And Variance In Normal Forms

Covariant postcomposition and contravariant precomposition have different
runtime owners. Their mathematical comparison through opposites is available
at proof time, but forcing both into one rewrite direction would erase the
variance used by `PathOut` and profunctor action.

Similarly, an identity may appear as an ambient categorical identity, a
functor identity, a displayed identity, or a specialized projection. These
forms are joined only where a typed consumer requires it. Broad eta-style
rewrites are avoided because unification is experimental and because a
functor-level normal form may be needed to act on the next cell.

## E.4 How A Checked Prose Claim Is Reviewed

For a code-facing claim, the review path is:

1. identify the mathematical interface and its direction;
2. locate the active owner declaration with lexical or type-aware search;
3. identify an independent regression or reviewer example;
4. decide whether the observation is runtime, proof-time, or propositional;
5. add or update the evidence-register entry;
6. cite the evidence identifier beside the prose claim;
7. run the evidence, assembly, source, and browser-render checks.

Changes to rewrite or unification behavior require the stronger repository
workflow: an owner-position probe, bounded typecheck, warning comparison when
relevant, focused assertions, and full CI before handoff. Book prose does not
authorize changing kernel normal forms merely to make an explanation shorter.

## E.5 What Has Not Been Proved Metatheoretically

The passing executable checks establish the selected interfaces and
regression observations. They do not by themselves prove global confluence,
strong normalization, canonicity, consistency of every future extension, or
soundness with respect to a complete weak omega-categorical model.

Those are research-level metatheorems. A future semantics chapter should state
its fragment, model, and computation theorem explicitly. Until then, the book
uses “computes” locally for named checked reductions and uses a formal-status
note for every stronger reading.

The current development SOP remains the operational authority for rule design
and validation. This appendix explains the mathematical reading needed by a
book reader; it is not a replacement for that SOP.
