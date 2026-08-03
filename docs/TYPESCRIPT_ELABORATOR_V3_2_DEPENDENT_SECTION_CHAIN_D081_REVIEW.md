# TypeScript Elaborator v3.2 Dependent Section Chain D-081 Review

Status: approved under the standing unattended-review delegation, with human
supersession preserved

Decision: `D-DTTLF-USABILITY-081`

Gate: `H-DTTLF-USABILITY-DEPENDENT-SECTION-CHAIN-01`

Reviewed proposal checkpoint:
`48394a2005cd8b483ae2de56f070c14d0826d7fd`

## Independent Review

The frozen proposal identifies a surface recursion boundary, not a missing
categorical construction. The current callback already constructs the full
typed contextual tree for

```text
GG[k](FF[k](s[k])).
```

It rejects only when `lowerDependentSectionComposition` insists that the
argument of the outer indexed-functor application be a direct section
evaluation. No parser, application resolver, Core checker, or active kernel
change is needed to represent the nested body.

The proposed fold has the correct semantic ambient category. A section
`s : Pi_cat E` is proof-time comparable to a displayed functor from the
constant terminal family to `E`. A displayed functor `FF : Functord E D`
therefore acts on the whole section by the existing generic
`comp_fapp0 (Catd_cat K) FF s`. Repeating the same operation for
`GG : Functord D Q` produces a section of `Q`. Since every intermediate is a
first-class displayed functor, object components and base-arrow action remain
owned by the active generic composition and section-action calculus; no
pointwise naturality equation is introduced.

Folding inner-to-outer preserves the existing one-layer normal form literally.
For a single `FF[k](s[k])`, the recursive factorer reaches the same closed
`FF`, the same closed `s`, and emits the same six-argument
`dependentCompositionCall`. This is a strong compatibility oracle and avoids
an associativity-dependent reassociation of the chain.

The restriction to one rigid section leaf and rigid closed displayed-functor
heads is mathematically honest. It establishes recursive occurrence of the
bound base variable while excluding variable-dependent functor heads,
transport terms, arbitrary point data, and outer capture that would need a
larger contextual algebra. Exact adjacent-family and common-base checks make
the recursion classifier-directed rather than a syntactic application fold.

Two and three layers are sufficient evidence for the implementation shape:
two closes the concrete checked negative, while three rejects a depth-two
switch masquerading as recursion. The current normalized contextual body and
usage multiset already retain every occurrence of the base token, so the
factorer can validate and erase scope without retaining callbacks or tokens.

The bounded action oracle is appropriate. The public TypeScript surface does
not yet expose general section-arrow elimination, and this gate must not add
it. Nevertheless, applying active `piapp1_fapp0` to the emitted iterated
`comp_fapp0` section in one Lambdapi conformance probe verifies that the result
has not been reduced to an object-only encoding.

Text syntax should remain downstream of semantics. The grammar and neutral
application resolver already construct the same nested application tree, so
automatic inheritance is plausible. The proposal correctly permits only a
parity assertion if that route works unchanged and forbids a parser/resolver
edit if it does not.

The arrow-induction example is correctly deferred. Its kernel semantics are
available, but a public compositional spelling of `E[rho(q)](u)` needs several
Sigma/transport/action routes. Folding those into this chain gate would make
the apparent one-constructor change misleading and harder to reject.

The validation boundary is proportional. Focused dependent-composition and
displayed-chain suites plus static checks are the implementation loop. Because
the shared categorical surface changes, root repository guidance still
requires one final `check:ts`; the proposal confines it to one run after all
bounded gates are green and explicitly forbids reassurance reruns.

## Decision

Approve exactly `DEPENDENT-SECTION-CHAIN-1AR` as frozen at proposal checkpoint
`48394a2005cd8b483ae2de56f070c14d0826d7fd`. Recursively recognize one rigid
closed section evaluation under an arbitrary finite nonempty chain of rigid
closed displayed-functor fibre applications at the same contextual base;
fold inner-to-outer only with existing `comp_fapp0 (Catd_cat K)`; preserve the
one-layer Core and existing evidence rule; prove two/three-layer behavior,
strict negatives, component computation, and internally owned section action;
and add no kernel/Core/transfer/parser/browser/book or public section-action
surface.
