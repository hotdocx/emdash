# TypeScript Elaborator v3.2 Compositional Text Parity D-078 Review

Status: approved under the standing unattended-review delegation, with human
supersession preserved

Decision: `D-DTTLF-USABILITY-078`

Gate: `H-DTTLF-USABILITY-COMPOSITIONAL-TEXT-PARITY-01`

Reviewed proposal checkpoint:
`19ec1adb1bd2ee3288338e7069759549c1f282a8`

## Independent Review

The frozen text slice is a bounded adapter continuation of the checkpointed
typed architecture, not a new elaborator layer.

The located grammar already records arbitrary alphabetic binder-mode suffixes,
single and grouped bindings, optional identifier annotations, and recursively
nested lambda nodes. The current failure of expanded
`lambda^n k. lambda^f a` and `lambda^n k. lambda^n a` therefore occurs at the
intentional expected-classifier boundary: root `^n` currently selects only a
dependent section, while nested lambdas without a supplied recursive contract
fail closed. Adding another parser, raw AST, or application heuristic would be
unnecessary and would duplicate existing authority.

Expected-classifier dispatch is the correct disambiguator. The outer `^n`
surface mode denotes natural variation in all three cases, while the expected
classifier distinguishes a dependent section, the first displayed hom
`Transf_cat K Cat_cat E D`, and the second iterated hom between displayed
functors. Two explicit expected contracts keep this distinction bidirectional
and prevent the text adapter from guessing classifiers from spelling alone.

Both proposed resolver routes call the public typed API literally. The first
constructs callback-scoped `E[k]` and `D[k]` categories and consequently
reaches the existing `contextualDisplayedFunctorLambda` plus
`factorDisplayedFunctorBody` path. The second applies `FF` and `GG` at the
active base and reaches the existing contextual natural point factorer. Thus
the resolver neither recreates body factorization nor accepts an external
naturality or functoriality payload. Exact Core and action ownership remain
properties of the typed methods already checkpointed under D-076 and D-077.

The proposal correctly retains the architectural non-uniformity discovered
after D-077: fixed-category `categoricalLambda` and indexed open-fibre
`lambda^f` do not yet share one universal top-level body compiler. Text parity
routes to the implemented classifier-specific method and does not hide that
boundary behind a cast or synthetic category.

Optional annotation checking reuses the existing category and displayed-family
comparison helpers. The final body continues through the neutral recursive
resolver, whose application, identity, composition, and mapper heads already
serve compact `^fd` and `^nd`. The negative matrix is sufficient to keep mode,
nesting, expected-classifier, endpoint, profile, scope, and coherent-body
boundaries fail-closed.

Advancing the public text revision and synchronizing every exact revision pin
is required because the accepted mathematical surface changes. That mechanical
update does not authorize browser presets, reviewer examples, documentation
copy, or public deployment.

## Decision

Approve exactly `COMPOSITIONAL-NATURAL-TEXT-PARITY-1D` as frozen at the
reviewed checkpoint. Add only the two expected contracts, two thin resolver
routes, focused tests, runner registration, and mechanical text-revision pin
updates. Preserve all compact and ordinary routes. Reject a second parser,
new Core/checker/kernel semantics, inferred coherence, a universal-bracket
claim, browser/reviewer scope, or scale work in this tranche.
