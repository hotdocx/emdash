# TypeScript Elaborator v3.2 Expanded Displayed-Functor Binder D-076 Review

Status: approved under the standing unattended-review delegation

Decision: `D-DTTLF-USABILITY-076`

Gate: `H-DTTLF-USABILITY-COMPOSITIONAL-FD-EXPANDED-01`

Reviewed proposal checkpoint:
`5929b2962ea6fe3465047556f9992bab4a827971`

## Independent Review

The frozen first-hom slice is the smallest sound bridge from the already
qualified compact displayed-functor abstraction to literal typed
`lambda^n k. lambda^f a` composition.

The active kernel already owns the mathematical comparison between
`Transf_cat K Cat_cat E D` and `Functord_cat E D`, including the runtime object
projection. The proposal therefore correctly adds no cast, curry, checker
equality, Core node, transfer rule, or Lambdapi owner. Its only new
representation is a construction-only descriptor for the open fibre `E[k]`.
That descriptor is callback-scoped, is not a `KernelExpression`, and cannot be
presented to the generic checker as a closed category.

Literal reuse of the current public methods would be unsound because
`CoreCategoricalCategory` denotes a closed kernel expression and the current
root ordinary-natural bracket rejects outer capture. Conversely, retaining
only the combined compact callback would leave the fundamental expanded
telescope unavailable. The selected shared scoped factorer resolves both
problems: it recursively eliminates the base and fibre tokens into an existing
internally coherent displayed-functor owner, after which thin wrappers retain
either the ordinary `Transf_cat` or compact `Functord_cat` facade.

The same-Core probe is decisive evidence for that seam. Existing compact
`:^fd` eta checks unchanged at the expanded `Transf_cat` type, so the bridge is
a frontend factorization/presentation change rather than new LF semantics.
The proposal also preserves the essential fail-closed condition: matching
fibre-shaped endpoints are insufficient unless the joint body is one of the
recursively factorable internally functorial constructions.

Deferring the analogous second-hom bridge is appropriate. It lets the scoped
open-fibre representation, callback discipline, exact Core parity, object
action, and arrow action graduate at the first hom before the same architecture
is reused for `lambda^n k. lambda^n a` and compact `:^nd`.

## Decision

Approve exactly `COMPOSITIONAL-FD-EXPANDED-1C` as frozen at the reviewed
checkpoint. Preserve the existing compact factorer as rollback evidence until
the focused parity matrix is green. Reject a fake open `KernelExpression`, an
arbitrary point-functor escape hatch, a new kernel owner, or second-hom/text
scope in this tranche.
