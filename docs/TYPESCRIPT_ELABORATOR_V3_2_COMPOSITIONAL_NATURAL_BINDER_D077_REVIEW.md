# TypeScript Elaborator v3.2 Expanded Displayed-Natural Binder D-077 Review

Status: approved under the standing unattended-review delegation

Decision: `D-DTTLF-USABILITY-077`

Gate: `H-DTTLF-USABILITY-COMPOSITIONAL-ND-EXPANDED-01`

Reviewed proposal checkpoint:
`f176d08b9aa831b05241ef301475379d78e32939`

## Independent Review

The frozen second-hom slice is the smallest sound continuation of the
checkpointed first-hom architecture.

The active kernel already owns the direct proof-time comparison between
`Hom_cat (Transf_cat K Cat_cat E D) FF GG` and
`Transfd_cat E D FF GG`, the runtime object projection from the latter facade,
the fibre component projection, and the internal base-arrow/higher-cell
action. The proposal therefore correctly adds no cast, curry, Core equality,
checker rule, transfer rule, or Lambdapi owner.

Reusing the existing open `indexed-functor` representation is preferable to
adding a second scoped public descriptor. It is already tied to the active
base ordinal, retains the recoverable closed displayed-functor owner, cannot
compile as a closed functor, and is rejected after its callback scope. The
inner natural abstraction can consequently validate both endpoint owners and
invoke the existing `factorDisplayedTransforPoint` recursion without
manufacturing an open `KernelExpression`.

The proposed private inner wrapper does not assert pointwise naturality. It is
created only after the point body has factored to an existing coherent closed
displayed transformation. The matching outer binder then removes the
remaining base component and retains exactly that Core term while selecting
the ordinary iterated-Hom facade. Compact `:^nd` retains the distinct
`Transfd_cat` facade. This is presentation-specific wrapping around one
internally owned semantic object, not a claim that arbitrary sections of
`Transf_catd` or pointwise arrows are transformations.

Delegating component and higher-action elimination from the expanded wrapper
to the retained displayed owner is also sound. It exposes existing
`tdapp0_fapp0` and `tdapp1_int_cell` behavior and adds no external naturality
payload. The required negative matrix prevents the private wrapper from
becoming a general coercion from open fibre arrows.

The focused eta, identity, composition, both-whisker, scope, and action matrix
is sufficient for this bounded architecture qualification. Arbitrary body
synthesis, every variance/dependency DAG, mixed `Functor_catd`/`Transf_catd`
sections, and text parity remain correctly excluded.

## Decision

Approve exactly `COMPOSITIONAL-ND-EXPANDED-1D` as frozen at the reviewed
checkpoint. Preserve the compact contextual factorer as rollback evidence
until byte-identical Core and action parity are green. Reject a fake open
kernel category/functor, an arbitrary point-arrow escape hatch, a new kernel
owner, or text/browser/scale scope in this tranche.
