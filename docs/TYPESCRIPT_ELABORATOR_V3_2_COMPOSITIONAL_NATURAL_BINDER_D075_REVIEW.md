# TypeScript Elaborator v3.2 Compositional Natural Action D-075 Review

Status: approved under the standing unattended-review delegation

Decision: `D-DTTLF-USABILITY-075`

Gate: `H-DTTLF-USABILITY-COMPOSITIONAL-NATURAL-ACTION-CORRECTION-01`

Reviewed proposal checkpoint:
`de900588d9961f3bb73d56ef7b1f535459c89015`

## Independent Review

The frozen correction is necessary and narrower than either apparent
alternative.

The generic action attempted under D-074 is mathematically valid in the active
Lambdapi kernel, but its TypeScript prerequisite `comp_cat_con_func` is an
opaque signature. Consequently the TypeScript checker cannot expose the
transparent-definition computation needed to align its retained `fapp0`
endpoints with canonical `comp_cat_fapp0` endpoints. Adding local endpoint
casts or hard-coded classifier equality would violate the internalization SOP;
importing transparent definitions would reopen the separately deferred
declaration-refinement architecture.

The active kernel already owns the exact required constructions:

- `comp_cat_con_fapp1_func` maps an ordinary transformation under fixed
  precomposition; and
- `comp_cat_cov_fapp1_func` maps an ordinary transformation under fixed
  postcomposition.

Their declared target categories state canonical `Transf_cat` endpoints
directly. Importing their signatures therefore preserves the active semantic
owner, lets the generic LF checker verify the result, and needs no runtime
rule, external naturality evidence, new Core node, or new kernel symbol.

## Decision

Approve the exact `COMPOSITIONAL-NATURAL-ACTION-CORRECTION-1B2` proposal.
Reject broader transparent-definition import, checker-specific coercion, and
new whiskering owners in this tranche. Preserve all already-passing D-074
branches and the compact `:^nd` factorer unchanged.
