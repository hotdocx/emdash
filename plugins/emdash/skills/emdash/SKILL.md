---
name: emdash
description: Work on algebra goals with exact polynomial computations, reusable native/internal module constructions and source-derived views using Emdash.
---

# Emdash algebra goal assistant

Help the user compute, explore and reuse mathematics. Carry routine source,
domain and artifact bookkeeping yourself. Computation and visualization do
not require a proof goal or an adopted assumption.

## Use the user's mathematical workspace

The `emdash-local` MCP tools operate on an explicit absolute `root`. Use the
user's selected working directory, not the plugin's installed cache directory.
Inspect existing `emdash.goal.json` source with `emdash_inspect` before changing
it. If there is no workspace, initialize the user's requested mathematical
input with `emdash_initialize`. Its default example is for a requested demo;
do not substitute that example for a different problem.

The current computational profile is rational polynomials with 1–4 ordered
variables, up to eight generators and a membership query. Coefficients and
exponents use exact strings (`"1/2"`, `"3"`), not floating-point numbers.
`emdash_compute` returns the actual retained coefficient combination and
remainder. `emdash_render` derives approximate SVG/HTML curve views for a
two-variable input. Link the resulting files when useful and explain relevant
approximation limits without turning the task into certification work.

To change the input, pass the current inspected `sourceRevision` as
`expectedRevision` to `emdash_update`, with the complete mathematical source.
The assistant supplies this revision; do not ask the user to copy hashes.
Reinspect after a stale-source or busy result. The ordinary source file can
also be edited with the host's normal file tools; old artifacts then become
stale. Notes and other user files remain independently editable.

## Reuse a retained relation

After a positive computation, `emdash_construct` builds a whole two-step free
complex from the retained coefficient vector and applies its upper map to one.
Its default `mode: "native"` works over the supported rational polynomial ring
and adopts no equation. It does not assert that the relation generates the whole
kernel or that the complex is exact or a resolution.

For a task that calls for internal construction through the computed-equation
route, select `mode: "internal"` and supply an explicit `adoptionReason`. The
runtime assembles a transparent typed Core complex from the actual matrices and
one recorded computed-equation assumption, then consumes its projected
differential in another typed action. State that assumption status in the
mathematical result. This does not satisfy a separately requested checked-proof
requirement, and standalone TypeScript reduction of the complex projections is
not newly qualified by it.

Keep the two actions distinct: `nativeImageOfOne` is the native image of the
unit vector, whereas `goal_reuse_image` applies the internal differential to a
supplied symbolic rank-one vector `a`. For the default column `(-x, 1, -1)`,
the mathematical action is `a ↦ (-x*a, a, -a)`; its value at `1` is the column.
Do not report the column as the value on an arbitrary formal argument, or claim
the internal Core expression was reduced to those coordinates.

The current internal interpretation supports integer polynomials in a supplied
commutative ring. Native rational computation/construction remains useful when
that interpretation rejects a coefficient. Do not silently clear denominators,
replace the input, or recompute a different witness to make internalization pass.

## Portable command and TypeScript authoring

The MCP tools and CLI use the same operation catalog. If the MCP connection is
unavailable, the installed runtime is usable directly. The plugin root is two
directories above this skill's directory. Resolve that actual location; do
not assume a contributor checkout or an unversioned npm command exists.

```text
node <plugin-root>/dist/emdash-agent.cjs capabilities
node <plugin-root>/dist/emdash-agent.cjs inspect --root <absolute-workspace>
node <plugin-root>/dist/emdash-agent.cjs compute --root <absolute-workspace>
node <plugin-root>/dist/emdash-agent.cjs render --root <absolute-workspace>
node <plugin-root>/dist/emdash-agent.cjs construct --root <absolute-workspace>
```

`capabilities` returns the exact source schema, example, operation names and
bounds. For mathematical authoring through ordinary TypeScript expressions,
the adjacent `dist/authoring.cjs` exports the existing polynomial builders,
`createAlgebraGoalSource` and `serializeAlgebraGoalSource`, with declarations.
Run such an authored producer explicitly through the normal authorized host,
then update the inert workspace data. Inspection and MCP requests do not load
user modules. Read the plugin's README for source/artifact details when needed.

Report useful mathematical results and next constructions. Distinguish native
exact computation, approximate views and any optional formal evidence. Do not
describe the native engine as Singular or a computed result as a checked Core
proof. Unsupported domains or interpretations need a stated mathematical
choice, not a silent replacement of the requested problem.
