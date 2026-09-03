# Bounded Long Exact Homology Owner Audit

Date: 2026-09-03

Plan-ID: `TS-EMDASH-BOUNDED-LONG-EXACT-HOMOLOGY-AND-BOOK`

Baseline: `054b43bd777d260f5da8b1242294ce0335780d0d`

Status: completed audit; kernel-side implementation active

## Scope

This audit records the exact owners and endpoint calculations required before
implementing the six-term snake exact sequence and its bounded-homology
specialization. It is subordinate to
`TYPESCRIPT_EMDASH_BOUNDED_LONG_EXACT_HOMOLOGY_AND_BOOK_PLAN.md` and to the
active kernel/SOP.

## Focused Baseline

The new worktree is clean and bootstrapped from the integrated snake baseline.
Recent predecessor evidence is retained for unchanged warning and TypeScript
boundaries. Fresh focused checks in this worktree give:

- `emdash3_2_abelian_snake_connecting_result.lp`: quiet pass below 90 seconds;
- `emdash3_2_short_exact_sequences.lp`: quiet pass;
- `examples/short_exact_sequences.lp`: quiet pass;
- root TypeScript typecheck: pass; and
- 19 focused bounded-complex, one-degree homology, native snake, and
  categorical-snake tests: pass.

No repository aggregate was run. The inherited health-report exception remains
the unrelated `dependent_simplex_faces` baseline recorded by the completed
snake plan.

## Existing Mathematical Owners

| Concern | Active owner | Available data |
|---|---|---|
| local adjacent-zero pair | `emdash3_2_computational_homology.lp` | incoming/outgoing arrows, zero point, selected kernel, boundary lift, reconstruction |
| local exactness | `emdash3_2_short_exact_sequences.lp` | `ComputationalExactAt`, defined as epicity of the actual boundary lift |
| short exactness | `emdash3_2_short_exact_sequences.lp` | zero pair, incoming monicity, outgoing epicity, local exactness |
| selected images/coimages | `emdash3_2_abelian_images.lp` | comparison and factorization plus cone/cocone annihilation consequences |
| comparison bimorphism | `emdash3_2_abelian_image_bimorphisms.lp` | constructive monic/epic comparison and public one-Abelian-capability wrapper |
| balancedness | `emdash3_2_abelian_bimorphisms.lp` | `IsoEvidence` from explicit monic and epic evidence |
| snake spine | `emdash3_2_abelian_snake_lemma.lp` | `delta`, `beta`, `lambda`, `alpha`, `gamma`, surrounding kernels/cokernels, fiber product, pushout, `p1`, `p2`, `q1`, `q2` |
| connecting arrow | snake normal-test and connecting modules | both derived normal tests, `u`, `partial`, both reconstruction paths, paired factor-space result |
| bounded complexes | native and formal bounded-complex owners | recursive/array spine, adjacent-zero agreements, degreewise homology |
| functorial homology | native and formal functorial-homology owners | chain squares, cycle lift, boundary descent, induced homology map |

## Exact Six-Term Object And Arrow Matrix

Fix the completed triple

```text
A --delta--> B --beta--> X --lambda--> D,
lambda o beta o delta = 0.
```

The completed spine supplies

```text
alpha : A -> Ker(lambda),       mu : Ker(lambda) -> X,
gamma : Coker(delta) -> D,      epsilon : B -> Coker(delta),
mu o alpha = beta o delta,
gamma o epsilon = lambda o beta.
```

Select the remaining structural objects:

```text
k_alpha : Ker(alpha) -> A,
k_beta  : Ker(beta) -> B,
k_gamma : Ker(gamma) -> Coker(delta),
c_alpha : Ker(lambda) -> Coker(alpha),
c_beta  : X -> Coker(beta),
c_gamma : D -> Coker(gamma).
```

The five six-term arrows are owned as follows.

### `Ker(alpha) -> Ker(beta)`

Use the test `delta o k_alpha`. Its composite with `beta` is zero because
`beta o delta = mu o alpha` and `alpha o k_alpha = 0`. Select the factor through
`k_beta` by kernel universality.

### `Ker(beta) -> Ker(gamma)`

Use the test `epsilon o k_beta`. Its composite with `gamma` is zero because
`gamma o epsilon = lambda o beta` and `beta o k_beta = 0`. Select the factor
through `k_gamma` by kernel universality.

### `Ker(gamma) -> Coker(alpha)`

This is the already completed nonsplit connecting arrow. It remains the
central owner; no alternate definition is introduced.

### `Coker(alpha) -> Coker(beta)`

The arrow `c_beta o mu` coannihilates `alpha` because
`mu o alpha = beta o delta` and `c_beta o beta = 0`. Select its colift through
`c_alpha` by cokernel universality.

### `Coker(beta) -> Coker(gamma)`

The arrow `c_gamma o lambda` coannihilates `beta` because
`lambda o beta = gamma o epsilon` and `c_gamma o gamma = 0`. Select its colift
through `c_beta` by cokernel universality.

Every map is therefore a selected point of an existing contractible factor
space. None is a new primitive or manually entered square.

## Adjacent-Zero Proof Matrix

The five zero composites should use these owners.

1. `Ker(alpha) -> Ker(beta) -> Ker(gamma)`:
   compare after monic `k_gamma`; reduce to `epsilon o delta o k_alpha = 0`
   by the two kernel reconstructions and cokernel annihilation of `delta`.
2. `Ker(beta) -> Ker(gamma) -> Coker(alpha)`:
   use the selected factor of the compatible pair into
   `FiberProduct(k_gamma,epsilon)`. The equations
   `u o p1 = q1 o beta o p2` and `q2 o partial = u`, followed by monic `q2`,
   reduce the composite to `beta o k_beta = 0`.
3. `Ker(gamma) -> Coker(alpha) -> Coker(beta)`:
   use the selected cofactor out of `Pushout(mu,c_alpha)`. Precompose by epic
   `p1`; the two final reconstruction paths reduce to
   `c_beta o beta o p2 = 0`.
4. `Coker(alpha) -> Coker(beta) -> Coker(gamma)`:
   compare after epic `c_alpha`; use both cokernel-colift reconstructions and
   `lambda o mu = 0`.

The fifth adjacent pair in the six displayed objects is the same count as the
four composites above: five objects gaps correspond to five arrows, hence four
arrow composites. The plan's earlier phrase “all five adjacent-zero equations
of each snake sequence” is imprecise and must be corrected to four for a
six-object/five-arrow sequence.

## Exactness Positions

Exactness is required at exactly four interior objects:

```text
Ker(beta), Ker(gamma), Coker(alpha), Coker(beta).
```

The expected proof architecture is:

- at `Ker(beta)`, use the canonical exactness of
  `delta -> B -> Coker(delta)`, then the alpha-kernel restriction;
- at `Ker(gamma)`, use the contractible fiber-product factor and the first
  normal-epi factor defining `u`;
- at `Coker(alpha)`, use the pushout cofactor and the final normal-mono factor
  defining `partial`; and
- at `Coker(beta)`, use the canonical exactness of
  `Ker(lambda) -> X -> lambda`, then the gamma-cokernel quotient.

Each exactness proof should produce `ComputationalExactAt` for the actual
adjacent pair. If an intermediate reusable lemma is missing, prefer a generic
kernel/cokernel exactness theorem over a snake-specific witness field.

## Exact-Spine Decision

`FiniteFamily(A,n)` is a homogeneous tuple in one fixed groupoid `A`. A
categorical sequence is dependent: after selecting objects, each arrow lives in
a different `Hom` groupoid determined by adjacent endpoints. Consequently a
plain `FiniteFamily` of arrows is not the correct primary owner.

The formal bounded-complex module already solves the analogous problem with a
recursive dependent Sigma tail that stores each next object, differential, and
adjacent-zero agreement. The exact-sequence owner should follow that precedent
if bounded iteration needs it.

Decision for the first implementation tranche:

- construct the concrete six-term window and its exactness first;
- record the exact projections needed by the one-degree homology consumer; and
- introduce a generic recursive exact spine only when those projections and
  the bounded iteration make its signature concrete.

This is not a decision against reusable exact sequences. It avoids designing a
generic telescope from guessed access patterns.

## Short-Exact Row Normal Form

For an arbitrary short-exact pair

```text
A --i--> B --p--> C,
```

the existing homology boundary is a selected map

```text
b : A -> Ker(p)
```

with `kernel_embedding o b = i`. Exactness says `b` is epic. Incoming monicity
makes `b` monic, hence balancedness constructs

```text
A ~= Ker(p).
```

Dually, cokernel universality constructs

```text
q : Coker(i) -> C
```

with `q o cokernel_projection = p`. Outgoing epicity makes `q` epic; the dual
exactness argument should make it monic, hence

```text
Coker(i) ~= C.
```

These are the required usability comparisons. The selected short-exact row is
the form where the kernel/cokernel endpoints are already the canonical runtime
objects. Arbitrary rows retain the two `IsoEvidence` values; no object path is
postulated.

## Bounded-Complex Substitution

For degree `n` in a degreewise short-exact sequence of complexes, instantiate
the generic triple by

```text
delta  = i_n,
beta   = d^B_n,
lambda = p_(n-1).
```

The upper chain square and degreewise zero/exactness data identify the induced
`gamma` with `d^C_n` through `Coker(i_n) ~= C_n`. The lower chain square
identifies `alpha` with `d^A_n` through `A_(n-1) ~= Ker(p_(n-1))`.

The raw connecting arrow therefore starts on cycles represented in the
canonical quotient row and lands in the quotient by boundaries represented in
the canonical kernel row. It still must:

- annihilate the selected source boundary so it descends to `H_n(C)`; and
- be annihilated by the target differential so it factors into target cycles
  before passage to `H_(n-1)(A)`.

Those are separate selected universal operations, not endpoint casts.

## Module Decomposition Hypothesis

The completed connecting target checks near the bounded limit. New formal work
should therefore begin with small one-way owners:

1. snake kernel-side objects, arrows, and reconstruction paths;
2. snake cokernel-side objects, arrows, and reconstruction paths;
3. four adjacent-zero points;
4. left exactness positions;
5. right exactness positions; and
6. whole six-term result and reviewer.

This split is accepted only when measured checks require it. It must follow
semantic boundaries and must not duplicate bodies or cap retained whole data.

## Book Placement

The integrated book has Chapters 0–30 and no additive/homological chapter.
Chapter 31 is the correct new owner. The old categorical-structures and final-
maintenance book branches are already ancestors of `main` and have no unique
work to merge.

The chapter should be drafted from the checked owner matrix above, then updated
after six-term exactness and the long-exact window become authoritative. It
should not describe the present connecting arrow as the complete snake lemma.

## Next Implementation Action

Start with the kernel-side map module:

- select `Ker(alpha)` and `Ker(beta)`;
- construct `Ker(alpha) -> Ker(beta)`;
- construct `Ker(beta) -> Ker(gamma)`;
- retain both kernel-lift reconstruction paths; and
- add a focused reviewer with exact endpoint assertions.

No rule or unifier is anticipated. If transparent endpoint conversion exceeds
the 90-second target, retain the literal selected-kernel owner shape and split
readable aliases from universal-property paths, following the completed snake
precedent.

## Kernel-Side Probe Result

The proposed owner was implemented in
`emdash3_2_abelian_snake_six_term_kernels.lp`. Both maps are direct selected
kernel lifts and both universal reconstruction paths remain explicit. The
owner and reviewer pass quiet and warning-enabled checks, inherit exactly the
`1,217` critical-pair and `169` replaceable-variable warning boundary, and add
no rule or unifier. Strict LHS audits report zero clauses.

The direct cokernel-side mirror is now implemented in
`emdash3_2_abelian_snake_six_term_cokernels.lp`. Both maps are selected
cokernel colifts with explicit reconstruction paths. Its owner/reviewer pass
quiet and warning-enabled checking at the same inherited `1,217`/`169`
boundary and add no rule or unifier.

The next dependency-ready action is the four adjacent-zero points.

The two outer points are now implemented. Long calculated paths are retained
in kernel/cokernel zero-foundation owners using the literal selected structural
heads. Small downstream modules apply reusable direct zero-cancellation lemmas
for selected kernel embeddings and cokernel projections. Quiet and
warning-enabled checks pass at the inherited `1,217`/`169` boundary; the
modules add no rule or unifier.

The remaining dependency-ready work is the two inner points, which must use
the already-selected fiber-product factor and pushout cofactor rather than a
new diagram interface.
