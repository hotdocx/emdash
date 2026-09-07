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

The two inner points are now implemented from exactly those selected universal
owners. On the kernel side, the compatible pair
`(Ker(beta) -> Ker(gamma), k_beta)` selects a fiber-product lift and retains
both projection paths. The `u` reconstruction and `beta o k_beta = 0` make
`u` vanish on this lift; the connecting reconstruction and monic `q2`
cancellation prove
`partial o (Ker(beta) -> Ker(gamma)) = 0`. On the cokernel side, the compatible
copair `(c_beta, Coker(alpha) -> Coker(beta))` selects a pushout cofactor and
retains both injection paths. Its first reconstruction and
`c_beta o beta = 0` kill the middle arrow; its second reconstruction, the two
connecting paths, and epic `p1` cancellation prove
`(Coker(alpha) -> Coker(beta)) o partial = 0`.

The former two-map kernel and cokernel sources were split, without changing
any symbol body, into narrow one-map foundations plus their existing public
surfaces. Readable selected fiber/pushout object projections moved unchanged
to the snake spine that owns those constructions. These owner corrections
remove unrelated endpoint proofs from inner consumers and avoid duplicate
semantic aliases.

All new mathematics is rule-free and has zero LHS-audit findings. Source-only
checks of the two dependency branches are green and warning-enabled checks
retain exactly `1,217` critical-pair plus `169` replaceable-variable reports.
Loading both already-green branches in one fresh Lambdapi process crosses the
uniform 90-second ceiling before the new root declaration is reached. The
focused `scripts/check_abelian_snake_six_term.sh` therefore copies the exact
current sources to a disposable directory, freshly compiles each dependency
branch under its own 90-second bound, and checks both final equations and the
reviewers against those exact objects. The temporary objects are then removed.
This is bounded compilation evidence, not opacity or a weakened theorem.

The whole six-object/five-arrow result is now implemented. It stores the
existing whole connecting-factor result, the other four selected arrows, and
the four adjacent-zero paths in one dependent Sigma snapshot. Nine readable
projections expose the five arrows and four paths; the reviewer checks that
the canonical instance reduces definitionally to every pre-existing named
owner.

A maximally expanded alternative attempted to store the four surrounding
`KernelFactorSpace`/`CokernelFactorSpace` types again inside the snapshot. Its
kernel-side package exceeded 90 seconds even after exact dependency priming.
That duplication was rejected: all four universal points and reconstruction
paths already remain named at their owning map modules, while the result
retains exactly the data needed by indexed exactness consumers.

The next dependency-ready action is exactness at the four interior positions.

## Exactness-Cover Criterion And First Position

The active `ComputationalExactAt` owner remains epicity of the actual selected
boundary into the selected kernel. A rule-free equivalent interface is now
implemented: for every annihilated cone `h:S -> B`, a
`ComputationalExactCoverWitness` retains an object `S'`, an epic map
`S' -> S`, a factor `S' -> A`, and the reconstruction after the cover.
Applying this family to the selected kernel makes the boundary epic.
Conversely, pulling the selected factor of `h` back along an epic boundary
constructs such a cover. No image/kernel object path or element language is
used.

Both canonical rows required by the snake proof are available. The selected
boundary for `Ker(f) -> A -> B` agrees with the identity. For
`A -> B -> Coker(f)`, `chi_f o p_f` is an epic point of the contractible
factor fibre defining `Im(f)`; the generic epic-factor-point theorem transports
that property to the actual selected boundary. The core cokernel proof keeps
one explicit pre-Abelian package and normal-mono/normal-epi capabilities,
following the measured image-bimorphism pattern. Direct bundled wrappers were
discarded after repeated endpoint-conversion timeouts.

Exactness at `Ker(beta)` is complete. Given a cone `psi` killed by
`Ker(beta) -> Ker(gamma)`, composing with `k_beta` gives a cone for the
canonical row `delta -> B -> Coker(delta)`. Its exactness cover supplies an
epic `S' -> S` and `a:S' -> A` with `delta a = k_beta psi e`. The alpha
reconstruction and `beta k_beta = 0` make `mu alpha a = 0`; monicity of `mu`
gives `alpha a = 0`, so `a` factors through `Ker(alpha)`. Monicity of
`k_beta` then proves that the first snake arrow after this factor is
`psi e`. These witnesses form the exact-cover family, and the generic theorem
returns `ComputationalExactAt` for the actual selected boundary.

The exact-source isolated gate is green through this first position. The new
modules add no rule or unifier, strict LHS audits are empty, and the
warning-enabled exactness foundation inherits the unchanged `1,217/169`
boundary. The next action is the analogous but longer cover construction at
`Ker(gamma)` using epic `p1`, the normal-epi factor `u`, and the connecting
reconstruction.

Exactness at `Ker(gamma)` is now complete. For a test `psi` killed by the
connecting arrow, a selected pullback along epic `p1` gives the first cover
and a map into the snake fiber product. The existing `beta o p2` lift defines
`xi` into `Ker(lambda)`. Pushout compatibility and the two final connecting
reconstructions show `q2 pi xi = 0`; monic `q2` gives `pi xi = 0`. Canonical
cokernel-row covers then provide a second epic cover and an `alpha`-preimage.

On the double cover, `beta` gives the same value on the covered `p2` leg and
the corresponding `delta` preimage. Their additive difference therefore has
a selected factor through `Ker(beta)`. Applying `epsilon` removes the delta
summand and uses fiber compatibility to recover `iota psi` after the composite
cover. Monic `iota` yields the required factorization through
`Ker(beta) -> Ker(gamma)`. Composition preserves epicity, so these data form a
`ComputationalExactCoverWitness`; the generic criterion returns exactness of
the actual selected boundary.

The cover carrier exposed a concrete usability omission, now corrected by
`computational_exact_cover_intro`; consumers no longer re-elaborate its nested
Sigma body. The canonical alpha-cover observations are split into foundation,
object, epimorphism, epicity, and factor/reconstruction targets because the
combined projection surface crossed 90 seconds. The exact-source isolated
gate is green through the second exactness reviewer. All new files remain
rule-free, and the warning-enabled generic difference helper inherits the
unchanged `1,217/169` warning boundary.

The next action is the dual exactness construction at `Coker(alpha)`.

## Monomorphic Extensions And Third Position

The dual local-extension criterion is now implemented. For a coannihilated
test `psi:B -> T` in a zero pair `A -> B -> D`, the witness retains an object
`U`, a monomorphism `m:T -> U`, a factor `y:D -> U`, and `m psi = y d`.
The constructor and projections reuse dependent Sigma. A family of extensions
implies the active exactness notion: push the actual boundary cokernel out
along the selected cycle embedding, apply the family to the first injection,
and cancel the resulting two monomorphisms. The boundary cokernel is zero,
so the boundary is epic. This supplies the needed direction without changing
`ComputationalExactAt`; a general converse has not been added.

For `Ker(f) -> A -> B`, a test descends to `Coim(f)`. The canonical map from
that coimage into `B` is monic by the existing comparison theorem; its pushout
along the descended test supplies the monomorphic extension. One explicit
pre-Abelian package and the two normality capabilities remain visible in this
generic construction.

The third snake chase now constructs exactness at `Coker(alpha)`. Given
`psi partial = 0`, pushing out `q2` gives `s q2 = m psi` with `m` monic.
The colift of `q1 beta` along `epsilon`, postcomposed with `s`, is `zeta`.
The connecting reconstruction and epic `p1` give `zeta iota = 0`.
Canonical kernel-row extension through `gamma` supplies `n zeta = y gamma`
with `n` monic. Thus `n s q1 - y lambda` kills `beta` and has a selected
cokernel colift `wbar`. Its reconstruction after `mu` and epic cancellation
of `pi` give `wbar c34 = n m psi`. The composite `n m` is monic, so the
generic extension criterion produces the actual exactness witness.

All stage probes and the reviewer pass. A combined comparison/cancellation
file crossed the 90-second bound; separating those two mathematical steps
made the comparison check in about 59 seconds. The direct generic-cokernel
epicity application also crossed the bound. A named transparent theorem
`abelian_snake_third_pi_epic`, with readable source/target and `pi` endpoints,
checks separately in about 65 seconds and lets the final cancellation check
in about two seconds. This is proof declaration granularity and endpoint
discipline; it introduces no opacity, axiom, rule, or unifier.

Integrated exact-source validation passed through the registered third
position and its reviewer, with the unchanged `1,217/169` warning inventory.
The strict audits, focused health-dispatch tests, catalog, TOC, report/link
hygiene, and staged whitespace checks also pass. The fourth position, at
`Coker(beta)`, has seven successful stage probes and a successful reviewer;
promotion and whole exact-result packaging are the next actions. In that
whole result, each exactness witness must refer to the actual projected
arrows and zero points of the stored snapshot, rather than to unrelated
fixed canonical maps.

## Fourth Position And Exact-Result Packaging Boundary

The seven fourth-position stages are promoted. If `psi:Coker(beta) -> T`
kills `c34`, the c34 reconstruction makes `psi c_beta` a test annihilating
`mu`. Canonical kernel-row extension through `lambda` provides monic `m`
and `y:D -> U` with `m psi c_beta = y lambda`. Precomposing `y gamma` with
epic `epsilon` and using the gamma reconstruction reduces it to
`m psi c_beta beta = 0`. Cokernel universality descends `y` through
`Coker(gamma)`. The c45 reconstruction and epic cancellation of `c_beta`
then produce the exact extension of `psi`; the generic criterion proves
`ComputationalExactAt` at `Coker(beta)`.

Unlike the third-position chain, this complete reviewer checks in one
fresh-source invocation within the ordinary 90-second limit. Its seven source
modules therefore use ordinary checker/health registration, and its reviewer
uses the ordinary example route. The direct proof does not need a new
validation group or a repeated run of the earlier multi-branch gate.

The next owner is `AbelianSnakeSixTermExactData(result)`, dependent on the
actual stored result. Each of its four chain pairs must be constructed from
that result's adjacent arrows and zero projection; its homology must use the
existing `computational_homology_at` on that pair. The canonical snapshot's
projection reductions should then let the four individual proofs inhabit
that data. The eventual whole exact result is the dependent Sigma of the
existing snapshot and these witnesses, not an independent product with
unrelated canonical exactness. This is the implemented package described next.

## Dependent Whole Exact Result

`AbelianSnakeSixTermExactResult` now retains the existing snapshot and its
four exactness witnesses in one dependent Sigma. Each pair function uses the
snapshot's actual adjacent arrow projections and its zero-path projection.
`AbelianSnakeSixTermExactData` applies the existing selected-homology
exactness classifier to those four pairs. The generic constructor and
projections are transparent; a negative typed consumer rejects exactness data
belonging to a different arbitrary snapshot.

The canonical instance uses the same five arrows and four zero points as
before. Four direct conversion checks confirm that its reconstructed pairs
are the existing pairs. A direct assignment of the old proofs to the expanded
new predicate timed out, including an isolated first-position assignment.
This is a checking-context limitation, not evidence that the pair identity or
the theorem is unavailable.

The accepted adapter compares at the pair owner. Each canonical identity has
an `eq_refl` witness, and `computational_exactness_reindex` uses ordinary
equality elimination on `computational_exact_at_selected`. Its reflexivity
beta test passes. The four canonical exactness instances then check promptly,
as does the dependent whole constructor. There is no new axiom, runtime rule,
unifier, kernel/cokernel object equality, or second homology construction.

The maintained canonical reviewer compares each proof projection with its
declared canonical instance. A direct comparison against the old, differently
presented bare proof type exceeded the bound; that diagnostic is not used as
the ordinary reviewer. The separate pair-conversion/reflexivity checks and
generic reindexing beta test preserve the explanation of how the old proofs
are reused. Twenty-seven focused assertions cover the pair projections, both
whole beta projections, two negative dependency/noncollapse guards, the
canonical pair/snapshot/proof observations, and reindexing beta.

The dependency sources were compiled in a fresh disposable copy in separate
bounded invocations. All promoted source and reviewer names checked against
those exact dependencies, and the generic reindexing reviewer also passed
from source with warnings enabled. The next required owner is selected
short-exact-row normalization and its canonical comparison with an arbitrary
`ComputationalShortExactTriple`.

## Short-Exact Comparison Continuation

For `A --i--> B --p--> D`, let `e:A -> Ker(p)` be the existing selected
boundary. Its epicity is the supplied exactness witness; `k e = i` and
monicity of `i` make `e` monic. Existing constructive balancedness should
therefore provide the required kernel comparison isomorphism.

For the other endpoint, cokernel universality gives `q:Coker(i) -> D` with
`q c_i = p`. The equation `(c_i k)e = c_i i = 0` and epicity of `e` give
`c_i k = 0`. Thus `c_i` is a normal-epi test for `p`, whose selected colift
`r:D -> Coker(i)` satisfies `r p = c_i`. Cancelling epic `p` and epic `c_i`
in these two reconstructions gives the inverse laws for `q` and `r`. No
section `D -> B` or object equality is involved.

A suitable fully selected normal row is `Im(i) -> B -> Coker(i)`, with
`Im(i) = Ker(Coker(i))`. Its short exactness follows from the canonical
kernel row and epicity of the selected cokernel projection. The source
comparison with `A` can use the kernel factor of `i` and the normal-mono
lift of the image embedding along `i`, with monic cancellation giving the
inverse laws. These are the next owner-position probes, not completed claims.

## Short-Exact Endpoint Comparison Result

The kernel and cokernel endpoint comparisons are implemented. For the kernel,
the existing boundary `e:A -> Ker(p)` is epic by the supplied exactness and
monic because `k e = i` with `i` monic. Constructive balancedness returns its
isomorphism evidence. For the cokernel, the selected colift
`q:Coker(i) -> D` has `q c_i = p`; the normal-epi test `c_i k = 0` is
derived by cancelling epic `e`. The selected inverse colift has `r p = c_i`,
and cancellation through `c_i` and `p` proves the two inverse equations.

The supporting constructor and cancellation modules remain generic and
rule-free. The seven reviewer assertions check the selected forward/inverse
arrows and their actual reconstruction equations, including a negative type
guard against treating `r` as a section into `B`. Quiet and warning-enabled
source checks pass, retaining `1,217` critical-pair and `169`
replaceable-variable reports. The additional unsolved-equation diagnostic
comes from that successful `assertnot` and is expected.

The selected image row and the PA-explicit monomorphism-to-image isomorphism
have successful probes. The generic whole normalization carrier uses two
existing `HFiber` classifiers over the isomorphism forward-arrow maps, indexed
by the actual normalized row. Its projections and canonical isomorphism
observations check. Combining the canonical compatibility into those fibres
still exceeds the bound in the current direct application; this is the
remaining row-5C experiment, not an endpoint-comparison limitation or a reason
to introduce object equality assumptions.

## Whole Short-Exact Normalization Result

Row 5C is now implemented. `ComputationalShortExactRow` retains one actual
chain pair and its short-exact evidence. The generic kernel-row constructor
takes the existing whole kernel as a parameter, obtains exactness through
identity covers, and continues to use the PA-selected homology. The selected
image-row constructor passes the existing image kernel to that constructor;
it needs only the pre-Abelian capability.

The successful endpoint presentation is the literal `computational_kernel_object`
of that whole image kernel, with one common preadditive projection expression.
The PA-explicit monic-image comparison uses that same presentation. Returning
the alternative readable image-object alias at the application boundary had
exceeded 90 seconds. These changes concern owner/endpoint presentation, not
the selected objects or the mathematics.

The comparison classifiers are generic `HFiber`s of composition with actual
row maps. A generic monomorphism-to-selected-row comparison constructs the
source point before specialization to the original short exact row. This
avoids the measured timeout from rebuilding the composite compatibility in
the fully specialized context. The target point reuses the selected cokernel
comparison. The resulting normalization is a dependent whole row plus those
two points, and its projections retain both actual isomorphisms and fibre
paths. No object equality, new axiom, runtime rule, or unifier is introduced.

The 21 new assertions cover generic row construction, its wrong-pair guard,
selected-row maps/evidence, both image-isomorphism factors/reconstructions,
generic comparison-point beta, whole normalization projections, and the
wrong-row compatibility guard. Canonical fibre paths are checked at their
stored-point interface; their original reconstruction is checked separately
at the generic comparison constructor because the specialized bare-path
comparison exceeded the bound.

The public normalization-only gate passes, including the existing endpoint
reviewer. It freshly compiles only the normalization dependency chain in a
disposable source copy, with every target bounded to 90 seconds. The root
checker, reviewer runner, and health dispatcher route this group separately
from the snake gate. The next implementation row is the degreewise bounded
short-exact sequence and the homology-window endpoint bridge.

## Native Degreewise Short-Exact Sequence

`algebra_polynomial_freyd_bounded_short_exact.ts` now packages three existing
bounded complexes, their existing inclusion/projection chain maps, computed
whole short-exact triples in every degree, and one retained zero row. The
constructor keeps input map and square-agreement references. It accepts equal
reconstructed presentations/differentials, but rejects a different raw
differential even when it induces the same quotient map: reusing the supplied
square at that different raw endpoint would require a separate comparison.

Strict lookup checks the declared support; explicitly extended lookup reuses
the stored zero row without rerunning short-exact computation. The companion
serializer retains all selected algebraic data, raw relation/agreement
witnesses, both chain-map endpoints, and bounded-free provenance. Derived
Gröbner caches remain implementation data, as in the existing serializers.

The main fixture is the nonsplit row `R → R → R/(x)` in degrees zero and one,
with inclusion multiplication by `x`, sub/middle differentials `x`, and zero
quotient differential. Substitution into the existing snake construction
already gives a nonzero connecting arrow. This is not yet the descended
homology-window arrow: comparisons, cycle factorization, and boundary descent
remain row 7. Twelve new tests and eleven immediate regressions pass, along
with root typecheck and affected-file lint. No new formal capability, runtime
rule, unifier, or public-barrel integration is claimed by this checkpoint.

The formal audit finds an existing recursive `CommRingFreydChainTail` and a
bounded-free chain-map precedent, but no bounded Freyd chain-map iterator.
The one-degree `CommRingFreydHomologyChainMap` already owns the two raw square
agreements. Row 6B must iterate that same agreement notion at actual bounded
spine projections and retain explicit witnessed exactness, without promoting
native decisions to a closed formal Abelian category.

## Formal Bounded Chain-Map Iterator

`emdash3_2_commutative_algebra_freyd_bounded_chain_maps.lp` fills that audited
gap. `CommRingFreydChainMapTail` follows both actual bounded complex tails,
selects the next raw component, retains the ordinary presentation-morphism
agreement, and recurses at the projected endpoints. The whole map stores its
first components, first law, and tail; in length zero it is simply an ordinary
raw presentation morphism. Constructors and projections are transparent.

`CommRingFreydChainMapSquare` is an alias for the same agreement used by the
existing one-degree functorial-homology owner. It introduces no new square
datatype. `comm_ring_freyd_chain_map_first_homology` directly pairs two stored
agreements as `CommRingFreydHomologyChainMap`; both existing law projections
compute to the original inputs. Thus the first consumer exercises real owner
computation, not only acceptance of declarations.

Twelve reviewer assertions pass in quiet and warning-enabled fresh-source
checks, including nil/cons, whole components/tail, both homology laws, and a
wrong-target negative. The inherited `1,223/169` warning inventory matches
the old bounded Freyd reviewer exactly. It is not the different generic
normalization closure's `1,217/169`. No rule clauses, new axioms, opaque
bridges, or quotient decoders were added. The next formal operation must
retain short-exact evidence on the actual inclusion/projection components;
the native ability to compute it is not itself a formal closed capability.

## Formal Degreewise Exact-Row Interface

The formal row and bounded-row iterator are now implemented. A
`CommRingFreydShortExactRow` stores the existing adjacent-zero agreement and
whole witnessed homology, then the incoming mono, outgoing epi, and
exactness witnesses. Crucially its exactness is indexed by that actual
stored homology boundary. Its five projections compute to the supplied data;
a negative consumer rejects reusing its exactness for another homology.

`CommRingFreydShortExactTail` follows the three actual complex tails and two
actual chain-map tails. Each row is typed at their next projected components,
and recursion uses their existing rest projections. The bounded predicate
retains the first two rows and that tail (only the first row at length zero).
The whole `CommRingFreydBoundedShortExactSequence` is a dependent package of
both chain maps and evidence on their actual components. A negative consumer
rejects rows for another map; no commuting squares are duplicated.

All seventeen row/iterator assertions pass from source with and without
warnings. The inherited Freyd inventory remains `1,223/169`; all four strict
audits find zero rule clauses. This completes the finite-support formal
interface, not a closed formal short-exact decision or the proof-CAS replay.
Native zero extension retains its one computed zero row; formal endpoint
consumers must carry the corresponding effective witnesses explicitly.
The next architecture gate is the actual homology window and its comparison,
cycle-factor, and source-boundary-descent constructions.

## Native Homology Window And Remaining Generic Owners

`algebra_polynomial_freyd_homology_window.ts` now constructs the actual
five-term window and all three native exactness results. Its source and
target remain the existing selected homology objects. Four comparison
isomorphisms retain actual forward/inverse maps and both inverse agreements:
`Coker(i_n) ⇄ C_n`, `A_(n-1) ⇄ Ker(p_(n-1))`,
`Z_n(C) ⇄ Ker(gamma)`, and `Coker(alpha) ⇄ Coker(d^A_n)`.
The alpha/gamma agreements identify the compared differentials with the
actual complex differentials.

The canonical target-cycle embedding induces
`H_(n-1)(A) → Coker(d^A_n)` by the existing homology cokernel's universal
property. The native normality operations compute its monicity witness and
factor the compared snake arrow through it. The actual source homology
cokernel then descends the resulting map. Both selected factors retain their
tests and reconstructions. This requires no global raw lift into target
cycles, which would be too strong in a nonsplit setting.

Outside-support complex terms reuse the sequence's zero presentation, but
the homology pair retains the true neighboring differential (for example
`0 → C_top`). Replacing that pair by the cached all-zero row would give the
wrong component endpoints for an induced map. The selected outside homology
retains its checked identity-equals-zero agreement instead.

The eight tests include the nonsplit two-degree example, a rank-`1,2,1`
three-degree example with a genuinely nonzero source boundary, all inverse
and reconstruction checks, both endpoint-zero windows, length-zero support,
negative input guards, and deterministic complete serialization sensitive to
the descent witness. Together with sixteen immediate regressions, 24 tests
pass; root typecheck and affected-file lint pass too.

The remaining generic prerequisites are real owner gaps, not failed native
computations. The source contains category-generic homology but only native
and witnessed Freyd induced homology maps. Generic kernel/cokernel map
construction must therefore be added in row 7C. Row 7B must construct the
canonical homology inclusion and prove monicity from the generic Abelian
owners; row 7D must derive target factor/source descent and all three
exactness witnesses from the completed generic snake theorem. Native
decisions are not substitutes for those proofs, and row 7 is not complete.

## Generic Monicity Of The Actual Homology Inclusion

Row 7B is now implemented independently of native decisions. For arbitrary
whole cokernels and `f = k b`, the comparison `j:Coker(b) → Coker(f)` is
the selected colift of `pi_f k`. Its annihilation and reconstruction paths
are derived. An actual pushout of `k` and `q_b` gives a cokernel factor
`s:Coker(f) → PO`; cancelling epic `q_b` proves `s j = inj2`. The generic
monic-factor lemma makes `j` monic when that injection is monic, and the
Abelian wrapper supplies its monicity by the existing pushout-stability
theorem. No pushout isomorphism is required.

The homology specialization passes its actual cycle embedding, boundary,
boundary reconstruction, and original whole boundary cokernel to this
theorem. It constructs the same canonical inclusion as the native window
and proves it monic. The public one-Abelian-capability observation delegates
to a PA/normality-explicit proof, following the earlier image-bimorphism
discipline. No different homology object or equality transport is introduced.

Two rejected presentation variants reached 90 seconds in both quiet and
warning-enabled checks: a shorter preadditive alias in the Abelian cokernel
wrapper, and direct bundled homology instantiation. The accepted common
literal preadditive form and PA-explicit stage pass, as do the ordinary
bundled observation and its cancellation consumer. These findings concern
conversion cost, not the theorem or runtime-rule orientation.

The thirteen assertions also reject a comparison at another cokernel object
and an inclusion at another whole homology object. Promoted quiet and
warning-enabled source checks pass; the inherited inventory is unchanged at
`1,217/169` and nine strict audits find no rule clauses. Generic induced
homology maps and complete window exactness remain required in rows 7C/7D.

## Generic Kernel, Cokernel, And Homology Maps

The generic map operations and laws are now implemented. Their compatibility
owner is the existing internal Hom-fibre of ordinary pre/postcomposition.
`HomPostcompFactor` and `HomPrecompFactor` are transparent aliases of that
owner. When the target is itself a composite, its reconstruction displays
the familiar square, but no additional square primitive or independent
commutativity field is introduced.

Kernel maps derive their target annihilator from a lower factor point and
source-kernel annihilation, then use the actual target kernel lift. Cokernel
maps are the corresponding upper-factor construction using the actual source
cokernel colift. Existing uniqueness gives reconstruction, identity,
composition, and equality under a changed visible component. Inverse visible
components with both compatibility factors give actual `IsoEvidence`.

A `ComputationalChainPairMap` retains the middle arrow and its two internal
factor points. Its ordinary three components and two compatibility equations
are projections; a conventional components/paths constructor is only a
transparent usability view. Identity and composition reuse the factor
operations. Different proofs of the same chain-zero equation do not change
this map-data type, while different intermediate arrows remain constrained.

The homology operation first applies the kernel map to the actual cycles.
Target-kernel monicity and the two original boundary reconstructions derive
boundary compatibility; it is not an additional input. The cokernel-map
operation then acts on the actual boundary cokernels. Its identity,
composition, extensionality, and inverse laws follow from those generic map
laws. Different kernel, cokernel, or whole homology choices are compared by
constructed isomorphisms, without object equality or transport.

Five reviewers contain 49 assertions, all green from source with and without
warnings. Besides the operation/law and choice comparisons, six negative
guards reject wrong targets, universal objects, and intermediate chain
pairs; the same-arrows/different-zero-proof consumer prevents an unnecessary
false negative. The factor-only warning closure is `1,117/157`, and the
additive/kernel closures remain `1,217/169`. All twenty strict audits pass.

This completes the generic machinery subrow 7C1, not its canonical snake
instantiations. Row 7C2 must derive a snake triple from an actual map between
short-exact rows and instantiate the endpoint isomorphisms there. The full
window proof remains row 7D. A packaged category-of-complexes homology functor
and closed formal Freyd quotient effectiveness are not silently claimed.

## Row-to-snake endpoint comparisons (row 7C2)

The new `emdash3_2_chain_pair_map_snake.lp` derives the existing snake triple
from one existing row-pair map. Its upper internal factor and the lower
pair's zero equation derive triple-zero; short-exactness is not needed until
the comparison arrows are made invertible. The comparison module proves
`gamma = last(F) ∘ q_top` and `alpha = a_bottom ∘ first(F)` by actual
cokernel/kernel uniqueness.

`emdash3_2_kernel_domain_comparison.lp` and its cokernel-codomain dual
construct isomorphisms of supplied whole universal objects. Their row
instances give `cycles(last(F)) ≅ Ker(gamma)` and
`Coker(alpha) ≅ coker(first(F))`. The source cycles and target cokernel are
parameters representing the actual consumer's choices, not freshly selected
replacements. Forward/inverse maps are the existing generic maps and both
inverse laws are derived. The bottom comparison uses the existing
balancedness-constructed inverse; literal agreement with a differently
chosen native inverse representative is not claimed merely from uniqueness.

The internal definitions keep PA and normality explicit. Direct one-Abelian
wrappers were too expensive; ordinary dependent elimination of the existing
Sigma package supplies the one-Abelian view at its original endpoints. This
is a transparent definition with constructor beta, not opacity, an equality
bridge, or a new eta rule on arbitrary neutral packages. Whole short-exact
rows project their original pair/evidence into this interface.

Fresh-source cumulative reviewers exceeded 90 seconds. Verbose checks locate
successful assertions and substantial dependency import cost; fresh exact
dependency staging plus source/target reviewer separation checks all 28
assertions without changing their statements. The last isolated target beta
took 71.36 seconds, so final interaction cost is still a redesign concern.
The inherited warning inventory remains `1,217/169`; no new rule is added.
The promoted final-name quiet/warning gates now pass through the registered
staging script, including ordinary-check dispatch. Seventeen strict rule
audits, thirteen focused dispatch tests, catalog/TOC and document hygiene
pass. Temporary compilation objects are removed; the unrelated global health
exception is unchanged. Row 7C2 is complete, not full window exactness.

## Public homology ownership and the reference baseline

These endpoint comparisons explain one algorithm, not the public identity of
homology connecting. The public arrow is `H_n(C) → H_(n-1)(A)`; the snake
arrow has different endpoints and is an implementation/proof helper. The
2026-09-07 user clarification prioritizes a separately named homology
operation, native bounded assembly, categorical lowering, and a working
proof–CAS delegation/replay/adoption route. The completed native window is
its operational gate. Generic window exactness remains required but does not
block that first operational baseline. A later internal/functorial redesign
may replace today's logical packaging while retaining these reference
algorithms, typed interfaces, laws, and nonsplit regression examples.
