# Proof–CAS Delegation Owner Audit

Date: 2026-08-31

Plan: `TYPESCRIPT_EMDASH_PROOF_CAS_DELEGATION_PLAN.md`

Status: initial owner audit complete; selected root-goal, immutable-environment,
native-Zariski vertical slice; implementation pending.

Baseline: `79f3bb7fd05446fe14739bfb056b7dc2d254affd`

## Audit Question

What is the smallest existing-owner path by which one stable emdash proof
goal can delegate to a typed algebra operation, retain the whole computation,
and use the result formally without either:

- adding computation to Core/kernel reduction;
- extending the inert proof-plan grammar with an effectful node;
- treating a computation-status flag as an equality proof; or
- transferring an unrelated formal mathematical theory merely to demonstrate
  plumbing?

The selected answer is a closed root-hole proof document plus one explicit
formal/computational realization, one native exact algebra operation, and a
separate immutable trusted-assumption adoption action.

## Exact Owner Map

| Role | Existing owner | Relevant boundary |
| --- | --- | --- |
| typed algebra operation | `AlgebraOperation<I,O>` in `algebra_engine.ts` | stable operation identity and input/output runtime schemas |
| execution result | `AlgebraComputed<O>` in `algebra_engine.ts` | retains actual engine, algorithm, exact/heuristic quality, assumptions, diagnostics, reusable intermediates, and normalized output |
| direct execution | `computeAlgebraOperation` | validates operation/engine support and schemas before and after execution |
| graph execution | `AlgebraComputationGraph` / `executeAlgebraComputationGraph` | explicit topology and schema flow; no proof semantics |
| graph serialization | `serializeAlgebraComputationGraph` | deliberately topology-only; runtime input values are absent |
| proof source | `CoreProofPlan` | inert `exact`, `intro`, `apply`, `have`, and named `hole` nodes only |
| open proof compilation | `compileCoreProofDocument` | freshly checks target and replays the plan under one exact LF declaration environment |
| stable goal evidence | `CoreProofPlanExecution.snapshot.goals` / `CoreProofArtifact.state.goals` | stable source IDs and portable rendered targets; not an exact-Core goal map |
| source replacement | `createCoreProofPlanHoleReplacement` / `applyCoreProofPlanPatch` | immutable source patch only; fresh replay remains semantic authority |
| low-level assumption | `CoreLfDeclarationEnvironment.extend` | immutable extension; absent body defaults to opaque; declaration type is checked in the preceding environment |
| declaration authoring | `createCoreLfAuthoredDependencyModuleDeclarationFragment` | source-oriented transfer AST; useful later, but does not accept an arbitrary existing `KernelExpression` type directly |
| formal algebra realization | `AffineFormalAlgebraRealization` / `AffineFormalPolynomialReifier` | binds one quotient parent to one selected formal ring and deterministic element reifier |
| formal cover realization | `AffineFormalCoverRealization` | retains generators, coefficients, law status, and exact computational cover parent |
| computational Zariski operation | `algebraZariskiReferenceOperations(...).unimodular` | ideal input to whole unimodular output under the native reference engine |
| computational serializers | `serializeAlgebraPolynomialIdeal` / `serializeAlgebraUnimodularCombination` | canonical operation payload encodings already exist |
| formal law target | `affineFormalCoverLawType` | exact dot-product-equals-one Core target, but currently requires an already law-bearing realization |
| formal cover construction | `buildAffineFormalCoverTerms` | constructs existing formal finite-family, unimodular, and cover terms only after an actual law term is supplied |
| active formal owners | `emdash3_2_commutative_algebra_finite.lp` | `comm_ring_finite_dot`, `CommRingUnimodularPresentation`, its intro, `CommRingZariskiCoverPresentation`, and its intro |

## Proof-Goal Boundary

`executeCoreProofPlan` internally relates stable source goal IDs to session
metavariables. Its public execution returns both:

- the in-memory `CoreProofState.goals`; and
- a portable snapshot whose goals are produced in exactly the same order.

However, `compileCoreProofDocument` intentionally returns only the portable
artifact/goal graph and an optional completed checked term. It does not expose
the in-memory execution or an exact `KernelExpression` target for every named
inner goal.

The first bridge therefore selects a stricter complete consumer:

```text
CoreProofDocumentInput
  with plan = coreProofPlanHole(goalId, expectation=type)
  and contextDepth = 0.
```

For this root hole, the exact goal target is the document's already checked
`type`. The bridge can compile it fresh, require exactly one incomplete goal
with the selected ID and depth zero, and retain canonical Core serialization
of the exact target. This is a genuine named proof goal and requires no
positional guess or new proof-plan API.

General nested/local goals remain a later consumer. They require either a
public exact named-goal projection from `CoreProofPlanExecution` or explicit
Pi-abstraction of their local context. That mechanism is not needed for the
first complete vertical slice.

## Trusted-Adoption Boundary

`CoreLfDeclarationEnvironment.extend` is the direct semantic owner for one
new assumption:

```text
environment.extend({
  name,
  type: exactGoalType,
  mode,
  provenance
})
```

With no body, transparency defaults to `opaque`. The environment remains
immutable, rejects duplicate names, and validates the declaration type. An
ordinary `coreProofPlanExact(kernelFree(name))` then closes the root hole only
when replayed in that extended environment.

This is preferable for the first runtime adoption to converting exact Core
back into the source-oriented `CoreLfTransferExpression` grammar. A companion
portable adoption artifact must record that the body-free declaration came
from an explicitly trusted computation. Later source/workspace publication
may lower that record into the existing declaration-fragment facade, but it
is not a prerequisite for in-memory checked use.

The affine bridge invariant remains unchanged:

```text
trusted-computation metadata does not produce a law term.
```

Trusted adoption first creates an actual opaque Core reference at the exact
law type. That reference may then be supplied as explicit formal data to a new
law-bearing cover realization. The bridge never turns its original status
flag into a proof.

## TypeScript Formal-Signature Gap

The completed affine bridge constructs exact backend-neutral Core and checks
representative probes with Lambdapi. It does not currently install the active
commutative-algebra/finite-family signatures into a TypeScript
`CoreLfDeclarationEnvironment`.

Consequently, a TypeScript proof document cannot yet typecheck the exact
Zariski law merely from the current bridge artifact. Its target mentions
portable references including:

```text
bridge_tau
bridge_eq
bridge_CommRing
bridge_comm_ring_carrier
bridge_comm_ring_zero / one / add / neg / mul
bridge_nat_zero / succ
bridge_finite_family_nil / cons
bridge_comm_ring_finite_dot.
```

The cover term additionally mentions the existing unimodular and cover
classifiers/intros. These are not new mathematical owners. The selected
solution is a small reviewed exact opaque signature mirror for only this
dependency-closed portable surface, built in the TypeScript LF declaration
environment and checked against bounded Lambdapi conformance. It adds no Core
owner, definition, runtime rule, or proof rule.

A permissive fake environment in which every reference merely has type
`TYPE` is rejected: it would let TypeScript accept malformed formal targets
and would not constitute proof-assistant integration.

## Formal-Law Target Gap

`affineFormalCoverLawType(realization)` currently calls
`buildAffineFormalCoverTerms(realization)`. The latter correctly refuses a
trusted/no-law realization. This makes law-target construction circular:

```text
need law type to adopt law
  -> law-type helper asks for completed cover terms
  -> completed cover terms require law.
```

The target itself needs only the already reified generators, coefficients,
ring, family length, and finite-family constructors. The selected correction
is to construct those family terms directly through the existing public
`buildAffineFormalFamily`, allowing the law-type helper to accept a
trusted/no-law realization while keeping `buildAffineFormalCoverTerms`
strict. This changes no formal meaning and weakens no trust check.

## Zariski Operation And Payloads

The first exact computation is:

```text
algebraZariskiReferenceOperations(ring).unimodular
  : AlgebraPolynomialIdeal
      -> AlgebraUnimodularCombination.
```

Its native implementation delegates to the existing whole
`algebraUnimodularCombination`. Positive output retains the original ideal,
Gröbner computation, membership result, coefficients, combination, and zero
remainder. Negative output retains the nonzero remainder and cannot be passed
to `algebraZariskiCoverPresentation`.

Canonical request/result payloads already exist:

- `serializeAlgebraPolynomialIdeal(input)`; and
- `serializeAlgebraUnimodularCombination(output)`.

The realization payload should be adapter-owned and include at least:

- computational quotient identity and revision;
- canonical formal-ring Core;
- ordered formal generator Core;
- realization status and exponent bound; and
- exact reified computational cover generator/coefficient terms used by the
  interpretation.

Every callback-derived term must use the existing repeated deterministic
reification checks before entering the artifact.

## Selected Positive And Negative Fixtures

The positive fixture is the existing rational affine-line ideal generated by
`x` and `1-x`. It computes coefficients, reifies the ordered generator and
coefficient families, and targets the exact formal equation:

```text
dot(coefficients,[x,1-x]) = 1.
```

The negative fixture is the singleton ideal generated by `x`. Its whole
result has a nonzero remainder, so the interpretation records a negative
observation, exposes no adoptable positive claim, leaves the proof plan open,
and cannot build a formal cover.

## Second Consumer Assessment

The ideal-membership operation is an appropriate genericity candidate because
it has typed native input/output and retains combination coefficients and a
remainder. It does not yet have a dedicated canonical output serializer; the
adapter can provide one from the retained polynomial serializers.

Its formal interpretation needs care. The active formal polynomial algebra is
universal-property-only and the supplied formal ring is not automatically a
model of the CAS quotient ideal. A positive computational membership result
therefore cannot silently become equality in an arbitrary supplied formal
ring. The later row must do one of the following explicitly:

- carry formal data that the chosen generator realization kills every ideal
  relation;
- use trusted adoption of the exact resulting formal equality and record that
  realization assumption; or
- select a different existing ring-level consumer.

No formal quotient owner is authorized by this audit.

## Rejected Immediate Alternatives

- Add `compute` to `CoreProofPlan`: rejected because proof plans are inert and
  all current nodes replay through the checked refiner.
- Invoke a CAS from Core reduction or Lambdapi rewriting: rejected because
  algebra execution may be bounded, partial, asynchronous, or external.
- Let `trusted-computation` carry a law term: rejected because it collapses
  computation metadata and explicit logical assumption.
- Reify arbitrary `KernelExpression` back into the full LF transfer grammar:
  rejected as unnecessary for the first runtime adoption and a much broader
  round-trip problem.
- Use topology-only graph serialization as a request fingerprint: rejected
  because it omits runtime input values by design.
- Give every formal bridge reference the fake type `TYPE`: rejected because
  it would not check the active formal dependency shape.
- Transfer formal module/Čech/homology theories now: rejected because the
  first complete ring-level consumer already tests the architectural seam.

## Baseline Evidence

At baseline `79f3bb7`:

- root workspace contract passes;
- root TypeScript typecheck passes;
- 61 focused proof-plan, LF-workspace/declaration-authoring, Zariski, formal
  realization, reifier, and cover tests pass;
- the registered kernel aggregate was started as required by the root handoff
  and passed the active nucleus plus the directly relevant finite-family,
  commutative-algebra, finite-unimodular, polynomial, and localization owners;
  it was terminated after it continued into unrelated HIT/Gray/site modules,
  in accordance with the user's proportional-testing boundary; and
- no Lambdapi or TypeScript source changed during this audit.

The owner-specific `emdash3_2_commutative_algebra_finite.lp` check is the
appropriate bounded formal baseline for the first implementation slice.

## Audit Decision

Proceed with:

1. immutable generic request/adapter/result/artifact contracts;
2. closed root-hole named goals only in the first tranche;
3. direct native exact execution and observation before adoption;
4. direct immutable `CoreLfDeclarationEnvironment` extension for explicit
   trusted assumptions;
5. ordinary exact proof-plan replacement and fresh replay;
6. the minimal exact TypeScript signature mirror needed by the portable
   formal Zariski law/cover surface;
7. noncircular law-target construction from existing family data; and
8. the `x,1-x` positive plus `x` negative Zariski fixtures.

This is sufficiently concrete to begin `PCD-CONTRACT-2A`. It preserves the
separate computation, formal-realization, explicit-assumption, and checked
proof boundaries while providing a complete path between them.
