# Affine Localization And Čech Delegation Owner Audit

Date: 2026-08-31

Plan: `TYPESCRIPT_EMDASH_AFFINE_LOCALIZATION_CECH_DELEGATION_PLAN.md`

Status: initial owner audit complete; no new Lambdapi mathematical owner is
required for the selected binary/ternary face-unit route.

Baseline: `ae85a4bf02c0cea9fc68eda8f0b984172fd072e0`

## Selected Boundary

The first complete consumer starts from the already-retained computational
principal localizations in an affine cover and produces:

- adopted inverse equations;
- explicitly trusted whole localization properties;
- existing formal localization/chart packages;
- computed face-product decomposition equations;
- formally derived face-unit evidence;
- localization-universal overlap factors/maps/agreements; and
- the existing packed formal Čech presentation.

All selected goals are closed declaration-scope goals. General contextual
proof-goal support is not needed.

## Exact Owner Map

| Role | Existing owner | Audit result |
| --- | --- | --- |
| localization computation | `algebraLocalizationReferenceOperations(...).localize` | exact quotient-element input to whole adjoined-inverse presentation |
| computational inverse check | `AlgebraPrincipalLocalization.inverseEquation` | exact Boolean retained after quotient normalization |
| formal localization realization | `defineAffineFormalLocalizationRealization` | correctly separates trusted/no-evidence from explicit law/universal data |
| inverse-law target | `affineFormalInverseLawType` | circular: currently calls a builder requiring the inverse law |
| whole property target | `affineFormalLocalizationPropertyType` | already noncircular over trusted realization fields |
| universal field | `affineFormalLocalizationUniversalFromProperty` | existing `sigma_Snd` projection from an adopted whole property |
| formal unit | `buildAffineFormalLocalizationUnitTerms` | strict; requires actual inverse-law Core term |
| formal localization/chart | `buildAffineFormalLocalizationTerms` | strict; requires actual inverse law plus universal field |
| cover localization family | `buildAffineFormalCoverLocalizationTerms` | uniformly builds chosen formal localizations/charts in cover order |
| product is unit | `comm_ring_localization_inverted_unit` | projects unit evidence from an existing localization property |
| factor of unit product | `comm_ring_unit_mul_left` / `_right` | existing rule-free formal theorem; sufficient after a face decomposition path |
| unit transport | `comm_ring_unit_transport_backward` | moves unit evidence from the codomain product image to the selected binary decomposition |
| overlap factor | `comm_ring_localization_factorization_is_contr` | derives contractible factor space from lower localization property plus target unit |
| overlap map/agreement | localization factor projections | already derived; no handwritten map/triangle needed |
| formal simplex | `defineAffineFormalCechSimplexLocalization` | strict; requires whole formal localization matching retained product chart |
| formal overlap | `buildAffineFormalCechOverlapTerms` | currently receives manual face-unit terms; derivation can replace caller input |
| packed Čech data | `buildAffineFormalCechPresentation` | existing whole consumer; no differential/cosimplicial claim |
| assumption adoption | proof–CAS trusted adoption | correct in memory, but adopted declaration provenance is not source-spanned for direct durable emission |

## Inverse-Law Circularity

The current helper computes its target by calling
`buildAffineFormalLocalizationUnitTerms`, which refuses a trusted/no-law
realization. The target requires only:

```text
formal source/target rings
formal structure map
formal localized element
formal selected inverse.
```

It can construct directly:

```text
map(f) * inverse = 1.
```

The strict unit/localization builders remain unchanged. This is the same
noncircular-target correction already accepted for unimodular cover laws.

## Universal-Property Classification

`AlgebraPrincipalLocalization` constructs the quotient presentation with an
inverse variable and validates the inverse equation. It does not evaluate the
dependent statement that every target factorization space is contractible.

Therefore:

- the inverse equality is `computed-equation`;
- `IsCommRingLocalizationAt` is `trusted-presentation-semantics`; and
- factor maps selected from that property are `derived-formally`.

After adoption of the whole property `P`, the existing expression
`sigma_Snd(P)` supplies exactly the universal field expected by the current
formal localization builder. No parallel localization classifier or opaque
equality bridge is required.

## Uniform Face-Unit Derivation

No general finite-product formal owner is needed for this consumer.

For every retained Čech face, computational data identifies:

```text
domain product d
removed cover element r
codomain product c
```

and exact quotient computation validates `d*r = c`. Reify this at the
codomain localization map as one adopted computed equation:

```text
map(d) * map(r) = map(c).
```

Then use only existing formal owners:

```text
unit(map(c))
  -- transport backward along map(d)*map(r)=map(c) -->
unit(map(d)*map(r))
  -- comm_ring_unit_mul_left -->
unit(map(d)).
```

This works uniformly for binary, ternary, and higher finite simplices because
the entire lower-dimensional product is treated as the left binary factor.
No `Fin`, deletion calculus, family append, finite multiplication owner, or
arity-specific proof is required.

The only per-face opaque assumption is the exact computed product-
decomposition equality. The resulting unit evidence, factor map, and triangle
are formal consequences. The plan's proposed finite-product row is therefore
rejected for this goal with a concrete existing-owner route, not merely
deferred.

## Formal Product-Term Alignment

The existing polynomial reifier canonicalizes quotient representatives rather
than preserving the original multiplication tree. Consequently the equality
between reified `d*r` and reified `c` is generally not definitional. The
computed decomposition adapter must target that exact formal equality rather
than relying on syntactic conversion.

This is preferable to changing the global element reifier or inventing a
second product representation. It preserves canonical polynomial
reification, records the exact place where ring equations are trusted, and
lets ordinary unit transport own the semantic consequence.

## Computed-Assumption Source Need

The completed trusted adoption stores the exact assumption term and a
canonical artifact, but its derived provenance has no source span. The live
Zariski test rebuilds an equivalent source-spanned declaration before probe
emission.

A finite affine cover needs many assumptions in dependency order. The
selected source layer should accumulate adoptions one at a time over an exact
base environment, rebuild each body-free declaration with a deterministic
virtual source span, and retain:

- classification (`computed-equation` or
  `trusted-presentation-semantics`);
- originating goal/request/result/adoption artifacts;
- exact Core type and declaration name;
- predecessor environment identity/order; and
- canonical source/module identity.

It should emit through `serializeCoreLfKernelProbe` with existing active-owner
bindings. It should not reify Core back into `CoreLfTransferExpression`.

## Required Signature-Mirror Extension

The existing twenty-signature Zariski mirror is insufficient for TypeScript
checking of localization and overlap terms. The exact dependency-closed
extension must cover only the active owners actually used by:

- structured ring maps and application;
- unit evidence, construction, transport, and product-factor projection;
- localization property/package constructors and projections;
- affine basic-open chart construction;
- localization factor contractibility and projections; and
- packed formal overlap/Čech terms.

These remain opaque TypeScript LF signature mirrors plus focused Lambdapi
conformance. They add no mathematical owner or runtime/proof rule.

## Selected Positive And Negative Fixtures

Positive fixtures:

- binary affine line `D(x),D(1-x)` through degree one; and
- ternary affine plane `D(x),D(y),D(1-x-y)` through degree two.

Each must use the same localization and face-decomposition adapters. The
ternary fixture may not introduce handwritten arity-specific evidence.

Negative fixtures include:

- foreign or changed localization output;
- false inverse equation;
- universal-property result with the wrong evidence classification;
- face product/reified target drift;
- missing/reordered/duplicate assumption-source entries; and
- attempted overlap construction before all dependencies are adopted.

## Baseline And Validation

The implementation changes TypeScript/Core bridge and may extend only
signature mirrors; no Lambdapi source change is selected by the audit.

Use focused localization, formal bridge, overlap, Čech, adoption/workflow,
graph, and conformance suites. The exact formal target is
`emdash3_2_commutative_algebra_affine_spec.lp` and its dependency chain.
Focused live probes should be used at the final binary/ternary boundary.

The predecessor's full TypeScript aggregate already established unrelated
stale source pins on clean `main`. Do not absorb or repeatedly rerun those
maintenance failures in this goal.

## Audit Decision

Proceed with:

1. source-persistent exact-Core computed assumptions;
2. a noncircular inverse-law target;
3. inverse-equation and universal-semantics localization adapters;
4. a face-product decomposition operation/adapter;
5. formally derived face units through transport and
   `comm_ring_unit_mul_left`;
6. uniform binary and ternary whole Čech consumers; and
7. focused live backend conformance.

Reject a new finite-product Lambdapi layer for this goal because the existing
binary factor-unit theorem plus one exact computed decomposition path handles
every retained face uniformly.
