# Affine Formal-Computational Bridge Owner Audit

Date: 2026-08-30

Plan: `TYPESCRIPT_EMDASH_AFFINE_FORMAL_BRIDGE_PLAN.md`

Status: `BRIDGE-AUDIT-1A` complete; selected first slice is the algebraic
finite Zariski-cover presentation over a supplied formal commutative ring.

## Authority Reviewed

The audit read the mandatory repository and Lambdapi SOP, the TypeScript v3.2
handoff, the current-status owner map, Foundations, the relevant active
Lambdapi modules and examples, and the explicit-Core builder/declaration/probe
serialization APIs. Active source wins over prose.

Focused unchanged checks passed for:

```text
emdash3_2_commutative_algebra_finite.lp
emdash3_2_commutative_algebra_localization.lp
emdash3_2_commutative_algebra_affine_schemes.lp
```

Each check was bounded by 90 seconds. No active Lambdapi source was edited.

## Formal Owner Map

| Computational datum | Current formal owner | Classification |
| --- | --- | --- |
| supplied formal commutative ring | `CommRing` in `emdash3_2_commutative_algebra.lp` | exact existing owner |
| formal ring element and operations | `comm_ring_carrier`, `comm_ring_zero`, `comm_ring_one`, `comm_ring_add`, `comm_ring_neg`, `comm_ring_mul` | exact existing owners |
| structured ring map | `CommRingHom` and `comm_ring_hom_apply` in `emdash3_2_commutative_algebra_category.lp` | exact existing owner |
| length-indexed elements/coefficients | `FiniteFamily`, `finite_family_nil`, `finite_family_cons` in `emdash3_2_finite_families.lp` | exact existing owner |
| finite dot product | `comm_ring_finite_dot` in `emdash3_2_commutative_algebra_finite.lp` | exact existing owner |
| coefficients plus unit equation | `CommRingUnimodularPresentation` / `comm_ring_unimodular_intro` | exact first bridge target |
| algebraic finite cover | `CommRingZariskiCoverPresentation` / `comm_ring_zariski_cover_intro` | exact first bridge target |
| cover plus chosen universal localizations | `CommRingZariskiCoverFamily` in `emdash3_2_commutative_algebra_zariski.lp` | existing owner, but requires additional formal localization packages |
| localization at one element | `CommRingLocalizationAt` in `emdash3_2_commutative_algebra_localization.lp` | existing universal-property owner; not derivable from an adjoined-inverse CAS presentation alone |
| basic-open affine chart | `affine_spec_basic_open_chart` in `emdash3_2_commutative_algebra_affine_spec.lp` | existing owner after a supplied `CommRingLocalizationAt` |
| affine scheme presentation | `AffineSchemePresentation` in `emdash3_2_commutative_algebra_affine_schemes.lp` | existing assumption-explicit owner requiring structure-sheaf and locality capabilities |
| realized ambient binary affine cover | `BinaryAffineCoverPresentation` and `AffineCoverChartRealization` | existing global/site-relative owner; CAS algebraic cover data is insufficient by itself |
| concrete polynomial quotient ring | none | missing formal representation; the polynomial owner is universal-property-only and explicitly has no monomial/quotient syntax |
| finite Čech nerve/cochain presentation | none located | missing owner; generic category/diagram ingredients exist, but no current concrete Čech package matches the CAS datum |

## TypeScript Explicit-Core Map

| Need | Existing TypeScript owner | Use |
| --- | --- | --- |
| explicit backend-neutral term | `KernelExpression` and constructors in `kernel.ts` | primary bridge interchange |
| scoped higher-order construction | `CoreLfScopedBuilder` in `lf_builder.ts` | build calls, binders, and closed terms without callbacks in Core |
| arbitrary reviewed formal symbol | builder/free `KernelExpression` reference plus generic call | no new `CoreOwnerId` required |
| checked external signature mirror | `CoreLfDeclarationEnvironment` | typecheck reviewed active signatures before use |
| deterministic Lambdapi name mapping | `serializeKernelExpression(...externalFreeReferences)` | map portable Core free names to active formal owners only at emission |
| declaration/assertion probe | `serializeCoreLfKernelProbe` in `lf_probe.ts` | emit `require open emdash.emdash3_2`, local declarations, assertions, and source map |
| multi-module compilation | transfer compiler and declaration workspace | later rows if the bridge grows beyond one focused module |

The global Core owner catalog and `LAMBDAPI_V32_OWNER_BINDINGS` remain
unchanged. Bridge symbols are reviewed free declarations, not new trusted Core
nodes.

## Gap And Trust Classification

### Selected formal cover slice

Given:

- `R : CommRing` as a formal Core term;
- formal terms for every computational cover element;
- formal terms for every computational coefficient; and
- a formal term proving the finite dot product equals one;

the bridge can deterministically construct:

```text
comm_ring_zariski_cover_intro
  R n generators
  (comm_ring_unimodular_intro R n generators coefficients law)
```

where `n`, `generators`, and `coefficients` use the existing Nat/FiniteFamily
constructors. This inhabits the exact active
`CommRingZariskiCoverPresentation R` owner and requires no Lambdapi edit.

### Status boundary

- `explicit-data`: caller supplies the formal ring, realized elements, and
  formal law term. The bridge may build and check the cover term.
- `checked`: the supplied or reconstructed law term is checked against the
  exact equality type by TypeScript and/or bounded Lambdapi conformance.
- `trusted-computation`: computational equality is recorded as bridge
  metadata only. It does **not** manufacture an inhabitant of the formal
  equality or cover type.

An opaque equality declaration is not an accepted implementation of
`trusted-computation` in this goal.

### Quotient-element reification

The formal library has no concrete quotient-ring carrier matching
`AlgebraPresentedAlgebra`. Therefore the first realization requires a
supplied formal ring `R`, one formal term per computational polynomial
generator, and a coefficient reifier. Canonical quotient representatives may
then be evaluated into `R` using existing ring operations. This realizes
elements into a selected formal ring; it does not claim that `R` was formally
constructed as the CAS quotient.

### Localization

The CAS equation `f * f^-1 = 1` supplies formal `CommRingUnitEvidence` only
when its inverse and law are realized. It does not prove the contractible
factorization field of `IsCommRingLocalizationAt`. A bridge to
`CommRingLocalizationAt` must therefore accept a supplied formal universal
property/package or remain at unit evidence. No automatic whole localization
inhabitant is selected.

### Affine schemes

`AffineSchemePresentation(R)` requires an `AffineStructureSheafPresentation`
and `AffineCoordinateLocalizationLocality`. A CAS presented algebra, cover,
or localization does not construct those capabilities. Formal affine-scheme
realization must accept them as supplied semantic data; it cannot be the first
bridge slice.

### Čech data

No current concrete Čech owner was found. `BRIDGE-CECH-5A` must later choose
between:

1. a representation through an existing generic finite diagram/cochain owner,
   if a focused construction is actually expressible; or
2. a separately reviewed minimal concrete owner justified by the implemented
   cover consumer.

It must not silently call a TypeScript data record a formal Čech inhabitant.

## Selected Next Row

`BRIDGE-CONTRACT-1B` will implement a parent-aware, backend-neutral contract
for the selected algebraic cover slice. Its first acceptance case is a binary
cover with explicitly supplied formal ring, element, coefficient, and law
terms. It will validate computational parent/arity alignment, build the exact
Nat/FiniteFamily/Core term, emit deterministic Lambdapi using reviewed external
bindings, and fail closed for trusted-without-law or foreign realization data.

No active Lambdapi declaration, rewrite rule, unification rule, or formal
quotient/localization/scheme owner is required for that row.
