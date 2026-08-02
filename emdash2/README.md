# m— / emdash

`emdash` is an experimental Lambdapi specification for functorial type
theory and a future proof assistant for strict/lax omega-categories,
omega-functors, omega-transformations (“transfors”), directed families, and
dependent categorical structure.

Its computational style treats coherence as typed computation: rewrite rules
select runtime normal forms, while narrowly scoped unification rules compare
proof-time presentations when neither direction should become computation.

## Headline result

The current development contains an opaque one-dimensional
walking-endomorphism directed HIT with a base `*` and a genuinely directed
loop `ell : * -> *`. A Cat-valued code, a contextual decoder, and a
directed normalization cell establish the checked carrier equivalence

```text
Hom_WalkingEnd(*,*) ≃_Type Nat.
```

The concrete one-object category `BNat` is a separate model, not the
definition of `WalkingEnd`. The loop is not the identity, has no right
inverse, and carries no native omega-equivalence evidence. The detailed
mathematical reading is in
`reports/EMDASH_FOUNDATIONS.md`.

## Where to start

- `emdash3_2.lp` is the active kernel and computation authority.
- `emdash3_2_presheaves.lp` owns the rigid Cat-valued presheaf facade,
  restriction along ordinary functors, transparent Yoneda and slice
  presentations, and Cat-valued higher sieves.
- `emdash3_2_sieves.lp` owns native subterminal categories, ordinary sieves
  as pointwise-subterminal higher sieves, and ordinary pullback. It does not
  itself declare `Omega` or topology.
- `emdash3_2_sites.lp` owns ordinary-sieve membership, the maximal sieve,
  proposition-valued sieve coverages, the three Grothendieck topology laws,
  and the direct chaotic-topology model. It does not add `Omega`, free
  coverage saturation, sheafification, or descent.
- `emdash3_2_finite_families.lp` owns Nat-indexed right-associated finite
  families, their constructors/projections, pointwise map, and sethood. It
  introduces no `Fin`, list/Sum/inductive interface, or package eta.
- `emdash3_2_commutative_algebra.lp` owns set-carrier commutative-ring
  operation and law packages, readable observations, and the concrete
  one-element zero ring.
- `emdash3_2_commutative_algebra_category.lp` owns structured ring morphisms,
  their preservation/sethood theorems, transparent explicit-map observations,
  pointwise structured-map extensionality, `CommRing_cat`, and the selected
  stable identity/composition comparisons. The invertibility-sieve consumer
  selects its full-action carrier functor without a competing capped rule.
- `emdash3_2_commutative_algebra_product.lp` owns the rule-free componentwise
  product ring and map action, including whole structured-map identity and
  composition paths without installing a primitive product-functor facade.
- `emdash3_2_commutative_algebra_f2.lp` owns the closed Boolean-carrier
  two-element commutative ring, with all laws proved by internal elimination.
- `emdash3_2_commutative_algebra_finite.lp` owns finite ring sums and dot
  products, their structured-map preservation theorems, retained unimodular
  coefficient data, and algebraic finite Zariski-cover presentations. It does
  not yet declare `Spec`, basic opens, localization families, topology,
  powers/radicals, fractions, polynomials, or quotients.
- `emdash3_2_commutative_algebra_polynomial.lp` owns polynomial algebras by
  their universal property as free commutative `R`-algebras on a variable
  classifier. It selects no monomial/coefficient/quotient syntax or concrete
  positive-variable representation; the reviewer proves `R[Empty] = R`.
- `emdash3_2_commutative_algebra_localization.lp` owns proposition-valued unit
  evidence, unit transport/preservation, and localization at one element by
  contractible pointwise factorization. It selects no concrete fractions,
  finite families, polynomials, or Zariski presentation.
- `emdash3_2_commutative_algebra_localization_unit.lp` constructs the
  pointwise identity as the universal localization of any already invertible
  element. In particular, localization at one computes to the original ring.
- `emdash3_2_commutative_algebra_localization_zero.lp` derives multiplication
  and negation at zero, proves that invertible zero forces a contractible
  carrier, and constructs the computing universal localization `R[1/0]=0`.
- `emdash3_2_commutative_algebra_localization_idempotent.lp` constructs the
  fixed-image ring `eR={x | e*x=x}` for `e^2=e` and proves that the computing
  scaling map `x |-> e*x` has the full localization universal property. It is
  quotient-free and rule-free.
- `emdash3_2_commutative_algebra_localization_split.lp` specializes that
  construction to `(1,0)` in a product ring. Its closed `F2 x F2` instance
  proves the idempotent differs from zero and one, and its affine-basic-open
  restriction computes as `(x,y) |-> (x,0)`.
- `emdash3_2_commutative_algebra_localization_comparison.lp` owns product-unit
  algebra and the universal-property comparison between localization at `f*g` and
  localization first at `f`, then at the image of `g`. It retains canonical
  maps and pointwise triangles, but no equality of chosen packages or inverse
  law for the comparison maps.
- `emdash3_2_commutative_algebra_localization_overlap.lp` derives both whole
  comparison-map cancellation paths by contractible factorization and
  packages the forward comparison as an `OmegaEquivAlong CommRing_cat` plus a
  first-class `OmegaEquiv` facade. It remains fraction-free and rule-free.
- `emdash3_2_commutative_algebra_presheaves.lp` transparently presents
  CommRing-valued presheaves, their actual structured restriction maps,
  pointwise identity/composition paths, and proposition-valued invertibility
  support along arrows. It assembles that support as a higher and ordinary
  sieve with literal membership computation, but no ringed site.
- `emdash3_2_commutative_algebra_locality.lp` packages selected localization
  factors over all elements of the invertibility sieve as one internal cone.
- `emdash3_2_commutative_algebra_matching.lp` sends localization elements and
  equality paths to coherent carrier-valued matching sections, with literal
  components computing by those selected factors.
- `emdash3_2_commutative_algebra_glue.lp` packages selected glue as a genuine
  functor on matching families and their arrows, together with two computing
  component observations. It is the rule-free Cartier/basic-open
  locality interface, not ordinary sheaf descent over a covering sieve or a
  native `OmegaEquivAlong`/whole internal equivalence.
- `emdash3_2_walking_end_hit.lp` owns the walking HIT, Code,
  encode/decode, Nat comparison, and directed negative results.
- `emdash3_2_checks.lp` and `examples/` contain executable
  regressions and reviewer-facing examples.
- `reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`
  explains the current architecture and safe implementation workflow.
- `reports/EMDASH_FOUNDATIONS.md` is the mathematician-facing guide.
- `reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`
  owns comment, example, and future parser notation.
- `reports/INDEX.md` indexes current plans and dated decision records.
- `AGENTS.md` contains mandatory repository-working rules.

The active one-way library extensions are:

- `emdash3_2_presheaves.lp` — Cat-valued presheaves, opposite-functor
  restriction, Yoneda, slices, and Cat-valued higher sieves;
- `emdash3_2_sieves.lp` — native subterminal categories, ordinary-sieve
  property packages, and pullback preservation;
- `emdash3_2_sites.lp` — direct ordinary-sieve Grothendieck topologies and the
  chaotic model, separate from generated coverages and sheafification;
- `emdash3_2_finite_families.lp` — reusable Nat/Sigma finite families,
  pointwise mapping, and sethood without a new inductive former;
- `emdash3_2_commutative_algebra.lp` — set-carrier commutative-ring objects,
  their operation/law projections, and the one-element zero-ring model;
- `emdash3_2_commutative_algebra_category.lp` — structured ring morphisms,
  morphism sethood/extensionality, the ordinary `CommRing_cat` facade, and
  stable pointwise identity/composition comparisons, without a carrier
  functor;
- `emdash3_2_commutative_algebra_product.lp` — rule-free componentwise product
  rings and structured maps, with whole identity/composition paths;
- `emdash3_2_commutative_algebra_f2.lp` — the closed two-element
  commutative-ring model on `Bool_grpd`;
- `emdash3_2_commutative_algebra_finite.lp` — finite sums/dot products and
  base-change-stable unimodular/Zariski-cover presentation data, separate from
  topology and polynomial syntax;
- `emdash3_2_commutative_algebra_polynomial.lp` — contractible-extension
  universal properties for free commutative `R`-algebras on variables,
  separate from concrete polynomial syntax and from topology;
- `emdash3_2_commutative_algebra_localization.lp` — explicit units and
  universal-property localization at one element, without fraction syntax;
- `emdash3_2_commutative_algebra_localization_unit.lp` — the rule-free
  identity localization of an already-unit element and the canonical
  localization at one for every ring;
- `emdash3_2_commutative_algebra_localization_zero.lp` — the rule-free
  universal localization at zero in the zero ring, providing the
  computational empty-basic-open case without fraction syntax;
- `emdash3_2_commutative_algebra_localization_idempotent.lp` — the rule-free
  fixed-image localization `R[1/e]=eR` for a supplied idempotent, with
  computing operations, structure map, and universal factors;
- `emdash3_2_commutative_algebra_localization_split.lp` — the rule-free
  `(1,0)` product localization and closed non-endpoint `F2 x F2` affine
  restriction computation;
- `emdash3_2_commutative_algebra_localization_comparison.lp` — stable
  pointwise ring-map composition plus universal-property iterated/product-
  localization comparison data, without fractions or package equality;
- `emdash3_2_commutative_algebra_localization_overlap.lp` — whole internal
  product/iterated cancellation, fixed-forward omega-equivalence evidence,
  and its first-class facade, without new runtime rules or fraction syntax;
- `emdash3_2_commutative_algebra_presheaves.lp` — transparent ring-valued
  presheaves, computational restriction, full-action carrier support, and the
  whole ordinary invertibility sieve, without topology or a sheaf package;
- `emdash3_2_commutative_algebra_locality.lp` — topology-visible support and
  the internal localization-factor cone over its category of elements;
- `emdash3_2_commutative_algebra_matching.lp` — coherent Pi matching families
  and computational restriction from localization elements;
- `emdash3_2_commutative_algebra_glue.lp` — selected functorial glue plus
  `glue(restrict(x))=x` and literal component recovery, without a whole
  internal equivalence, sheafhood, `Spec`, or scheme;
- `emdash3_2_eq1_hom_action.lp` — native equality-valued next-hom
  action and groupoidality;
- `emdash3_2_eq1_evidence_property.lp` — evidence-property,
  retract-truncation, and finite-category object truncation;
- `emdash3_2_nat_arithmetic.lp` — reusable Nat arithmetic and sethood;
- `emdash3_2_walking_end_hit.lp` — the selected WalkingEnd
  development.

The retired D0/D1 compatibility layer and obsolete v2/v3.1 scratch material
are not active interfaces.

## Quick start

Prerequisites: `lambdapi` on `PATH` and Node 22.13 or newer. From a
fresh worktree, initialize the shared pnpm workspace once:

```bash
../scripts/bootstrap-worktree.sh
```

```bash
EMDASH_TYPECHECK_TIMEOUT=60s make check
make examples
make ci
```

Useful focused commands:

```bash
scripts/probe.sh tmp/probes/name.lp
make check-warnings
make warning-summary
make audit-rules
make catalog
make toc
make health
```

Keep exploratory typechecks bounded. The current SOP explains rewrite,
unification, inferred-slot, and owner-position probing policy. CI checks the
stable source-metrics snapshot in the generated health report; run
`make health` after a change that alters those metrics.

## Functorial Type Theory book

The new book, *Functorial Type Theory: Univalent Foundations for Mathematics*,
is authored in `book/` as chapter-sized Markdown sources. It leads with
the WalkingEnd/Nat theorem and then adapts the prerequisite spine of the HoTT
Book to the directed setting.

```bash
../scripts/pnpmw run book:assemble
../scripts/pnpmw run book:check
../scripts/pnpmw run book:render
../scripts/pnpmw run book:release
```

`book/book.json` owns source order and metadata;
`book/evidence.json` maps checked prose claims to active declarations
and reviewer evidence. The generated
`print/public/emdash-book.md` is ignored and must not be edited by hand.
The release command produces and checks the ignored, versioned PDF declared by
the manifest; see `book/RELEASE.md` for its checksum and visual-QA policy.
See `book/README.md` and `print/README.md` for authoring and
renderer workflows.

## Status

Emdash v3.2 remains a research implementation. It does not yet claim a
finished surface parser, a complete weak omega-category metatheory, a full
computational univalence principle for every intended structure, or the full
initiality of the walking endomorphism. The living reports state these
boundaries precisely; dated reports preserve why earlier designs were chosen
or retired.
