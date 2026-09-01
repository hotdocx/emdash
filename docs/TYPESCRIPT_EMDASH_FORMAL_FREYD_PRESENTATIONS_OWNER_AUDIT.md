# Formal Freyd Presentations Owner And Boundary Audit

Date: 2026-09-01

Plan-ID: `TS-EMDASH-FORMAL-FREYD-PRESENTATIONS`

Status: completed categorical skeleton audit; explicit class-level descent and
Abelian structure remain separately gated

## Audited Authorities

- `emdash2/emdash3_2_commutative_algebra_category.lp`
- `emdash2/emdash3_2_commutative_algebra_presentations.lp`
- `emdash2/emdash3_2_groupoidification_hit.lp`
- `emdash2/emdash3_2_groupoidification_universality.lp`
- `emdash2/emdash3_2_truncation_reflector.lp`
- `src/v3_2/algebra_polynomial_presentation_morphism.ts`
- `src/v3_2/algebra_polynomial_freyd_category.ts`

## Finite-Free Category Probe

The transparent recursive identity matrix checks and exposes the expected
rank-one column. A warning-enabled follow-up audit refines the original
timeout diagnosis: runtime identity checks, and runtime composition to a rigid
matrix head also checks quickly. The 90-second failure is specifically the
rule reducing generic `comp_fapp0` directly to the transparent
`comm_ring_matrix_comp` body. Its overlap with strict functoriality unfolds
Nat recursion, finite families, vectors, and the commutative-ring record while
local confluence compares the two branches.

The rigid runtime composition candidate reports twenty higher-action critical
pairs. This count is not a veto; it identifies genuine competing normal forms
that need consumer-driven joins. Replacing the plain source/middle/target
variables by `_` fails type preservation, so those dimensions are justified
interface data rather than compound reducible guards. The promoted rules and
unifiers have no unreviewed compound inferred slots.

The selected owner mirrors `CommRing_cat`:

- `Obj(CommRingFiniteFree_cat R)` computes to `Nat_grpd`;
- `Hom(n,m)` computes to `Path_cat(CommRingMatrix R m n)`;
- generic category identity/composition remain runtime owners;
- rigid pointwise identity/composition matrix heads meet them through
  proof-time unifiers and `eq_refl` theorem views; and
- constructor-level `sigma_Fst`/`sigma_Snd` rules expose the matrix columns.

A direct unifier between the rigid composition head and the transparent
Nat-recursive `comm_ring_matrix_comp` body did not establish the whole
comparison after unfolding. A defined readable alias does not remain a rigid
unification discriminator, and an immediately following `eq_refl` theorem
cannot make that missing comparison true. That equality is not postulated.
The rigid head is the finite-free category's selected representation; the
older transparent operation remains the direct presentation/CAS surface. A
constructed finite-family path between them is the next formal prerequisite.

## Homwise Quotient Construction

At fixed presentations `P,Q`, the agreement category has raw morphisms as
objects and path categories of explicit `H` agreement data as Homs. No custom
quotient HIT is introduced. Existing `Groupoidify` turns all such arrows into
paths, and `Trunc_grpd trunc_zero` makes ordinary Hom equality
proposition-valued.

The class map and agreement-path functions check. The untruncated groupoid
retains higher witness/syzygy information; the truncated Hom is the ordinary
category carrier.

## Freyd And Representable Boundaries

`CommRingFreydPresentation_cat R` has presentation objects and the quotient
Hom sets. The relation-free rank-one presentation defines elements
representably. Agreement between raw rank-one-source maps produces element
equality through the same homwise quotient.

The generic category head supplies Freyd identity and composition, but this
tranche does not construct the proof that they equal classes of explicit raw
identity/composition representatives. That descent requires a functorial
binary raw-composition operation over agreement categories plus
groupoidification/truncation recursion. Preadditivity and biproducts depend on
the same missing class-level descent and remain explicit follow-up work.

## Computational And Abelian Boundaries

The TypeScript direct category computes raw identity/composition and uses
target-factorization congruence as equality. Its representable-element view
matches module membership. Graph/compiler execution preserves whole
relation-witness bytes.

Operational-field polynomial rings expose a Gröbner/syzygy weak-kernel
capability record, but no formal theorem currently turns it into weak kernels
of the finite-free category or Abelian structure on the Freyd category. The
constructive weak-kernel-to-Abelian theorem is the next categorical capability
goal, after explicit quotient-class identity/composition descent.
