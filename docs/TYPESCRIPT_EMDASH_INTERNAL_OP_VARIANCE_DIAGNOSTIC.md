# Internal Opposite: Confirmed Variance And Empty-Type Diagnostic

Date: 2026-09-08

Status: confirmed inherited soundness defect; repair architecture requires review

Parent: [strict internal homology pilot](TYPESCRIPT_EMDASH_STRICT_INTERNAL_HOMOLOGY_PILOT_PLAN.md)

Related: [foundational variance-owner inventory](TYPESCRIPT_EMDASH_HOMOLOGY_VARIANCE_OWNER_AUDIT.md)

## Finding

The committed categorical encoding accepts a closed defined term of
`τ Empty_grpd`. That classifier decodes to the native inductive `empty`,
which has no constructors. The reproducer uses only the committed kernel;
it adds no rewrite, unification rule, primitive witness or extra axiom.

This is a soundness defect of the current categorical encoding, not a report
of a Lambdapi checker implementation defect. Lambdapi is checking a term
against the supplied declarations and rules. Their combination is too strong.
Passing existing checks therefore remains evidence of elaboration and
computation, not evidence that the encoded theory is consistent.

The current structural-action prototypes were not promoted. They are not
needed by the counterexample. The defect also reproduces at the original
long-exact baseline and on the separate post-migration branch.

## Exact Reproduction

The tracked, explicitly non-library fixture is
[internal_op_empty_reproducer.lp](../emdash2/audits/internal_op_empty_reproducer.lp).
From `emdash2`:

```bash
scripts/probe.sh audits/internal_op_empty_reproducer.lp
```

Acceptance currently reproduces the defect. The fixture is intentionally
outside the positive source/reviewer registries. It must not be imported
into the mathematical library. After repair, the derivation must fail for
the correct variance reason, while positive companion tests confirm that
the kernel and legitimate opposite operations still work; a syntax error,
missing import or timeout is not evidence of a repair.

The proof defines an operation

```text
reverse_C : Hom_C(x,y) → Hom_C(y,x)
```

for an arbitrary C. Specializing C to `Grpd_cat` and reversing the ordinary
constant function `Empty_grpd → Unit_grpd` gives a function
`Unit_grpd → Empty_grpd`. Applying that function to `tt` produces the
closed empty-type witness.

`Grpd_cat` is used here as a category, not as a groupoid. Its objects are
groupoid/type classifiers; its arrows decode to ordinary functions. The
function Empty→Unit need not be invertible. The diagnostic does not prove
or assume that the constructed reverse is an inverse: any function
Unit→Empty already produces an empty-type inhabitant when applied to `tt`.
`internal_op_arrow_reverse` is a new transparent diagnostic definition, not
a primitive or an axiom added to the kernel.

## Why The Declared Variance Forces This

The active kernel simultaneously provides:

1. `Hom_cat Cat_cat A B = Functor_cat A B`, with genuine directed
   transformations in these functor categories;
2. a covariant whole `op : Functor Cat_cat Cat_cat`;
3. object action `op[A] → Op_cat A` and first action `op[F] → Op_func F`;
4. the generic whole hom action of every functor and its object projection;
5. ordinary point-selection functors, constant transformations and component
   evaluation; and
6. `Hom_{Cᵒᵖ}(x,y) = Hom_C(y,x)`.

For f:x→y, use the point functors X,Y:1→C and the constant transformation
f:X⇒Y. Covariant whole hom action of `op` gives a functor

```text
Functor(1,C) → Functor(1,Cᵒᵖ)
```

whose object images are Xᵒᵖ and Yᵒᵖ. It consequently maps f to a
transformation Xᵒᵖ⇒Yᵒᵖ. Its component is an arrow x→y in Cᵒᵖ, hence an
arrow y→x in C. This is the reverse operation used above.

But the ordinary opposite of f:X⇒Y has direction Yᵒᵖ⇒Xᵒᵖ. The existing
`Op_transf` correctly records that direction. The problem is packaging the
same pointwise opposite as a covariant whole functor on the fully directed
`Cat_cat`, which forces a different higher action.

This mismatch is visible even before questions about associativity, cut
orientation or computation of a laxity witness. Changing implicit guards,
making a head opaque, adding a leaf con alias, or switching global strictness
rules does not by itself correct the declared higher variance.

The distinction from ordinary category theory matters. Sending C to Cᵒᵖ
and F to Fᵒᵖ is a covariant functor on the **1-category** of categories and
functors. The current `Cat_cat` is not that truncation: its Hom categories
are directed `Functor_cat` values, so it also forces action on transformations.
At that level the opposite operation reverses their direction.

## Baseline Controls

All runs use the 90-second per-target bound with ordinary subject-reduction
checking. Source copies were read from clean core files; neither reference
worktree was changed.

| Core source | Reference | Reproducer result |
|---|---|---|
| current long-exact branch | `6fc0b02ef84f362e574855609871cc199c874128` | accepted; `hint_internal_op_empty_audit-20260908-133704.log` |
| original main/goal baseline | `054b43bd777d260f5da8b1242294ce0335780d0d` | accepted; `hint_internal_op_empty_baseline-20260908-134357.log` |
| separate post-migration tip | `114dc19fdee4b952f1c75be4e2000d6ff7195741` | accepted; `hint_internal_op_empty_parallel-20260908-134552.log` |

Logs are under `emdash2/logs/probes/`. The copied-core controls and earlier
walking-arrow reversal experiment remain under `emdash2/tmp/probes/`.
The walking-arrow reverse Hom has no empty normal form in the current join
scaffold, so that experiment alone was not called a contradiction. The
`Grpd_cat` specialization supplies the decisive native-empty witness.

## Consequences For The Active Goal

- The classical homological constructions and native CAS algorithms are not
  refuted by this diagnostic. Their existing implementation and independent
  differential evidence remain useful reference material.
- Kernel typechecking alone cannot currently certify the mathematical
  validity of encoded proofs. Do not call the whole proof–CAS formal boundary
  sound or the long-exact goal complete under this signature.
- Pause promotion of the new higher-opposite-dependent structural/homology
  rules. Preserve their checked computations, failed alternatives and
  orientation audit as experiments, not a qualified final calculus.
- The ordinary con-owner port is not the origin: the original baseline
  already admits the witness. The parallel strictness migration is not a
  repair either, as the independent control shows.
- Do not merge parallel branches, publish artifacts, rewrite checkpoints or
  delete reference implementations in response to this finding.

## Recommended Repair Direction — Not Yet Implemented

The [bounded repair plan](TYPESCRIPT_EMDASH_INTERNAL_OP_VARIANCE_REPAIR_PLAN.md)
now records a checked non-library Co₂/whole-action prototype. It also records
a stronger copied-core control: removing the literal `op` declaration and
its six direct rules still leaves `Op_catd(id_Cat)` able to reconstruct the
same bad covariant operation and derive the native empty type. No kernel
repair is promoted; unrestricted same-base opposite-family formation must
be migrated together with the universe-level source.

Preserve the intended directed functor categories and correct the variance of
internal opposite. In the elementary 2-categorical reading, the required
source is a co-opposite universe:

```text
op : Catᶜᵒ → Cat,
```

where co reverses 2-cells, not the direction of functors. The corresponding
higher-dimensional formulation must make the degree of duality explicit.
This is a signature/design change, not simply another normalization rule.
The complete omega/transfor profile and computation package still requires
review and prototypes; the sketch is not claimed as an implemented fix.
The op/co distinction is the standard one reviewed in Stephen Lack,
[A 2-categories companion, §1.6](https://arxiv.org/pdf/math/0702535#page=7).
The proposed source for internal opposite follows from the transformation
directions above; that reference is not a claimed proof of an emdash repair.

Audit at least `op`, `Op_catd_func`, `Op_catd`, `Op_funcd`, the mixed-family
constructors and the dependent internal-Hom/laxity ladders. In particular,
pointwise fibre opposite, base reversal and reversal of higher transformations
must not be conflated. A same-base pointwise opposite may require a restricted
base/coherence profile or a correspondingly dualized base.

A deliberately restricted universe with suitable invertible higher cells is
another possible boundary, but globally replacing all directed functor Homs
by groupoids would change the project's intended foundation. It should not
be adopted merely to hide the counterexample. Nor should the empty type,
generic higher hom action, or the whole-to-point projection be weakened just
to prevent this particular proof from checking.

The recommended next tranche is an isolated variance-repair design and its
positive/negative conformance suite, followed by propagation to the affected
families. The original bounded long-exact objective stays intact, but the
repair is a prerequisite before formal qualification and final book claims.

## Current Design Candidates After This Finding

| Candidate | Current status | Role after repair |
|---|---|---|
| existing factor-space/path homology and snake construction | committed working reference implementation | preserve algorithms, selected objects and proof bodies for comparison; current typing is not a soundness certificate |
| shape-only walking/ordinal diagrams | whole evaluation and some introductions implemented | complementary indexing route; no all-shape/native equivalence assumed |
| native fixed-flag zero-triangles and cubical map boundaries | compatibility layer committed at `febf287d` | retain as local data/variance evidence, not a global complex category |
| native PathOut plus varying walking-arrow diagrams | leading bounded-complex prototype; canonical nonidentity edge computation checked experimentally | most likely homology representation if it survives the corrected variance/coherence requirements |
| independent primitive homology/snake mirror grammar | not selected | no need established; do not replace internal Homs by manually stored commuting diagrams |

Thus the likely homology shape has become clearer, but the final foundation
is not settled. The variance repair must precede further claims that the
hybrid prototype is a correct complete computational-and-internal calculus.
