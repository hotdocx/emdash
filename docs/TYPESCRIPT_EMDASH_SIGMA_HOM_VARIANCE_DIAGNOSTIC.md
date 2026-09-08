# Sigma Hom: Independent Constant-Family Soundness Diagnostic

Date: 2026-09-08

Status: inherited empty-type derivation confirmed; correction remains a prototype

Parent: [foundational variance repair](TYPESCRIPT_EMDASH_INTERNAL_OP_VARIANCE_REPAIR_PLAN.md)

Related: [internal-op diagnostic](TYPESCRIPT_EMDASH_INTERNAL_OP_VARIANCE_DIAGNOSTIC.md)

## Finding

The active Sigma-Hom rule and constant-family product rule together admit a
second closed inhabitant of `τ Empty_grpd`. The tracked non-library
[reproducer](../emdash2/audits/sigma_hom_empty_reproducer.lp) adds only
transparent definitions. It introduces no rewrite, unifier, primitive
functor, equality axiom or opaque proof. Its terms do not call the whole
`op` or a pointwise opposite-family constructor.

This is a defect in the encoded categorical signature/rules, not an assertion
that Lambdapi's implementation is defective. The independent controls below
also show that it predates the current homology/Co₂ prototype work.

## The Conflicting Whole-Category Readings

The current nucleus declares, in its Sigma-total section:

```text
Sigma(const_K(C)) → K × C
Hom_(Sigma E)((x,u),(y,v)) → Op(Sigma(homd_(id_E,x,u,y,v))).
```

The dependent-Hom family on the right is indexed by Hom_K(x,y)ᵒᵖ, and its
fibre at p is Hom_E[y](E[p](u),v). The outer opposite reverses the base
direction but also reverses fibre arrows; there is no compensating fibre
duality in that rule.

Specialize K to the terminal category and E to const_1(C). The product route
gives `1 × Hom_C(u,v)`. The generic Sigma-Hom route gives
`1 × Op(Hom_C(u,v))`. Those are not generally the same higher category.
The mismatch is invisible in their object carriers and becomes visible in
higher arrows. Thus checking the pair (p,alpha) alone is insufficient.

## Closed Derivation, Not Merely A Warning

For an arbitrary E, the generic Sigma-Hom rule lets the identity functor of
its right-hand category check as a functor from its left-hand category. A
typed reflexivity proof establishes that its object action is identity.
Specializing these already-checked definitions to a constant E supplies a
functor

```text
1 × Hom_C(u,v) → 1 × Op(Hom_C(u,v))
```

with paths fixing its objects. Mapping an arrow and adjusting its endpoints
by those paths then yields an arrow with reversed direction in Hom_C(u,v).
All adjustments use existing core inclusion, path symmetry and composition;
they are diagnostic proof terms, not a new implementation equality bridge.

Take C to be Cat_cat, u the terminal category and v an arbitrary category D.
Then Hom_C(u,v) is Functor_cat(1,D). Constant point functors and constant
transformations turn the construction into

```text
reverse_D : Hom_D(x,y) → Hom_D(y,x).
```

Finally take D = Grpd_cat, reverse the ordinary function Empty → Unit, and
apply the resulting function Unit → Empty to tt. Lambdapi accepts the closed
empty-type term. No groupoidality of Grpd_cat is assumed. The diagnostic does
not require the constructed reverse to be an inverse.

## Controls And Exact Evidence

All runs use the ordinary subject-reduction checker and a 90-second per-target
limit. Reference worktrees are unchanged.

| Core | Result and log under emdash2/logs/probes |
|---|---|
| current nucleus at `b21ec9c2` | accepted: `sigma_hom_empty_reproducer-20260908-155454.log` |
| original baseline `054b43bd` | accepted: `hint_sigma_hom_empty_baseline-20260908-155455.log` |
| parallel post-migration `114dc19f` | accepted: `hint_sigma_hom_empty_parallel-20260908-155456.log` |
| copied current core with literal op and its six direct rules removed | accepted: `hint_sigma_hom_empty_no_literal_op-20260908-155458.log` |

The baseline and parallel source-copy hashes match their exact Git blobs.
The earlier generic category-path and point-law probes remain under ignored
`tmp/probes/hint_sigma_hom_*` paths. The tracked reproducer is self-contained
over the nucleus and does not depend on those ignored modules.

After repair this derivation must fail for the repaired Sigma-Hom reason,
while positive companions still check. A timeout, syntax error or missing
import does not establish repair. Keep it outside positive library registries.

## Narrow Correction Candidate

The [contravariant-totalization prototype](../emdash2/audits/contravariant_sigma_total_dual_prototype.lp)
uses the separately probed total dual All and its shifted dual CoAll:

```text
H : Op(K) → Cat
Sigma_con(H) = All(Sigma(All_catd(H))).
```

Here All_catd(H) has base CoAll(Op(K)), and total-dualizing the total gives a
whole projection to `All(CoAll(Op(K))) = K`. Both the base and the fibre are
dualized coherently. No new primitive Sigma_con constructor is added.

The local checks establish:

- Sigma_con(const_(Op K)(C)) computes to K × C, not K × Op(C);
- the unchanged object pair (k,h) projects to k;
- the projection retains a further whole Hom action; and
- using Sigma_con(homd_(...)) gives the correct terminal-base constant-family
  Hom and does not convert to the old flipped-fibre reading.

The initial four positive and one negative checks pass in
`hint_contravariant_sigma_total_dual-20260908-155913.log`. This is necessary
constant-family and typing evidence, not a complete repair: the imported
kernel still contains the old Sigma rule. Recursive Sigma Hom, projection,
map/action, composition and consumer qualification remain to be migrated and
checked together.

The tracked companion also passes with warnings enabled in
`contravariant_sigma_total_dual_prototype-20260908-161119.log`: 1,212
critical pairs / 157 pattern reports, unchanged from its imported
total-duality prototype, with complete parser accounting. Both new audit
files pass the strict inferred-LHS check and are absent from the positive
source registries. Active-reference and report-lifecycle checks pass. No
kernel/library code or generated book/catalogue/health artifact is modified
by this diagnostic checkpoint.

## Consequences For The Long-Exact Goal

The op repair alone cannot qualify the foundation. The Sigma-Hom repair is
also required before rebuilding the dependent-Hom target on total-category
operations. Retain all original CAS/reference implementations and book draft
evidence, but do not treat their current formal typechecking as a consistency
certificate. Do not narrow the original long-exact objective or replace
arbitrary families by extra regraded-family assumptions.

No active kernel rule is changed by this diagnostic tranche. No parallel
branch is merged, no artifact is published and no unrelated aggregate is run.
