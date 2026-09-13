# Family/Section Profile Collapse: Soundness Diagnostic

Date: 2026-09-12

Status: historical diagnostic; further investigation deferred by user direction

Parent: [native universality/homology plan](TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_AND_HOMOLOGY_PLAN.md), NUH-1B2g

Ledger: [native owner ledger](TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_OWNER_LEDGER.md)

Source: active nucleus blob `91f1974ece225e399604dce24710bf1437ad3ef5`

Subsequent user direction: do not continue this audit or make it a
prerequisite for the current native-universality/homology goal. Focus on
the [mathematical duality theory](TYPESCRIPT_EMDASH_DUALITY_SEMANTIC_THEORY.md).
The prototype strictness migration in
`goal/opaque-action-profile-classifiers-v3.2` will be integrated after that
goal. The experiment instructions and proposed next steps below are
historical evidence, not the active work queue.

## Finding

The current constant-section comparisons and unrestricted strict-naturality
interfaces together derive F(x)=F(y) for every ordinary F:K→A and every
p:x→y. Take K=A=Grpd, F=id and p:Empty→Unit. Equality transport then turns
the point of Unit into an inhabitant of Empty.

This is a mathematical incompatibility in the encoded interfaces. It does
not involve homology, exactness, chosen kernels/cokernels, the finite LES
indexing design, or the deferred symbolic endpoint checker experiment.
The reproducer adds no rule, unifier, primitive witness or axiom.

There are three recorded routes to the same collapse. The first consumes the
existing family-transport theorem. The second uses earlier object-level
ordinary naturality cuts. The third uses earlier stable-head ordinary
naturality comparisons and survives removal of the second route's two cuts.
Removing the late theorem alone is insufficient.

The strict-reference native-index calculations remain useful conditional
evidence. They do not qualify a generic family/section profile that already
admits this collapse. An unrestricted “all Functord maps are strict” reading
is incompatible with the current constant-section interface.

## Exact Conflict And Proof

The active source supplies all four ingredients:

1. An arbitrary F:Functor(K,A) also inhabits
   Functord(const_K(1),const_K(A)), and its ordinary Transf presentation.
2. The family component at k is the functor 1→A selecting F(k).
3. Constant-family transport along every p is the identity functor.
4. Unrestricted strict naturality identifies D(p)∘FF(x) and FF(y)∘E(p).

For E=const_K(1), D=const_K(A), FF=F, ingredient 4 therefore identifies
the two functors selecting F(x) and F(y). Evaluation at the unique point
of 1 gives F(x)=F(y) in Obj(A). This derivation uses ordinary equality
congruence, rather than treating a directed arrow as an equality by hand.

The final specialization is:

```text
p : Empty → Unit,        p = λ e, tt
F = id_Grpd
e : Empty = Unit         (from the endpoint theorem)
ind_eq(e, G ↦ G, tt) : Empty.
```

The equality eliminator in this source transports backwards, from the
family at the right endpoint to the family at the left endpoint. Its use
here is ordinary elimination of the equality produced by the incompatible
categorical laws.

Empty and Unit still have distinct normal forms. The control that rejects
`eq_refl(Empty) : Empty=Unit` passes even in the defective source. A negative
reflexivity/conversion test alone consequently does not certify consistency.

## Affected Owners

Locations below refer to the unchanged active source, not the staged prefixes.

| Owner | Active location and role | Required treatment |
| --- | --- | --- |
| Catd/Functord/Transfd facades | `emdash3_2.lp`, §3 around 5484–5610; linked to the ordinary functor/transfor hierarchy | Record which actual transformation profile each classifier contains; facades cannot erase a profile distinction |
| Constant section comparisons | §8b, around 12590; both Transf and Functord object classifiers compare with Functor(K,A) | Preserve arbitrary ordinary F and its action in the generic section interface |
| Constant-family transport | §8b, around 12638 | Keep identity family transport distinct from the section's own action |
| Constant-section component beta | §13, around 14885 | Retain the evaluation of the supplied F; moving this unchanged rule earlier suffices for the isolation |
| Ordinary strict naturality | §6d, around 11136–11281; whole, capped, stable-head and object-level routes | Migrate the connected profile assumptions together; changing one exposed theorem is insufficient |
| Family whole comparisons and paths | §16a, around 15479–15660 | Do not expose their equality types for an arbitrary displayed map |
| Displayed laxity | `fdapp1_int_cell` and `functord_laxity_transf`; existing native homd action | Retain the directed comparison and its higher action; do not replace it by generic endpoint equality |

The theorem-name inventory finds direct extension consumers in
`emdash3_2_dependent_simplex_ordinal_dimension3.lp`,
`emdash3_2_direct_cover_completion_hit.lp`,
`emdash3_2_pathout_transformation_reframing.lp`,
`emdash3_2_pathout_transformation_lift.lp` and
`emdash3_2_gray_interchanger_orientation.lp`, besides the central diagnostics.
This is a lexical inventory of explicit calls. Implicit use of rewrite or
unification rules has a larger dependency surface and must be checked at
the affected owner positions. No downstream migration is claimed here.

## Reproducible Isolation

The non-library fixtures are:

- [late family-theorem route](../emdash2/audits/family_section_strict_transport_empty_reproducer.lp);
- [earlier object-cut route](../emdash2/audits/family_section_object_cuts_empty_reproducer.lp);
- [earlier stable-head route](../emdash2/audits/family_section_stable_cuts_empty_reproducer.lp); and
- [ordinary section controls](../emdash2/audits/family_section_profile_controls.lp).

Run from `emdash2`:

```bash
bash scripts/check_family_section_profile.sh
```

The driver pins the current source and preserved preferred total-op patch.
It checks the late theorem route against an unchanged full-source copy.
For the earlier routes it applies that existing patch and truncates before
pointwise opposite-family formation, then copies the unchanged
constant-section component beta to the end of the dependency-complete
slice. Its `op` has the preferred shifted source. This slice contains no
declaration of Sigma_cat, Op_catd, homd_, or homd_int and no late
Functord-transport comparisons/theorems. It retains hom_int.

| Checked source | Recorded result |
| --- | --- |
| Unchanged active source | The late family theorem derives Empty |
| Preferred constant-family slice, original cuts retained | Earlier object cuts derive Empty |
| Same slice, two object-level naturality cuts subtracted | Object-cut proof rejected at its generic equality; stable-head proof still derives Empty |
| Same slice, those two cuts and two stable-head comparisons subtracted | Both recorded earlier proofs rejected at their generic equality comparisons |
| All three constant-family slices | Ordinary/visible section views, component evaluation, identity family transport, and forward ordinary Empty→Unit action check |

This establishes a source dependency isolation from the omitted
Sigma/native-Homd owners and from the old literal covariant-op signature.
It is not a consistency proof for the remaining prefix, a generic strict/lax
repair, or a claim that four deletions suffice. In particular, other whole
and capped globally strict naturality cuts are still present in the
subtraction variants and remain part of the connected migration obligation.
No variant is installed into the active kernel.

The durable run retained sources, raw logs, source hashes and completed
manifest under `/tmp/emdash-family-section-profile.GGJG5j`. The earlier
disposable exploration is under `/tmp/emdash-profile-collapse.qqis4fc3`.
The driver reconstructs the durable experiment without either directory.

All checker invocations were serial, subject-reduction enabled and bounded
by the repository resource guard. No repository-wide typecheck ran. The
active consumer reports the unchanged 1,144 critical-pair and 157 pattern
warnings. All three slices report 856 and 134 respectively; their complete
warning inventories agree after mapping unchanged source lines. Rule-free
positive consumer inventories agree exactly with their source variants.
The three slice LHS audits and four fixture audits pass, with zero
unreviewed slots. Identical warning counts across both accepting and
rejecting variants are further evidence that counts do not decide soundness.

These diagnostics are deliberately excluded from positive examples, the
library and generated feature catalogs. “Diagnostic checks passed” means
that the expected defect and discriminating rejections were reproduced.

## Selected Profile Direction

Preserve the generic directed section behavior. For a displayed map FF:E→D
and p:x→y, the intended generic interface retains

```text
D(p) ∘ FF(x) ⇒ FF(y) ∘ E(p).
```

For constant families its component is precisely F(p):F(x)→F(y). For
K=A=[1] and F=id, that arrow is noninvertible and has different endpoints.
This elementary case must survive any profile redesign. Making all fibre
categories ordinary does not make every Cat-valued displayed map strict:
the displayed comparison is still allowed to be that nonidentity arrow.

For an actually strict map, equality/computation of the two routes belongs
to its qualified strict interface. The generic classifier must not infer
strictness merely from the family endpoints or from an objectwise view.
A pseudo profile also does not license identity computation: an invertible
comparison can retain nonidentity data.

Endpoint equality alone is too weak to define the strict profile. In the
one-object category with endomorphisms {1,e} and e²=e≠1, the identity
functor has equal object values everywhere, but its constant-section
comparison at e is still the nonidentity e. The corresponding one-object
group {1,g}, g²=1, tests the separate pseudo case: the comparison is
invertible without being an identity. These are required semantic controls
for the next profile construction, alongside the walking-arrow case.

The next bounded design/implementation row must specify:

1. The generic, strict and opposite-profile transformation carriers, their
   inclusions/forgetful operations, and retained comparison cells. An
   explicit strict carrier or a checked inclusion is a possible mechanism;
   its exact native signature is not yet selected.
2. Which existing whole Hom, section, evaluation, currying and composition
   owners act on which profiles. No blanket identification of different
   profiles through existing facade unifiers is allowed.
3. The profile change induced by O/R/T and their shifted universe actions.
   The strict-reference dimension arithmetic remains conditional evidence;
   it cannot manufacture inverse laxity for arbitrary inputs.
4. The profile of native homd_int's supplied E/D/FF and supporting index.
   Preserve native syntactic ownership and the source ladder. Neither a
   total-category definition nor a replacement-family premise resolves
   this profile obligation.

Start with the constant-section cases above and a represented strict map,
retaining their nonidentity action. Test the entire connected naturality
family, including the late whole comparisons, against the Empty witnesses
before proposing a full native integration. Later restore only the strict
operations that have an actual mathematical construction and matching
higher action.

This scoped prerequisite does not authorize integrating the unrelated
in-flight strictness branch. It follows from the affected native family
interface itself. Keep the spectral and symbolic endpoint deferrals intact.
