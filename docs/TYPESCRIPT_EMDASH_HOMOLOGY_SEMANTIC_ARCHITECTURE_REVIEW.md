# Semantic Architecture: Universality, Duality, Homology And Computation

Date: 2026-09-12

Status: proposed semantic design and further review; no implementation migration started

Parent: [homology retrospective](TYPESCRIPT_EMDASH_HOMOLOGY_RETROSPECTIVE_REVIEW.md)

Governing implementation ledger: [bounded long-exact plan](TYPESCRIPT_EMDASH_BOUNDED_LONG_EXACT_HOMOLOGY_AND_BOOK_PLAN.md)

## Current Architectural Corrections

The user's further clarification on 2026-09-12 fixes three design choices.
These supersede the earlier review's contrary recommendations:

1. At the computational-and-internal formal layer, whole categorical
   universality and Došen-style operations are primary. A mathematically
   valid pointwise IsContr/cone characterization does not justify making
   manual cone construction and factor manipulation the formal programming
   interface. Such characterizations can support interpretation, verification
   and derived observations.
2. `hom_int` and `homd_int` retain foundational syntactic ownership, including
   their internalized dependency and higher-action ladders. A total-category
   Hom projection is a derived view/comparison or semantic check. It must not
   replace these foundations or become a second dependent-Hom calculus.
3. The proposed simplicial generalization fixes ONE endpoint c and varies
   the other. The identity at c provides the distinguished point. The earlier
   two-pole suspension example was not an adequate formulation of that idea.

The goal is to generalize the role of endomorphisms to an internal dependent
Hom family and its simplicial iteration. Whether the resulting stabilization
and representability results generalize all of Heine's theory is a research
objective, not an established consequence of the existing constructors.

## Revised Recommendation

Write and review the semantic specification before resuming the opposite or
dependent-Hom migration. The last review's instruction to resume at the
failed owner is a recovery locator, not the best design sequence. A local
typing failure should be evaluated against a chosen global mathematical
meaning, rather than determine that meaning one patch at a time.

The proposed architecture has four connected layers:

1. The existing internalized `hom_int`/`homd_int` foundations, with explicit
   variance and transformation profiles; total-category constructions remain
   derived applications and comparison interfaces.
2. Whole universal constructions and coherent diagram categories, with
   ordinary Abelian homology as a locally discrete specialization.
3. Effective algebra implementations, connected through reusable model and
   representation contracts rather than per-example hand assembly.
4. Derived, stable and potentially directed spectral extensions, with
   specified comparison functors to the ordinary and groupoidal cases.

This is a coherent semantic design target with concrete reference models.
It is not a claim that every existing emdash declaration already has that
interpretation, or a consistency proof for the unrepaired kernel. In
particular, the strict and Gray profiles below cannot be silently identified.

## 1. Whole Categorical Universality Owns Formal Computation

### Formal ownership and ordinary mathematical interpretation

The desired formal primitive structure is the whole universal operation,
expressed through emdash's existing adjunction and internal-Hom calculus.
For kernels and cokernels its familiar ordinary interpretation is

```text
J(X)=(X→0),       J ⊣ K
I(X)=(0→X),       Q ⊣ I

κ:K⇒domain       from the counit of J ⊣ K
q:codomain⇒Q     from the unit of Q ⊣ I.
```

The arrow/diagram category here must have the profile appropriate to the
claimed universal construction. Its native internal Hom supplies the maps;
the author should not reconstruct an independent record of commuting
squares for each application.

Whole mate functors, unit/counit observations and the generic Došen cuts
then supply factorization, reconstruction and composition. For example,
an existing native diagram arrow h:J(X)→d has mate K(h)∘ηₓ:X→K(d).
The whole Hom comparison, not a pointwise factor-selector callback, owns
that operation. For a coherent family this remains the whole construction
β=K(h)∘η and H=Q∘Arr(β).

The proposed dependency is

```text
whole universal structure and its computational observations
  → formal H, induced maps, connecting and structural theorems
  → derived ordinary factor/contraction views where needed
  ↔ interpretation in the selected CAS algorithms.
```

The following elementary characterization explains the ordinary semantics;
it is not the proposed formal authoring interface.

For f:A→B, a kernel k:K→A has f∘k=0 and unique factorization:

```text
for every X and u:X→A with f∘u=0,
there is a unique v:X→K with k∘v=u.
```

When Hom sets are sets, this is equivalently contractibility of the factor
fibre. That makes IsContr useful for constructive semantics and verification.
It does not make it the preferred computational owner at the formal layer.
The paths compare parallel module maps; they do not assert that arbitrary
module maps are invertible.

The active [kernel/cokernel records](../emdash2/emdash3_2_kernels_cokernels.lp)
use exactly this sort of factor space. The formal Freyd Hom-category rule
is `Path_cat(CommRingFreydHomSet(...))`, so this ordinary reading has an
explicit local justification. It is stronger evidence than sethood of
the object collection of some arbitrary higher Hom category.

The account by a terminal object among annihilating arrows is also a valid
semantic characterization. The formal calculus should expose that
universality as whole categorical structure with computation, rather than
make each homological construction manually chase its cone records.

### What the current implementation has and what still needs redesign

The [generic mate module](../emdash2/emdash3_2_adjunction_mates.lp) already
provides whole functors with whole/point cancellation. H already has the
desired composite definition. Those are foundations to reuse.

However, [KernelPresentation](../emdash2/emdash3_2_kernel_adjunction_presentations.lp)
is indexed by the older selected operation family W. The
[whole-owned record adapter](../emdash2/emdash3_2_kernel_adjunction_records.lp)
defines its lift by applying mate to unmate of an old W-selected lift; its
contractibility proof is transferred from the old record and recentered.
This preserves selections and endpoints, but it is not a completed inversion
of the dependency between whole universality and the old factor API.

The proposed refactor separates the formal whole K/Q structure from its
realization over W/V. Derived compatibility modules can retain the existing
CAS choices. Ordinary contraction evidence should then follow from the
whole universal comparison at the appropriate profile, rather than be a
prerequisite through which every formal construction must operate.

In particular, forming a native complex input should not need a kernel
selection merely to turn that input into a diagram. Its structural
differential/zero data should produce the relevant native homd/diagram
object, after which the whole mate constructs the boundary into cycles.
The current inverse-mate raw-input adapter remains comparison evidence, not
the architectural requirement for the new primary input interface.

There is no need to delete valid old proofs or forbid equality everywhere.
Earlier approved plans explicitly retained contractible factor views and
path-valued laws. The user's current direction strengthens the primary
formal architecture; it does not retroactively show that every use of
IsContr violated an explicit SOP rule. The relevant SOP requires native
whole owners and generic action, and supports this ownership correction.

Nor does packaging K/Q as adjunctions make every Abelian exactness argument
an automatic normalization result. A computational exactness/connecting
package must still justify its normality and interaction laws. The design
task is to internalize these constructions and proofs around whole owners,
not assert exactness through an unjustified rewrite.

### Higher groupoidal and directed settings

In an (∞,1)-category, mapping spaces are groupoidal, and equivalences of
mapping spaces or contractible homotopy fibres are still the right way to
express universality. Here the fibre must retain the entire cone, including
its nullhomotopy and its compatibility under factorization.

For a homotopy kernel, the intended comparison is

```text
Map(X,K) ≃ Fib(Map(X,A) → Map(X,B), 0).
```

The right side includes both u:X→A and a specified nullhomotopy of f∘u.
Taking a factor fibre over u alone forgets that information. This is a
relevant limitation of extrapolating the current ordinary record: its
`KernelFactorSpace` is a fibre over the underlying arrow, while the supplied
annihilation proof is not part of that fibre's equality target. In Hom sets
the missing higher compatibility is propositionally automatic. It is not
automatic in a general mapping space. For example, the homotopy fibre of
0→B in a pointed stable setting is ΩB; an ordinary kernel intuition would
lose precisely that loop information.

For genuinely directed higher Homs, require the full categorical comparison:

```text
Hom𝒞(X,K) ≃ the category of the chosen kind of cones from X to f.
```

Specify whether these are strict, pseudo or lax cones, and require the
comparison naturally in X, with its higher action. A strict enriched limit
uses the corresponding strict representing isomorphism; a weak limit uses
the appropriate equivalence. A lax kernel, a homotopy fibre and an ordinary
kernel are not interchangeable names for this datum.

Contractibility of the object collection or core of a directed factor
category does not establish that comparison. A one-object category with
endomorphism monoid ℕ has a singleton object set and a trivial core, but
retains nonidentity directed endomorphisms. Conversely a category can have
a terminal object without being equivalent to the terminal category.
Neither `IsContr(Obj(Factors))` nor mere contractibility of its nerve is a
substitute for the required representability statement.

### Equality remains useful

| Expression | Appropriate use |
| --- | --- |
| Equality in Hom(X,Y) when that Hom is a set | Ordinary commuting diagrams, zero equations, universal uniqueness |
| Paths in a mapping space | Invertible homotopies and their higher coherences |
| A directed 2-cell f⇒g | Lax comparison, which need not imply equality or invertibility |
| Isomorphism/equivalence of selected objects | Relating different universal choices |
| Equality in Obj(𝒞) | Actual object equality, or a justified univalence image; not an arbitrary replacement for an isomorphism |
| Runtime conversion | Deliberately selected computational equations, not all mathematical equivalences |

The goal is to centralize and expose the right mathematics, not eliminate
every `@=` spelling. Selected whole K/Q/H objects should be the operational
endpoints; paths can prove their laws without rebuilding those endpoints.

There is a relevant assembly principle in the supplied Cisinski–Cnossen–
Nguyen–Walde draft. Its §5.9 explicitly introduces a functoriality-of-universals
**axiom**, and derives an objectwise adjoint criterion from it. It requires
an actual fibration and supplies comparisons with chosen fibre universals.
This is useful semantic guidance, not an already proved emdash constructor
or a promise of literal equality of all chosen representations. The inspected
dated source is [the September 7 text](/home/user1/algebraic-geometry/cisinski-Book-project-Synthetic-Category-Theory-2026-sep-7.txt),
§5.9 and Theorem 5.9.12.

## 2. The Two Previous Failures Have Different Diagnoses

The small additive-law reproducer shows that the resource failure does not
require the chosen homology, kernel/cokernel or connecting algorithms. It
does **not** show that all representation choices are irrelevant: the
problem still occurs at native zero-cone/Sigma projections used by those
representations. Another layout could expose a cheaper comparison.

The justified conclusion is that switching between snake and direct
connecting is not a demonstrated remedy. Investigate the shared observation
and conversion layer. There is no evidence that a different mathematical
definition of homology is needed. Nor has a common cause been established
between this resource failure and the independent Sigma variance defect
merely because both involve Sigma machinery.

The `Homd_target_section_catd` failure is different. Under the repaired
duality meanings, the old composite requires a family over R(Z), while its
input E is a family over Z. Its rejection is a real semantic type mismatch,
not an expensive comparison of known-equivalent terms. Earlier wrong
explicit annotations were mechanical issues; the surviving base mismatch
was not. Identifying R(Z) with Z for arbitrary Z would erase genuine higher
variance. The [repair history](TYPESCRIPT_EMDASH_INTERNAL_OP_VARIANCE_REPAIR_PLAN.md#total-op-prefix-preserved-result-at-deferral)
records this distinction.

This refutes reuse of that particular old target expression with the new
meanings. It does not refute the native dependent-Hom constructor. Repair
its variance and supporting target presentation while retaining
`homd_int`/`hom_int` as foundations. Derived total-category views can help
check that repair without taking over its ownership.

## 3. A Coherent Duality And Dependent-Hom Story

### Specify the transformation environment first

There are compatible reference settings, rather than one unqualified
functor category with every interpretation at once:

- Strict ω-categories, strict ω-functors and strict higher transformations
  have the cartesian-enriched reference interpretation.
- Strict ω-categories with oplax transformations organize into a Gray
  ω-category. The lax variant has the corresponding opposite enrichment
  convention. Noninvertible interchange is retained.

Ara–Guetta develops these distinctions, the compatible dualities and the
comma/Grothendieck constructions. Its total dual is monoidal for the Gray
tensor; not every dimension-selected duality is monoidal or anti-monoidal.
See [§§2.22–2.27 and §§3,7](https://arxiv.org/pdf/2503.08832v3).

The semantic specification should assign every generic constructor to an
environment and an ambient universe level. Strict-profile inclusions can
reuse the broader vocabulary, but no rule may implicitly turn arbitrary
lax naturality into strict naturality. Likewise, a Gray universe of
categories must not be treated as a strict ω-category merely because its
objects happen to be strict ω-categories.

### A general variance law, with a small public vocabulary

For semantic bookkeeping, let Dₛ reverse the dimensions in S. Its Hom law
removes one dimension from the index set and swaps endpoints exactly when
1 belongs to S. Composition of dualities is symmetric difference of the
reversal sets. This describes directions; compatibility with the selected
tensor/transformation environment is a separate required condition.

The preferred public operations remain:

```text
O : total reversal, dimensions 1,2,3,…
R : homwise O, dimensions 2,3,4,…
T : R∘O, reversal of dimension 1 only

Hom(OC,x,y) = O(Hom(C,y,x))
Hom(RC,x,y) = O(Hom(C,x,y))
Hom(TC,x,y) = Hom(C,y,x).
```

In the appropriate universe the total opposite has type

```text
op : R(Cat) → Cat
O(Fun(A,B)) ≃ Fun(OA,OB).
```

The second comparison uses the matching transformation profile. Functors
retain their direction; transformations and modifications change as dictated
by their components. None of this creates reverse arrows inside C.

Two further precautions make this a global account:

1. O/R are a useful small basis for this repair, not a complete kit of all
   higher dualities. They do not generate the odd/even reversal masks.
   If R itself is internalized as a whole operation in a strict-cartesian
   universe, its source variance shifts again, to dimensions 3 and above.
   More generally, internalization shifts S to {s+1 : s∈S}. The semantic
   ledger must track these shifts even if the implementation derives them
   through generic Hom-level constructions instead of adding public names.
2. Applying R to the objects of a lax functor category does not automatically
   give a same-profile enriched operator between the dualized categories.
   At low dimensions fibre co-duality can exchange lax and oplax naturality.
   Each such operator needs the correct profile, not just plausible object
   and component formulas. The prefix prototype's checked projections are
   evidence to audit against this requirement, not a substitute for it.

This level-aware, profile-aware rule is more important than choosing between
the spellings `Op2` and `CoAbove2`.

### Families and total categories are distinct operations

A covariant family E over K has transport E(p):Eₓ→Eᵧ along p:x→y, with the
chosen coherence. Model it through a total category and a projection
π:∫E→K with the relevant cocartesian structure.

Fibrewise total dualization produces

```text
Eᴼ : R(K) → Cat
Eᴼ = op ∘ R(E),       Eᴼ(k)=O(E(k)).
```

In contrast, dualizing the **whole projection** produces
O(∫E)→O(K), exchanging the corresponding cartesian/cocartesian roles.
Fibre duality, base reversal and duality of the whole total category are
different constructions. Negative sections must be specified as sections
of the correctly based dual family; their constant-family behavior is a
consequence to derive, not a reason to force a regrading of arbitrary E.

In the strict coherent transport convention, a positive section y has
components yₚ:E(p)(yₓ)→yᵧ. A negative section x, read in Eᴼ over R(K), has
components xₚ:xᵧ→E(p)(xₓ). The mixed Hom action is then the well-typed
composite

```text
h:xₓ→yₓ   ↦   yₚ ∘ E(p)(h) ∘ xₚ : xᵧ→yᵧ.
```

This explains the contravariant slot without reversing an arbitrary arrow
inside a fibre. Higher coherences come from the chosen section and
relative-Hom structures, with their actual profiles. For a constant family,
total-dualizing its negative section yields a functor T(K)→C. These are
semantic requirements that the repaired section/presheaf presentation must
meet, not permission to erase R(K) in other inputs.

For a strict 2-categorical covariant example, an arrow in ∫E is

```text
(p,u):(x,a) → (y,b),       u:E(p)(a) → b.
```

A 2-cell from (p,u) to (q,v) consists of

```text
α:p⇒q,       θ:u⇒v∘E(α)ₐ.
```

This gives a simple semantic control on Sigma Hom. With terminal base and
constant family C, α is an identity and θ has its original direction in C.
The fibre is not replaced by its opposite. Higher cells, composition and
projection are inherited from the chosen total/comma construction, rather
than guessed from this low-dimensional pair formula alone.

Contravariant families use the matching cartesian convention, with arrows
described by a→p*(b). This is another reason that an outer opposite on a
covariant Sigma cannot stand in for every contravariant totalization.

### Retain homd_int; derive total-category Hom observations

The previous recommendation to make relative Hom of a total projection the
semantic owner was too strong and is withdrawn. Emdash's foundational
constructors remain `hom_int` and `homd_int`, with their native sections,
projections, cuts and iterable higher action.

For π:ΣE→K, the generic whole Hom action of π supplies a useful observation:

```text
Hom∫E((x,a),(y,b)) → HomK(x,y).
```

In a suitable interpretation, the fibre over p:x→y describes arrows over p.
With covariant transport, its point reading is

```text
HomEᵧ(E(p)(a), b).
```

This is a consistency/comparison requirement for the native homd projections
and Sigma-Hom rules. A named whole projection or additional derived
comparison can be useful. Such a symbol should be defined through the
existing action where possible; a primitive observation would need a
concrete computational justification and must retain its relation to the
native owners. No independent pointwise relative-Hom grammar is proposed.

The foundational dependency stays

```text
hom_int / homd_int and their whole projection/action ladders
  → native displayed cells and simplicial iteration
  → applications using Sigma/PathOut and derived total-Hom observations.
```

Semantic explanations may run in either direction; implementation ownership
does not. This does not redefine the separate existing Sigma/Pi foundations.
The current presheaf/section target still needs its corrected variance,
but no replacement of `homd_int` by extracting arrows from a total
category is authorized or recommended. No arbitrary Z→R(Z), inverse
transport or replacement family is introduced.

Likewise, a presheaf is an object of the correctly oriented functor/module
category. For a nonsymmetric Gray tensor, start from left/right Hom actions
and their interchange; do not assume that every uncurry operation lands in
a cartesian product with ordinary transposition. This keeps the Hom,
presheaf, opposite-family and Sigma meanings mutually accountable.

### What should precede implementation

Complete a semantic owner table for totalization, sections, both Hom
arguments, displayed maps/transfors, universes, products/tensors, Pi and
the dependent-Hom target. Preserve the existing foundational owner of each
operation. For each entry state its domain, codomain, transformation profile,
syntactic computation, semantic interpretation and compatibility with O.
Derived views must identify their native owner and avoid circular
redefinitions. Derive the constant-family, identity and dimension-2/3
observations on paper before choosing new runtime rules, proof-time
usability or explicit equivalences.

This is a finite review of the relevant constructors under a general
variance law, not a request to implement an unlimited duality library before
returning to homology. The two existing Empty derivations remain essential
negative controls when implementation eventually resumes.

## 4. Ideal Complex And LES Architecture

### Ordinary complexes first have a precise diagram meaning

For an additive category 𝒜, a chain complex is a zero-preserving enriched
diagram on the differential shape with objects n, generators
dₙ:n→n−1, and relations dₙ₋₁∘dₙ=0. This is not an arbitrary functor from
an ordinal: the zero relations are part of the shape/structure.
This is a semantic characterization, not a requirement for another complex
grammar or frontend; corrected native homd/Sigma constructions may realize it.

Its ordinary chain maps are compatible diagram maps. A three-term
restriction produces the native zero-diagram input of the existing H.
Therefore the architectural target is

```text
Ch(𝒜) ─restriction at n→ Complex₃(𝒜) ─H→ 𝒜
Hₙ : Ch(𝒜) → 𝒜.
```

The present one-degree H and native zero-cone category form a local building
block, not an asserted implementation of all Ch(𝒜). Bounded complexes use
finite data and support evidence. Chosen zero padding may compute directly;
an already retained outside-support object can instead carry zero-object
evidence without being replaced by a different raw presentation.

On the category of short exact sequences of complexes, whole connecting
has the type

```text
δₙ : Hₙ∘quotient ⇒ Hₙ₋₁∘subcomplex.
```

Construct the whole LES as a degree/role diagram with separate exactness
and support laws:

```text
L(n,A)=Hₙ(A),   L(n,B)=Hₙ(B),   L(n,C)=Hₙ(C)
(n,A) → (n,B) → (n,C) → (n−1,A).
```

Operational row/complex data is shared once. Endpoint types are obtained
from these observations, not from `last(trim(flatten(...)))`. The degree
indices may be mathematical integers externally and constructor-based
offsets internally. A successor-shaped sequence interface is reusable;
the three-role shape is the particular LES instance. Avoid hard-coding that
shape into every exact sequence, exact couple or filtered complex.

This is my preferred design independently of the old timeout. It gives
clear interfaces for later shifts, exact functors, filtrations and long
exact sequences of Ext. Its concrete record/projection implementation still
needs the actual comparison measurements recorded in the retrospective.

### Where the simplicial/cubical work went

The [pilot history](TYPESCRIPT_EMDASH_STRICT_INTERNAL_HOMOLOGY_PILOT_PLAN.md#complementary-shapes-cells-and-cubical-maps)
distinguishes three resources that remain useful:

| Resource | Role | Actual retained boundary |
| --- | --- | --- |
| Native dependent triangles | d∘e⇒0 and higher local cells | The old chain-zero path has a checked fixed-flag triangle image |
| Derived cubical Homs | Chain-map squares with shared middle component | The two original squares and their whole boundary view are implemented |
| Shape categories and simplicial/ordinal data | Indexing, substitution, faces and diagram composition | No general equivalence with the native complex presentation is claimed |

The implementation modules are
[native triangles](../emdash2/emdash3_2_chain_pair_native_triangles.lp),
[cubical maps](../emdash2/emdash3_2_chain_pair_cubical_maps.lp) and
[factor squares](../emdash2/emdash3_2_hom_factor_cubical.lp).

They were not discarded. A general varying-flag complex category and the
coherent prism between zero triangles were not completed by these bridges.
The working H instead uses the existing native comma/zero-cone construction
in the ordinary Freyd target, whose higher compatibilities become
equality-valued. This is a specialization of native categorical machinery,
not a proof that simplices or cubes were unnecessary.

The ideal higher extension should derive triangles, squares, prisms and
their iterated boundary actions through the existing homd_int/hom_int
foundations with corrected variance. A single
directed d²⇒0, or two independently supplied squares, does not provide all
higher coherence of a general complex. Specify that higher diagram first;
its ordinary specialization should recover Ch(𝒜).

There is another relevant bridge in Markl–Trnka: pointed categories with
kernels are characterized via an arrow 2-monad and a simplicial décalage
construction. Their further bivariant Abelian programme is explicitly
future work. This supports investigating the connection without importing
a nonexistent complete homological normalization theorem.
[Paper, introduction and Theorems 8,26](https://arxiv.org/pdf/2601.20322v1).

## 5. What The Model Boundary Means, And What Can Be Automated

The current example does not make the user construct a closed formal model.
It names a supplied model M and normality input, prepares a reifier, and
records explicit interpretations of the retained computed results. The
[test setup](../tests/v3_2_algebra_formal_freyd_long_exact_homology_tests.ts)
declares those model inputs without bodies. The
[point-observation adapter](../src/v3_2/algebra_formal_freyd_model_observation.ts)
deliberately accepts that supplied-input interpretation and rejects arbitrary
reinterpretation of a defined model body.

A model is a reusable dictionary saying what formal R-module objects, maps,
kernel/cokernel operations and whole H mean in this implementation. A
reifier translates particular matrices, coefficients and stored witnesses
into formal terms. These are related but different jobs.

| Work | Can the example user be spared it? | What remains to justify |
| --- | --- | --- |
| Name coefficients, reify matrices, collect dependencies, build observation terms | Yes; ordinary adapter/elaborator automation | Correct translation and ownership |
| Find the registered backend, model and normality capability | Yes, once for each supported algebra profile | The selected backend/model contract |
| Build kernel/cokernel map action and whole structure from proved ordinary universals | Yes; reusable library assembly | Respect for quotient equality, choices and functoriality |
| Prove that a returned syzygy family is complete | Users need not prove it per example | A verified algorithm or a sound certificate checker/theorem |
| Supply an effective finite-presentation kernel for every arbitrary CommRing | No unconditional guarantee | Mathematical coherence and effective algorithms are genuine hypotheses |

For R=ℚ[x] and S=R/(x), the user-facing goal should be to specify the modules
and maps of `0→R ─x→ R→S→0`, then use H or LES. The registered algebra
implementation should select the model/reifier, preserve the computed
choices, produce the formal observations and report the applicable evidence
mode. The user should not manually assemble that pipeline for every example.
No special obstruction comes from nonsplitting; the calculation uses
universal factors and does not require a section S→R.

What was meant by “closed model construction” is a library theorem or
verified construction which supplies the dictionary itself, rather than
assuming an M and separately adopting agreements such as

```text
Hᴹ(z) = the reified retained native presentation.
```

Automation can hide the current plumbing immediately in principle. It
cannot turn a supplied semantic assumption into a derived theorem merely
by generating its name. Both a pragmatic registered trusted backend and a
certified backend are possible designs; they should expose the same
mathematical interface and accurately retain their different evidence.

For example, checking d∘G=0 only shows that the returned columns G lie in
the kernel. It does not show that they generate it: even G=0 passes that
test. A stronger certificate plus a generic theorem can establish all-test
factorization and uniqueness. Thus “the existing finite equation inventory
does not prove universality” is not a claim that a universal property can
never have a finite computational certificate.

Effective hypotheses also matter. The current finite-presentation setting
has a stronger boundary than the category of all R-modules. Posur's
constructive Freyd theorem identifies weak kernels/coherence and effective
lifting as the relevant inputs. It also gives computability failures outside
those hypotheses. These are reasons for a capability-indexed backend, not
reasons to impose repeated manual labour on polynomial users.
[Constructive Freyd categories, §4.1 and §5](https://arxiv.org/pdf/1712.03492).

### Selection coherence is the subtle part

Two algorithms or two representatives can produce isomorphic kernel objects
with different ranks, bases or relation matrices. A deterministic algorithm
alone does not imply that outputs on quotient-equal inputs are literally
the same raw presentation. A reusable model therefore needs one coherent
selection policy, or a presentation-aware input/realization interface with
canonical comparison isomorphisms. Posur discusses this distinction in
[Remark A.6](https://arxiv.org/pdf/1712.03492#page=37).

Preserve exact native object identity inside one retained computation, as the
current workflow does. Across separate choices, use the mathematically
appropriate comparisons unless a stronger representation theorem applies.
Replacing every such isomorphism by equality of raw presentation records is
not a legitimate automation shortcut. Conversely, requiring every user to
write the comparisons by hand is unnecessary; universal uniqueness can
supply them through reusable code and proofs.

## 6. Anticipate Ext, Stable Homology And Directed Spectra

### Ordinary chain maps do not yet give chain homotopies

If 𝒜 has discrete Hom categories, its ordinary diagram category of complexes
does too. One does not obtain chain homotopies merely by calling a chain
map a natural transformation. They require the appropriate enriched/coherent
mapping structure. In homological grading the dg Hom differential is

```text
∂(h) = dB∘h − (−1)ʳ h∘dA,       h has degree r.
```

Degree-0 cycles are chain maps; a degree-1 h with ∂h=f−g is a chain
homotopy. This is a distinct, reusable enrichment that can connect to the
native cell language; it is not silently supplied by the two current
commuting squares.

The intended progression is:

```text
Ch(𝒜)                 ordinary complexes and chain maps
dg/coherent complexes  mapping complexes and chain homotopies
D(𝒜) or its ∞-version  localization at quasi-isomorphisms
Ext and derived Hom    invariant whole operations with effective methods.
```

With the relevant resolution hypotheses, one computes Ext by homology of a
Hom complex, and conceptually

```text
Extⁿ𝒜(M,N) ≅ HomD(𝒜)(M,N[n]).
```

Resolutions are implementation methods whose comparison/independence must
be accounted for. Enough projectives/injectives and finite effective
resolution segments are capabilities, not properties of every abstract
Abelian category. [Stacks, Ext groups](https://stacks.math.columbia.edu/tag/06XP).

### Ordinary stable and groupoidal comparisons

In the conventional (∞,1) stable setting, suspension and looping are
inverse equivalences; fibre/cofibre sequences supply exactness. Its homotopy
category is triangulated, and an Abelian heart requires a t-structure.
Taking a truncation of arbitrary directed Homs does not automatically
produce that Abelian layer. [Lurie, Stable ∞-Categories](https://arxiv.org/abs/math/0608228).

For a pointed space X, the conventional comparison is

```text
π₁(X,x) = ‖ΩₓX‖₀
πₙ(X,x) ≅ ‖Map∗(Sⁿ,X)‖₀,       n≥1.
```

The group structure is part of the loop/sphere construction, not just the
underlying truncated set. The fundamental groupoid is the 1-truncation of
X. The inspected van Doorn text defines homotopy groups by set-truncating
iterated loop spaces; the existing emdash Circle/Integer result is a
concrete baseline, not an implemented general sphere theory.
[Dissertation](https://arxiv.org/abs/1808.10690v1).

For a directed category C, specify whether the intended space is its core
or its groupoidification. They differ: the core of the walking arrow has
two components, while its groupoidification is connected. Mapping a
groupoidal sphere into C cannot simply recover every directed feature of
C. Keep native directed Hom data available and perform the chosen
groupoidal realization explicitly where the classical comparison needs it.

### One fixed point and one varying endpoint

Fix c:C. The proposed starting datum is the WHOLE represented family

```text
𝓗c : C → Cat
𝓗c(y) = HomC(c,y),       id_c ∈ 𝓗c(c).
```

This is an observation of `hom_int` and its represented-family interface,
not a new external assignment of Hom sets. Its action sends p:c→y along
u:y→z to u∘p, retaining the whole next Hom action. Its distinguished fibre
at c is EndC(c). In the groupoidal case it is the based path family, with
loop space as that distinguished fibre.

For a point-preserving functor F:(C,c)→(D,d), the existing whole hom action
gives the displayed map 𝓗c→F*𝓗d. If F preserves the point by a specified
equivalence rather than literally, that equivalence supplies the appropriate
comparison. There is no independent recursive action for the new family.

This expresses the user's one-fixed-endpoint proposal. The earlier
two-pole suspension described a different construction and is withdrawn as
the organizing model for this proposal.

### The simplicial successor is already visible in the native foundation

Take E=𝓗c. With p:c→x fixed, a further dependent cell over u:x→y and
q:c→y has the shape

```text
u∘p ⇒ q.
```

That is the native dependent triangle. One lower flag is fixed while the
next endpoint/face varies. Iterating the same native mechanism gives
tetrahedra and further dependent simplices. The actual
[flagged simplex module](../emdash2/emdash3_2_dependent_simplex_native_dimensions.lp)
already defines

```text
S₁(C,c)       = PathOutC(c)
S₂(C,c,p)     = PathOutS₁(p)
S₃(C,c,p,t)   = PathOutS₂(t).
```

Its maps are derived through the existing whole action, and its further Hom
action remains at the generic owners. These are reusable constructors and
finite-dimensional evidence, with the inherited variance qualifications.
They are not yet a stabilized theory or a complete all-dimensional global
simplex category.

### Retain the dependency and the marked fibre

A family with one distinguished element over c is not a family of pointed
categories at every y. There need not be any arrow c→y, much less a chosen
one. Supplying p:c→y by extending the native context is legitimate; assuming
a global choice of such p is not. Dependent iteration should retain these
contexts and their substitutions.

Also retain the projection when using the total PathOut presentation. In
spaces the total based path space Σy:X, (c=y) is contractible by path
induction. Its fibre at c can nevertheless be nontrivial: for the circle
that fibre is ΩS¹≃ℤ. A proposed generalized loop operation that kept only
the bare total and forgot its projection/marked fibre would lose that
information in the classical specialization.

The intended datum is thus the native family together with its base and
distinguished identity, or a total presentation retaining those structures.
This does not by itself supply stabilization: a represented family is
already determined by its pointed base. The dimension-changing operation
and its category of dependent contexts must still be specified, rather than
calling an information-preserving repackaging of (C,c) a new spectrum.

### A concrete route toward generalizing Heine

[Heine v2](https://arxiv.org/pdf/2605.05195v2) defines spectrum objects by
an endomorphism tower with alternating variance (§5.2). Its main
representability theorem also requires exactness, colimit and categorical-
sphere compatibility conditions; its oriented exact sequences distinguish
left/right behaviour by degree (§7). Those results do not follow merely
from possessing a Hom constructor. The reviewed portions now include the
main-result statement and the definition of spectrum objects, alongside
the earlier introduction/§7 reading.

The proposed generalization should replace the diagonal-only transition by
an internal dependent-Hom transition retaining the one fixed point and its
varying-endpoint/flag data. It need not be forced to act as an endofunctor
on the old category of pointed categories. It may instead organize a
variance-correct tower of categories of dependent contexts:

```text
⋯ ─R₂→ 𝒞₂ ─R₁→ 𝒞₁ ─R₀→ 𝒞₀.
```

The candidate generalized spectrum is a compatible system of objects of
these categories, with the specified transition comparisons. The required
work is to define the 𝒞ₙ and Rₙ through native whole constructions, then
justify the relevant limit/stabilization universal property. This is a
design scheme, not an implemented definition with those names.

There is a useful precise comparison target: diagonal observations Δₙ
should commute coherently with the transitions,

```text
Δₙ(Rₙ X) ≃ Ω(Δₙ₊₁ X),
```

including Heine's matching variance twists. Such a comparison of towers
would induce a functor to his spectrum category. It would not by itself
prove equivalence, preservation of exactness, or generalization of the
representability theorem.

The companion suspension should be formulated as the relevant whole
adjoint to the dependent-Hom transition, with internal unit/counit and
Došen computation. This keeps the suspension question in the foundational
calculus instead of choosing a two-pole construction in advance.

The staged research obligations are:

1. Native dependent contexts and reindexing, with the marked face retained.
2. Whole transition and suspension/adjunction, including their next action.
3. Diagonal and groupoidal comparisons, and a nonidentity off-diagonal case.
4. Stabilization, appropriate fibre/cofibre operations and exactness.
5. Additional hypotheses for representability, tensor structure and the
   comparison with ordinary homology/Ext or spectral geometry.

For the off-diagonal test, a category with one arrow c→d and one with two
parallel arrows c⇉d have the same End(c) but different 𝓗c(d). The proposed
local operation must retain this distinction before any justified
localization. This is a test of the dependent operation, not a claim that
Heine's full homology theory cannot distinguish these categories.

Generalizing all of Heine's theory is therefore a meaningful research
programme with a native starting point. It remains an objective to prove;
the first theorem should establish the dependent transition/adjunction and
its diagonal comparison, rather than assume the entire spectral package.

### Spectral algebraic geometry

Anticipate symmetric monoidal structure, derived tensor/base change,
internal derived Hom, module categories, descent and localizations. Ordinary
spectral algebraic geometry uses sheaves of E∞-rings; replacing these with
directed categorical algebra would be an additional theory requiring its
own comparison. [Lurie, Spectral Algebraic Geometry, introduction](https://www.math.ias.edu/~lurie/papers/SAG-rootfile.pdf).

The existing polynomial and sheaf computations can serve as ordinary
realizations and regression examples. They should not be reclassified as
spectral objects by naming alone. The useful present design decision is to
make realization, exactness preservation and effective algebra capabilities
explicit, so future derived/stable methods can use them without rebuilding
the ordinary computation interface.

## 7. Concrete Design Decisions Before The Next Code Tranche

| Decision | Proposed answer |
| --- | --- |
| Universality | Whole adjunction/internal-Hom calculus owns formal computation; IsContr/factor views are derived interpretation or verification interfaces |
| Duality | Total O plus homwise shift, tracked by semantic dimension/profile laws; no unrestricted same-base opposite families |
| Dependent Hom | hom_int/homd_int retain foundational ownership; total-Hom projections and relative interpretations are derived comparisons |
| Complexes | Ordinary zero-diagrams and coherent directed diagrams explicitly distinguished; native simplex/cube views derived and compared |
| LES | Whole family on the category of short-exact complexes; degree/role observations; exactness/support separate; flattening downstream |
| Proof-CAS usability | One registered model/reifier per supported algebra profile; automatic per-example preparation and observations |
| Proof-CAS correctness | Clearly separate backend trust from verified universal-provider and interpretation theorems |
| Future scope | One-point dependent-Hom/simplicial transition, with a suspension adjunction and diagonal comparison; later dg/derived and stable results require their own theorems |

First review the native-owner/semantic comparison table and discriminating
examples: terminal-base Sigma, a noninvertible base 2-cell, negative constant
sections, full relative Hom, an ordinary kernel and a homotopy fibre,
two quotient-equal matrix representatives, a nonsplit LES, and the based
Hom family with a varying endpoint and retained projection. These examples
test the intended mathematics before selecting normalization equations.

Then undertake separate bounded implementation tranches: coupled variance
repair preserving native Hom owners; whole-universality dependency refactor;
ordinary model/reifier automation; whole-H snake/direct comparison; and the
endpoint representation study. A certified model construction and the
one-point dependent stabilization need their own hypotheses and milestones.
The current algorithms and reviewed formal fragments remain evidence for
these designs, rather than a compatibility constraint on every future
representation.

## Review Scope And Validation

This follow-up read the relevant actual IsContr/kernel/functor/relative-Hom
and model definitions, the supplied-model test setup, pilot and repair
ledgers, the native triangle/cubical history, and the cited selected primary
material. No archived instruction was treated as new execution authority.
Only review documents and their parent-plan links were edited. Local link,
Markdown/whitespace, active-reference and report-lifecycle checks are the
owning validation; no LP/CAS implementation or generated artifact changed.
