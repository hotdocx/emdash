# Dependent Suspension And Categorical Spectra: Research Review

Date: 2026-09-18

Status: mathematical design review; proposed higher construction, no implementation or stabilization theorem

Scope: the user's present request reopens spectral design analysis, including
the correction that the section g is indexed by C₀′. It does not launch a
kernel migration, integrate the action-profile branch, or change the completed
homology work. Earlier spectral deferrals describe those earlier goals.

## Assessment And Recovered Context

The proposal has a sound local interpretation: a coherent family of displayed
arrows above specified base arrows, with one fixed source and varying targets.
It suggests a dependent suspension defined by a universal property and a
subsequent stabilization of dependent contexts. The local interpretation is
substantially more definite than the spectrum construction: the latter still
needs a category of levels, a whole transition, compatible boundary shifts,
and a stabilization theorem.

The most relevant earlier records are:

- [Reference inventory, HRI-04 to HRI-10 and the user's independent hypothesis](TYPESCRIPT_EMDASH_HOMOLOGICAL_REDESIGN_REFERENCES.md).
- [Semantic architecture review, section 6](TYPESCRIPT_EMDASH_HOMOLOGY_SEMANTIC_ARCHITECTURE_REVIEW.md#6-deferred-brainstorming-ext-stable-homology-and-directed-spectra).
- [Dependent-simplex foundations plan](../emdash2/reports/REPORT_EMDASH_V3_2_DEPENDENT_HOM_SIMPLEX_FOUNDATIONS_PLAN_2026-08-19.md).

The earlier review already retained one fixed endpoint, a varying endpoint,
the base projection, the marked identity fibre, and a possible tower of
dependent contexts. It explicitly withdrew a fixed two-pole construction as
the organizing model for this proposal. The present review preserves that
decision. Fixed-pole constructions below are comparison tests, not replacements
for the user's varying-endpoint proposal.

The additional datum in the present formulation is a target section together
with a section of the dependent-Hom family after substitution of the chosen
base arrows. This makes a dependent cell-introduction interface visible.

## A Well-Typed Local Formulation

Use different letters for the base, the parameter category, and the displayed
family. In one consistent reading of the user's notation, set:

    B = C₀                         base category
    A = C₀′, i : A → B              category of allowed parameters
    E : B → Cat                    displayed family underlying C₁
    c : B, u : E(c)                fixed source and source fibre object
    p_a : c → i(a)                 coherently varying base arrows
    s_a : E(i(a))                  a section s of i*E

Write p_! for the action of E along p. In a strict covariant reference model,
the dependent Hom is

    D_E(c,u; b,v; p) = Hom_{E(b)}(p_!u, v),   p : c → b.

This is the identity-displayed-map specialization of the intended native
homd interface. For a displayed map F:D→E, the last endpoint is F_b(v).

The corrected substituted family is

    R_{i,p,s}(E,u)(a) = D_E(c,u; i(a),s_a; p_a),
    g : Γ_A R_{i,p,s}(E,u).

Thus g is indeed indexed by A=C₀′, as the user's correction requires. There
is no reason for it to extend to every object of B. Substitution by (i,s,p)
is the whole construction; it must include action on arrows and higher cells,
not only the displayed object formula.

At each parameter, g_a is the vertical arrow

    (p_a)_!u → s_a

in E(i(a)). Equivalently, it determines an arrow in the total category above
p_a, from (c,u) to (i(a),s_a). This total-category description is a semantic
observation of native homd, not a replacement foundational owner.

If C₁ was instead meant to be a family over C₀′ from the outset, use A as
its base and specify a source object of A. Applying i* to that same family
would have the wrong domain. The two readings should not be combined.

For an ordinary base, a strict E, and a natural p:const_c⇒i, the family
r_a=(p_a)_!u transports strictly. A section s has maps
s_h:E(i(h))(s_a)→s_b. In the ordinary-fibre case, coherent g means

    s_h ∘ E(i(h))(g_a) = g_b,     h:a→b,

after the source identification supplied by p. Higher directed versions
replace the appropriate equations by specified comparisons and their higher
coherences; the strict and lax profiles cannot be silently identified.

For a basepoint-compatible specialization, additionally choose a parameter
a₀ with i(a₀)=c, p_{a₀}=id_c and s_{a₀}=u, with the appropriate coherent
identifications in a weak model. Normalizing g_{a₀}=id_u is a further
condition. Without these data, the marked source in E does not automatically
become the identity pointing of the substituted Hom family.

## What C₀′ Can Mean

There are two substantially different possibilities.

1. A parametrizes arrows already in B. In an ordinary category, the canonical
   choice is the coslice c↓B with target projection i:c↓B→B. Its objects are
   pairs (b,p:c→b), and the tautological p is a natural transformation
   const_c⇒i. The projection need not be injective: different arrows can
   have the same target. A section over this A may depend on p as well as b.
2. A new category B⁺ is freely generated from B by adjoining arrows. The
   canonical functor then goes B→B⁺. The family to be evaluated along the
   new arrows must live over B⁺, or be extended there by an additional
   construction. A family over the original B has no transport along arrows
   that did not exist in B.

If B is literally the discrete two-element set {c,d}, c≠d, there is no arrow
c→d. A functor A→B cannot send an arrow to a nonexistent arrow between those
two values. Freely adjoining that directed arrow gives the walking-arrow
category; adjoining an invertible arrow gives a different, groupoidal base.
Neither retains the discrete two-point category as the base of that arrow.

The first reading is the clean default for a general dependent-Hom operation.
It avoids manufacturing arrows or choosing one arrow to each endpoint. The
second reading belongs naturally in a free-construction/suspension discussion.
The higher analogue of the coslice must have the variance described below;
the ordinary formula does not select a lax/oplax convention automatically.

Requiring all p_a to be equivalences is optional extra structure. It excludes
noninvertible base directions. It does not, by itself, make g_a invertible.

There is a useful distinction between choosing paths over A and choosing
paths over all of B. For a space B, data p_b:c=b for every b:B is precisely
a contraction of B. More generally p:const_c⇒i over A says that i is
nullhomotopic in the groupoidal interpretation; it does not say that B is
contractible. The user's domain correction therefore matters mathematically.

In an ordinary category, a natural p:const_c⇒id_B normalized by p_c=id_c
forces c to be initial: naturality at any f:c→b gives f=f∘p_c=p_b. Mere
objectwise arrow choices without naturality do not imply this conclusion.

Even the canonical total of based paths in a space is contractible. Its
projection to B still retains the loop spaces as fibres. Consequently a
construction must keep the projection and marked fibre rather than discard
them after taking a total category.

There is also a possible redundancy in g. In the ordinary strict reference
model, let A=c↓B and let a₀=(c,id_c). There is a unique arrow λ_a:a₀→a
above p_a. A section s already has an action

    s_{λ_a} : E(p_a)(s_{a₀}) → s_a.

Consequently any g₀:u→s_{a₀} determines a coherent g by

    g_a = s_{λ_a} ∘ E(p_a)(g₀).

Conversely, naturality along λ_a forces this formula, so evaluation at a₀
identifies the set of such coherent g with Hom_{E(c)}(u,s_{a₀}). If
s_{a₀}=u and g₀=id_u, g is exactly the section's existing action. This is
an ordinary-model observation, not a claim of uniqueness for arbitrary lax
higher sections. It shows why endpoint objects and a whole endpoint section
are different inputs, and why the entire R family should remain primary
instead of immediately replacing it by its section object.

## Variance Is Part Of The Definition

The user's opposite on the base Hom is meaningful. In a strict 2-categorical
reference model, a 2-cell α:p⇒q induces

    E(α)_u : E(p)u → E(q)u,
    α* : D_E(...;q) → D_E(...;p),
    α*(h) = h ∘ E(α)_u.

This is contravariant dependence on the base arrow, while the final fibre
endpoint is covariant. Arbitrary independently varying tuples cannot simply
be treated as a covariant product of these inputs.

An elementary discriminating example takes E(c)=1, E(d)=[1], with E(p)
selecting 0, E(q) selecting 1, E(α) the arrow 0→1, and v=0. Then

    D_E(...;p) = {id₀},       D_E(...;q) = ∅.

The correct induced function goes ∅→{id₀}. Reversing it would require a
function {id₀}→∅. This is an independent semantic direction check, not an
appeal to the current Lambdapi checker.

For changing endpoints, suppose h:a→b, k=i(h), the section supplies
s_h:E(k)s_a→s_b, and the arrow parameters supply

    β_h : p_b ⇒ k∘p_a.

In the strict transport model, the induced map on R sends t to

    E(p_b)u --E(β_h)--> E(k)E(p_a)u --E(k)(t)--> E(k)s_a --s_h--> s_b.

This fixes the necessary orientation. A noninvertible comparison in the
opposite direction cannot be used here by pretending it has an inverse.
Strict equality or an invertible comparison permits both presentations.
For genuinely lax E, its compositor direction is another requirement: the
displayed formula uses E(kp)u=E(k)E(p)u, or an appropriately directed
comparison. It is not a construction for every lax profile without further
work. Higher opposites must also be specified dimension by dimension.

The intended implementation remains whole native homd followed by typed
substitution. The formula above specifies the semantic test that the
substitution must pass; it does not propose a second external Hom calculus.

## A Section, A Free Suspension, And A Spectrum Are Different Data

The section g equips an existing family with chosen displayed arrows. It
does not say that the family is freely generated by them. To formulate a
dependent suspension, let P be a family of generating categories over A and
seek a free object with generators

    merid(a,z) : D_E(c,u; i(a),s_a; p_a),     z:P(a).

The case P(a)=1 has exactly the user's one-generator-per-parameter form.
The whole P includes its higher cells and parameter action. In a directed
HIT presentation, merid is a directed constructor; replacing it with an
ordinary identity/path constructor would impose invertibility.

A candidate universal property is

    Map_boundary(ΣᵈP, (E,u,s)) ≃ Map_{Fam(A)}(P, R(E,u,s)).

Here i and p are fixed boundary data; maps on the left preserve that boundary
and the marked endpoints. Both mapping objects must use the selected
strict/lax/pseudo profiles. This is a proposed whole adjunction, including
unit, counit, higher action, and beta/uniqueness behavior. Its general higher
existence is not proved by listing the point and arrow constructors.

There is a direct ordinary sanity case. Let B=[1], c=0, A=1, i(*)=1 and
p the unique nonidentity base arrow. For a set P, define the free diagram
L(P):[1]→Cat by L(P)(0)=1 and L(P)(1) the category with objects N,S,
arrows N→S indexed by P, and only identities otherwise. The transition
selects N; mark the source object and S. A boundary-preserving map L(P)→E
is exactly a function P→Hom_{E(1)}(E(p)u,s): its objects are fixed and its
generating arrows are the remaining choices. This verifies a small instance
of the proposed universal property in ordinary mathematics. It is not a
formalized higher construction or the proposed global organizing model.

Allowing the target to vary also makes cone-like constructions possible.
The free graph N→a, N→b has contractible groupoidification; the free category
with two parallel arrows N⇉S has groupoidification of homotopy type S¹.
Thus preserving separate endpoints versus identifying them can change even
the first homotopy type. A dependent cone, an unreduced suspension, and a
reduced suspension need distinct boundary/universal conditions.

For an ordinary suspension prespectrum, the levels are iterated suspensions
and the structure maps are supplied by that construction. They need not
already be equivalences X_n≃ΩX_{n+1}; passing to an Ω-spectrum model can
require spectrification. The analogous distinction is necessary here.

## The Higher-Dimensional And Simplicial Content

The local construction has a concrete triangle specialization. Take

    F:B→D,       E(b)=Hom_D(z,F(b)),
    u:z→F(c),    s_a:z→F(i(a)).

Then g_a is a 2-cell

    F(p_a) ∘ u ⇒ s_a.

Its three edges are visible, and coherent variation compares such triangles.
Further represented dependent-Hom iteration exposes tetrahedral and higher
boundary data. For an arbitrary E, a displayed arrow is not automatically a
simplex in one fixed ambient category; the hom-shaped specialization explains
that interpretation.

The native
[flagged simplex module](../emdash2/emdash3_2_dependent_simplex_native_dimensions.lp)
already uses

    S₁(C,c) = PathOut_C(c),
    S₂(C,c,e) = PathOut_{S₁}(e),
    S₃(C,c,e,t) = PathOut_{S₂}(t).

It provides relevant syntactic infrastructure and finite-dimensional
computations, subject to the current foundational diagnostics. The marked
lower boundary is part of the type of the next level. Generalizing this
requires retaining those flags, whole substitution, and the correct face
actions. Identities/degeneracies, face identities, completeness, and any
Segal comparison are separate obligations. Directed cells do not justify
imposing a Kan condition that would invert them.

A simplicial or flagged presentation alone is not stabilization. Iterating
a representation of an already given category may simply redescribe that
category in progressively dependent contexts.

## A Candidate Spectrum Architecture

Keep the universal family before choosing g. Its off-diagonal fibres have
no canonical identity object. Selecting g points those fibres, but that
selected arrow need not be an identity or an equivalence. This is a real
difference from the endomorphism operation, whose pointing is automatic.

The natural prospective level is therefore a dependent context carrying
its base, family, source, target/arrow parameters, and required marked lower
faces. Write D_n for a category of such contexts and seek whole transitions

    R_n : D_{n+1} → D_n.

Neither D_n nor R_n is defined by the component formula alone. In particular,
one must specify morphisms, their boundary comparisons, higher action,
reindexing, and the evolution of the flags. If left adjoints exist, write
L_n⊣R_n for the dependent suspensions.

A candidate prespectrum then has structure maps

    X_n → R_n(X_{n+1}),

or equivalently L_n(X_n)→X_{n+1}. The analogue of an Ω-spectrum requires
these comparisons to be equivalences in the chosen category of contexts.
Such objects form a compatible-system limit once the tower is defined.
Calling this a stabilization additionally requires the intended universal
property and a compatible invertible shift. An arbitrary heterogeneous
tower need not have a shift automorphism merely because its limit exists.

This is preferable to requiring, without further explanation, that the
underlying C_{n+1} be a fibration over C_n. Ordinary categorical spectra have
bonding comparisons to endomorphism categories, not a canonical projection
of each underlying category onto the preceding one. A proposed extra
fibration requirement must be included in the comparison theorem.

At the local diagonal, b=c, v=u, p=id_c, one recovers

    D_E(c,u; c,u; id_c) ≃ End_{E(c)}(u),

pointed by id_u. This is the vertical endomorphism category. Endomorphisms
in the total category can also lie over nonidentity endomorphisms of c;
the diagonal does not include them all. A terminal base removes that
distinction and is the simplest ordinary-loop comparison case.

To compare whole towers, construct observations Δ_n and coherent equivalences

    Δ_n R_n ≃ Ω Δ_{n+1},

with the appropriate higher variance. The local diagonal formula alone
does not prove this. A comparison functor also does not prove equivalence
or strict generality of the resulting theories.

Negative indices become meaningful after establishing the dimension shift.
They cannot be supplied by declaring negative-dimensional ordinary
categories. A nonnegative tower can already encode the required unbounded
deloopings when its shift construction has been proved.

## Literature Comparisons And Cohomology

[Kern v2](https://arxiv.org/html/2410.02578v2), sections 2.3 and 3,
describes all-cell desuspension for flagged categories, a categorical-spectrum
limit using endomorphisms, and a comparison with pointed (∞,ℤ)-categories;
Corollary 3.3.5 gives the groupoidal comparison with spectra. These are
comparison targets, not a novelty or equivalence theorem for the present
proposal. Existing ℤ-category language already has cells with distinct
boundaries. The potentially additional content here is the retained
displayed dependency and transport during the shift.

[Heine v2](https://arxiv.org/html/2605.05195v2), Definition 5.2.1,
uses an alternating C/Cᶜᵒᵖ tower at the enriched level. Theorem 2.0.1's
representability result includes reducedness, filtered-colimit preservation,
oriented excision, and categorical-sphere compatibility. A dependent-Hom
family supplies none of those hypotheses automatically.

There are two especially useful existing comparison directions:

- Parametrized spectra: over a space B, spectra can be modeled by functors
  Bᵒᵖ→Sp. Base change and sections are central, with twisted cohomology as
  an application. See [Ando–Blumberg–Gepner, introduction and sections 3–5](https://arxiv.org/html/1112.2203v2).
- Enriched categories/modules: off-diagonal Hom(x,y) carries left
  End(y)- and right End(x)-actions by composition. It need not carry the
  unit and multiplication of End(x) itself. A stable theory retaining
  such Homs may naturally have many objects or module-like coefficients.
  This is a structural observation, not an identification of the user's
  construction with a known spectral-enrichment theory.

For a directed base, covariant and contravariant parameterizations differ.
Also, ordinary homotopy-pullback looping in an underlying (∞,1)-category
does not automatically compute directed endomorphism categories: the latter
require the appropriate enriched/oriented construction. Consequently merely
writing spectrum objects in a slice does not establish the desired theory.

For ordinary spectra, the familiar cohomology comparison target is

    Ẽᵏ(X) = π₀ Map_Sp(Σ∞X, ΣᵏE)

for pointed X. For a local system of spectra E over a space B and q:X→B,
the corresponding section-spectrum expression is

    Hᵏ(X;q*E) = π_{−k} Γ_X(q*E).

The latter explains why retaining base dependence could be useful for the
long-term cohomology goal. A directed generalization first has categorical
mapping/section objects. A degree shift, suitable excision, and a qualified
groupoidal or additive comparison are needed before claiming classical
generalized cohomology groups or long exact sequences. A bare set truncation
does not supply the missing abelian-group structure.

The full reading coverage for this review is selective: Kern's relevant
definitions/comparison statements and Heine's introductory hypotheses and
spectrum tower were inspected, not their complete proof developments.
Ando–Blumberg–Gepner's introductory parametrization/base-change formulation
was inspected. Lessard's primary abstract and Masuda's v2 metadata/correction
were checked; Stefanich's thesis and the remaining inventory were not newly
reviewed in full. No claim of literature exhaustiveness is made.

## Feasibility And The First Useful Milestone

The local displayed-arrow construction is mathematically feasible in the
strict reference model. Its whole higher realization, free adjoint, and
stabilization are distinct research milestones. The first useful theorem is
the dependent-Hom/suspension adjunction with explicit reindexing and the
ordinary diagonal comparison, before a representability theorem is attempted.

The following tests would make that milestone concrete:

| Test | Required observation |
| --- | --- |
| Discrete two-point base | No arrow between distinct points appears without changing the base. |
| One versus two parallel arrows c→d | The represented off-diagonal family distinguishes them although End(c) agrees. This does not claim that existing categorical homology cannot distinguish them. |
| Walking noninvertible 2-cell | The empty/singleton Hom test above has the correct contravariant direction. |
| Terminal-base diagonal | The local operation recovers pointed End, and its adjunction has the expected specialization. |
| Free singleton-base example | Maps out are exactly the generating displayed arrows, with appropriate beta behavior. |
| Groupoidal based-path family | The projection and its loop fibre survive although the total based-path space is contractible. |
| Change of parameters A′→A | Restriction commutes with the construction as a whole family, including its next action. |
| First nontrivial triangle and tetrahedron | Directed comparison cells remain visible; no unrequested inverse or strict equality is introduced. |

Implementation cannot presently use the generic kernel's successful typing
as a semantic certificate. The active
[Homd-target diagnostic](TYPESCRIPT_EMDASH_HOMD_TARGET_POLARITY_DIAGNOSTIC.md)
records a reversed target action, and the
[Sigma-Hom](TYPESCRIPT_EMDASH_SIGMA_HOM_VARIANCE_DIAGNOSTIC.md),
[opposite](TYPESCRIPT_EMDASH_INTERNAL_OP_VARIANCE_DIAGNOSTIC.md), and
[family/section-profile](TYPESCRIPT_EMDASH_FAMILY_SECTION_PROFILE_DIAGNOSTIC.md)
diagnostics record related or independent defects. The intended hom_int and
homd_int owners remain foundational; a future qualified implementation must
respect their repair boundaries. This review neither resumes those migrations
nor depends on the invalid higher actions to establish its reference examples.

The present work changes documentation only. The mathematical examples are
explicit arguments in ordinary/strict reference models, not newly checked
Lambdapi terms. No kernel, TypeScript, book, or repository aggregate is called
for by this review. Whitespace and local-link checks cover the document edits.
