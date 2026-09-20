# Dependent Suspension And Categorical Spectra: Research Review

Date: 2026-09-18

Last reviewed: 2026-09-19

Status: categorical Π-section and join source review; suspension-algebra design, no implementation or stabilization theorem

Scope: the user's present request reopens spectral design analysis, including
the correction that the section g is indexed by C₀′. It does not launch a
kernel migration, integrate the action-profile branch, or change the completed
homology work. Earlier spectral deferrals describe those earlier goals.

## Assessment And Recovered Context

The latest user clarification takes ordinary Hom and categorical Π as the
constructor interface: join has a varying inclusion endpoint; suspension
has constant endpoints. This is the current starting point. The section
below records its relation to the active binary join, the required section
profile, reduced pointing, prespectrum algebras and fibrewise suspension.
The earlier family/collage and varying-boundary proposals remain reference
alternatives; they are not prerequisites for this simpler formulation.

The proposal has a sound local interpretation: a coherent family of displayed
arrows above specified base arrows, with one fixed source and varying targets.
The original review incorrectly made that fixed-base interpretation the
starting formulation for constructing the suspension of the input C₀. The
user's two-point objection identifies the missing distinction: input points
can label newly generated arrows without already being their endpoints in
the base. The follow-up below supplies explicit ordinary constructions,
their dependent elimination data, and a family-to-pointed-category adjunction.
The higher spectrum construction still needs a category of levels, a whole
transition, compatible boundary shifts, and a stabilization theorem.

The most relevant earlier records are:

- [Reference inventory, HRI-04 to HRI-10 and the user's independent hypothesis](TYPESCRIPT_EMDASH_HOMOLOGICAL_REDESIGN_REFERENCES.md).
- [Semantic architecture review, section 6](TYPESCRIPT_EMDASH_HOMOLOGY_SEMANTIC_ARCHITECTURE_REVIEW.md#6-deferred-brainstorming-ext-stable-homology-and-directed-spectra).
- [Dependent-simplex foundations plan](../emdash2/reports/REPORT_EMDASH_V3_2_DEPENDENT_HOM_SIMPLEX_FOUNDATIONS_PLAN_2026-08-19.md).

The earlier review retained one fixed endpoint, a varying endpoint, the base
projection, the marked identity fibre, and a possible tower of dependent
contexts. Its withdrawal of a fixed two-pole construction described that
earlier proposal. The user's latest clarification explicitly distinguishes
join from fixed-endpoint suspension; that clarification now governs this
review instead of requiring the older varying-boundary architecture.

The additional datum in the present formulation is a target section together
with a section of the dependent-Hom family after substitution of the chosen
base arrows. This makes a dependent cell-introduction interface visible.

## Categorical Π, Join And Suspension Algebras — Latest Clarification

Ordinary Hom is the appropriate first interface in the revised signatures.
The family a↦Hom(north,inclusion(a)) has dependent values because its endpoint
varies. Explicit homd is needed when lifting arrows into a displayed motive
and remains part of the section-action implementation. It need not appear
in the primary meridian constructor.

Here Π E denotes a category of directed sections; a meridian is an object
of that category. For the intended generic section profile,

    Π(a:A), K ≃ Functor(A,K)

when K is a constant family. A section can vary as a functor even though
family transport is identity. This is different from an ordinary strict
limit of the constant Cat-valued diagram, or choices on Obj(A) that ignore
the arrows of A.

The active core explicitly gives this comparison as a proof-time unification
rule at Pi_cat(Const_catd(A,K)); the Pi runtime head stays stable. The
represented Hom family along a constant diagram has a separate runtime
fold to Const_catd(A,Hom(north,south)). Thus the suspension constructor has
the intended reading

    meridian : Obj(Π(a:A), Hom(north,south))
             ≃ an object of Functor(A,Hom(north,south)).

These are existing declaration/comparison facts, not a consistency claim.
The [family/section diagnostic](TYPESCRIPT_EMDASH_FAMILY_SECTION_PROFILE_DIAGNOSTIC.md)
records the conflict with the old unrestricted strict-naturality cuts.
The intended construction must retain the section's own directed action.

### Unary Join And The Active Binary Join

The user's unary Join(A) is the left cone, mathematically 1⋆A, with data

    inclusion : A ⊢ J
    north     : Obj(J)
    meridian  : Obj(Π(a:A), Hom_J(north,inclusion(a))).

For u:a→b, the positive directed section profile supplies a cell

    inclusion(u) ∘ meridian(a) ⇒ meridian(b).

For A the walking arrow, this is the triangle cell. Higher action includes
the corresponding coherence. Requiring strict equality selects a strict
cone; requiring an invertible comparison selects a pseudo cone. These are
distinct higher constructions. The earlier ordinary category/Set examples
do not decide between them.

The [active core](../emdash2/emdash3_2.lp) implements the binary version:

| Requested unary datum | Current owner or specialization |
| --- | --- |
| J | Join_cat(Terminal_cat,A) |
| inclusion | join_snd_func(Terminal_cat,A) |
| north | Image of Terminal_obj under join_fst_func(Terminal_cat,A) |
| Whole meridian | join_cross_transf(Terminal_cat,A) |
| Shaped observation | join_cross_hom, through Prof_cell_eval |
| Nondependent recursion | join_elim_func, with its left branch selecting the supplied north |

For binary Join_cat(A,B), the cross object is a Prof_transf_cat from
Terminal_prof(A,B) to Unit_prof(J) reindexed along the two inclusions.
Prof_transf_cat unfolds to Functord_cat over Aᵒᵖ×B. Its source here is
the constant terminal family, exactly the terminal-source presentation
used by Pi_cat. Its mathematical reading is therefore

    Obj(Π(a:Aᵒᵖ,b:B), Hom_J(inl(a),inr(b))).

Specializing the left side to 1 and identifying 1ᵒᵖ×A with A gives the
user's unary section. The binary-base presentation is already native;
no unary wrapper or terminal-product runtime collapse is introduced here.

The recursor has runtime beta rules for whole branch restrictions, their
point observations, the primitive cross observation and the extracted
whole/component Hom action on the cross. The
[mapping-recursion module](../emdash2/emdash3_2_join_mapping_recursion.lp)
adds whole observations and JoinMapObjectData, an object classifier rather
than an established category of all mapping data. The downstream
[cross-compatibility module](../emdash2/emdash3_2_join_cross_compatibility.lp)
declares a whole propositional beta comparing the action-derived cross
observation with the recursor-owned cross. This is not a runtime fold.

The current interface supplies constructor data and selected nondependent
computation. It does not supply a general dependent join eliminator, a
generic directed-HIT declaration schema, or a whole observation/extension
equivalence with join eta. A complete universal specification still needs
the algebra category and its higher maps, initiality/uniqueness, and the
selected computation principles. Listing the Π constructor data alone
does not prove those properties.

### Unreduced And Reduced Suspension

Correct Join(A) to Susp(A) in the user's suspension north field. The
unreduced signature is

    north,south : Obj(ΣᵘA)
    meridian    : A ⊢ Hom_{ΣᵘA}(north,south).

This is equivalently the Π-section of the constant Hom family. A need not
be pointed. The output is bipointed and can be pointed by choosing south.
For A=[1], meridian gives two parallel 1-cells and a 2-cell between them;
for discrete two-point A, it gives two unrelated parallel arrows.

A remains the meridian's domain. Replacing the right factor of Join(1,A)
by 1 would instead give Join(1,1), retaining only one generating arrow.
The constant endpoint in the suspension signature must not erase the
parameter category of the constructor.

In the appropriate strict enriched reference model the suspension has
Hom(north,south)=A, terminal self-homs and an empty reverse hom. Its
fixed-endpoint mapping property is

    Functor_bipointed(ΣᵘA,(C,n,s)) ≃ Functor(A,Hom_C(n,s)).

The higher interpretation must use compatible chosen functor/transformation
profiles; it is not supplied automatically by the present core's syntax.

For the usual spectrum interface use reduced suspension of pointed (A,a★).
Collapse the marked meridian, identifying its endpoints. The strict
presentation has north=south=★ and meridian(a★)=id_★. Thus an economical
reduced algebra in pointed (C,c★) is

    meridian : Functor₊((A,a★),(End_C(c★),id_c★)).

Weak pointing uses specified comparison/coherence data; these observations
authorize no global identity rewrite. Omitting south because it is the
basepoint does not itself impose the reduction. For pointed A=1, unreduced
suspension is the walking arrow, while reduced suspension is terminal.
In spaces the marked meridian is invertible and the standard comparison
between pointed unreduced and reduced models is available. An arbitrary
noninvertible directed meridian cannot supply that comparison.

These suspension/endomorphism targets are described in
[Kern, sections 2.1 and 3.1](https://arxiv.org/html/2410.02578v2).
No general Susp/Suspd owner was found in the active emdash3_2 source
inventory; the specialized walking-endomorphism and circle developments
do not themselves provide it.

### Algebra Data For Prespectra And Ω-Spectra

The user is right that a map from a free suspension can be given by its
algebra data. For unreduced suspension of fixed Cₙ this means

    n,s : Obj(Cₙ₊₁),       m : Cₙ ⊢ Hom_{Cₙ₊₁}(n,s).

This is an algebra for the constructor signature with parameter Cₙ. Its
equivalence with maps out needs the whole recursion/uniqueness principle
with the matching profiles.

For pointed levels (Cₙ,cₙ), reduced suspension instead gives

    σₙ : ΣCₙ →₊ Cₙ₊₁
       corresponding to
    λₙ : Cₙ →₊ End_{Cₙ₊₁}(cₙ₊₁).

Point preservation sends cₙ to id(cₙ₊₁), retaining the appropriate weak
comparison when needed. Arbitrary such maps define categorical prespectrum
data. The Ω-spectrum condition requires each λₙ to be an equivalence.
Stable localization/spectrification provides another presentation of
spectra when its hypotheses are established.

The pointed endomorphism-algebra interface can therefore be specified
without first implementing a suspension HIT. The free suspension remains
useful as the left-adjoint/computation interface. The endomorphism-tower
definition is [Kern, Definition 3.1.4](https://arxiv.org/html/2410.02578v2#S3.SS1).
At the enriched level, [Heine, Definition 5.2.1](https://arxiv.org/html/2605.05195v2#S5.SS2)
includes alternating higher variance, which these object formulas do not
remove. The use of dependent Π notation alone does not establish a theory
different from existing categorical spectra.

### Dependent Elimination And Fibrewise Suspension

For a motive D:ΣᵘA→Cat, dependent elimination uses u:D(north), v:D(south)
and a coherent family of displayed lifts

    g(a) : Homd_D(meridian(a);u,v).

It produces a section over ΣᵘA. This is where explicit homd belongs; it
introduces no external parameter base and is not already parametrized
spectrum structure.

For parametrization, fix B and coherent pointed families Cₙ over B. When
the chosen suspension functor acts on their family profile, its fibrewise
lifting is

    (Σ_B Cₙ)(b) = Σ(Cₙ(b)).

At the ordinary functor level, base-arrow action applies Σ to the supplied
pointed transport. Structure maps are whole pointed displayed maps over B,

    σₙ : Σ_B Cₙ →_B Cₙ₊₁,

whose components are σₙ(b):Σ(Cₙ(b))→₊Cₙ₊₁(b). Their object action uses
two distinct binders:

    b:B, z:Σ(Cₙ(b)) ⊢ σₙ(b,z):Cₙ₊₁(b).

The target is indexed by b, not by the suspended element z. A target that
depends on z is instead a motive for dependent elimination. For varying
source and target families, retain the whole displayed-map owner rather
than assuming their pointwise functor categories form a covariant family.

If Suspd means this fibrewise lifting, it need not be a new primitive HIT:
functoriality of Σ and compatibility with reindexing can define it. The
objectwise formula does not yet supply the pointing, higher action and
lax/Gray variance for arbitrary directed bases. Over a groupoidal base
with space-valued levels, the classical comparison is the model Bᵒᵖ→Sp;
see [Ando–Blumberg–Gepner, introduction](https://arxiv.org/html/1112.2203v2).
For that classical comparison use space suspension, or the appropriate
groupoidal reflection of categorical suspension. Categorical suspension
need not itself preserve groupoidal carriers: the reduced categorical
suspension of the pointed discrete two-point set is Bℕ, not Bℤ.

## Two-Point Construction And Correction — 2026-09-19

Let X={a,b} be discrete. First separate three roles: X labels the new arrows,
Y indexes their target objects, and the category T being generated contains
those arrows. X need not already have any nonidentity arrows.

For sets X,Y and a map t:X→Y, define T(t) by the following free presentation:

    objects:       N and S(y), for y:Y
    generators:    μ(x):N→S(t(x)), for x:X

There are no other nonidentity arrows: no two generators compose. In
particular, N is fresh and distinct from the objects S(y). The choice of t
records which generators share an endpoint. This is an explicit ordinary
category, so its existence and mapping property can be proved directly.

For the two-point input there are two useful cases:

| Endpoint assignment | Objects and arrows | Interpretation |
| --- | --- | --- |
| Y=1, t(a)=t(b)=★ | N,S with two independent arrows μ(a),μ(b):N→S | Unreduced directed suspension of the discrete two-point set |
| Y={a,b}, t=id | N,S(a),S(b), with μ(a):N→S(a) and μ(b):N→S(b) | Freely varying targets; the directed cone 1⋆X |

The first has classifying-space homotopy type S¹, while the second is
contractible. Each nerve has no nondegenerate simplices above dimension
one, so these statements are the elementary circle-versus-tree comparison.
Neither construction needs an arrow a→b in X.

For this discrete example, the first presentation can also be obtained from
the second by identifying S(a) and S(b), keeping the two generating arrows
distinct. Equivalently it is the categorical pushout of 1⋆X along X→1.
This is an optional presentation of the free object, not a requirement to
run a join construction before specifying its generators. An ordinary
categorical quotient for a nondiscrete X must not be assumed to model higher
categorical suspension: it can identify data that should become higher cells.

Thus the user's expectation that a join appears when every input point keeps
its own endpoint is correct in this free ordinary model. The dependent
generalization should retain the endpoint assignment rather than promise
that its most freely separated endpoint case has a different underlying
category from the join.

The same input can be written as a family P over Y:

    P(y) = {x:X | t(x)=y},       X ≅ Σ(y:Y) P(y).

Then the crucial equation for the generated category is

    Hom_T(N,S(y)) ≅ P(y).

Putting both labels into one fibre yields two parallel arrows. Putting one
label in each of two fibres yields the cone. The bare total set X does not
determine which of these dependent inputs is intended. This motivates a
constructor on families, with a chosen constant-base specialization for
ordinary suspension.

The ordinary mapping property is completely explicit. A functor T(t)→D
is precisely data

    n:Obj(D),       s:Y→Obj(D),
    γ(x):Hom_D(n,s(t(x))),       x:X.

The extension sends the objects and generating arrows to these specified
values. The only composition laws to check are identities. A transformation
between two such functors consists of components at n and the s(y), with
the commuting square for each γ(x). This also identifies the whole functor
category with the corresponding category of data, not just its object set.

For X={a,b}, Y=1, this says exactly that a map out of the directed suspension
chooses two objects and two parallel arrows between them.

### Where The Original Dependent Hom Appears

Now let E:T(t)→Cat be a strict covariant family. A section of its total
projection is specified by

    u:E(N),       v(y):E(S(y)),
    g(x):Homd_E(μ(x);u,v(t(x))).

In the reference interpretation the last line means

    g(x):Hom_{E(S(t(x)))}(E(μ(x))(u),v(t(x))).

This is the earlier displayed-arrow formula with its base arrows generated
in T(t). It is the dependent elimination/section principle for this free
category. Freeness supplies the section extending these data; for this
discrete input there are no additional nonidentity compositional relations.

For the ordinary suspension there are u:E(N), v:E(S), and two independent
displayed arrows over μ(a) and μ(b). For the varying-target case the two
target objects lie in the distinct fibres E(S(a)) and E(S(b)).

The index of the generating data g is X. The resulting section is over
T(t). These roles differ from the earlier assignment A=C₀′, B=C₀. The
user's earlier domain correction was right for that fixed boundary setup;
it did not specify the generator/base distinction needed to construct the
new object. If an enlarged C₀′ is intended to carry newly generated p,
it belongs on the generated-base side of this distinction.

The generated arrows live in T(t), not between the labels in X. Adding an
arrow a→b to the generator-index category and requiring g to be coherent
along it is extra input: it can impose an equation between the chosen
arrows in an ordinary model, or a comparison 2-cell in a higher model.
For example, sections of a constant two-element set over the discrete
two-point category can choose the two values independently; sections over
the walking arrow must choose equal values. Such a change must not silently
identify the two meridians of the suspension of a discrete set.

This gives a precise role to the user's p idea: p is introduced by the
constructor, and g specifies its dependent lift. A join-like source of p
is compatible with dependent elimination. The existence of a dependent
eliminator alone does not, however, establish a new suspension functor:
the generalized input family and its retained endpoints supply that further
content.

### A Small Adjunction That Can Already Be Established

Extend the ordinary model to a category Y and a covariant set-valued family
P:Y→Set. Form a category L(Y,P) containing Y as a full subcategory and
one new distinguished object N, with

    Hom(N,y)=P(y),       Hom(y,N)=∅,       Hom(N,N)={id_N}.

The homs within Y are unchanged, and composing p:N→y with h:y→z is the
element P(h)(p). The functor laws for P give the remaining category laws.
This is the ordinary collage of the family, or weighted cone. The general
collage definition and mapping property are recorded in
[Shulman, Definition 4.1 and Theorem 4.3](https://arxiv.org/html/1507.01065#S4).

Let FamCov have objects (Y,P) and morphisms (F,α), where F:Y→Z and
α:P⇒Q∘F. Let Cat₊ here mean categories with a chosen object and functors
preserving that object strictly. Define

    R(D,d) = (D, Hom_D(d,−)).

A pointed functor L(Y,P)→(D,d) is exactly a functor F:Y→D together with
a natural family α:P⇒Hom_D(d,F(−)): its values on arrows from N are α,
and its other values are F. Conversely these data uniquely define the
pointed functor. The correspondence is natural in both variables, giving

    Hom_Cat₊(L(Y,P),(D,d)) ≅ Hom_FamCov((Y,P),R(D,d)),
    L ⊣ R.

This adjunction is an ordinary mathematical construction, not merely a
proposed mapping formula. The constant-base case Y=1 gives the directed
suspension of a set. The constant-singleton family P gives the ordinary
join 1⋆Y. The right adjoint retains the whole varying-target Hom family,
including postcomposition, rather than just the diagonal endomorphism set.

This supplies a concrete semantic comparison for native hom_int. Its
displayed section principle supplies the homd comparison above. It does
not replace native hom_int/homd_int with a second implementation calculus.
The generic higher collage and its relevant action profiles are not
currently qualified by the emdash kernel.

For a strict ordinary Y and a strict family P:Y→Cat, a corresponding strict
2-category model has Hom(N,y)=P(y) and the old homs of Y as discrete
categories. Objects of P(y) become 1-cells; arrows of P(y) become 2-cells;
postcomposition is P's functor action. This explains the dimension increase
without interpreting arrows in the input as equations between generators.
Arbitrary weak omega-categorical bases, dependent families and Gray/lax
profiles require their own extension of this model and its mapping property.

### Pointing And Reduction

The user's original C₀ was pointed, so an additional distinction is needed.
Mark a∈X and reduce the free presentation by making μ(a) an identity. This
identifies N with S(t(a)) as well as imposing that arrow relation.

For the same X={a,b}, the results are:

| Endpoint assignment | Reduced presentation |
| --- | --- |
| Y=1 | One object, one freely generated endomorphism from b: the walking endomorphism category Bℕ |
| Y=X, t=id | Two objects a,b and one nonidentity arrow a→b: the walking arrow |

The basepoint label becomes an identity only in this reduced construction.
Identifying endpoints without specifying what happens to the marked arrow
is a different construction. These are ordinary free presentations for this
discrete input; no general higher quotient rule is asserted. The distinction
agrees with the role of the marked meridian in reduced categorical
suspension; see [Kern, Construction 3.1.1](https://arxiv.org/html/2410.02578v2#S3.SS1).

The reduced varying-target presentation closely matches adjoining a path
from the original selected point to the other input point. Its groupoidal
realization is an interval, whereas Bℕ has the circle homotopy type. These
different outcomes record different endpoint data, not failure of the free
construction. Requiring the generated arrow itself to be invertible is a
further choice.

### Displayed Categories And Transport Families Must Be Distinguished

There is a useful check on the original covariant-family formula. The
minimal parallel-arrow suspension projects to I=(0→1), sending N to 0, S
to 1 and both generators to the same base arrow. Both fibres are terminal.
This projection is a displayed category, but it is not a cocartesian
fibration: neither of its two lifts factors the other through a vertical
arrow, since the only vertical endomorphism of S is id_S.

Consequently that minimal projection cannot be the Grothendieck total of a
strict covariant E:I→Cat with terminal fibres. Such a family has exactly one
displayed arrow over the generator, by Hom_1(★,★)=1. General displayed
structure and a family with chosen covariant transport are different notions.

A transport-family presentation is nevertheless available with extra data:
take E(0)=1 with object u and E(1) the free category with objects w,v and
two arrows w→v. Let E(0→1)(u)=w. Its homd at u,v is the two-element set.
The total has the extra object (1,w) and the canonical transport arrow
(0,u)→(1,w); its full subcategory on (0,u),(1,v) is the minimal suspension.
This is exactly the ordinary free-diagram example retained later in the
review, now with its extra-object boundary made explicit.

In the dependent eliminator above, E is instead a motive over the already
generated T(t). There is no requirement that T(t) itself be a transport
family over I. Keeping these two uses of displayed categories separate
prevents the previous typing discussion from excluding the basic example.

The revised immediate recommendation is to use this explicit family/collage
model and its two-point controls as the starting comparison. The remaining
research is the native higher construction, its profile-correct displayed
eliminator, the choice of retained boundary data between levels, and eventual
stabilization. Existence of the small ordinary adjunction is no longer an
unspecified prerequisite.

## Fixed-Base Dependent-Hom Formulation

Use different letters for the base, the parameter category, and the displayed
family. This describes data over an already specified boundary; it is not
by itself a constructor that suspends its base B. In particular B need not
be the original input X=C₀. Set:

    B                              existing or newly generated base
    A, i : A → B                   category of allowed parameters
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

Thus g is indexed by A; in the earlier notation where A=C₀′, the user's
domain correction applies. There is no reason for it to extend to every
object of B. Substitution by (i,s,p)
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

The first reading parametrizes an existing dependent-Hom operation. The
second reading is appropriate when the requested construction introduces
new arrows, as the user's two-point suspension example requires. A free
cone may intentionally have a contraction; the observations below do not
rule out using it as a generated base.
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

The latest clarification selects a smaller immediate boundary: qualify the
whole Π-section interpretation, its existing join presentation, the
walking-arrow suspension example, and the reduced pointed algebra interface.
Categorical prespectrum data can then use the pointed End formulation
without waiting for a new dependent suspension primitive. A generic
suspension recursor/uniqueness theorem and the higher family action remain
separate implementation milestones.

The earlier displayed-arrow and family/collage constructions have explicit
ordinary reference models. The following controls remain relevant to those
more general alternatives; they are not additional prerequisites imposed
on the newly clarified prespectrum interface.

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
