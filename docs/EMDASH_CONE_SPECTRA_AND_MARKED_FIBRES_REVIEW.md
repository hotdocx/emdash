# Cone Spectra, The Join–Slice Adjunction, And Marked Fibres

Date: 2026-09-20

Status: ordinary adjunction and obstruction arguments; proposed higher relative/flagged continuation

Scope: the user's intended suspension is now the left cone J(A)=1⋆A,
pointed at its new north vertex. The old point is retained by its meridian,
not identified with north. This supersedes the preceding recommendation to
make reduced suspension the default for this research question. No kernel
implementation, profile migration, persistent goal or Git mutation is begun.

The [earlier review](EMDASH_DEPENDENT_SPECTRA_RESEARCH_REVIEW.md) retains the
Π-section/source audit and the history of the alternative formulations.
Source was inspected at the clean checkpoint 5d358a56. The positive results
below are ordinary mathematical reference arguments. The known higher
variance/profile defects remain qualifications on the active emdash encoding.

## Assessment

The left cone has a genuine adjunction with a varying-endpoint construction:
the join–slice adjunction, specialized to cone and coslice. The user's
meridian is the dependent component of its unit. A meridian at the old
basepoint is a legitimate point in the corresponding fibre/total category.
Neither fact requires that meridian to be an identity.

Two further distinctions control the spectral question. First, retaining the
old point as a nonidentity arrow changes the category of structured objects
in which the adjunction lives. Second, a bare cone cannot replace suspension
in a nontrivial reduced homotopy-invariant cohomology theory. Retaining a
boundary inclusion or a dependent family may avoid losing the necessary
information, but that makes the relative structure essential to the theory.

## The Ordinary Cone–Coslice Adjunction

Let Cat₊ mean the category of ordinary categories with a chosen object and
functors preserving that object strictly. Define

    L : Cat → Cat₊,       L(A) = (1⋆A,N),
    R : Cat₊ → Cat,       R(C,c) = c↓C.

An object of c↓C is an arrow p:c→y. A morphism from p:c→y to q:c→z is
an arrow u:y→z satisfying u∘p=q. A tip-preserving functor 1⋆A→C is exactly
a functor F:A→C with a natural cone m:const_c⇒F. This is equivalent to a
functor A→c↓C, sending a to m(a):c→F(a). Hence

    Hom_Cat₊((1⋆A,N),(C,c)) ≅ Hom_Cat(A,c↓C),
    L ⊣ R.

This is the terminal-left-factor case of the standard
[join–slice adjunction](https://kerodon.net/tag/016H). With transformations
fixed at the tip, the same description identifies the corresponding
ordinary mapping categories.

The unit is the whole functor

    η_A : A → N↓(1⋆A),
    η_A(a) = (inclusion(a),meridian(a)).

Its composite with the coslice target projection is inclusion. The
meridian alone is a section of the pullback family

    a ↦ Hom_{1⋆A}(N,inclusion(a)).

Together, inclusion and that section present η_A. Thus the user's unit
intuition is correct after packaging its source and target this way. A
section-valued presentation of a unit does not require a new species of
adjunction; the Grothendieck total converts the section into an ordinary
map. A specifically fibred/indexed adjunction would additionally require
the relevant compatible reindexing structure.

The counit sends a cone on c↓C to C: its new tip goes to c, an object
p:c→y goes to y, and its generating meridian goes to p. These descriptions
also verify the two ordinary triangle identities: restricting the counit
after the unit recovers the original inclusions and arrows.

For a fixed F:A→C, the section category Π(a:A),Hom_C(c,F(a)) is the
category of cones over that particular F. A right adjoint defined only
from (C,c) cannot assume F or an inclusion is already supplied. It must
either totalize the endpoint data, as c↓C does, or live in a richer category
whose objects retain that boundary functor.

## Keeping The Family Rather Than Its Total

There is a useful factorization through the family/collage adjunction of
the earlier review:

    A → (A,constant 1) → Coll(A,1)=1⋆A,
    (C,c) → (C,Hom_C(c,−)) → total = c↓C.

Here the arrows indicate successive operations. The right adjoint of
A↦(A,constant 1), in the ordinary covariant-family category, is the
Grothendieck total. The right adjoint of the collage construction is the
represented Hom family. Composing the two adjunctions gives cone–coslice.

Consequently retaining (C,Hom_C(c,−)) is meaningful, but its paired left
operation is the collage on families; the pure cone is its constant-1
specialization. One cannot keep the old Cat→Cat₊ left functor and silently
change the right functor's codomain from Cat to a category of families.

Also distinguish the full coslice from the family restricted to inclusion.
In the ordinary cone J(A), north is initial, so

    Hom_{J(A)}(north,inclusion(a)) = 1.

The restricted family's total is therefore equivalent to A. The full
coslice north↓J(A), however, also contains id_north and is isomorphic to
J(A). For a discrete two-point A, these totals have respectively two and
three objects. Recovering A from its restricted cone family is retention
of the boundary, not already a stabilization theorem.

These terminal-fibre statements are specific to the ordinary strict cone.
A higher lax cone retains triangle and higher comparison cells; its Hom
categories must not be declared terminal merely by analogy with this model.
In the classical space cone the paths from north to any included point do
form a contractible fibre, so the restricted path family is equivalent to
the terminal family over A. Keeping that base preserves A, but by itself
does not create the classical suspension's degree shift.

## The Point Of A Displayed Family

For a pointed base (A,a★), a family E:A→Cat with a chosen object

    e★ : Obj(E(a★))

is a family with a marked fibre object. Equivalently, its total has the
point (a★,e★), and the projection to A preserves the selected points.
This is ordinary pointed/displayed data, not a new kind of object forced
by spectra. An arbitrary point of the total also chooses its base point;
requiring its first component to be the already chosen a★ is the extra
compatibility condition.

For the user's family

    H_A(a) = Hom_{J(A)}(north,inclusion(a)),

the chosen point is precisely

    (a★,meridian(a★)) : Obj(Σ(a:A) H_A(a)).

It is well typed even when meridian(a★) is noninvertible. It is an object
of a Hom category, hence a 1-cell in J(A); its identity as a fibre object
is the 2-cell id_meridian(a★). There is no reason to identify the original
1-cell with id_north, whose target is different.

One marked fibre object is less data than a section over every a. The
meridian constructor actually provides such a whole section, from which
the marked fibre object is obtained by evaluation. A pointed object of the
slice Cat/A, in the usual sense, instead includes a section of the whole
projection; that terminology should not be confused with a point in one
specified fibre. Nor does a general lax section automatically give a
strict/pseudo family of pointed categories preserved by transport.

The two basepoints must remain separate: H_A has base A pointed at a★;
J(A) is pointed at north. Inclusion sends a★ to inclusion(a★), not to
north. If one instead views Hom_{J(A)}(north,−) as a family over J(A)
pointed at north, the marked meridian lies over inclusion(a★), not over
that basepoint. Restricting along inclusion, or retaining that additional
marked endpoint, is essential to the user's stated fibre point.

## An Exact Pointed Lift Using A Marked Arrow

The choice of north as the cone point is coherent. What it does not do is
make inclusion a point-preserving map. Its defect is exactly the retained
arrow

    p★ = meridian(a★) : north → inclusion(a★).

Thus the natural output remembers a marked arrow, not only its source.
Let Cat⟨→⟩ mean ordinary categories with a chosen arrow and functors
preserving that arrow, including its endpoints. Define

    L₁(A,a★) = (J(A),meridian(a★)),
    R₁(C,p:c→d) = (c↓C,p).

Then L₁:Cat₊→Cat⟨→⟩ is left adjoint to R₁. A map from L₁(A,a★) to
(C,p) is a cone with F(a★)=d and m(a★)=p. Under the ordinary cone–coslice
correspondence this is exactly a pointed functor

    (A,a★) → (c↓C,p).

The unit takes a★ to meridian(a★), not to id_north. The counit described
above preserves the selected arrow. This proves the marked ordinary
adjunction directly and realizes the user's pointing convention without
collapsing either endpoint.

This is also the usual lifting of the cone–coslice adjunction to
undercategories: a marked input point is a map 1→A, and its cone is the
map from the walking arrow J(1) that selects meridian(a★).

There is a useful obstruction to skipping this extra structure. The
endofunctor on Cat₊ which forgets the old point and returns (J(A),north)
cannot be a left adjoint in the ordinary point-preserving category:
the initial object is the one-object pointed category, but its image is
the walking arrow pointed at its source, which is not initial. For example,
there are two point-preserving functors from that walking arrow to itself.
Left adjoints preserve initial objects.

Allowing directed comparison arrows as part of a pointed map changes the
ambient category and may provide another formulation. Its limits, zero
objects, adjunction and stability properties would then need their actual
definitions; the obstruction above concerns ordinary point-preserving maps.

For iteration, a category with only one selected object does not determine
which outgoing arrow should point its next coslice. The user's marked
meridian supplies that missing choice. Further shifts may need further
marked cells or boundary flags. A tower can record them, but merely allowing
an arbitrary new mark at each step does not prove that its shift is an
equivalence: a predecessor then carries choices not determined by its
successor. A complete shifted context must account for those choices.

## The Obstruction To The Usual Absolute Suspension Axiom

Consider the classical space interpretation of the proposed operation:

    J(X)=Cone(X), pointed at its new tip.

This is pointed contractible. Therefore, for any reduced homotopy-invariant
cohomology theory E,

    Ẽᵏ(J(X))=0.

If one asks for the usual suspension isomorphism with J in place of Σ,

    Ẽᵏ(X) ≅ Ẽᵏ⁺¹(J(X)),

then Ẽᵏ(X)=0 for every X and k. This is a direct argument from reducedness,
homotopy invariance and contraction of the cone. Thus nontrivial ordinary
generalized cohomology cannot satisfy that axiom for the bare cone.

The coslice side gives the same warning. For a groupoid C, c↓C is
contractible: between p:c→y and q:c→z the unique arrow is q∘p⁻¹.
For spaces the total based-path space is likewise contractible. Changing
its chosen point from id_c to p does not change its homotopy type. Hence
an Ω-like equivalence to that bare total has a trivial groupoidal result.

These conclusions do not prove that all directed or relative cone theories
are trivial. A directed category with an initial object need not be
equivalent as a category to the terminal category, and a higher lax cone
need not have strictly terminal Hom categories. The argument specifically
rules out recovering nontrivial ordinary reduced cohomology by forgetting
the retained data and using the bare topological cone as suspension.

At the ordinary level iterated cones on a point give [1], [2], [3], ... .
This suggests simplex/flag or resolution structures. Such iteration alone
does not supply the inverse shift, excision or additive structure of a
stable theory. Higher join versions have their corresponding coherence
data, so this ordinary ordinal calculation is not asserted as the exact
normal form of the current lax omega-level kernel join.

## What Retaining The Boundary Can Recover

A concrete way to keep the cone primary is to retain the diagram

    A --inclusion--> J(A),     north,     meridian(a★).

In the space comparison this includes the cone pair (Cone(A),A). For a
well-pointed CW model, the quotient Cone(A)/A is unreduced suspension;
collapsing the marked meridian as well gives reduced suspension. These can
be derived observations of the retained diagram rather than the primary
directed objects.

Relative cohomology records the information lost by forgetting A. The long
exact sequence of the cone pair, together with the splitting supplied by
a★, gives

    Eᵏ⁺¹(Cone(A),A) ≅ Ẽᵏ(A).

For ordinary integer cohomology and A a discrete two-point set, the cone
itself has H¹=0, while

    H¹(Cone(A),A) ≅ ℤ.

Indeed the relevant cokernel is that of the diagonal map ℤ→ℤ² on H⁰.
This is an elementary nontrivial comparison case for a cone-based theory.
For a one-point A the relative group vanishes, as expected.

Retaining only north and one meridian, while forgetting the boundary as a
whole, is not enough for this comparison. The family projection, its base
and the inclusion supply the missing structure. A possible programme is
therefore relative/flagged directed stabilization with a classical cofiber
observation. This is a design proposal, not an existing equivalence with
spectra or a proof of its stability axioms.

The mark being nonidentity also has an algebraic consequence. Hom_C(c,d)
has left End_C(d) and right End_C(c) actions, but its objects do not have
the same concatenation operation as endomorphisms of a single point.
Choosing p:c→d gives a point, not an automatic unit for such a multiplication.
If p is an equivalence, postcomposition by a chosen inverse identifies
(Hom_C(c,d),p) with (End_C(c),id_c), with the required coherence. Without
invertibility that argument is unavailable. Infinite-loop/additivity
arguments consequently need the actual compatible higher composition;
they do not follow just from choosing a point in the Hom.

## Higher Comparison And Next Mathematical Gates

The known name is join–slice adjunction. A relevant higher reference is
[Ara–Maltsiniotis, Join and slices for strict infinity-categories](https://arxiv.org/abs/1607.00668v4),
which constructs higher joins and right adjoint slices, while explicitly
distinguishing higher lax/oplax functorialities. The newer
[Ara–Guetta comma work](https://arxiv.org/html/2503.08832v3)
supplies a Gray framework for comma and Grothendieck functoriality. These
are comparison sources; no identification of their full interfaces with
the current emdash Π/profile encoding is established in this review.

The native candidates remain hom_int, homd_int and PathOut. The
[core PathOut definition](../emdash2/emdash3_2.lp) is the Sigma total of
the represented Hom family; the preceding review records the join owners.
Its higher comparison must respect the recorded Op, Sigma and section
diagnostics rather than treat current successful typing as a soundness proof.

The next useful milestones are:

1. Specify the exact structured level: family with one marked fibre object,
   category with a marked arrow, retained cone boundary, or a compatible
   higher flag. Do not silently forget one of these data during a shift.
2. Give the whole cone–slice adjunction at that level, including the unit's
   marked point and the appropriate higher comparison orientation.
3. Test a nonidentity marked arrow and a noninvertible triangle. The mark
   must not become an identity through an unrequested strictness rule.
4. Define the intended Ω-like equivalence over the correct base/context,
   then prove a reversible shift if that is the desired stability notion.
5. Test the groupoidal observation on the two-point cone pair. It should
   recover the nonzero relative group rather than observe only the
   contractible total cone.
6. Only then formulate the chosen excision, exactness and representability
   claims. Those are further mathematical conditions, not consequences
   of the adjunction's existence.

Reading coverage: the ordinary Kerodon adjunction statement, the primary
Ara–Maltsiniotis bibliographic/abstract record, selected Ara–Guetta
introductory comma/Grothendieck descriptions, and the active native owners
were inspected. No full review of either higher monograph/paper or new
Lambdapi qualification is claimed. The elementary constructions and
obstructions are the explicit reference arguments above. Changes are
documentation only, with exact-diff and local-link/whitespace validation.
