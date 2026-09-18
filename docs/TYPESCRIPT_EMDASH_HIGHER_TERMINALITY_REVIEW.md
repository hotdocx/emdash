# Higher Terminality: Whole Data, Profiles And Current Boundaries

Date: 2026-09-18
Status: UA-3 review; ordinary primary family interface remains qualified
Authority: [living universality plan](TYPESCRIPT_EMDASH_CATEGORICAL_UNIVERSALITY_INVENTORY_AND_FOLLOWUP_REVIEW.md)

## Decision

Keep the primary implemented family interface at the existing adjunction
owner: p:C→1 ⊣ t:1→C for terminality, and t⊣p for initiality. Its ordinary
family consumers are derived and already used by native kernel/cokernel
inputs. Keep their ordinary guards and actual inverse maps. The old selected
TerminalObject package remains an adapter input with its current cuts; do
not add !ₜ↪idₜ or a global terminal-uniqueness unifier in this goal.

The higher design should express contraction of the whole represented Hom
family. The existing native vocabulary already forms the relevant types:

```text
R_t = hom_con(C,t,C,id_C) : Catd(Op_cat C)
L_t = hom_(C,C,id_C,t)    : Catd(C)

CatdContraction(R_t)     terminal direction
CatdContraction(L_t)     initial direction
```

These use the original internal Hom owners. They do not define dependent Hom
through a projection or replace hom_int/homd_int. Forming these types does not
construct their inhabitants from the old TerminalObject data.

The original package's higher interpretation needs a specified naturality
profile and a whole contraction proof. That work belongs with the deferred
profile/duality qualification. This goal completes the ordinary migration and
the present review; it does not silently extend their interpretation to all
directed ω-categories.

## What The Original Package Actually Supplies

[TerminalObject](../emdash2/emdash3_2_terminal_objects.lp) includes all of:

- a selected t and one whole !:id_C⇒const_t;
- canonical components !ₓ:x→t;
- the off-diagonal point action ![f]↪!ₓ;
- the cut !ᵧ∘f↪!ₓ;
- IsContr(Obj(Hom_cat(C,x,t)));
- derived uniqueness paths f=!ₓ and !ₜ=idₜ.

It is therefore inaccurate to treat the package as only its IsContr field.
Conversely, its displayed point rules do not by themselves say that the
entire Hom-action functor is constant on directed higher cells. A functor can
have one object value and still act nontrivially on endomorphisms. The
generic action and naturality profile must be included in the interpretation.

## Why The Profile Matters

For the 2-dimensional terminology, strict 2-naturality constrains both arrows
and 2-cells; pseudonaturality supplies invertible comparison cells, while lax
naturality permits noninvertible ones. These distinctions are explicit in
clingman–Moser, Definitions 2.1 and 3.1, and in Lack's discussion of weak
morphisms. [clingman–Moser](https://link.springer.com/article/10.1007/s10485-022-09691-z),
[Lack](https://www.math.uchicago.edu/~may/IMA/Lack.pdf).

The following argument is this review's own 2-categorical analysis. Suppose
!:id_C⇒const_t is pseudonatural and !ₜ is isomorphic to idₜ. Fix x and put
D=C(x,t). Naturality supplies an invertible natural comparison

```text
const_(!ₓ) ≅ (!ₜ∘−) : D→D.
```

Whiskering the isomorphism !ₜ≅idₜ supplies (!ₜ∘−)≅id_D. Thus
const_(!ₓ)≅id_D as whole functors. Together with the canonical D→1 and the
chosen object !ₓ:1→D, this gives D≃1 with actual inverse data. The source-variable
coherence comes from the whole naturality data, in the corresponding strict
or pseudo sense; a strict presentation of a pseudonatural family needs its
own qualification. Strict naturality is a
special case. This explains why the full ! package can be much stronger than
object/core contractibility when its naturality comparisons are invertible.
An ω-dimensional version must retain the corresponding coherent higher data;
the 2-dimensional argument alone is not its implementation or qualification.

A small lax example separates the assumptions. Take a strict 2-category with
objects x,t and hom-categories

```text
C(x,x)=1,  C(t,t)=1,  C(t,x)=∅,
C(x,t)=D.
```

D has one object u and endomorphisms {1,z}, with z²=z and z absorbing.
Only 1 is invertible. Composition with the two identity hom-categories is
the evident identity action. Define !ₓ=u and !ₜ=idₜ. A normal lax transformation
id_C⇒const_t has comparison z at u and identity comparisons at identity arrows.
Its identity/composition axioms hold; naturality for z is z=z². Both hom-cores
into t are terminal groupoids, and the stated point action and terminal cuts
hold. Yet D is not equivalent to 1, since its endomorphism set has two elements.

This example concerns the stated lax interpretation of these data. The
branch's globally installed strictness rules and unprofiled higher operations
remain under their separate recorded qualification. No kernel inconsistency
test or alternative implementation theory is introduced here. The missing
invertibility is substantive; it is not repaired by changing the notation
for IsContr or by identifying !ₜ with idₜ at runtime.

## What Already Follows From A Supplied Adjunction

For a supplied J:p⊣t, the existing whole
Adjunction_hom_prof_comparison(J) retains the coherent comparison over the
entire represented profunctor. Evaluation at (x,★), followed by the existing
DefIso symmetry, gives

```text
Hom_cat(C,x,t) ≅ Terminal_cat.
```

For J:t⊣p, evaluation at (★,x) gives Hom_cat(C,t,x)≅Terminal_cat directly.
These are whole Hom functors with selected inverses, not merely paths between
objects. The conditional audit forms these data and their inverse cuts with
no OneCat(C) assumption. It also retains the original whole terminal-direction
profunctor comparison. The corresponding family-contraction types above form
using the native hom_con/hom_ owners.

The premise J already supplies the strong computational Hom-comparison
contract. This observation does not derive J from the old T or identify all
weak higher universalities with the current DefIso-valued contract. The
existing selected-terminal adapter and the ordinary family-diagram operations
still need their stated guards. Public generic mate operations already expose
these conditional observations, so this review adds no redundant public API.

## Requirements For A Later General Upgrade

1. Specify the strict, pseudo or lax naturality of the whole terminal family,
   including the invertibility needed to contract every directed Hom level.
2. Construct the whole represented-family comparison with its selected inverse
   through the native Hom and family owners; point/core contraction is a
   downstream observation.
3. Qualify the higher meaning of the chosen inverse laws in the relevant
   functor categories. Object univalence alone does not erase noninvertible
   directed cells. For groupoidal Homs or genuinely truncated observations,
   paths remain suitable and can be simpler. With suitable category/functor-
   category univalence, a whole equivalence can be expressed by equality at
   that level; retain its actual maps for operational use.
4. Qualify the higher adjunction lift and arrow/diagram realization separately.
   Their current ordinary constructors cannot be generalized by deleting C1.
5. Review the old cuts and selected choices independently of this semantic
   upgrade. The working bare-variable uniqueness unifier remains positive
   inference evidence; it does not supply the whole contraction or resolve
   the !ₜ/identity critical pair.

The next execution gate for that upgrade is the deferred profile/duality work,
followed by a consumer needing the higher interface. Current native homology
continues to use the qualified whole ordinary operations. No spectra,
stabilization or other future application is investigated here.
