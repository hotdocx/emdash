# Native Duality: Syntactic Owners And Internal Computation

Date: 2026-09-12

Status: selected finite operator design; isolated prototypes checked; active kernel migration pending

Parent: [native universality and homology plan](TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_AND_HOMOLOGY_PLAN.md)

## Architectural Clarification

The implementation uses selected native category constructors, internal
functors and their fapp/tapp/Hom projection rules. It does not introduce an
operation indexed by arbitrary sets of dimensions, an external category
model interpreter, or a generic tensor/profile-transport service.

The previous revision's D_S notation explained possible semantics. Calling
that exposition the implemented architectural specification was misleading.
Its arbitrary-set calculus and transported-tensor construction are removed
from the active design. A semantic explanation may check an intended native
rule; it does not supply that rule's internal term, higher action or
computational qualification.

The selected O/R/T meanings are coherent. The complete internal calculus,
especially its native Homd target/module and downstream projection ladder,
is still being implemented. No claim that a general external account has
completed that work is intended.

The user's other scope directions remain in force: preserve hom_int and
homd_int as foundations; set further Empty/prototype-strictness audits aside;
integrate `goal/opaque-action-profile-classifiers-v3.2` after this goal.

## 1. What Actually Exists In The Code

The active nucleus is [emdash3_2.lp](../emdash2/emdash3_2.lp), still at blob
`91f1974ece225e399604dce24710bf1437ad3ef5`. Its declarations have not yet
been replaced by the prototype.

| Interface | Active nucleus | Isolated native prototype |
| --- | --- | --- |
| Op_cat | Hom(Op A)(x,y) reduces to Hom(A)(y,x) | Hom(Op A)(x,y) reduces to Op(Hom(A)(y,x)) |
| op | Functor(Cat,Cat) | Functor(CoAbove2_cat(Cat),Cat) |
| CoAbove2_cat | absent | native category constructor, with Hom computing to Op of the original Hom |
| CoAbove3_cat | absent | supporting shifted constructor, with Hom computing to CoAbove2 of the original Hom |
| Transpose_cat / CoOnly2_cat / Reverse12_cat | absent | transparent compositions of the selected constructors |
| Homd target | old section-family composite | corrected HomPresheaf composition checked in isolation; surrounding target unfinished; shared index remains an alternative candidate |
| general D_S API | absent | not proposed or implemented |

The relevant source artifacts are the
[total-op patch](../emdash2/audits/total_op_reinterpretation.patch),
[further-shift patch](../emdash2/audits/native_index_family_shift.patch),
[structural Sigma patch](../emdash2/audits/native_sigma_precomp.patch),
[index prototype](../emdash2/audits/native_homd_index_prototype.lp) and
[whole-family prototype](../emdash2/audits/native_index_family_prototype.lp).
They run against copied owner-position prefixes. They are not imported into
the active library.

The subsequent [HomPresheaf owner patch](../emdash2/audits/hom_presheaf_transpose.patch)
corrects an existing defined classifier. Its guarded
[focused gate](../emdash2/scripts/check_hom_presheaf_transpose.sh) checks the
fibre Functor(Transpose(Hom_Z(x,y)),Cat), the actual homd_ endpoint and
both nonidentity argument actions. This tranche introduces only defined
helper terms and changes that defined composition; it adds or relocates
no rewrite/unification rule. Its typed source-2-cell component is an
observation, not yet a verified component formula. The remaining target
input/projection work is recorded in NUH-1D4 of the owner ledger.

Reviewer declarations such as a typed eq_refl assertion are tests of those
candidate rules. They are not the operations implementing duality. In
particular, the temporary native_op_pullback_agrees check was replaced by
an explicit typed assert, avoiding the appearance of an exported theorem.
The SOP requires typed reflexivity when testing a unif_rule; plain
`assert t ≡ u` checks conversion instead. Neither test constructs a family
by transporting along a path of family objects.

## 2. Selected Category Constructors

O and R are mathematical shorthand for the proposed native names Op_cat
and CoAbove2_cat. Their defining Hom computations are:

```text
Obj(Op_cat C) ↪ Obj C
Hom_cat(Op_cat C,x,y) ↪ Op_cat(Hom_cat(C,y,x))

Obj(CoAbove2_cat C) ↪ Obj C
Hom_cat(CoAbove2_cat C,x,y) ↪ Op_cat(Hom_cat(C,x,y)).
```

The first reverses all positive-dimensional cells; the second keeps
1-arrows and reverses their higher cells. Iteration is obtained by applying
the existing Hom eliminator again. No external enumeration of cell
dimensions is involved.

The transpose is an ordinary definition:

```text
Transpose_cat C ≔ CoAbove2_cat(Op_cat C)
Hom_cat(Transpose_cat C,x,y) ↪ Hom_cat(C,y,x).
```

This is the source variance needed by the native ordinary Hom owners.
The prototype changes their actual source types to Transpose_cat where
appropriate; it does not replace hom_int by an external construction.

Involution and the required commutations are computational clauses at
these same owners. They must be checked with the affected projection rules,
as with any other native constructor.

## 3. The Internal Operation op

Op_cat is a category-forming syntactic constructor. The lowercase op is
its whole internal functor, with the proposed type

```lambdapi
constant symbol op
  : τ (Functor (CoAbove2_cat Cat_cat) Cat_cat);
```

Its observations stay in the ordinary native functor calculus:

```text
fapp0(op,A) ↪ Op_cat A
fapp1_fapp0(op,F) ↪ Op_func F.
```

Op_func(F) is itself a functor Op(A)→Op(B). Its full Hom action computes
through another Op_func at the original reversed-endpoint Hom action:

```text
(Op_func F)_(x,y)
  ↪ Op_func(F_(y,x)).
```

Thus transformations and further cells are handled by the next existing
Hom/fapp projection. The changed source of op records their variance
internally. A pointwise assignment A↦Op(A), without this whole action,
would not implement the required operation.

The ordinary-category convention remains understandable: opposite is
covariant on categories and functors, while natural transformations add
the next dimension. The native source CoAbove2_cat(Cat_cat) retains that
distinction in the type itself.

## 4. The Further Shift Used By The Current Prototype

The whole varying-source index construction also internalizes R. Its
current supporting constructor is:

```text
Obj(CoAbove3_cat C) ↪ Obj C
Hom_cat(CoAbove3_cat C,x,y) ↪ CoAbove2_cat(Hom_cat(C,x,y)).
```

The actual whole functor in the prototype is:

```lambdapi
constant symbol native_homwise_dual
  : τ (Functor (CoAbove3_cat Cat_cat) Cat_cat);
```

Its object projection is CoAbove2_cat; its whole Hom projection is the
existing experimental CoAbove2_functor_cat_func. This is why the current
prototype has a third supporting constructor. It is a concrete dependency
of that native whole action, not the first installment of an arbitrary
set-indexed duality API. Its final placement belongs to native integration.

Two useful aliases remain definitions:

```text
CoOnly2_cat C ≔ CoAbove2_cat(CoAbove3_cat C)
Reverse12_cat C ≔ CoAbove3_cat(Op_cat C).
```

They reverse dimension 2 alone and dimensions 1–2 respectively. Their
Hom computations follow from the selected constructors. The prototype's
native_transpose_universe and native_transpose_family are likewise
internal compositions, retaining the CoOnly2 source in their types.

## 5. Families Use Native Internal Action

The user's final clarification confirms that Op_catd means pointwise
opposite. It is not the opposite of the entire total projection. Keep E
for the family, E[x] for its fibre and π:Sigma_cat(E)→K for its total
projection, so these different inputs are not conflated.

The proposed family constructor has this actual native type:

```lambdapi
injective symbol Op_catd [K : Cat] (E : τ (Catd K))
  : τ (Catd (CoAbove2_cat K));
```

It remains an injective primitive symbol. There is no `≔` body and no
primitive-to-defined-symbol migration. The composite-to-constructor fold
is a separate computational clause:

```text
op ∘ CoAbove2_func(E) ↪ Op_catd(E).
```

This clause relates the native internal action to its stable primitive
head. It is not a metalevel definition by applying an external model.

The operation levels are distinct:

| Native term | Type in the corrected prototype | Object value at x |
| --- | --- | --- |
| Op_func(E), with E:K→Cat | O(K)→O(Cat) | E[x], viewed as an object of O(Cat) |
| CoAbove2_func(E) | R(K)→R(Cat) | E[x], viewed as an object of R(Cat) |
| Op_catd(E) | R(K)→Cat | O(E[x]) |
| Op_func(π), with π:ΣE→K | O(ΣE)→O(K) | the ordinary total-functor dualization |

In particular, CoAbove2_func(E) does not first replace the fibre E[x]
by R(E[x]). Composing with the internal op therefore produces O(E[x]),
not T(E[x]). Pointwise opposite and opposite of the total projection must
not be identified by an unqualified formula for Sigma totals.

Its whole constructor package is:

```text
Op_catd_func K
  : Functor(CoAbove2_cat(Catd_cat K),
            Catd_cat(CoAbove2_cat K)).
```

At points the result computes to Op_cat(E[k]). At arrows the package
projects to Op_funcd; its fibre component projects to Op_func of the
original fibre component. The family is built through the internal op and
CoAbove2_func action, with a constructor fold for the resulting composite.
It is not computed by an external procedure on semantic family records.

The base change is explicit. For a base functor F, the corresponding
reindexing comparison uses CoAbove2_func(F). An ordinary 1-category K
has no higher directed cells to reverse, which explains the familiar
same-base presentation in that specialization.

The first higher base cell explains the shift directly. If α:p⇒q in K,
then E(α):E(p)⇒E(q). Reversing the component arrows inside the fibres
gives E(α)ᴼ:E(q)ᴼ⇒E(p)ᴼ. Base 1-arrows still act by functors
E(x)ᴼ→E(y)ᴼ, while base 2-cells act in the reversed direction.
CoAbove2_cat(K) records exactly this behavior and its higher iterations.
The internal construction is the composite

```text
CoAbove2_cat(K) ─CoAbove2_func(E)→ CoAbove2_cat(Cat_cat) ─op→ Cat_cat.
```

Lax/oplax directions must be read from the particular native operator's
type and action. This design supplies no generic external mechanism that
silently converts one context to another. Concrete native comparison and
projection owners must express any needed passage. The separate global
strictness migration remains outside this goal.

## 6. Native Homd Keeps Its Syntactic Ownership

The proposed shared index changes the target classifier of homd_int. It
bundles the existing y,v,a arguments of homd_(FF,x,u,y,v)[a]; it does not
add a new kind of dependent Hom. This is a substantive packaging proposal,
so its necessity must be justified against the direct old/new owner types.
Its minimality has not been established by the auxiliary prototypes.

The shared index is a supporting native construction. In the current
prototype, with C=Sigma_cat(D), it is assembled from:

```text
native_index_hom_catd(D,x) ≔ hom_(Sigma_proj1_func(D),x)
J_x ≔ Sigma_cat(Op_catd(native_index_hom_catd(D,x)))
S_x(D) ≔ CoAbove2_cat(J_x).
```

The suppressed bases in this display are explicit in the checked LP
prototype: Op_catd changes C to CoAbove2_cat(C). Its points are native
Sigma constructors retaining (y,v,a:x→y), and its arrows retain
(s,β:D(s)v→w,θ:b⇒s∘a). The existing prototype computes structural source
arrows and source-2-cell components through native owners.

The whole family and target are also actual internal compositions:

```text
native_index_family(D) : Reverse12_cat(Z) → Cat
native_homd_target_family(D) : Catd(CoOnly2_cat(Z))
native_transpose_family(E) : Catd(CoOnly2_cat(Z)).
```

The intended homd_int(FF) relates the last two families. Its source-fixed
value is a whole functor on S_x(D), whose endpoint observation is

```text
Hom_(E[y])(E[a](u),FF[y](v)).
```

This is still homd_int's internal operation and projection ladder. The
supporting index does not redefine dependent Hom from a total-category
projection. Nor is a manual cone/factor record the primary program.

The remaining work includes the family-map/module action, complete native
homd source/target and projections, and their downstream consumers.
Existing point and source-action computations do not certify that the
entire ladder is already implemented.

The immediate priority is the direct homd_int source/target and projection
adjustment. The explored G:D→D′ index map concerns additional naturality
in the family parameter and is parked until a direct native consumer needs
it. It must not replace the primary homd_int(FF) constructor by an
identity-specialized Hom followed by auxiliary map operations.

## 7. What Is And Is Not Settled

The selected dual constructors have clear intended meanings and a concrete
syntactic implementation strategy. Several corresponding native operations
already compute in the isolated prototypes. That is the established
boundary.

The full internal duality/Homd calculus is not yet completed. In particular,
mathematical notation for a duality cannot stand in for a missing internal
whole constructor, a required comparison, or its next action. The earlier
claim that an external general framework settled the internal architecture
was too broad.

Proceed with the selected native owners and make the direct homd_int
adjustment explicit before expanding auxiliary index functoriality. Finish
native target integration and the universality/homology rows. Validate the
affected whole action and its concrete projections with localized guarded checks.
No D_S API, arbitrary tensor transport, further Empty audit, or integration
of the other profile branch is scheduled in this goal.

Preserve the existing rewrite/unif architecture while making the required
variance adjustments. In particular, opposite/reindexing naturality was
already a proof-time unification comparison; its two runtime histories
should not be collapsed just to accommodate a new consumer. Additional
comparisons or rule moves must be justified at a concrete core owner.
