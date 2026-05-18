# emdash v3 Catd, Hom, Pi, and Constant-Family Architecture Plan

## Status

Draft planning report for the next `emdash3_1.lp` iteration. This document
updates and supersedes the earlier `Hom_fam` / `Transf_fam` framing.

The active source remains `emdash3_1.lp`, guided by
`REPORT_EMDASH_V3_CONSOLIDATED.md`. This report is intentionally
decision-oriented: it records the intended final architecture before
implementation, including which symbols should be primitive stable heads,
which should be rewrite contracta, and which should be mere notation or
definitions that must not appear on rewrite-rule left-hand sides.

## Semantic Reset: `Catd` Means Directed Cat-Valued Family

The v3 design may keep the v2-style `catd` terminology, but only with a hard
semantic reset.

```text
old emdash2 Catd Z:
  general displayed/isofibration-like object over Z

new emdash3 Catd Z:
  directed Cat-valued family over Z
  semantically the same object as Functor Z Cat_cat
```

This keeps migration names such as `Catd_cat`, `Functord_cat`,
`Transfd_cat`, `Fibre_cat`, `Functor_catd`, and `Transf_catd`, but avoids the
old inconsistency: there is no hidden arbitrary cleavage or generic
isofibration structure. A v3 `Catd` is the canonical directed category-family
layer.

There is no need to preserve `Fam_cat`, `Fam`, or `Fam_app_cat` as alternate
public vocabulary. The final report and implementation should use `Catd`
terminology directly.

## Rewrite SOP: Canonical Heads vs Notation

The most important operational rule is:

```text
Do not duplicate operations of a redex into its contractum.
Only add primitive stable heads for genuinely new dependent, reordered,
or internal structure.
```

Definitions and aliases may be useful as local notation or later standard
library conveniences, but they should not be used as discriminants on the
left-hand side of rewrite rules. Rewrite LHSs should use primitive stable
heads and genuine canonical constructors, not abbreviations such as a
definition of `Fibre_cat` as `fapp0`.

In particular:

```text
Fibre_cat E z := fapp0 E z
```

may exist as notation, but future rewrite rules should match the canonical
underlying operation unless `Fibre_cat` is deliberately promoted to a real
primitive stable head. Under the current final design, `Fibre_cat` is
notation-only.

This SOP also applies to `fdapp0_*` and `tdapp0_*`: if they are definitions
from ordinary `tapp0`/`fapp1` operations, they should not appear in kernel
rewrite LHSs as if they were primitive constructors.

## Current v3.1 Facts To Be Replaced

The current `emdash3_1.lp` still uses the earlier family vocabulary:

```text
Fam_cat K := Functor_cat K Cat_cat
Fam K := Obj (Fam_cat K)
Fam_app_cat E k := fapp0 E k
Const_fam K A := Obj_func A . Terminal_func K
Pi_cat E := Transf_cat (Terminal_fam K) E
```

These definitions are semantically suggestive but operationally too
reducible for the intended final kernel:

- `Fam_cat` is currently an alias, not the canonical family category head.
- `Const_fam` is currently a composite, not a matchable constructor.
- `op_val_func` and `Homd_source_fam` are definitions, not stable family
  constructors.
- `Pi_cat` is represented through `Transf_cat`, while `piapp0` is already a
  primitive projection.
- `Functor_mix_fam_func K` currently packages `Functor_fam` as an internal
  curried two-argument constructor:
  `Op(Fam(Op K)) -> (Fam K -> Fam K)`. This role should not be lost; it
  should be migrated to the corrected `Catd` vocabulary if internal pipelines
  still need the packaged constructor.
- `Functor_cat` and `Transf_cat` are currently declared `constant`, which
  blocks the intended special-case contractions.

Those assumptions are allowed to change. Finding the final architecture is
allowed to relax/remove `constant` qualifiers and replace them with
rewrite-capable symbols, likely still with controlled injectivity and
unification helpers where appropriate.

## Lessons From v2

v2 contains the useful stable-head discipline but attached it to a broader
`Catd` semantics. The v3 design keeps the useful discipline and changes the
meaning.

Important v2 lessons:

- `Functord_cat` is the stable category of dependent/displayed functors.
- `Transfd_cat` is the stable category of displayed transfors.
- `Hom_cat (Functord_cat E D) FF GG --> Transfd_cat FF GG` is already the
  right hom-category contraction pattern.
- v2 distinguished fibrewise constructors such as `Functor_catd` and
  `Transf_catd` from full displayed naturality data such as `Transfd_cat`.
  That distinction remains important in v3.
- v2 kept both `tapp1_*` and `fapp1_*` as stable heads, with a rewrite rule
  saying `tapp1_*` at identity folds to `fapp1_*`. The dependent v3 story
  should mirror this with `tdapp1_*` and `fdapp1_*`.

The v3 correction is that `Catd Z` is not a general isofibration over `Z`;
it is the canonical directed `Cat`-valued family over `Z`.

## Canonical Category Spine

The core canonical rewrite spine should be:

```text
Functor_cat K Cat_cat
  --> Catd_cat K

Hom_cat (Catd_cat K) E D
  --> Functord_cat E D

@Transf_cat K Cat_cat E D
  --> Functord_cat E D

Hom_cat (Functord_cat E D) FF GG
  --> Transfd_cat FF GG
```

This is the central design discovery since the earlier report was created.

`Functord_cat` must be a primitive stable head because it is the contractum of
at least two independent redexes:

```text
Hom_cat (Catd_cat K) E D
@Transf_cat K Cat_cat E D
```

The second contraction is a major improvement over the v2 architecture:
ordinary operations for `Transf_cat` become immediately available to
Cat-valued family morphisms, and then normalize into `Functord_cat`.

`Transfd_cat` remains the canonical hom category of `Functord_cat`:

```text
Hom_cat (Functord_cat E D) FF GG
  --> Transfd_cat FF GG
```

At this level, no further analogous `Transf_cat --> Transfd_cat` contraction
has been found. A modification is a hom inside the category of family
morphisms; it is not simply an ordinary `Transf_cat` between ordinary
functors until one projects it to a base object.

## Canonical Names

The final canonical vocabulary should be:

```text
Catd_cat K
  category of directed Cat-valued families over K

Catd K
  object classifier for Catd_cat K

Fibre_cat E k
  notation for fapp0 E k, not a rewrite discriminator

Const_catd K A
  constant directed family at A

Terminal_catd K
  terminal directed family, likely Const_catd K Terminal_cat

Op_catd E
  pointwise opposite family over the same base

Functor_catd A B
  mixed-variance pointwise family of functor categories

Hom_catd E X Y
  mixed-variance pointwise family of hom categories

Transf_catd A B FF GG
  mixed-variance pointwise family of transfor categories

Functord_cat E D
  category of natural families of functors E[k] -> D[k]

Transfd_cat FF GG
  category of natural families of transformations, i.e. modifications
```

The name `Op_catd` must be documented carefully: in this v3 directed-family
layer it means pointwise opposite of fibres over the same base. If a future
base-opposite operation is needed, it should be introduced separately or
clearly distinguished.

## Alias vs Primitive Classification

### Not Primitive: Object-Level Family Projections

With the contraction:

```text
@Transf_cat K Cat_cat E D --> Functord_cat E D
```

the component functor of a family morphism is just ordinary `tapp0`
specialized to `Cat_cat`.

Therefore these are definitions or notation, not primitive kernel heads:

```text
fdapp0_func E D z
  := @tapp0_func K Cat_cat E D z

fdapp0_fapp0 FF z
  := @tapp0_fapp0 K Cat_cat E D z FF

Fibre_func FF z
  := @tapp0_fapp0 K Cat_cat E D z FF
```

This was one of the main simplifications discovered during review.

### Not Primitive: `tdapp0_func`

For a modification:

```text
Xi : Transfd_cat FF GG
```

where:

```text
FF GG : Functord_cat E D
```

the projection at a base object `z` is also not primitive. It is the hom-action
of the ordinary component projection:

```text
tdapp0_func z FF GG
  := fapp1_func (@tapp0_func K Cat_cat E D z) FF GG
```

Its domain reduces by the canonical spine:

```text
Hom_cat (@Transf_cat K Cat_cat E D) FF GG
  --> Hom_cat (Functord_cat E D) FF GG
  --> Transfd_cat FF GG
```

Its target reduces by the ordinary functor-category hom rule:

```text
Hom_cat (Functor_cat (E[z]) (D[z])) (FF[z]) (GG[z])
  --> Transf_cat (FF[z]) (GG[z])
```

Thus `tdapp0_func` is not primitive kernel structure. It may be introduced
later as notation, but rewrite LHSs should use the canonical expression unless
we intentionally promote a fold head for normalization convenience.

The corresponding object-action notation is also derived:

```text
tdapp0_fapp0 Xi z
  := fapp0 (tdapp0_func z FF GG) Xi

Fibre_transf Xi z
  := fapp0 (tdapp0_func z FF GG) Xi
```

If the v2 names `tdapp0_fapp0` or `Fibre_transf` are reused, they should be
notation or folds for this derived object-action, not independent primitive
operations.

### Primitive: Full Arrow-Level Dependent Operations

The object-level projections collapse into ordinary `tapp0` and `fapp1`
machinery. The arrow-level dependent operations do not.

The weak fibrewise hom-action is definable:

```text
fibre_fdapp1 FF z u v
  := fapp1_func (fdapp0_fapp0 FF z) u v
```

But this only acts inside one fibre category. It does not see base arrows,
dependent homs, or `homd_`-style data.

The full `fdapp1_*` must remain a dedicated stable head because it acts on
dependent hom data: base motion and fibre motion together. This is the next
simplicial/dependent iteration, not merely ordinary `fapp1_func` in a fibre.

Likewise, full `tdapp1_*` must remain a dedicated stable head. The attempted
derivation from `tapp1_fapp1_func` plus evaluation is not a clean
non-circular kernel definition; it already needs the dependent
projection/uncurrying machinery that `tdapp1_*` is meant to expose.

Therefore the final mirror is:

```text
non-dependent:
  tapp1_* at identity --> fapp1_*
  but both tapp1_* and fapp1_* are stable heads

dependent:
  tdapp1_* at identity --> fdapp1_*
  but both tdapp1_* and fdapp1_* are stable heads
```

The identity specialization rule should be retained:

```text
tdapp1_* FF FF (id (Functord_cat E D) FF)
  --> fdapp1_* FF
```

This is not evidence that `fdapp1_*` is a mere alias; it is the same pattern as
ordinary `tapp1_*` versus `fapp1_*`.

## Stable Heads Still Needed

The following remain genuine stable infrastructure, plus explicitly noted
derived folds that may be introduced for normalization convenience:

```text
Catd_cat
Functord_cat
Transfd_cat

Const_catd
Terminal_catd
Op_catd

Functor_catd
Hom_catd
Transf_catd

fib_cov_transf
fib_cov_tapp0_func
fib_cov_tapp0_fapp0

Pi_cat
full section-action folds (`piapp1*`) only if needed for normalization;
these are not ordinary `tapp1_fapp0` aliases, but derived/specialized folds
of the section-as-`Functord` dependent action

homd_
homd_int / related internal homd projections

fdapp1_*
tdapp1_*
```

The `fib_cov_*` heads remain necessary because they express a reordered,
internal family action: fix a fibre object and obtain a functor/transfor in the
base-arrow variable. Lambdapi will not derive that argument reordering
internally from ordinary `fapp1`.

## Family Constructors

### Constant Families

`Const_catd K A` should be a primitive stable constructor, not a composite
through `Obj_func A` and `Terminal_func K`.

Pointwise computation:

```text
fapp0 (Const_catd K A) k
  --> A
```

The constant action must be omega-aware. A capped rule such as:

```text
fapp1_fapp0 (Const_catd K A) f
  --> id_func A
```

is not enough by itself. Prefer a functor-level constant action, likely via a
general constant functor head:

```text
Const_func [A B : Cat] (b : Obj B) : Functor A B
```

and then:

```text
fapp1_func (Const_catd K A) x y
  --> Const_func (id_func A)
```

The exact implicit arguments should be settled by a Lambdapi probe, but the
principle is functor-level computation first, capped object-level computation
second.

### Opposite Families

The operational role currently played by `op_val_func K` should become a
stable directed-family constructor:

```text
Op_catd [K : Cat] (E : Catd K) : Catd K
```

with pointwise rule:

```text
fapp0 (Op_catd E) k
  --> Op_cat (fapp0 E k)
```

and constant compatibility:

```text
Op_catd (Const_catd K A)
  --> Const_catd K (Op_cat A)
```

`Homd_source_fam` from the current file should disappear as a current
operational dependency. Future homd source types should use the stable
pointwise-opposite constructor directly.

If internal pipelines need the pointwise-opposite operation as a functor
object, add a packaged operation such as:

```text
Op_catd_func K : Functor (Catd_cat K) (Catd_cat K)
```

but keep the primitive constructor `Op_catd E` as the normal form that future
rules target.

### Mixed-Variance Functor Families

The current `Functor_fam` should be migrated to:

```text
Functor_catd [K : Cat]
  (A : Catd (Op_cat K))
  (B : Catd K)
  : Catd K
```

with pointwise rule:

```text
fapp0 (Functor_catd A B) k
  --> Functor_cat (fapp0 A k) (fapp0 B k)
```

This is the corrected mixed-variance successor of v3 `Functor_fam`, not the
old v2 same-base fibrewise-only `Functor_catd`.

The current `Functor_mix_fam_func K` packaging should be migrated if it remains
needed for internal constructor pipelines. The corrected analogue should package
the same mixed-variance operation in `Catd` vocabulary, schematically:

```text
Functor_catd_mix_func K
  : Functor
      (Op_cat (Catd_cat (Op_cat K)))
      (Functor_cat (Catd_cat K) (Catd_cat K))
```

with object-action reducing to a curried form whose second object-action
normalizes to `Functor_catd A B`.

### Mixed-Variance Hom Families

After `Const_catd`, `Op_catd`, and `Pi_cat` are stable, introduce:

```text
Hom_catd [K : Cat]
  (E : Catd K)
  (X : Obj (Pi_cat (Op_catd E)))
  (Y : Obj (Pi_cat E))
  : Catd K
```

with pointwise rule:

```text
fapp0 (Hom_catd E X Y) k
  --> Hom_cat (fapp0 E k)
        (piapp0 X k)
        (piapp0 Y k)
```

The source endpoint is a section of `Op_catd E` because source position is
contravariant. Since `Obj (Op_cat A)` reduces to `Obj A`, this still gives an
object of the original fibre at each point.

The base-arrow action of `Hom_catd` should be expressed using the eventual
section-action layer and `homd_`, not by inventing an isolated object-level
transport head. The notation `piapp0 X k` below should be read as section
evaluation notation, not as a primitive rewrite head.

### `Functor_catd` As A Constant-`Cat_cat` Instance

Semantically:

```text
Functor_catd A B
  ~= Hom_catd (Const_catd K Cat_cat) X Y
```

More precisely, after non-dependent Pi reduction:

```text
X : Obj (Pi_cat (Op_catd (Const_catd K Cat_cat)))
Y : Obj (Pi_cat (Const_catd K Cat_cat))
```

should reduce to:

```text
X : Obj (Functor_cat K (Op_cat Cat_cat))
Y : Obj (Functor_cat K Cat_cat)
```

Then `Op_func X` has type:

```text
Functor (Op_cat K) Cat_cat
```

which canonically lands in `Catd (Op_cat K)`. The bridge should be:

```text
Hom_catd (Const_catd K Cat_cat) X Y
  --> Functor_catd (Op_func X) Y
```

The exact LHS should use stable heads and keep inferred arguments implicit.

### `Transf_catd` As A `Hom_catd` Specialization

The corrected pointwise transformation-family constructor is:

```text
Transf_catd A B FF GG
```

with intended context:

```text
A  : Catd (Op_cat K)
B  : Catd K
FF : Obj (Pi_cat (Op_catd (Functor_catd A B)))
GG : Obj (Pi_cat (Functor_catd A B))
```

with bridge:

```text
Hom_catd (Functor_catd A B) FF GG
  --> Transf_catd A B FF GG
```

and pointwise rule:

```text
fapp0 (Transf_catd A B FF GG) k
  --> Transf_cat (piapp0 FF k) (piapp0 GG k)
```

because:

```text
Hom_cat (Functor_cat (A[k]) (B[k])) FF[k] GG[k]
  --> Transf_cat FF[k] GG[k]
```

This `Transf_catd` is a functorial family of transfor categories. It is not
the same as `Transfd_cat`.

```text
Transf_catd:
  pointwise/mixed family of transformation categories

Transfd_cat:
  category of natural/displayed transformations, i.e. modifications
```

## Pi Categories

`Pi_cat E` should be a primitive stable head for the category of sections of a
directed family.

The current representation:

```text
@Transf_cat K Cat_cat (Terminal_catd K) E
```

is semantically right, but operationally conflicts with the general
`Transf_cat --> Functord_cat` contraction. The final design therefore needs
joining rules:

```text
@Transf_cat K Cat_cat (Terminal_catd K) E
  --> Pi_cat E

Functord_cat (Terminal_catd K) E
  --> Pi_cat E
```

Probably also directly or indirectly:

```text
Hom_cat (Catd_cat K) (Terminal_catd K) E
  --> Pi_cat E
```

This avoids an unjoined critical pair:

```text
@Transf_cat K Cat_cat (Terminal_catd K) E
  --> Functord_cat (Terminal_catd K) E

@Transf_cat K Cat_cat (Terminal_catd K) E
  --> Pi_cat E
```

### Non-Dependent Pi

For constant families, prefer a direct category-level reduction:

```text
Pi_cat (Const_catd K A)
  --> Functor_cat K A
```

This states the non-dependent Pi principle directly: a section of the constant
family at `A` is a functor `K -> A`.

This category-level reduction is preferable to an object-only bridge such as:

```text
Pi_const_to_func : Obj (Pi_cat (Const_catd K A)) -> Obj (Functor_cat K A)
```

because the whole section category reduces and the ordinary functor-category
infrastructure remains available.

Projection compatibility should align with ordinary functor application:

```text
piapp0 F k
  := fapp0 F k
```

in the constant-family case after `Pi_cat (Const_catd K A)` reduces to
`Functor_cat K A`. This is definitional/notation-level compatibility, not a
new rewrite rule headed by `piapp0`.

Similarly, any arrow/higher projection notation should align with ordinary
functor action:

```text
piapp1_fapp0 F f
  := fapp1_fapp0 F f
```

in the constant-family case, plus functor-level variants if the final
section-action design supports them. This line is the degenerate
constant-family collapse of the full section-action fold. It should not be
used to infer that the general `piapp1*` operation is merely ordinary
`tapp*`/`fapp*` notation.

### General Pi Projection Through `homd_`

Do not introduce an isolated projection like:

```text
piapp_base f s
```

The category in which a section's arrow component lives is already expressed
by `homd_`.

For:

```text
E : Catd K
s : Obj (Pi_cat E)
x y : Obj K
f : Hom_K x y
```

the section arrow component should be an object of:

```text
fapp0 (homd_ E x (piapp0 s x) y (piapp0 s y)) f
```

which reduces morally to:

```text
Hom_cat (E[y]) (E(f)(s[x])) (s[y])
```

There are two operations one might be tempted to call `piapp1`, and they must
be kept separate.

The weak off-diagonal object obtained from the ordinary transfor projection is
definable from `tapp1_fapp0` and terminal-object evaluation:

```text
piapp1_obj s f
  := fapp0
       (@tapp1_fapp0 K Cat_cat (Terminal_catd K) E x y s f)
       Terminal_obj
  : Obj (fapp0 E y)
```

This uses only that `Pi_cat E` is a `Transf_cat (Terminal_catd K) E`
instance. It produces an object in the target fibre. It does not produce the
dependent hom object:

```text
Hom_cat (E[y]) (E(f)(s[x])) (s[y])
```

The full section-action component is the homd-valued object:

```text
piapp1_fapp0 s f
  : Obj (fapp0 (homd_ E x (piapp0 s x) y (piapp0 s y)) f)
```

This is not a simple alias for `tapp1_fapp0` or `fapp1_fapp0`. Conceptually it
is the specialization of the full dependent action of the section-as-
`Functord`:

```text
s : Obj (Functord_cat (Terminal_catd K) E)
```

applied to the unique terminal dependent hom over the base arrow `f`. In the
same sense as full `fdapp1_*`, it sees base motion and fibre motion together.
If rewrite rules need this component as a matchable normal form, it should be
a stable derived fold/specialized projection whose ancestor is the dependent
action layer (`fdapp1_*`, or the corresponding internal `tdapp1_*` identity
fold once available), not ordinary `tapp*`/`fapp*` alone.

Thus the full `piapp1*` layer should not be scheduled as independent primitive
Pi theory. It should be implemented only after the dependent `fdapp1_*` /
`tdapp1_*` infrastructure is available, by specializing that infrastructure to

```text
s : Functord_cat (Terminal_catd K) E
```

and then projecting the image of the unique terminal dependent hom over the
base arrow `f`. This is exactly the same reason `fdapp1_*` cannot be replaced
by a weak fibrewise `fapp1_func`: the desired section component lives in a
dependent hom over a base arrow.

Thus the next Pi projection layer should be shaped around `homd_`, for
example:

```text
piapp1_fapp0 s f
  : Obj (fapp0 (homd_ E x (piapp0 s x) y (piapp0 s y)) f)
```

and preferably an iterable section-level or functor-level head should
accompany it, rather than only this capped object projection.

The object projection should also have a packaged functor form if feasible,
but this package should itself be a definition/composite, not a separate
primitive with a β-rule to `piapp0`.

```text
piapp0_func E k
  := comp_cat_fapp0
       (fapp0_func Terminal_obj)
       (@tapp0_func K Cat_cat (Terminal_catd K) E k)

piapp0 s k
  := fapp0 (piapp0_func E k) s
```

Equivalently, object-level section evaluation is terminal-object evaluation of
the ordinary component:

```text
piapp0 s k
  := fapp0
       (@tapp0_fapp0 K Cat_cat (Terminal_catd K) E k s)
       Terminal_obj
```

The exact type may need adjustment after the `Pi_cat` joining rules are tested,
but the old plan's functorial-projection requirement should be kept in this
derived/definitional form.

### Hom Of A Pi Category: Deferred Issue

The tempting rule:

```text
Hom_cat (Pi_cat E) s t
  --> Pi_cat (Hom_catd E ?s ?t)
```

should not be asserted yet. The `?s` issue is real: `Hom_catd E X Y` expects
source/target data with the mixed variance needed to make a functorial family
of hom categories. For two sections `s,t : Pi_cat E`, the variation over the
base is natural section data, not obviously the same syntactic input expected
by `Hom_catd`.

The better preliminary joining rule may be:

```text
Hom_cat (Pi_cat E) s t
  --> Transfd_cat s t
```

because sections can be read as objects of:

```text
Functord_cat (Terminal_catd K) E
```

and the hom category of `Functord_cat` is `Transfd_cat`.

This is also why the bridge:

```text
Hom_catd (Functor_catd A B) FF GG
  --> Transf_catd A B FF GG
```

should not be expected to syntactically fire here, even though the object-level
semantics is morally related. The `Pi_cat` hom problem is about natural
section data; `Hom_catd` expects mixed-variance data already organized as a
functorial family.

Then, if:

```text
alpha : Hom_cat (Pi_cat E) s t
```

is projected at a base object `z`, and then at the unique object of
`Terminal_cat`, one obtains morally:

```text
alpha z * : Hom_cat (E[z]) (s[z]) (t[z])
```

So at the object level this behaves approximately like:

```text
alpha : Pi_cat (Hom_catd E ?s ?t)
```

but syntactically and operationally this should be deferred. The report should
record the issue, not prematurely implement a fragile rule.

## Directed Hom Infrastructure

The existing `homd_` endpoint is still the right idea:

```text
homd_ E x u y v
  : Functor (Op_cat (Hom_cat K x y)) Cat_cat
```

morally:

```text
f |-> Hom_{E[y]}(E(f)(u), v)
```

In the new `Catd` vocabulary, `homd_` should be adjusted to use:

```text
Catd
Fibre_cat / fapp0
fib_cov_*
Op_catd
Functor_catd
Pi_cat
Hom_catd
```

but its final endpoint role remains the same. It supplies the dependent hom
over base arrows used by `Sigma_cat`, the eventual full section-action folds,
`fdapp1_*`, and `tdapp1_*`.

## How We Arrived Here

The earlier report focused on adding `Hom_fam` and `Transf_fam` after making
`Const_fam`, `Op_fam`, and `Pi_cat` stable. That was directionally useful but
incomplete.

The review since then discovered the canonical category spine:

```text
Functor_cat K Cat_cat --> Catd_cat K
@Transf_cat K Cat_cat E D --> Functord_cat E D
Hom_cat (Functord_cat E D) FF GG --> Transfd_cat FF GG
```

This changed the architecture. Instead of building a parallel family theory,
v3 should make the directed-family layer the canonical normal form of
Cat-valued functors, and should reuse ordinary `Transf_cat` operations before
they contract to `Functord_cat`.

Then the alias/primitive split became clear:

```text
fdapp0_*:
  aliases of tapp0_* specialized to Cat_cat

tdapp0_func:
  alias of fapp1_func (tapp0_func ...)

fibrewise fdapp1:
  alias of fapp1_func applied to the component functor

full fdapp1_*:
  stable dependent hom-action head

full tdapp1_*:
  stable dependent transformation-action head
```

The contrast is important:

```text
object-level / fibre projection:
  collapses to ordinary tapp/fapp machinery

arrow-level / dependent-hom action:
  needs its own stable simplicial/dependent head
```

Finally, the v2 naming became useful again once its semantics were reset. We
can keep `Catd`, `Functord`, and `Transfd` terminology for migration and
readability, but the new semantics is always directed `Cat`-valued families,
not arbitrary displayed isofibrations.

## Proposed Implementation Order

### Phase 0: Baseline And Report Lock

- Treat this report as the design target before editing `emdash3_1.lp`.
- Keep `emdash3_1.lp` typechecking before each implementation phase.
- Add temporary assertions only as needed to probe Lambdapi elaboration, then
  keep the useful ones as regression checks.
- Run:

```bash
lambdapi check -w emdash3_1.lp
```

- Avoid `.scratchpad/` unless explicitly doing historical recovery.

### Phase 1: Canonical `Catd` Spine

- Replace the `Fam_*` layer with canonical `Catd_*` vocabulary.
- Introduce stable:

```text
Catd_cat K
Catd K
Functord_cat E D
Transfd_cat FF GG
```

- Relax `Functor_cat` from `constant` to rewrite-capable, then add:

```text
Functor_cat K Cat_cat --> Catd_cat K
```

- Relax `Transf_cat` from `constant` to rewrite-capable, then add:

```text
@Transf_cat K Cat_cat E D --> Functord_cat E D
```

- Add:

```text
Hom_cat (Catd_cat K) E D --> Functord_cat E D
Hom_cat (Functord_cat E D) FF GG --> Transfd_cat FF GG
```

- Add controlled unification helpers analogous to the existing
  `Functor_cat`/`Transf_cat` helpers.

### Phase 2: Migrate Current Directed-Family Code

- Rename/rework existing `Fam_*` uses in `emdash3_1.lp` to `Catd_*`.
- Do not keep `Fam_*` as public compatibility vocabulary.
- Ensure definitions used only as notation do not appear in rewrite LHSs.
- Preserve current working assertions by translating them to the canonical
  `Catd` names.

### Phase 3: Constant And Opposite Families

- Add stable:

```text
Const_catd K A
Terminal_catd K
Op_catd E
```

- Add pointwise computation and constant-action rules.
- Ensure constant action is functor-level before adding capped object rules.
- Replace uses of `op_val_func`/`Homd_source_fam` in future operational rules
  with the stable pointwise-opposite constructor.

### Phase 4: Pi As A Stable Section Category

- Promote `Pi_cat E` to a primitive stable head.
- Add joining rules:

```text
@Transf_cat K Cat_cat (Terminal_catd K) E --> Pi_cat E
Functord_cat (Terminal_catd K) E --> Pi_cat E
```

- Add or preserve a section-category functor:

```text
Pi_func K : Functor (Catd_cat K) Cat_cat
fapp0 (Pi_func K) E --> Pi_cat E
```

- Add non-dependent Pi:

```text
Pi_cat (Const_catd K A) --> Functor_cat K A
```

- Add derived section-evaluation notation, not a primitive `piapp0` rewrite
  head.
- Add `piapp0_func E k` as a definitional packaged projection at a base object,
  if feasible:

```text
piapp0_func E k
  := comp_cat_fapp0
       (fapp0_func Terminal_obj)
       (@tapp0_func K Cat_cat (Terminal_catd K) E k)
```

- Design the section-action layer through `homd_`. The weak off-diagonal
  object projection is definable from `tapp1_fapp0` plus `Terminal_obj` if it
  is useful as notation. The full homd-valued `piapp1*` component is different:
  do not implement it before `fdapp1_*` / `tdapp1_*`. If rewrite rules need it
  as a normal form, expose it as a stable derived/specialized fold from the
  section-as-`Functord` dependent action, not as an ordinary `tapp*`/`fapp*`
  alias.
- Defer the full `Hom_cat (Pi_cat E) s t` rule except for documenting the
  likely `Transfd_cat s t` joining direction.

### Phase 5: Mixed-Variance Constructors

- Add corrected:

```text
Functor_catd A B
Hom_catd E X Y
Transf_catd A B FF GG
```

- Add pointwise rules.
- Add bridge:

```text
Hom_catd (Const_catd K Cat_cat) X Y
  --> Functor_catd (Op_func X) Y
```

- Add bridge:

```text
Hom_catd (Functor_catd A B) FF GG
  --> Transf_catd A B FF GG
```

### Phase 6: Reordered/Internal Action Heads

- Add or preserve:

```text
fib_cov_transf
fib_cov_tapp0_func
fib_cov_tapp0_fapp0
```

- Port `homd_` and `homd_int` to the new `Catd` vocabulary.
- Keep endpoint rules small and stable; avoid matching large reducible
  composites in implicit arguments.

### Phase 7: Arrow-Level Dependent Heads

- Add full:

```text
fdapp1_*
tdapp1_*
```

- Keep fibrewise `fdapp1` as notation/derived structure only.
- Add the identity fold:

```text
tdapp1_* at identity --> fdapp1_*
```

- Do not define `tdapp1_*` from `tapp1_fapp1_func` in the kernel. Later
  coherence bridges may relate them, but `tdapp1_*` is a dedicated stable head
  for the dependent/simplicial layer.

## Validation Plan

After each phase, run:

```bash
lambdapi check -w emdash3_1.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

For every new stable head, add at least one assertion exercising its intended
normal form. For every rewrite involving `Functor_cat`, `Transf_cat`,
`Catd_cat`, `Functord_cat`, `Transfd_cat`, `Const_catd`, `Op_catd`,
`Functor_catd`, `Hom_catd`, `Transf_catd`, `Pi_cat`, `fib_cov_*`,
`fdapp1_*`, or `tdapp1_*`, add a focused assertion for the generic case and,
where relevant, a constant-family case.

If a typecheck hangs, inspect the most recent rewrite LHS first, especially
rules involving:

```text
Functor_cat
Transf_cat
Catd_cat
Functord_cat
Transfd_cat
Pi_cat
Const_catd
Op_catd
Hom_catd
```

## Open Design Questions

- Should `Terminal_catd K` be a separate canonical head, or should
  `Const_catd K Terminal_cat` be the canonical normal form?
- Can `Functor_cat` and `Transf_cat` remain marked `injective` after the
  special contractions, or should injectivity be represented only through
  controlled unification helpers?
- What is the exact functor-level shape for the full homd-valued
  section-action layer beyond the capped projection into `homd_`: a direct
  `piapp1*` stable fold, or a displayed specialization of `fdapp1_*` /
  identity-specialized `tdapp1_*`? The weak off-diagonal object obtained from
  ordinary `tapp1_fapp0` is already definable and should not be confused with
  this question.
- Should `Hom_cat (Pi_cat E) s t` reduce directly to `Transfd_cat s t`, or
  should that be reached through a more explicit section-as-`Functord`
  coercion/fold?
- What exact name should distinguish pointwise-opposite `Op_catd E : Catd K`
  from any future base-opposite operation?
- Which convenience aliases, if any, belong in a later standard-library layer
  rather than the kernel file?
