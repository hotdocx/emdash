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

Update 2026-05-19: the dependent-hom pair `homd_int` / `homd_` should be
treated as primitive stable heads only together with their full internal
action. An object-action rule for `fapp0 (homd_ ...)` is necessary but not
sufficient: the internal arrow/higher action rules must compute as if the
endpoint were the semantic `hom_con` construction described below. The
previous object-only primitive experiment is therefore an incomplete
implementation strategy, not the final design.

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

It also applies to compound expressions in inferred/implicit positions even
when every head in the expression is stable. For example, avoid spelling
`Op_cat (Hom_cat K x y)` in an implicit source-category slot of a rule headed
by `fapp1_func` or `fapp1_fapp0`; use `_` there and keep the discriminating
argument as the explicit functor head, such as `homd_ ...`.

## Pre-Migration v3.1 Facts Already Replaced

At the time this plan was first written, `emdash3_1.lp` still used the earlier
family vocabulary:

```text
Fam_cat K := Functor_cat K Cat_cat
Fam K := Obj (Fam_cat K)
Fam_app_cat E k := fapp0 E k
Const_fam K A := Obj_func A . Terminal_func K
Pi_cat E := Transf_cat (Terminal_fam K) E
```

The live `emdash3_1.lp` has since migrated this layer to the `Catd`
vocabulary. The following notes remain as rationale for why the old `Fam_*`
shape should not be reintroduced. These definitions were semantically
suggestive but operationally too reducible for the intended final kernel:

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

Those assumptions were allowed to change, and the current implementation has
already relaxed the relevant `constant` qualifiers and replaced the public
family layer with rewrite-capable `Catd` heads plus controlled unification
helpers.

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

The full dependent action must be represented by internal stable heads because
it acts on dependent hom data: base motion and fibre motion together. This is
the next simplicial/dependent iteration, not merely ordinary `fapp1_func` in a
fibre.

The current v3 candidate heads for this role are the internal pair
`tdapp1_int_func_transfd` / `fdapp1_int_transfd`, not yet arbitrary surface
`tdapp1_*` / `fdapp1_*` names. Later, if less-internal or external
`tdapp1_*` / `fdapp1_*` heads are introduced as projection/Groth bridges, they
should inherit the same identity-specialization shape. They should not be
defined by a direct shortcut from ordinary `tapp1_fapp1_func` plus evaluation;
that would already need the dependent projection/uncurrying machinery the
internal heads are meant to expose.

Therefore the settled internal mirror is:

```text
non-dependent:
  tapp1_* at identity --> fapp1_*
  but both tapp1_* and fapp1_* are stable heads

dependent:
  tdapp1_int_func_transfd at identity --> fdapp1_int_transfd
  with any later tdapp1_* / fdapp1_* surface mirror deferred
```

The internal identity specialization rule should be retained:

```text
tdapp1_int_func_transfd FF FF (id (Functord_cat E D) FF)
  --> fdapp1_int_transfd FF
```

This is not evidence that `fdapp1_int_transfd` is a mere alias; it is the same
identity-specialization pattern as ordinary `tapp1_*` versus `fapp1_*`.

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
piapp1_func / piapp1_fapp0, or a close variation, as later
terminal-specialization heads for full section action; these are not ordinary
`tapp1_fapp0` aliases, and their exact shape should be settled after the
internal dependent-action layer

homd_
homd_int / related internal homd projections

tapp1_int_func_transf
fapp1_int_transf
tdapp1_int_func_transfd
fdapp1_int_transfd

eventual fdapp1_* / tdapp1_* surface heads or folds, derived after the
internal layer is settled
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

The packaged head should be a section over the base-arrow category:

```text
piapp1_func [K] [E : Catd K]
  (s : Obj (Pi_cat E))
  (x y : Obj K)
  : Obj (Pi_cat
      (homd_ E x (piapp0 s x) y (piapp0 s y)))
```

Equivalently, exposing the silent terminal source family:

```text
piapp1_func s x y
  : Functord
      (Terminal_catd (Op_cat (Hom_cat K x y)))
      (homd_ E x (piapp0 s x) y (piapp0 s y))
```

where the second type contracts to the first by the joining rule
`Functord_cat (Terminal_catd J) H --> Pi_cat H`.

Then the capped object projection is evaluation of this section at the base
arrow:

```text
piapp1_fapp0 s f
  := piapp0 (piapp1_func s x y) f
```

or, if `piapp0` remains only notation, the same rule should be written with
the unfolded `tapp0_fapp0` plus `Terminal_obj` evaluation rather than with
`piapp0` on the rewrite-rule LHS.

This is not a simple alias for `tapp1_fapp0` or `fapp1_fapp0`. Conceptually
`piapp1_func` is the specialization of the full dependent action of the
section-as-`Functord`:

```text
s : Obj (Functord_cat (Terminal_catd K) E)
```

applied to the unique terminal dependent hom over the base arrow `f`. In the
same sense as full `fdapp1_*`, it sees base motion and fibre motion together.
If rewrite rules need this component as a matchable normal form, it should be
a stable terminal-specialization head whose computation is justified by the
dependent action layer (`fdapp1_*`, or the corresponding internal `tdapp1_*`
identity fold once available), not ordinary `tapp*`/`fapp*` alone.

Thus the full `piapp1*` layer should be a primitive stable head with its own
type, but not an independent primitive theory. It should be introduced with,
or immediately after, the dependent `fdapp1_*` / `tdapp1_*` infrastructure by
specializing that infrastructure to

```text
s : Functord_cat (Terminal_catd K) E
```

and then projecting the image of the unique terminal dependent hom over the
base arrow `f`. This is exactly the same reason `fdapp1_*` cannot be replaced
by a weak fibrewise `fapp1_func`: the desired section component lives in a
dependent hom over a base arrow.

The preferred rewrite should be packaged, not merely capped:

```text
terminal-specialization of fdapp1_* for
  s : Functord_cat (Terminal_catd K) E
  and Terminal_obj in the source fibre
  --> piapp1_func s x y
```

This fold requires terminal `homd_` computation. The source dependent-hom
family of the `fdapp1_*` specialization must normalize to the terminal family
over the base-arrow category; otherwise the joining rule
`Functord_cat (Terminal_catd J) H --> Pi_cat H` will not expose the desired
`Pi_cat` target for `piapp1_func`.

If a later derived `fdapp1_*` signature returns a larger displayed functor
whose target point `(y, piapp0 s y)` is internal, the LHS may need one
additional projection before any fold to `piapp1_func`, with `piapp1_fapp0`
obtained afterward by section evaluation.
At the modification level the same normalization should also be reachable by
first using the internal identity fold, and only later any derived surface
fold if such a surface head is introduced:

```text
tdapp1_int_func_transfd at identity --> fdapp1_int_transfd
```

and then applying the terminal-specialization fold above.

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

For the Pi section-action fold, `homd_` also needs terminal-family normal
forms. At minimum:

```text
homd_ (Terminal_catd K) x Terminal_obj y Terminal_obj
  --> Terminal_catd (Op_cat (Hom_cat K x y))
```

Semantically every fibre is:

```text
Hom_cat Terminal_cat Terminal_obj Terminal_obj
  --> Terminal_cat
```

but the family-level rule is the useful one: `fdapp1_*` needs its source
dependent-hom family to become a `Terminal_catd` head before the packaged fold
to `piapp1_func` can be stated cleanly.

A more general constant-family rule would also be coherent:

```text
homd_ (Const_catd K A) x u y v
  --> Const_catd (Op_cat (Hom_cat K x y)) (Hom_cat A u v)
```

The terminal rule is then the `A = Terminal_cat` instance, possibly with an
extra reduction of `Hom_cat Terminal_cat Terminal_obj Terminal_obj`. If
`Terminal_catd` remains its own canonical stable head, keep the direct
terminal rule as the operational normal form.

### Terminal and Constant Semantic Joinability

The direct terminal `homd_` rule is still useful, but the semantic path through
the defined helper `homd_semantic_func` should also reduce to the same
functor-level normal form. Since `homd_semantic_func` is a definition, the
joinability must come from the symbols it unfolds through, not from a rewrite
rule headed by `homd_semantic_func`.

The better route is not a special `hom_ Terminal_cat ...` rule for arbitrary
terminal-valued functors. The better route is a constant-functor calculus,
because both `Terminal_catd` and `Const_catd` cases should be instances of the
same phenomenon.

Missing rule inventory:

```text
fapp1_func (Const_func A B b) x y
  --> Const_func (Hom_cat A x y) (Hom_cat B b b) (id B b)

fapp1_fapp0 (Const_func A B b) f
  --> id B b

Op_func (Const_func A B b)
  --> Const_func (Op_cat A) (Op_cat B) b
```

Composition with constant functors is also needed:

```text
comp_cat_fapp0 F (Const_func A B b)
  --> Const_func A C (fapp0 F b)

comp_cat_fapp0 (Const_func B C c) G
  --> Const_func A C c
```

The first composition rule is especially important because
`fib_cov_tapp0_func` should stay defined as the semantic functor

```text
comp_cat_fapp0
  (fapp0_func u)
  (fapp1_func E x y)
```

so that fibre transport remains definitionally tied to the ordinary functor
action of the family `E`.

Under this design, do not add direct constant/terminal rules headed by
`fib_cov_tapp0_func`. Instead, the following should be desired normal forms
obtained by unfolding `fib_cov_tapp0_func` and applying the constant-functor
calculus above:

```text
fib_cov_tapp0_func (Const_catd K A) x y u
  --> Const_func (Hom_cat K x y) A u
```

The corresponding object-level helper should also be semantic, not an
independent v2-style stable transport primitive:

```text
fib_cov_tapp0_fapp0 E x y f u
  := fapp0 (fib_cov_tapp0_func E x y u) f
```

Then constant-family object transport computes by cascade:

```text
fib_cov_tapp0_fapp0 (Const_catd K A) x y f u
  --> fapp0 (Const_func (Hom_cat K x y) A u) f
  --> u
```

This means the old current v3 rule

```text
fapp0 (fapp1_fapp0 E f) u
  --> fib_cov_tapp0_fapp0 E x y f u
```

must be removed when `fib_cov_tapp0_fapp0` becomes a definition: the definition
expands back through `fib_cov_tapp0_func` to the same functor-action
projection, so keeping both directions would create a bad loop/overlap.

For `Terminal_catd`, either derive it via `Const_catd K Terminal_cat`, or keep
the analogous direct terminal rules temporarily until the terminal-vs-constant
canonicalization question is settled:

```text
fib_cov_tapp0_func (Terminal_catd K) x y u
  --> Const_func (Hom_cat K x y) Terminal_cat u

fib_cov_tapp0_fapp0 (Terminal_catd K) x y f u
  --> u
```

Returning `u`, not necessarily `Terminal_obj`, avoids needing terminal-object
eta immediately.

The semantic endpoint also needs the hom of a constant functor to collapse:

```text
hom_ A B (Const_func B A u) w
  --> Const_catd B (Hom_cat A w u)
```

Then `hom_con` gets the desired constant behavior by unfolding through `hom_`
plus `Op_func (Const_func ...)`.

Finally, the terminal family should be the canonical constant terminal family:

```text
Const_catd K Terminal_cat --> Terminal_catd K
```

This rewrite may instead become a definition of `Terminal_catd` as
`Const_catd K Terminal_cat`, or a carefully tested unification bridge, but defer
that choice until the next implementation step. Do not duplicate terminal rules
unnecessarily if the constant-family route can supply them.

This lets the semantic terminal path end at the same canonical functor-level
result as the direct terminal `homd_` rule:

```text
homd_semantic_func Terminal
  unfolds to hom_con Terminal ... (fib_cov_tapp0_func Terminal ...)
  fib_cov_tapp0_func Terminal -> Const_func ... Terminal ...
  hom_con/hom_ over Const_func -> Const_catd ... Terminal_cat
  Const_catd ... Terminal_cat -> Terminal_catd ...
```

Avoid a broad unification rule saying every terminal object is
`Terminal_obj` unless later evidence shows it is necessary. The
constant-functor route gives functor-level joining for the semantic and direct
terminal paths, and also solves the `Const_catd` case at the same time.

### `homd_int` / `homd_` Must Be Full Internal Heads

There are two viable implementation shapes for the dependent-hom endpoint
layer.

The first is the old definitional endpoint:

```text
homd_ E x u y v
  := hom_con
       (Fibre_cat E y)
       v
       (Hom_cat K x y)
       (fib_cov_tapp0_func E x y u)
```

This automatically inherits whatever object, arrow, and higher action is
available for `hom_con` and `hom_`. Its downside is that `homd_` is not a
primitive stable head for family-level normal forms such as terminal and
constant dependent homs.

The preferred v3 direction is therefore the second shape: keep the dependent
hom package as primitive stable heads, but make their computation
observationally equal to the semantic `hom_con` endpoint at every internal
level. This applies to both:

```text
homd_int
  the internal dependent-hom package, analogous to ordinary hom_int

homd_
  the fixed-endpoint projection/evaluation layer, analogous to ordinary hom_
```

The primary target is the internal layer. At the current planning stage, the
only v2 heads that are clearly candidates for adaptation are:

```text
tapp1_int_func_transf
fapp1_int_transf
tdapp1_int_func_transfd
fdapp1_int_transfd
```

The v3 port should not yet commit to additional stable heads from v2. Symbols
such as hom-action packagings, endpoint `fapp1_func` / `fapp1_fapp0` folds,
and later external `fdapp1_*` / `tdapp1_*` heads may become useful as a
cascade derived from these four internal heads, but that is a later design
choice. First settle the fully-internal `homd_int`-based statements and folds;
then decide which less-internal or capped operations should be promoted from
notation/derived structure to stable heads. Do not make the less-internal
`fapp1_func (homd_ ...)` rules the architectural foundation.

Endpoint rules remain useful as sanity and joining rules. The object rule
should delegate to the semantic endpoint rather than duplicating the current
transport formula:

```text
fapp0 (homd_ E x u y v) f
  --> fapp0 (homd_semantic_func E x u y v) f
```

At the moment `homd_semantic_func` should reduce through the semantic
definition of `fib_cov_tapp0_func`; the object-level `fib_cov_tapp0_fapp0`
should be only the projection

```text
fapp0 (fib_cov_tapp0_func E x y u) f
```

not an independent transport primitive. This keeps the endpoint formula tied to
`fapp1_func E x y`, while still giving constant/terminal reductions by cascade
once the constant-functor calculus is present. Keeping the `homd_` object rule
as a semantic delegation prevents the endpoint rule from depending directly on
a provisional pointwise transport shortcut.

The immediate `fib_cov_transf` shape, following v2, is expected to be:

```text
fib_cov_transf [Z] (E : Catd Z)
  (x : Obj Z)
  (u : Obj (Fibre_cat E x))
  : Transf
      (hom_ (id_func Z) x)
      E
```

and the component stable head should be the `tapp0_fapp0` projection:

```text
tapp0_fapp0 y (fib_cov_transf E x u)
  --> fib_cov_tapp0_func E x y u
```

with Lambdapi LHSs keeping the inferred source/target functors implicit:

```text
rule @tapp0_fapp0 $Z Cat_cat _ _ $y
      (@fib_cov_transf $Z $E $x $u)
  ↪ @fib_cov_tapp0_func $Z $E $x $y $u
```

This is still not the most-internal transport package. The variables `x` and
`u` remain external Lambdapi arguments. A later, more-internal version should
push those endpoint parameters inside, analogously to the effort that produced
`homd_int`, but with the argument order rearranged for covariance/action. That
more-internal `fib_cov` package is a TODO and should not block the present
endpoint semantic cleanup.

The most-internal feasible shape is not the external package

```text
fib_cov_transf E x u : Transf (hom_ (id_func Z) x) E
```

but rather a new internal object whose projections recover that package.

The key target family should be:

```text
FibCov_target_catd [Z] (E : Catd Z)
  := hom_con
       (Catd_cat Z)
       E
       (Op_cat Z)
       (hom_int Z Z (id_func Z))
```

Why this works:

```text
FibCov_target_catd E at x
  ~= Hom_{Catd_cat Z}(hom_ (id_Z) x, E)
  ~= Transf_cat (hom_ (id_Z) x) E
```

Important detail: do not use `Edge_catd_fam` here, because current
`Edge_catd_fam` is pointwise-op:

```text
x,y |-> Op_cat (Hom_cat Z x y)
```

For covariant fibre transport we want the raw representable
`hom_ (id_func Z) x`, so the right ingredient is
`hom_int Z Z (id_func Z)`.

Then the most-internal package can mirror `Homd`:

```text
FibCov_cat [Z] (E : Catd Z)
  := Transf_cat Z Cat_cat E (FibCov_target_catd E)

FibCov [Z] (E : Catd Z)
  := Obj (FibCov_cat E)

fib_cov_int [Z] (E : Catd Z) : FibCov E
```

Projection cascade:

```text
tapp0_fapp0 x (fib_cov_int E)
  : Functor (E[x]) (Transf_cat (hom_ (id_func Z) x) E)

fapp0 (tapp0_fapp0 x (fib_cov_int E)) u
  : Transf_cat (hom_ (id_func Z) x) E
```

So the old external head becomes a projection normal form:

```text
fib_cov_transf E x u
  : Transf (hom_ (id_func Z) x) E
```

with rules shaped like:

```text
rule @tapp0_fapp0 $Z Cat_cat _ _ $x (@fib_cov_int $Z $E)
  ↪ @fib_cov_src_func $Z $E $x

rule fapp0 (@fib_cov_src_func $Z $E $x) $u
  ↪ @fib_cov_transf $Z $E $x $u
```

Then the component rule remains:

```text
rule @tapp0_fapp0 $Z Cat_cat _ _ $y
      (@fib_cov_transf $Z $E $x $u)
  ↪ @fib_cov_tapp0_func $Z $E $x $y $u
```

This is on par with `homd_int`: it internalizes `x,u` into the source family
of a transfor. The variance also looks correct: source is `E`, not
`Op_catd E`, because transport is covariant in the fibre object `u`.

With a generalized displayed functor argument `FF : Functord D E`, the
endpoint semantic helper should be read as:

```text
homd_semantic_func FF x u y v
  := hom_con
       (Fibre_cat E y)
       (FF_y v)
       (Hom_cat Z x y)
       (fib_cov_tapp0_func E x y u)
```

where the endpoint-level fibre action is:

```text
FF_y v :=
  fapp0 (@tapp0_fapp0 Z Cat_cat D E y FF) v
```

This `FF_y v` projection is endpoint-level, not the fully-internal displayed
action. That is acceptable for `homd_semantic_func`, which is itself an
endpoint semantic helper. The fully-internal action remains the job of
generalized `homd_int`, `tdapp1_int_func_transfd`, and `fdapp1_int_transfd`.

The object rule must still be accompanied, or justified by, the corresponding
internal arrow-level action. Schematic endpoint-level joining rules are:

```text
fapp1_func (homd_ E x u y v) f g
  --> fapp1_func
        (hom_con
           (Fibre_cat E y)
           v
           (Hom_cat K x y)
           (fib_cov_tapp0_func E x y u))
        f g

fapp1_fapp0 (homd_ E x u y v) [f] [g] alpha
  --> fapp1_fapp0
        (hom_con
           (Fibre_cat E y)
           v
           (Hom_cat K x y)
           (fib_cov_tapp0_func E x y u))
        [f] [g] alpha
```

The exact Lambdapi rules should use explicit `@...` applications and `_` in
implicit category positions unless the category is an actual discriminator.
Do not spell reducible compound expressions in implicit LHS slots merely to
make the rule typecheck.
For the endpoint action rules specifically, the source category of
`fapp1_func` / `fapp1_fapp0` should be `_`, not the compound
`Op_cat (Hom_cat K x y)`, because the functor argument `homd_ ...` is the real
discriminator.

The same principle applies one level up: rules for internal heads such as
adapted v3 versions of `fapp1_int_transf`, `tapp1_int_func_transf`,
`tdapp1_int_func_transfd`, and `fdapp1_int_transfd` should delegate to, or
compute through, the corresponding action of the semantic `hom_int` /
`homd_int` packages. Endpoint `homd_` should not invent independent
object-only transport.

The terminal and constant-family normal forms above remain desired
family-level normal forms, but they are acceptable only if they are full
internal normal forms. Their `homd_int`, `homd_`, `fapp0`, `fapp1_func`, and
`fapp1_fapp0` behavior must join with the general action rules and the action
rules for `Terminal_catd` / `Const_catd`. If joinability is not immediate,
implement the general full-action rules first and defer the terminal/constant
whole-family rules until the critical pairs are understood.

### Open Arity Issue: General Dependent Hom Action

The current v3 shapes:

```text
homd_int [K] (E : Catd K)
homd_ [K] (E : Catd K) x u y v
```

express the dependent-hom family induced by the ambient action of one family
`E`. By contrast, ordinary `hom_int` and `hom_` both have an explicit functor
argument:

```text
hom_int [A B] (F : Functor B A)
hom_ [A B] (F : Functor B A) (W : Obj A)
```

For future `fdapp1_*` and `tdapp1_*` rules, this asymmetry may matter. A full
dependent action along a family morphism probably requires generalized
versions of both internal and endpoint heads:

```text
homd_int [K] [D E : Catd K] (FF : Obj (Functord_cat D E)) ...
homd_ [K] [D E : Catd K] (FF : Obj (Functord_cat D E)) ...
```

or separate generalized heads, with the current `homd_int E` and
`homd_ E x u y v` kept as identity/ambient-family specializations.

This matches the v2 pattern more closely than the current v3 arity does. In
v2, internal displayed operations such as `tdapp1_int_func_transfd` and
`fdapp1_int_transfd` are typed using `homd_int` applied to displayed functors,
for example identity displayed functors and the displayed functor `FF` being
acted on. The endpoint `homd_` also carries a displayed functor argument.

This is not settled by the current report. Before implementing `fdapp1_*`,
`tdapp1_*`, or the full `piapp1_*` fold, review whether the dependent hom
package must carry an explicit `FF` argument analogous to the functor argument
of ordinary `hom_int` / `hom_`. Do not force the existing arity into those
rules if doing so requires object-level shortcuts or loses the internal arrow
action.

Concrete candidate for the next implementation pass, corrected after review:

```text
Op_funcd [K] [E D : Catd K] (FF : Functord E D)
  : Functord (Op_catd E) (Op_catd D)

homd_int [K] [D E : Catd K] (FF : Functord D E)
  : Functord (Op_catd E) (Homd_target_catd D)
```

Here `D` is the probe/source family and `E` is the target family of `FF`.
This order mirrors ordinary `hom_int [A B] (F : Functor B A)`, where the
hom object is contravariant in the target of the functor and remembers the
probe/domain in the displayed target family.

The final architecture should use one generalized `homd_int` symbol, not a
permanent pair `homd_int` / `homd_int_funcd`. During incremental migration,
the existing one-family `homd_int E` may be kept temporarily as an
identity-specialization alias or compatibility head, but permanent rewrite
rules should be written against the generalized `homd_int ... FF` shape:

```text
old/compat homd_int E  :=  generalized homd_int (id_funcd E)
Op_funcd (id_funcd E) --> id_funcd (Op_catd E)
```

With those two heads available, the internal displayed action can be typed in
the direct v2 shape:

```text
tdapp1_int_func_transfd [K] [E D : Catd K] [FF GG : Functord E D]
  : Functor
      (Transfd_cat FF GG)
      (Transfd_cat
        (homd_int (id_funcd E))
        (comp_catd_fapp0
          (homd_int GG)
          (Op_funcd FF)))

fdapp1_int_transfd [K] [E D : Catd K] (FF : Functord E D)
  : Transfd
      (homd_int (id_funcd E))
      (comp_catd_fapp0
        (homd_int FF)
        (Op_funcd FF))

fapp0 (tdapp1_int_func_transfd FF FF) (id (Functord_cat E D) FF)
  --> fdapp1_int_transfd FF
```

Type alignment check for the target composite:

```text
GG : Functord E D
homd_int GG : Functord (Op_catd D) (Homd_target_catd E)
Op_funcd FF : Functord (Op_catd E) (Op_catd D)

comp_catd_fapp0 (homd_int GG) (Op_funcd FF)
  : Functord (Op_catd E) (Homd_target_catd E)
```

This keeps the fully-internal layer first. Do not introduce the v2 auxiliary
hom-action packaging heads (`tdapp1_int_fapp1_*`, external `tdapp1_*`,
external `fdapp1_*`) in the same pass unless a typechecking blocker proves
that one is needed as a named projection.

### Internal Endpoint Rule for `fapp1_int_transf (homd_ ...)`

In addition to the less-internal endpoint rules for `fapp1_func` and
`fapp1_fapp0`, there is an ordinary internal endpoint rule to consider:
`fapp1_int_transf` applied to the endpoint functor `homd_ ...`.

For the current one-family endpoint shape, the intended rule is simply:

```text
fapp1_int_transf (homd_ E x u y v)
  --> fapp1_int_transf (homd_semantic_func E x u y v)
```

With explicit Lambdapi applications, the LHS should keep the source category
implicit, just like the `fapp1_func (homd_ ...)` rule:

```text
rule @fapp1_int_transf _ Cat_cat (@homd_ $K $E $x $u $y $v)
  ↪ @fapp1_int_transf
        (Op_cat (Hom_cat $K $x $y))
        Cat_cat
        (@homd_semantic_func $K $E $x $u $y $v)
```

After `homd_` is generalized with an explicit displayed functor argument, the
identity specialization should have the same shape, with
`homd_ (id_funcd E) x u y v` on the LHS. This rule is enough for the ordinary
internal endpoint action: it says that the stable endpoint head behaves
exactly as the semantic `hom_con` endpoint when used by `fapp1_int_transf`.

It should join with the already-planned component endpoint rules:

```text
fapp1_func (homd_ E x u y v) f g
  --> fapp1_func (homd_semantic_func E x u y v) f g

fapp1_fapp0 (homd_ E x u y v) f g alpha
  --> fapp1_fapp0 (homd_semantic_func E x u y v) f g alpha
```

This is not yet the fully displayed `fdapp1_int_transfd` story. The displayed
rule will be about the generalized `homd_int ... FF` layer and its component
projections. For now, the endpoint `fapp1_int_transf` rule is the correct
less-internal semantic joining rule.

Rewrite-SOP constraint: keep compound categories such as
`Op_cat (Hom_cat K x y)` out of implicit LHS slots. The LHS should
discriminate on the explicit stable functor argument `homd_ ...`, while the
RHS may use the fully explicit semantic expression.

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

full internal fdapp1:
  fdapp1_int_transfd first; surface fdapp1_* later if needed

full internal tdapp1:
  tdapp1_int_func_transfd first; surface tdapp1_* later if needed
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
  implement `piapp1_func`, or a close variation, only after the internal
  dependent-action layer is settled. The packaged fold should come from the
  terminal specialization of the internal/derived dependent action; any
  `piapp1_fapp0` is then section evaluation at a base arrow. This is not an
  ordinary `tapp*`/`fapp*` alias.
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

  Audit the `fib_cov_tapp0_func` / `fib_cov_tapp0_fapp0` layer while doing this.
  Keep `fib_cov_tapp0_func` as a defined semantic helper based on
  `comp_cat_fapp0 (fapp0_func u) (fapp1_func E x y)`. Convert
  `fib_cov_tapp0_fapp0` away from the current v2-style primitive/stable
  transport rule and into the defined projection
  `fapp0 (fib_cov_tapp0_func E x y u) f`. New `homd_` rules should delegate
  through `homd_semantic_func`, so the later projection from `fib_cov_transf`
  remains localized.
  The immediate `fib_cov_transf E x u` transfor still has external `x,u`
  parameters. Record it as an intermediate package only; the most-internal
  version should eventually push `x,u` inside, in the same spirit as
  `homd_int`.

- Port `homd_int` and `homd_` to the new `Catd` vocabulary as a pair.
- Before committing to the current v3 arity, review the v2 pattern where both
  `homd_int` and `homd_` carry a displayed functor argument. The likely v3
  generalized arity is schematic `FF : Obj (Functord_cat D E)`, with the
  current one-family forms kept as identity/ambient specializations if useful.
- The concrete first pass should generalize the existing `homd_int` head
  itself, plus introduce `Op_funcd`. If the current one-family `homd_int E`
  is kept during migration, it should be temporary compatibility structure,
  not a second permanent head used by new rewrite-rule LHSs.
- Keep `homd_int` / `homd_` as primitive stable heads only if full internal
  action rules are added. The endpoint-level minimum includes object and arrow
  action: `fapp0`, `fapp1_func`, and `fapp1_fapp0` should compute as if the
  endpoint were the semantic `hom_con (fib_cov_tapp0_func ...)` endpoint.
  The internal `homd_int` rules are the real foundation; endpoint rules are
  projections or joining checks.
- Add terminal/constant whole-family `homd_int` / `homd_` normal forms only
  after checking that they join with the general internal and endpoint action
  rules.
- Keep endpoint rules small and stable; avoid matching large reducible
  composites, or stable-but-compound expressions such as
  `Op_cat (Hom_cat ...)`, in implicit arguments.

### Phase 7: Arrow-Level Dependent Heads

- Add full:

```text
adapted v3 tapp1_int_func_transf / fapp1_int_transf
adapted v3 tdapp1_int_func_transfd / fdapp1_int_transfd
```

- For the displayed pair, use the concrete generalized `homd_int` / `Op_funcd`
  target shape described in the open-arity section before adding any
  less-internal endpoint packaging.
- Prioritize the fully-internal heads. The v2 pattern is:

```text
fapp1_int_transf F
  := tapp1_int_func_transf F F (id F)

fdapp1_int_transfd FF
  := tdapp1_int_func_transfd FF FF (id FF)
```

  Any less-internal/external packagings should be considered only afterward,
  as Grothendieck, projection, or normalization bridges derived in cascade
  from these four heads.
- Keep fibrewise or capped `fdapp1` forms as notation/derived structure only
  unless a later review identifies a genuine primitive role.
- Add the identity fold:

```text
tdapp1_int_func_transfd at identity --> fdapp1_int_transfd
```

- Do not define the internal displayed heads from ordinary `tapp1_fapp1_func`
  in the kernel. Later coherence or projection bridges may relate the layers,
  but those bridges should be designed only after the four internal heads are
  settled.
- Before implementing these heads, settle whether the dependent hom package
  needs an explicit family morphism argument
  `FF : Obj (Functord_cat D E)`, analogous to the functor argument of ordinary
  `hom_int` / `hom_`, or whether the current `homd_int E` and
  `homd_ E x u y v` remain only ambient/identity specializations used by more
  general heads.

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
`homd_int`, `homd_`, `tapp1_int_func_transf`, `fapp1_int_transf`,
`tdapp1_int_func_transfd`, `fdapp1_int_transfd`, or any later explicitly
introduced derived cascade head, add a focused assertion for the generic case
and, where relevant, a constant-family case.

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
  section-action fold from the internal/derived dependent action to
  `piapp1_func`, especially if a later `fdapp1_*` surface signature keeps the
  target point `(y, piapp0 s y)` internal and therefore needs an extra
  projection before the terminal-specialization fold?
  The weak off-diagonal object obtained from ordinary `tapp1_fapp0` is already
  definable and should not be confused with this question.
- Should `Hom_cat (Pi_cat E) s t` reduce directly to `Transfd_cat s t`, or
  should that be reached through a more explicit section-as-`Functord`
  coercion/fold?
- What exact name should distinguish pointwise-opposite `Op_catd E : Catd K`
  from any future base-opposite operation?
- Which convenience aliases, if any, belong in a later standard-library layer
  rather than the kernel file?
