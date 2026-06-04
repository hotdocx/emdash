# emdash v3 Faithful Surface Syntax, Pretty-Printer, Parser, and Elaborator Plan

Date: 2026-05-24

Last updated: 2026-06-04, consolidating the indexed binder syntax around
`:^n` and clarifying the roles of `Functor_catd`, `Transf_catd`, and `Pi_cat`.

## Scope

This report records the proposed design for a faithful mathematical surface
syntax for the current `emdash3_2.lp` kernel.

The word "implementation" in this report does not mean implementing the
TypeScript parser, pretty-printer, elaborator, or typechecker yet. The immediate
implementation target is documentation and design consolidation:

- define a stable surface syntax for emdash expressions;
- describe how a manual pretty-printer should render current Lambdapi/kernel
  expressions;
- describe how a future algorithmic pretty-printer, parser, elaborator, and
  typechecker should relate to that syntax;
- provide enough syntax examples to document the current internal constructors,
  especially `homd_int`, `fib_cov_int`, `tapp1_int_*`, `tdapp1_int_*`,
  `fdapp1_int_transfd`, `piapp1_func`, and `piapp1_fapp0`;
- prepare follow-up edits to `emdash3_2.lp` and `reports/EMDASH_FOUNDATIONS.md`
  so important symbols are annotated with their faithful surface syntax.

The TypeScript implementation is expected to live in the parent `emdash1`
workspace later. This report is intentionally a design artifact for that future
work and for near-term comments/docs in the Lambdapi development.

## Design Thesis

The default emdash syntax should be the mathematical surface syntax, not the
Lambdapi kernel syntax.

For example, the current kernel declaration:

```lambdapi
injective symbol homd_int : Π [Z : Cat], Π [D E : τ (Catd Z)],
  Π (FF : τ (Functord D E)),
  τ (Functord (Op_catd E) (@Homd_target_catd Z D));
```

should not default-print as:

```text
homd_int(FF) : E^op ⇒_Z HomdTarget_Z(D)
```

except perhaps in a compact intermediate mode. The intended default surface
syntax should expose the dependent-hom expression itself:

```text
homd_int(FF) :
  (x :^n Z) →
    E[x]^op ⟶
      Π y :^n Z^op,
        D[y^-] ⟶_[y] (Hom_Z(x,y)^op ⟶ Cat)
```

The kernel/debug form remains important, but it should be a separate rendering
mode for diagnostics, rule debugging, and round-trip audits.

## Modes

The design has two essential printing modes.

### Surface Mode

Surface mode is the default user-facing pretty-printer output and the intended
input syntax for the future TypeScript emdash parser.

It expands kernel helper heads into mathematical notation when that expansion is
stable and faithful. It should prefer:

```text
Π y :^n Z^op,
  D[y^-] ⟶_[y] (Hom_Z(x,y)^op ⟶ Cat)
```

over:

```text
HomdTarget_Z(D)
```

Surface mode is still allowed to use named syntax for genuinely conceptual
operators when full expansion would obscure the expression. The default policy
should be: expand enough to show the mathematical type, but keep repeated
well-understood subexpressions readable.

### Kernel/Debug Mode

Kernel/debug mode prints close to the Lambdapi representation:

```text
τ (Functord (Op_catd E) (@Homd_target_catd Z D))
```

or, after wrapper erasure:

```text
Functord (Op_catd E) (Homd_target_catd Z D)
```

This mode is useful for:

- debugging rewrite heads and inferred arguments;
- comparing against `emdash3_2.lp`;
- proving `parse(pretty(t))` round-trips to the intended kernel expression;
- explaining why a surface expression elaborates to a particular stable head.

Kernel/debug mode should not be the default language syntax.

## Round-Trip Contract

The target invariant is:

```text
parse(pretty(kernel_term)) ≡ kernel_term
```

where `≡` means definitional equality in the emdash/Lambdapi kernel, not
necessarily syntactic equality of raw ASTs.

This invariant is realistic only if:

1. the pretty-printer is typed and context-aware;
2. the parser produces a surface AST without trying to decide all semantic
   correctness;
3. elaboration/typechecking resolves the surface AST into a kernel expression;
4. the pretty-printer uses a canonical orientation policy for variance and
   indexed arrows.

The printer should therefore emit explicit enough syntax to avoid guessing:

```text
:^n
Z^op
z^-
⟶_[z]
⇒_[z]
```

These annotations are part of the faithful syntax, not decoration.

## Context, Polarity, And Indexed Binders

The surface language needs an explicit notion of current variance/polarity.

### Single Indexed Binder

The current canonical plan uses one explicit indexed binder marker:

```text
z :^n Z
```

This means `z` is an indexed categorical variable over `Z`, with the usual
natural/displayed coherence expected of the expression formed around the
binder. The surrounding type former determines the construction:

```text
Π z :^n Z, K[z]          section category
Σ z :^n Z, K[z]          total category
(z :^n Z) → E[z] ⟶ D[z] displayed/natural family of functors
(z :^n Z) → FF[z] ⇒ GG[z] displayed/natural family of transfors
```

The older draft distinction between `:^f` and `:^n` is retired from the
canonical surface plan. It created the false impression that `Pi_cat` and
`Sigma_cat` involve only functorial variation while `Functord_cat` and
`Transfd_cat` involve natural variation. The better distinction is:

```text
The fibre/type family K[z], E[z], or D[z] varies functorially in z.
An inhabitant or morphism over the binder varies naturally/displayedly in z.
```

This matches the kernel fact that:

```text
Pi_cat E = Functord_cat(1_K,E)
```

so a section is already a special naturally/displayedly varying family, namely
a displayed functor out of the terminal family.

For now, `:^n` remains explicit to avoid a broad syntax churn in reports and
future comments. A later surface language may choose to omit the marker in
unambiguous binders, or introduce more refined markers such as an
object/isofibration-oriented `:^o`, but that is deliberately not part of the
near-term v3.2 cleanup.

### Polarity Flip

Plain variable occurrence uses the current binder polarity.

The suffix:

```text
z^-
```

means "the same object variable `z`, but with polarity inverted relative to the
current binder."

For example, under:

```text
Π y :^n Z^op, ...
```

plain `y` is in the `Z^op` polarity. If a family `D : Z → Cat` must be read at
that same underlying object, the faithful syntax is:

```text
D[y^-]
```

not:

```text
D[y]
```

This is the key correction for the `homd_int` target syntax. Under a
`Z^op`-binder, the domain family `D : Catd Z` is reached by a polarity flip:

```text
Π y :^n Z^op,
  D[y^-] ⟶_[y] (Hom_Z(x,y)^op ⟶ Cat)
```

The codomain presheaf part is indexed by plain `y`, because the current binder
already has the opposite-base polarity needed by that family.

### Design Rule

The parser should not infer polarity flips silently in the canonical syntax.
The pretty-printer should print `z^-` whenever a family occurrence is being read
against the opposite polarity of the current binder.

This rule makes the syntax noisier in a useful way. It is what gives the future
parser and elaborator enough information to reconstruct `Op_cat`, `Op_catd`,
and mixed-variance constructors predictably.

## Core Notation Table

The following table gives the intended default surface notation.

| Kernel shape | Surface syntax | Reading |
| --- | --- | --- |
| `Cat` / `Cat_cat` | `Cat` | category universe/category of categories, depending on level |
| `Obj A` | `Obj(A)` or implicit object sort | objects of `A` |
| `Hom_cat A x y` | `Hom_A(x,y)` or `x ⟶_A y` | hom-category in `A` |
| `Functor_cat A B` | `A ⟶ B` | ordinary functor category |
| `Functor A B` | `A ⟶ B` as a type of functors | ordinary functor type |
| `fapp0 F x` | `F[x]` or `F(x)` | functor object action |
| `fapp1_fapp0 F f` | `F[f]` | functor arrow action |
| `Transf_cat F G` | `F ⇒ G` | ordinary transfor/natural transformation category |
| `Transf F G` | `F ⇒ G` as a type of transfors | ordinary transfor type |
| `tapp0_fapp0 x ϵ` | `ϵ[x]` | transfor component |
| `Catd_cat K` / `Catd K` | `K → Cat` or `Catd(K)` | directed Cat-valued family over `K` |
| `Fibre_cat E z` | `E[z]` | fibre category |
| `Op_cat A` | `A^op` | opposite category |
| `Op_catd E` | `E^op` | pointwise opposite family |
| `Const_catd K A` | `const_K(A)` | constant family |
| `Terminal_catd K` | `1_K` | terminal family, i.e. `const_K(1)` |
| `Functor_catd A B` | `A[z^-] ⟶_[z] B[z]` | mixed-variance family of functor categories |
| `Transf_catd A B FF GG` | `FF[z^-] ⇒_[z] GG[z]` | mixed-variance family of transfor categories |
| `Functord_cat E D` | `(z :^n K) → E[z] ⟶ D[z]` | displayed-functor category |
| `Functord E D` | type of `(z :^n K) → E[z] ⟶ D[z]` | hidden object wrapper |
| `Transfd_cat FF GG` | `(z :^n K) → FF[z] ⇒ GG[z]` | displayed-transfor category |
| `Transfd FF GG` | type of `(z :^n K) → FF[z] ⇒ GG[z]` | hidden object wrapper |
| `Pi_cat E` | `Π z :^n K, E[z]` | section category |
| `Sigma_cat E` | `Σ z :^n K, E[z]` | total category |
| `Struct_sigma z u` | `(z,u)` | total object |
| `piapp0 s z` | `s[z]` | section object component |
| `piapp1_fapp0 s f` | `s[f]` | section arrow component |
| `comp_catd_fapp0 FF GG` | `FF ∘ GG` | displayed-functor composition |
| `id_funcd E` | `id_E` | displayed identity |

The table intentionally distinguishes:

```text
A ⟶ B
```

from:

```text
A[z^-] ⟶_[z] B[z]
```

and:

```text
F ⇒ G
```

from:

```text
FF[z^-] ⇒_[z] GG[z]
```

This distinction is necessary because `Functor_catd` and `Transf_catd` are not
ordinary functor/transfor categories. They are mixed-variance family
constructors.

### Type Former Clarification

The single indexed binder does not remove the important type-former
distinctions. The surrounding constructor is what determines the intended
surface reading.

For a base `Z`:

```text
Functor_catd M N
```

is a `Catd Z` whose fibre is:

```text
(Functor_catd M N)[z] = M[z^-] ⟶_[z] N[z]
```

Here `M` and `N` are displayed category families. The mixed variance is
expressed by the source occurrence `M[z^-]` and the indexed arrow marker
`⟶_[z]`.

Similarly:

```text
Transf_catd M N FF GG
```

is a `Catd Z` whose fibre is:

```text
(Transf_catd M N FF GG)[z] = FF[z^-] ⇒_[z] GG[z]
```

Here `FF` and `GG` are sections/objects of the mixed-variance functor family
`Functor_catd M N`, not category families themselves. This is why the transfor
notation should use `FF` and `GG`, while the functor-family notation should use
`M` and `N`.

The section category is a special displayed-functor category:

```text
Pi_cat K = Functord_cat(1_Z,K)
```

so the surface expression:

```text
Π z :^n Z, K[z]
```

can be read morally as:

```text
(z :^n Z) → 1 ⟶ K[z]
```

If `K = Functor_catd M N`, this expands to sections of mixed-variance functor
categories:

```text
Π z :^n Z, M[z^-] ⟶_[z] N[z]
```

If `K = Transf_catd M N FF GG`, this expands to sections of mixed-variance
transfor categories:

```text
Π z :^n Z, FF[z^-] ⇒_[z] GG[z]
```

No separate `Pid_cat` alias is needed for the second case at the surface level
or in the current kernel: `Transf_catd M N FF GG` is already a Cat-valued
family, so `Pi_cat (Transf_catd M N FF GG)` is the existing type former for
such sections. A dedicated alias should be added only if future rewrite rules
need a stable head for this shape.

## Indexed Arrow Syntax

The indexed arrows:

```text
⟶_[z]
⇒_[z]
```

mean "the arrow is formed in the current indexed context of `z`."

The recommended default forms are:

```text
A[z^-] ⟶_[z] B[z]
FF[z^-] ⇒_[z] GG[z]
```

rather than:

```text
A[z^-] ⟶_z B[z]
FF[z^-] ⇒_z GG[z]
```

or:

```text
A[z^-] ⟶^z B[z]
FF[z^-] ⇒^z GG[z]
```

Rationale:

- bracketed subscripts are easier to parse;
- `_[z]` visually marks an indexed context, not an ordinary category subscript;
- exponent notation should remain available for polarity and ordinary
  mathematical exponent-like syntax;
- the bracketed form can later generalize to compound contexts if needed.

## Named Placeholders: `~`, `—`, and Related Marks

The surface syntax may use placeholder marks for argument positions in internal
hom-like expressions.

Proposed meanings:

```text
~
```

marks the contravariant/probe/source slot.

```text
—
```

marks the covariant/target slot.

Potentially useful variants:

```text
–
```

may be reserved for a lighter-weight dash-like placeholder if a later notation
needs to distinguish object-level placeholders from family-level placeholders.

```text
~-
```

or another explicit polarity-marked placeholder may be introduced only if the
plain `~` and `—` convention becomes ambiguous.

For ordinary internal hom action, the intended reading is:

```text
Hom_B(F^op ~, G —)
```

This means: first transform the contravariant slot by `F^op`, and transform the
covariant slot by `G`.

In terms of the current kernel comments, this replaces a less precise compact
notation such as:

```text
Hom_B(G) ∘ F^op
```

with a surface expression that names the two argument positions:

```text
Hom_B(F^op ~, G —)
```

For displayed/dependent homs, analogous notation should be used:

```text
Homd_E(~, —)
Homd_D(FF^op ~, GG —)
Homd_E(s^op ~, s —)
```

These are not necessarily primitive parser forms at first. They can be
documented macro-like pretty forms whose expansion is specified in this report.

## Current Internal Constructors In Surface Syntax

This section gives proposed default pretty-printer outputs for the main
`*_int` constructors in `emdash3_2.lp`.

### `hom_int`

Kernel declaration:

```lambdapi
injective symbol hom_int [A B : Cat] (F : τ (Functor B A))
  : τ (Functor (Op_cat A) (Catd_cat B));
```

Surface context:

```text
A,B : Cat
F : B ⟶ A
```

Default surface type:

```text
hom_int(F) : A^op ⟶ (B → Cat)
```

Expanded surface reading:

```text
hom_int(F)(W)[y] = Hom_A(W,F[y])
```

or with placeholders:

```text
hom_int(F) = Hom_A(~, F —)
```

### `tapp1_int_func_transf`

Kernel shape:

```text
tapp1_int_func_transf(F,G)
  : Transf(F,G) ⟶
    Transf(hom_int(id_A), hom_int(G) ∘ F^op)
```

Surface context:

```text
A,B : Cat
F,G : A ⟶ B
```

Default surface type:

```text
tapp1_int(F,G) :
  (F ⇒ G) ⟶
  (Hom_A(~, —) ⇒ Hom_B(F^op ~, G —))
```

This is the internal ordinary hom-action of a transfor.

### `tapp1_int_fapp0_transf`

Surface context:

```text
ϵ : F ⇒ G
```

Default surface type:

```text
tapp1_int(ϵ) :
  Hom_A(~, —) ⇒ Hom_B(F^op ~, G —)
```

It is the object action of `tapp1_int(F,G)` at `ϵ`.

### `tapp1_int_fapp1_func_transf`

Surface context:

```text
ϵ,ϵ' : F ⇒ G
```

Default surface type:

```text
tapp1_int[ϵ,ϵ'] :
  Hom_{F⇒G}(ϵ,ϵ') ⟶
  Hom_{Hom_A(~,—)⇒Hom_B(F^op~,G—)}(tapp1_int(ϵ), tapp1_int(ϵ'))
```

This is a compact surface rendering of the functorial hom-action of
`tapp1_int_func_transf`. The exact pretty-printer may choose a more line-broken
form.

### `fapp1_int_transf`

Kernel shape:

```text
fapp1_int_transf(F)
  : Transf(hom_int(id_A), hom_int(F) ∘ F^op)
```

Surface context:

```text
F : A ⟶ B
```

Default surface type:

```text
fapp1_int(F) :
  Hom_A(~, —) ⇒ Hom_B(F^op ~, F —)
```

This is the identity-specialized ordinary internal action.

### `fib_cov_int`

Kernel declaration:

```lambdapi
constant symbol fib_cov_int : Π [K : Cat], Π (E : τ (Catd K)),
  τ (Functord E (@FibCov_target_catd K E));
```

Surface context:

```text
K : Cat
E : K → Cat
```

Default surface type:

```text
fib_cov_int(E) :
  (x :^n K) →
    E[x] ⟶
      ((y :^n K) → Hom_K(x,y) ⟶ E[y])
```

Object/action reading:

```text
fib_cov_int(E)(x,u)(y,f) = E[f](u)
```

In kernel terms, the final object action is:

```text
fapp0 (fib_cov_tapp0_func E x y u) f
```

The surface language should usually print that as:

```text
E[f](u)
```

when the family and base-arrow context are known.

### `homd_`

Kernel declaration:

```lambdapi
injective symbol homd_ [Z : Cat] [D E : τ (Catd Z)]
  (FF : τ (Functord D E))
  (x : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj Z))
  (v : τ (Obj (Fibre_cat D y)))
  : τ (Functor (Op_cat (Hom_cat Z x y)) Cat_cat)
```

Surface context:

```text
Z : Cat
D,E : Z → Cat
FF : (z :^n Z) → D[z] ⟶ E[z]
x,y : Z
u : E[x]
v : D[y]
```

Default surface type:

```text
homd_(FF,x,u,y,v) :
  Hom_Z(x,y)^op ⟶ Cat
```

Default surface expansion:

```text
homd_(FF,x,u,y,v)[f]
  = Hom_{E[y]}(E[f](u), FF[y](v))
```

For the identity-specialized one-family case:

```text
homd_(id_E,x,u,y,v)[f]
  = Hom_{E[y]}(E[f](u), v)
```

### `homd_int`

Kernel declaration:

```lambdapi
injective symbol homd_int : Π [Z : Cat], Π [D E : τ (Catd Z)],
  Π (FF : τ (Functord D E)),
  τ (Functord (Op_catd E) (@Homd_target_catd Z D));
```

Surface context:

```text
Z : Cat
D,E : Z → Cat
FF : (z :^n Z) → D[z] ⟶ E[z]
```

Default surface type:

```text
homd_int(FF) :
  (x :^n Z) →
    E[x]^op ⟶
      Π y :^n Z^op,
        D[y^-] ⟶_[y] (Hom_Z(x,y)^op ⟶ Cat)
```

Endpoint reading:

```text
homd_int(FF)(x,u)(y,v)(f)
  = Hom_{E[y^-]}(E[f](u), FF[y^-](v))
```

The `y^-` occurrences in the endpoint line reflect that `y` is bound over
`Z^op` in the inner section. Depending on how the eventual surface language
names underlying objects, the pretty-printer may normalize the endpoint display
to the visually simpler:

```text
Hom_{E[y]}(E[f](u), FF[y](v))
```

when `y` is no longer displayed under the `Z^op` binder. In canonical
round-trip syntax under the binder, however, `D[y^-]`, `E[y^-]`, and
`FF[y^-]` should be printed when those expressions consume data over `Z`.

### `homd_src_func`, `homd_src_sec`, and `homd_tgt_func`

These are projection heads used by the kernel to expose `homd_int` in stages:

```text
homd_int(FF)[x]              ↦ homd_src_func(FF,x)
homd_src_func(FF,x)[u]       ↦ homd_src_sec(FF,x,u)
homd_src_sec(FF,x,u)[y]      ↦ homd_tgt_func(FF,x,u,y)
homd_tgt_func(FF,x,u,y)[v]   ↦ homd_(FF,x,u,y,v)
```

Surface mode should normally hide these heads and print the composed expression
as direct application:

```text
homd_int(FF)(x,u,y,v)
```

or:

```text
Homd_E(~, FF —)(x,u,y,v)
```

Kernel/debug mode should print the staged heads because they are rewrite
discriminators in `emdash3_2.lp`.

### `tdapp1_int_func_transfd`

Kernel shape:

```text
tdapp1_int_func_transfd(FF,GG)
  : Transfd(FF,GG) ⟶
    Transfd(homd_int(id_E), homd_int(GG) ∘ FF^op)
```

Surface context:

```text
K : Cat
E,D : K → Cat
FF,GG : (z :^n K) → E[z] ⟶ D[z]
```

Default surface type:

```text
tdapp1_int(FF,GG) :
  (FF ⇛_K GG) ⟶
  (Homd_E(~, —) ⇛_K Homd_D(FF^op ~, GG —))
```

More expanded default surface type:

```text
tdapp1_int(FF,GG) :
  ((z :^n K) → FF[z] ⇒ GG[z]) ⟶
  ((z :^n K) →
     Homd_E(~, —)[z] ⇒ Homd_D(FF[z]^op ~, GG[z] —))
```

The compact placeholder form is likely preferable once the notation is
documented.

### `tdapp1_int_fapp0_transfd`

Surface context:

```text
ϵ : FF ⇛_K GG
```

Default surface type:

```text
tdapp1_int(ϵ) :
  Homd_E(~, —) ⇛_K Homd_D(FF^op ~, GG —)
```

### `tdapp1_int_fapp1_func_transfd`

Surface context:

```text
ϵ,ϵ' : FF ⇛_K GG
```

Default surface type:

```text
tdapp1_int[ϵ,ϵ'] :
  Hom_{FF⇛GG}(ϵ,ϵ') ⟶
  Hom_{Homd_E(~,—)⇛Homd_D(FF^op~,GG—)}(tdapp1_int(ϵ), tdapp1_int(ϵ'))
```

As with the ordinary version, this is a compact rendering of the internal
functorial hom-action.

### `fdapp1_int_transfd`

Kernel shape:

```text
fdapp1_int_transfd(FF)
  : Transfd(homd_int(id_E), homd_int(FF) ∘ FF^op)
```

Surface context:

```text
FF : (z :^n K) → E[z] ⟶ D[z]
```

Default surface type:

```text
fdapp1_int(FF) :
  Homd_E(~, —) ⇛_K Homd_D(FF^op ~, FF —)
```

This is the identity-specialized displayed internal action.

### Retired `piapp1_int` Projection Chain

Earlier drafts used a terminal-specialized `piapp1_int` projection chain. The
current `emdash3_2.lp` has retired those dedicated heads and keeps section
action at the generic displayed-action/projection layer, with `piapp1_func` and
`piapp1_fapp0` as the user-facing section-action package.

Surface context:

```text
K : Cat
E : K → Cat
s : Π z :^n K, E[z]
```

Default surface type:

```text
retired piapp1_int(s) :
  Homd_1(~, —) ⇛_K Homd_E(s^op ~, s —)
```

The important extracted surface action is:

```text
s[f] : Hom_{E[y]}(E[f](s[x]), s[y])
```

where:

```text
f : Hom_K(x,y)
```

This remains the canonical user-facing interpretation, but current kernel/debug
output should describe it through `piapp1_func`, `piapp1_fapp0`,
`fdapp1_int_transfd`, `Fibre_func`, and `homd_src_sec`, not through the retired
`piapp1_int_*` heads.

## Surface Expansion Of `HomdTarget`

The current kernel uses:

```text
Homd_target_section_catd Z D x
Homd_target_catd Z D
```

as stable readability and assertion handles.

Surface mode should usually expand:

```text
Homd_target_catd Z D
```

as:

```text
x ↦ Π y :^n Z^op,
      D[y^-] ⟶_[y] (Hom_Z(x,y)^op ⟶ Cat)
```

More explicitly:

```text
HomdTarget_Z(D)[x]
  =
  Π y :^n Z^op,
    D[y^-] ⟶_[y] (Hom_Z(x,y)^op ⟶ Cat)
```

However, the name `HomdTarget_Z(D)` should be reserved for compact or debug
output. It should not be the default final user-facing syntax for the type of
`homd_int`.

## Parser Architecture

The parser should not try to decide whether a parsed expression is semantically
correct.

Instead:

1. parse text into a surface AST;
2. preserve binder annotations, indexed-arrow annotations, and polarity flips;
3. pass the surface AST to elaboration;
4. let elaboration/typechecking resolve the surface expression to a kernel AST.

For example, parsing:

```text
Π y :^n Z^op,
  D[y^-] ⟶_[y] (Hom_Z(x,y)^op ⟶ Cat)
```

should produce a surface AST containing:

- an indexed binder node for `y :^n Z^op` under a `Π` type former;
- a polarity-flipped fibre occurrence `D[y^-]`;
- an indexed functor-family arrow `⟶_[y]`;
- an ordinary functor arrow `⟶`;
- an ordinary hom expression `Hom_Z(x,y)`;
- an opposite marker on the hom category.

The parser does not need to know, at parse time, whether `D : Catd Z` or whether
`Hom_Z(x,y)^op ⟶ Cat` has the expected family polarity. That belongs to
elaboration.

## Elaborator Architecture

The elaborator should consume the surface AST under a typed context.

Its responsibilities include:

- resolving whether `A ⟶ B` elaborates to `Functor_cat A B`;
- resolving whether `F ⇒ G` elaborates to `Transf_cat F G`;
- resolving whether `(z :^n K) → E[z] ⟶ D[z]` elaborates to `Functord E D`;
- resolving whether `(z :^n K) → FF[z] ⇒ GG[z]` elaborates to `Transfd FF GG`;
- resolving whether `A[z^-] ⟶_[z] B[z]` elaborates to `Functor_catd A B`;
- resolving whether `FF[z^-] ⇒_[z] GG[z]` elaborates to `Transf_catd A B FF GG`;
- inserting `Op_cat`, `Op_catd`, and polarity conversions from explicit `^op`
  and `^-` syntax;
- resolving compact placeholder expressions such as `Hom_B(F^op ~, G —)`;
- elaborating `Π z :^n K, E[z]` to `Pi_cat E`;
- elaborating `Σ z :^n K, E[z]` to `Sigma_cat E`;
- preserving enough source information to pretty-print helpful errors.

The elaborator should be allowed to use definitional equality and normalization
to check the final kernel term.

## Pretty-Printer Architecture

The pretty-printer must be typed and context-aware.

A raw AST pretty-printer is not sufficient because the same object variable may
need to print as:

```text
y
```

or:

```text
y^-
```

depending on the current binder polarity and the family being applied.

The pretty-printer should therefore track:

- the typed context;
- base categories and family categories;
- current binder polarity;
- known family domains, e.g. `D : Catd Z` versus `B : Catd (Op_cat Z)`;
- whether a term is being printed in surface mode or kernel/debug mode;
- whether a kernel helper head should be expanded or retained.

The canonical pretty-printer should prefer one spelling among convertible
alternatives. For the `homd_int` target, the canonical spelling should be:

```text
Π y :^n Z^op,
  D[y^-] ⟶_[y] (Hom_Z(x,y)^op ⟶ Cat)
```

not an equivalent version that hides the polarity flip.

## Symbol Syntax Audit From `emdash3_2.lp`

This section pressure-tests the proposed syntax against the current
`emdash3_2.lp` symbol inventory.

The audit suggests four classes of symbols.

### Syntax Classes

#### Surface Constructors

These should have direct default syntax because they are part of the intended
mathematical language.

Examples:

```text
Cat
Obj(A)
Hom_A(x,y)
A ⟶ B
F ⇒ G
K → Cat
E[z]
Π z :^n K, E[z]
Σ z :^n K, E[z]
A[z^-] ⟶_[z] B[z]
FF[z^-] ⇒_[z] GG[z]
```

#### Surface Macros

These are mathematically meaningful and should print in surface mode, but they
may expand to several kernel heads.

Examples:

```text
Hom_A(~, F —)
Hom_B(F^op ~, G —)
Homd_E(~, —)
Homd_D(FF^op ~, GG —)
E[f](u)
s[f]
```

#### Surface Projection Notation

These are not standalone conceptual constructors, but default syntax should use
them as projection/application notation.

Examples:

```text
F[x]
F[f]
ϵ[x]
FF[z]
ϵ[z]
ϵ[z,u]
s[z]
Σ(η)(z,u)
```

#### Kernel/Debug Heads

These should normally be hidden in surface mode. They exist for stable rewrite
matching, staged projection, or internal packaging.

Examples:

```text
fapp0_func
tapp0_func
piapp0_func
homd_src_func
homd_src_sec
homd_tgt_func
piapp1_func
piapp1_fapp0
Functor_cat_func
Functor_cat_fapp0_func
comp_cat_cov_func
Op_catd_func
```

Kernel/debug mode should still print these heads exactly enough to diagnose
rewrite behavior.

### Section 0: Groupoids And Equality

Kernel symbols:

```text
Grpd
τ
=
eq_refl
ind_eq
eq_trans
Unit_grpd
nat
```

Surface recommendations:

| Kernel symbol | Surface syntax | Class |
| --- | --- | --- |
| `Grpd` | `Type` or `Grpd` | open design |
| `τ A` | hidden coercion from object universe to host type | kernel/debug |
| `x = y` | `x = y` or `x =_A y` when ambiguous | surface constructor |
| `eq_refl x` | `refl_x` or `refl` | surface constructor |
| `ind_eq` | equality induction / hidden eliminator | kernel/debug |
| `eq_trans p q` | `q ∘ p` for equality paths, or `p · q` | surface macro |
| `Unit_grpd` | `Unit` | surface constructor |
| `nat` | `Nat` | surface constructor |

Open decision: whether the user-facing language says `Type`, `Grpd`, or a
universe symbol such as `𝒰`. Because v3 uses groupoidal types as the object
universe, `Grpd` is faithful, but `Type` may be better for proof-assistant
surface syntax. The pretty-printer should support a kernel/debug switch either
way.

### Section 1: Core Categories

Kernel symbols:

```text
Cat
Obj
Hom_cat
Hom
id
comp_fapp0
Op_cat
Path_cat
Core_cat
```

Surface recommendations:

| Kernel symbol | Surface syntax | Class |
| --- | --- | --- |
| `Cat` | `Cat` | surface constructor |
| `Obj A` | `Obj(A)` or implicit object sort | surface constructor |
| `Hom_cat A x y` | `Hom_A(x,y)` or `x ⟶_A y` | surface constructor |
| `Hom A x y` | type of `Hom_A(x,y)` objects | hidden wrapper |
| `id A x` | `id_x` | surface constructor |
| `comp_fapp0 g f` | `g ∘ f` | surface constructor |
| `Op_cat A` | `A^op` | surface constructor |
| `Path_cat A` | `Path(A)` | surface constructor |
| `Core_cat C` | `Core(C)` | surface constructor |

Design note: ordinary composition and equality-path composition should not both
blindly print as `∘` without type-directed disambiguation. The pretty-printer
can print `g ∘ f` for categorical arrows and `p · q` for equality paths if that
is clearer.

### Section 2: Functors, Universes, And Directed Families

Kernel symbols:

```text
Functor_cat
Functor
fapp0
fapp1_func
fapp1_fapp0
Grpd_cat
Cat_cat
Catd_cat
Catd
Functord_cat
Functord
id_funcd
comp_catd_fapp0
Transfd_cat
Transfd
id_transfd
id_func
comp_cat_fapp0
Op_func
Terminal_cat
Terminal_obj
Terminal_func
fapp0_func
Const_func
Obj_func
op
Functor_cat_func
Functor_cat_fapp0_func
comp_cat_cov_func
Op_catd_func
```

Surface recommendations:

| Kernel symbol | Surface syntax | Class |
| --- | --- | --- |
| `Functor_cat A B` | `A ⟶ B` | surface constructor |
| `Functor A B` | type of `A ⟶ B` | hidden wrapper |
| `fapp0 F x` | `F[x]` or `F(x)` | projection notation |
| `fapp1_func F` | `F[_]` as functor on homs | projection notation/debug |
| `fapp1_fapp0 F f` | `F[f]` | projection notation |
| `Grpd_cat` | `Grpd` as category | compact/debug |
| `Cat_cat` | `Cat` as category | compact/debug |
| `Catd_cat K` | `K → Cat` | surface constructor |
| `Catd K` | type of `K → Cat` families | hidden wrapper |
| `Functord_cat E D` | `(z :^n K) → E[z] ⟶ D[z]` | surface constructor |
| `Functord E D` | type of displayed functors | hidden wrapper |
| `id_funcd E` | `id_E` | surface constructor |
| `comp_catd_fapp0 FF GG` | `FF ∘ GG` | surface constructor |
| `Transfd_cat FF GG` | `(z :^n K) → FF[z] ⇒ GG[z]` | surface constructor |
| `Transfd FF GG` | type of displayed transfors | hidden wrapper |
| `id_transfd FF` | `id_FF` | surface constructor |
| `id_func A` | `id_A` | surface constructor |
| `comp_cat_fapp0 F G` | `F ∘ G` | surface constructor |
| `Op_func F` | `F^op` | surface constructor |
| `Terminal_cat` | `1` | surface constructor |
| `Terminal_obj` | `⋆` | surface constructor |
| `Terminal_func A` | `!_A : A ⟶ 1` | surface constructor |
| `Const_func b` | `const(b)` | surface constructor |
| `Obj_func y` | point functor `⟨y⟩ : 1 ⟶ Y` | surface constructor |
| `op` | `(-)^op : Cat ⟶ Cat` | surface macro/debug |
| `fapp0_func` | evaluation-at-object functor | kernel/debug |
| `Functor_cat_func` | curried functor-category constructor | kernel/debug |
| `Functor_cat_fapp0_func` | curried functor-category stage | kernel/debug |
| `comp_cat_cov_func` | curried postcomposition | kernel/debug |
| `Op_catd_func` | pointwise opposite package | kernel/debug |

Design lesson: `*_func` heads often package functoriality of an operation. They
should normally disappear in surface syntax and reappear only when the user asks
for kernel/debug output.

### Section 3: Curried Internal Hom

Kernel symbols:

```text
hom_
hom_con
hom_int
```

Surface recommendations:

| Kernel symbol | Surface syntax | Class |
| --- | --- | --- |
| `hom_ F W` | `Hom_A(W, F —)` | surface macro |
| `hom_con W F` | `Hom_A(F^op ~, W)` | surface macro |
| `hom_int F` | `Hom_A(~, F —)` | surface macro |

For `F : B ⟶ A`:

```text
hom_int(F) : A^op ⟶ (B → Cat)
hom_int(F)(W)[y] = Hom_A(W,F[y])
```

The placeholder syntax is useful here because it reveals variance and prevents
misreading `hom_int(F)` as merely a named helper.

### Section 4: Encoded Sigma Types For Object Layers

Kernel symbols:

```text
τΣ_
Struct_sigma
Σ_
sigma_Fst
sigma_Snd
```

Surface recommendations:

| Kernel symbol | Surface syntax | Class |
| --- | --- | --- |
| `τΣ_ P` | `Σ x : A, P[x]` at host/object layer | surface constructor |
| `Struct_sigma x u` | `(x,u)` | surface constructor |
| `Σ_ P` | groupoidal sigma `Σ x : A, P[x]` | surface constructor |
| `sigma_Fst s` | `s.1` | projection notation |
| `sigma_Snd s` | `s.2` | projection notation |

This object-layer Sigma is separate from `Sigma_cat E`, which is categorical
totalization. The surface language should distinguish them by context and
possibly by binder annotation:

```text
Σ x : A, P[x]          object/type-level Sigma
Σ z :^n K, E[z]        categorical total category
```

### Section 5: Ordinary Transfors And Internal Action

Kernel symbols:

```text
Transf_cat
Transf
tapp0_func
tapp0_fapp0
tapp1_fapp0
tapp1_int_func_transf
tapp1_int_fapp0_transf
tapp1_int_fapp1_func_transf
fapp1_int_transf
```

Surface recommendations:

| Kernel symbol | Surface syntax | Class |
| --- | --- | --- |
| `Transf_cat F G` | `F ⇒ G` | surface constructor |
| `Transf F G` | type of transfors | hidden wrapper |
| `tapp0_func Y` | component evaluation functor at `Y` | kernel/debug |
| `tapp0_fapp0 Y ϵ` | `ϵ[Y]` | projection notation |
| `tapp1_fapp0 ϵ f` | `ϵ[f]` or naturality action, deferred | open design |
| `tapp1_int_func_transf F G` | `tapp1_int(F,G)` | surface macro |
| `tapp1_int_fapp0_transf ϵ` | `tapp1_int(ϵ)` | surface macro |
| `tapp1_int_fapp1_func_transf ϵ ϵ'` | `tapp1_int[ϵ,ϵ']` | surface macro/debug |
| `fapp1_int_transf F` | `fapp1_int(F)` | surface macro |

The proposed ordinary internal-action syntax remains:

```text
tapp1_int(F,G) :
  (F ⇒ G) ⟶
  (Hom_A(~, —) ⇒ Hom_B(F^op ~, G —))
```

Identity specialization:

```text
fapp1_int(F) :
  Hom_A(~, —) ⇒ Hom_B(F^op ~, F —)
```

The reserved capped head `tapp1_fapp0` should be documented as open/deferred.
It is likely to become a compact notation for the selected component of
ordinary naturality, but the current v3.2 kernel deliberately keeps it abstract.

### Section 6: Directed Family Constructors And Pi

Kernel symbols:

```text
Fibre_cat
Pullback_catd
Const_catd
Terminal_catd
Op_catd
Op_funcd
Pi_cat
Pi_func
piapp0_func
piapp0
```

Surface recommendations:

| Kernel symbol | Surface syntax | Class |
| --- | --- | --- |
| `Fibre_cat E k` | `E[k]` | projection notation |
| `Pullback_catd E F` | `F^*E` | surface constructor |
| `Const_catd K A` | `const_K(A)` | surface constructor |
| `Terminal_catd K` | `1_K` | surface constructor |
| `Op_catd E` | `E^op` | surface constructor |
| `Op_funcd FF` | `FF^op` | surface constructor |
| `Pi_cat E` | `Π z :^n K, E[z]` | surface constructor |
| `Pi_func K` | `Π_K` as functor on families | compact/debug |
| `piapp0_func E k` | evaluation functor `ev_k` | kernel/debug |
| `piapp0 s k` | `s[k]` | projection notation |

Design lesson: `Pi_cat E` should print as a binder by default. The functorial
package `Pi_func` exists, but default syntax should show the section category.

### Section 7: Directed Sigma Categories

Kernel symbols:

```text
Sigma_cat
Sigma_func
Sigma_proj1_func
sigma_map_func
```

Surface recommendations:

| Kernel symbol | Surface syntax | Class |
| --- | --- | --- |
| `Sigma_cat E` | `Σ z :^n K, E[z]` | surface constructor |
| `Sigma_func K` | `Σ_K` as functor on families | compact/debug |
| `Sigma_proj1_func E` | `π₁ : Σ_K E ⟶ K` | surface constructor |
| `sigma_map_func η` | `Σ(η)` | surface constructor |

For:

```text
η : E ⇒_K D
```

the surface action is:

```text
Σ(η)(k,u) = (k, η[k](u))
```

The Sigma hom rule should eventually surface as:

```text
Hom_{Σ_K E}((x,u),(y,v))
  ≃ Σ f : Hom_K(x,y), Hom_{E[y]}(E[f](u), v)
```

The current kernel uses an `Op_cat (Sigma_cat (Op_cat (Hom_cat ...)) ...)`
normal form. Surface mode should hide that implementation orientation unless
the user asks for kernel/debug output.

### Section 8: Mixed-Variance Family Constructors

Kernel symbols:

```text
Functor_catd
Functor_catd_func
Functor_catd_fapp0_func
Hom_catd
Transf_catd
```

Surface recommendations:

| Kernel symbol | Surface syntax | Class |
| --- | --- | --- |
| `Functor_catd A B` | `A[z^-] ⟶_[z] B[z]` | surface constructor |
| `Functor_catd_func K` | curried mixed-variance constructor | kernel/debug |
| `Functor_catd_fapp0_func A` | partial mixed-variance constructor | kernel/debug |
| `Hom_catd E X Y` | `Hom_{E[z]}(X[z],Y[z])` as a family in `z` | surface macro |
| `Transf_catd A B FF GG` | `FF[z^-] ⇒_[z] GG[z]` | surface constructor |

Important polarity case:

```text
A : Catd (K^op)
B : Catd K
```

prints as:

```text
A[z^-] ⟶_[z] B[z]
```

under a current `z : K` index. If the current binder is instead
`z : K^op`, the printer must adjust which side gets the `^-` marker.

`Hom_catd E X Y` is not just ordinary `Hom_cat`; it is a family:

```text
z ↦ Hom_{E[z]}(X[z],Y[z])
```

where `X` is a section of `E^op` and `Y` is a section of `E`. Since object
sets are the same under opposite, surface syntax can print the intuitive
`X[z]` and `Y[z]`, with kernel/debug mode available for the exact `Op_catd E`
typing.

### Section 9: Edge And Presheaf Classifiers

Kernel symbols:

```text
Edge_catd_func
Presheaf_catd_func
HomPresheaf_catd_func
```

Surface recommendations:

| Kernel symbol | Surface syntax | Class |
| --- | --- | --- |
| `Edge_catd_func Z` | `Edge_Z` | compact macro |
| `Presheaf_catd_func K` | `Psh_K` | compact macro |
| `HomPresheaf_catd_func Z` | `HomPsh_Z` | compact macro |

Expansions:

```text
Edge_Z(x)[y] = Hom_Z(x,y)^op

Psh_K(A)[k] = A[k^-] ⟶ Cat

HomPsh_Z(x)[y] = Hom_Z(x,y)^op ⟶ Cat
```

These names are useful in explanatory docs, but default printing inside
`homd_int` should usually expand far enough to show:

```text
Hom_Z(x,y)^op ⟶ Cat
```

rather than stopping at `HomPsh_Z(x)[y]`.

### Sections 10-11: Homd Target, Fibre Transport, And Dependent Homs

Kernel symbols:

```text
Homd_target_section_catd
Homd_target_catd
homd_int
fib_cov_tapp0_func
FibCov_target_catd
fib_cov_int
fib_cov_src_func
fib_cov_transf
homd_
homd_src_func
homd_src_sec
homd_tgt_func
```

Surface recommendations:

| Kernel symbol | Surface syntax | Class |
| --- | --- | --- |
| `Homd_target_section_catd D x` | expanded `Π y :^n Z^op, ...` section | surface macro/debug |
| `Homd_target_catd D` | expanded dependent-hom target family | surface macro/debug |
| `homd_int FF` | `Homd_E(~, FF —)` expanded by default | surface macro |
| `fib_cov_tapp0_func E x y u` | `f ↦ E[f](u)` | surface macro |
| `FibCov_target_catd E` | `FibCovTarget(E)` or expanded | compact/debug |
| `fib_cov_int E` | covariant fibre transport package | surface macro |
| `fib_cov_src_func E x` | `u ↦ fib_cov(E,x,u)` | kernel/debug |
| `fib_cov_transf E x u` | `fib_cov(E,x,u)` | compact/debug |
| `homd_ FF x u y v` | `Homd(FF;x,u;y,v)` | surface macro |
| `homd_src_func` | staged first projection | kernel/debug |
| `homd_src_sec` | staged second projection | kernel/debug |
| `homd_tgt_func` | staged third projection | kernel/debug |

Default `homd_int` expansion:

```text
homd_int(FF) :
  (x :^n Z) →
    E[x]^op ⟶
      Π y :^n Z^op,
        D[y^-] ⟶_[y] (Hom_Z(x,y)^op ⟶ Cat)
```

Endpoint:

```text
homd_(FF,x,u,y,v)[f]
  = Hom_{E[y]}(E[f](u), FF[y](v))
```

Canonical under an explicit `y : Z^op` binder, occurrences that consume
`Z`-families must be polarity-flipped:

```text
D[y^-]
E[y^-]
FF[y^-]
```

Informal endpoint equations may suppress this when the binder context is no
longer being displayed.

### Section 12: Section Action

Kernel symbols:

```text
piapp1_src_obj
piapp1_func
piapp1_fapp0
```

Surface recommendations:

| Kernel symbol | Surface syntax | Class |
| --- | --- | --- |
| `piapp1_src_obj E s f` | `E[f](s[x])` | surface macro |
| `piapp1_func E s x y` | `s[x ⟶ y]` as section over homs | surface macro |
| `piapp1_fapp0 E s f` | `s[f]` | projection notation |

Canonical user-facing type:

```text
s[f] : Hom_{E[y]}(E[f](s[x]), s[y])
```

where:

```text
s : Π z :^n K, E[z]
f : Hom_K(x,y)
```

`piapp1_func` is the functor-level package over the base hom-category. Surface
mode should usually reveal the direct action `s[f]`; kernel/debug mode can show
`piapp1_func` when discussing iterability and internal action.

### Section 13: Displayed Internal Hom-Action

Kernel symbols:

```text
tdapp1_int_func_transfd
tdapp1_int_fapp0_transfd
tdapp1_int_fapp1_func_transfd
fdapp1_int_transfd
piapp1_func
piapp1_fapp0
```

Surface recommendations:

| Kernel symbol | Surface syntax | Class |
| --- | --- | --- |
| `tdapp1_int_func_transfd FF GG` | `tdapp1_int(FF,GG)` | surface macro |
| `tdapp1_int_fapp0_transfd ϵ` | `tdapp1_int(ϵ)` | surface macro |
| `tdapp1_int_fapp1_func_transfd ϵ ϵ'` | `tdapp1_int[ϵ,ϵ']` | compact/debug |
| `fdapp1_int_transfd FF` | `fdapp1_int(FF)` | surface macro |
| `piapp1_func E s x y` | section-action package over `Hom_K(x,y)` | compact/debug |
| `piapp1_fapp0 E s f` | `s[f]` | projection notation |

Default compact types:

```text
tdapp1_int(FF,GG) :
  (FF ⇛_K GG) ⟶
  (Homd_E(~, —) ⇛_K Homd_D(FF^op ~, GG —))

fdapp1_int(FF) :
  Homd_E(~, —) ⇛_K Homd_D(FF^op ~, FF —)

s[f] :
  Hom_{E[y]}(E[f](s[x]), s[y])
```

Design lesson: the compact placeholder syntax is not just abbreviation. It is
the clearest way to display how internal action changes the two argument slots.

### Section 14: Displayed Component Notation

Kernel symbols:

```text
Fibre_func
tdapp0_func
tdapp0_fapp0
Fibre_transf
Fibre_transf_app
```

Surface recommendations:

| Kernel symbol | Surface syntax | Class |
| --- | --- | --- |
| `Fibre_func FF z` | `FF[z]` | projection notation |
| `tdapp0_func z` | component-evaluation functor at `z` | kernel/debug |
| `tdapp0_fapp0 z ϵ` | `ϵ[z]` | projection notation |
| `Fibre_transf ϵ z` | `ϵ[z]` | projection notation |
| `Fibre_transf_app ϵ z u` | `ϵ[z,u]` or `ϵ[z](u)` | projection notation |

For:

```text
FF,GG : E ⇒_K D
ϵ : FF ⇛_K GG
```

surface mode should print:

```text
FF[z] : E[z] ⟶ D[z]
ϵ[z] : FF[z] ⇒ GG[z]
ϵ[z,u] : Hom_{D[z]}(FF[z](u), GG[z](u))
```

`Fibre_func` and `Fibre_transf` are readable definitions over stable projection
heads. They should not become new semantic surface constructors.

### Section 14b: Retired Terminal-Specialized `piapp1` Projection Chain

Retired kernel symbols:

```text
piapp1_int_src_transf
piapp1_int_src_app
piapp1_int_tgt_transf
```

Surface recommendations:

| Kernel symbol | Surface syntax | Class |
| --- | --- | --- |
| `piapp1_int_src_transf` | hidden staged projection | kernel/debug |
| `piapp1_int_src_app` | hidden staged projection | kernel/debug |
| `piapp1_int_tgt_transf` | hidden staged projection | kernel/debug |

These heads should not appear in default user syntax. Their whole purpose is to
make the older kernel route:

```text
piapp1_int(s) ↦ piapp1_func(E,s,x,y) ↦ s[f]
```

typecheck and normalize through stable intermediate heads.

Current `emdash3_2.lp` no longer keeps these heads. Kernel/debug mode should
show the generic route through `fdapp1_int_transfd`, `Fibre_func`,
`homd_src_sec`, `piapp1_func`, and `piapp1_fapp0` when that detail is needed.

Surface mode should print the result:

```text
s[f]
```

or, when the internal witness is the point:

```text
retired piapp1_int(s) : Homd_1(~, —) ⇛_K Homd_E(s^op ~, s —)
```

### Section 15: Generic Sigma/Pi Weakening Helpers

Kernel symbols:

```text
sigma_intro_transf
sigma_intro_tapp0_func
pi_eval_transf
const_section_func
section_pullback_func
section_pullback_sec
```

Surface recommendations:

| Kernel symbol | Surface syntax | Class |
| --- | --- | --- |
| `sigma_intro_transf E` | `introΣ_E` or `ηΣ_E` | surface constructor |
| `sigma_intro_tapp0_func E k` | `(k,-) : E[k] ⟶ Σ_K E` | projection/debug |
| `pi_eval_transf E` | `evalΠ_E` | surface constructor |
| `const_section_func K A` | `constSection_{K,A}` | surface constructor |
| `section_pullback_func F E` | `F^* : Π_B E ⟶ Π_A F^*E` | surface constructor |
| `section_pullback_sec F E s` | `F^*s` | projection notation |

Expected surface equations:

```text
introΣ_E[k](u) = (k,u)

evalΠ_E[k](s) = s[k]

constSection_{K,A}(a)[k] = a

(F^*s)[a] = s[F[a]]
```

These helpers are good examples for the future documentation pass because they
look simple in surface syntax but route through several kernel projection heads.

## Design Refinements From The Audit

The symbol audit strengthens several architecture decisions.

### Do Not Make Every Kernel Head A Surface Constructor

Many current symbols are stable heads needed by Lambdapi rewriting:

```text
homd_src_func
homd_src_sec
homd_tgt_func
piapp1_func
piapp1_fapp0
```

Default surface syntax should hide these. Treating them as ordinary user-level
constructors would expose implementation staging as mathematical structure.

### Track Variance As Metadata, Not String Syntax

The printer/parser design needs metadata such as:

```text
family E has base K
family A has base K^op
current binder z has base K
current binder y has base Z^op
```

Only with that metadata can the printer decide between:

```text
D[y]
D[y^-]
```

and can the elaborator reconstruct:

```text
Functor_catd [K] A B
```

from:

```text
A[z^-] ⟶_[z] B[z]
```

### Default Syntax Should Prefer User Actions Over Packages

For example, the default surface syntax should prefer:

```text
s[f] : Hom_{E[y]}(E[f](s[x]), s[y])
```

over:

```text
piapp1_func E s x y : Obj(Pi_cat (...))
```

The package head is still important in kernel/debug mode because it preserves
iterability and functor-level structure.

### Placeholder Syntax Is Necessary For Internal Action

Expressions such as:

```text
Hom_B(F^op ~, G —)
Homd_D(FF^op ~, GG —)
```

are clearer than pure composition notation because they show which argument slot
is transformed contravariantly and which is transformed covariantly.

This is likely the right surface notation family for the `*_int` constructors.

### Binder Syntax Needs A Stable Canonical Form

For round-tripping, the pretty-printer should pick one canonical spelling:

```text
Π y :^n Z^op,
  D[y^-] ⟶_[y] (Hom_Z(x,y)^op ⟶ Cat)
```

It should not alternate among equivalent forms such as:

```text
Π y :^n Z,
  D[y] ⟶_[y^-] (...)
```

unless a later design explicitly chooses that as the canonical orientation.

## Manual Documentation Rollout

Before any TypeScript implementation work, the syntax should be documented in
the current Lambdapi/report files.

Recommended follow-up edits:

1. Add a new section to `reports/EMDASH_FOUNDATIONS.md` summarizing the faithful
   surface syntax, with the core notation table and the polarity rule for
   `z^-`.
2. Add compact header comments in `emdash3_2.lp` near the main symbol groups:
   - ordinary functors/transfors;
   - `Catd`, `Functord`, and `Transfd`;
   - `Functor_catd`, `Hom_catd`, and `Transf_catd`;
   - `Pi_cat`, `Sigma_cat`, `piapp0`, and `piapp1`;
   - `fib_cov_int`;
   - `homd_` and `homd_int`;
   - ordinary `tapp1_int_*` constructors;
   - displayed `tdapp1_int_*`, `fdapp1_int_transfd`, `piapp1_func`, and
     `piapp1_fapp0`.
3. Keep those comments declarative and syntax-focused. Avoid changing rewrite
   rules just to match the surface syntax.
4. Add a short note that surface syntax and kernel heads are intentionally not
   one-to-one in all cases: some stable heads exist for normalization and
   rewriting, not because they should appear in user-facing syntax.

## Suggested `emdash3_2.lp` Header Comment Pattern

For each major symbol, use a compact comment block like:

```text
// Surface syntax:
//   homd_int(FF) :
//     (x :^n Z) →
//       E[x]^op ⟶
//         Π y :^n Z^op,
//           D[y^-] ⟶_[y] (Hom_Z(x,y)^op ⟶ Cat)
//
// Kernel role:
//   Stable internal dependent-hom package. Projection rules expose it through
//   homd_src_func, homd_src_sec, homd_tgt_func, then homd_.
```

For stable projection heads that are not default surface syntax:

```text
// Surface syntax:
//   Hidden in default mode as staged application of homd_int(FF).
//
// Kernel role:
//   Stable rewrite head used to expose the first projection of homd_int.
```

This pattern keeps the Lambdapi file readable while preventing a future reader
from mistaking implementation heads for the intended surface language.

## Open Design Questions

### Placeholder Inventory

The placeholders:

```text
~
—
–
```

need a final policy before the parser is implemented.

Current recommendation:

- use `~` for the contravariant/probe/source placeholder;
- use `—` for the covariant/target placeholder;
- reserve `–` for a future distinction if needed;
- do not introduce additional dash-like symbols until a concrete ambiguity
  appears.

### Indexed Binder Marker

The current canonical proposal uses:

```text
:^n
```

The mnemonic is "natural/displayed indexed variation." In the near-term v3.2
docs and comments, `:^n` should be used for `Π`, `Σ`, and displayed-family
arrow binders:

```text
Π z :^n K, E[z]
Σ z :^n K, E[z]
(z :^n K) → E[z] ⟶ D[z]
```

Earlier drafts used `:^f` for section and total binders. Treat that spelling as
legacy report syntax, not as the canonical plan. If a later implementation
drops explicit binder markers entirely, it should do so as a separate
surface-language simplification, not as part of the v3.2 comment cleanup.

### Compact `Homd` Macro Syntax

The report uses compact expressions such as:

```text
Homd_E(~, —)
Homd_D(FF^op ~, GG —)
```

These should be treated as documented macro-style pretty forms for now. The
parser can support the fully expanded binder syntax first:

```text
Π y :^n Z^op,
  D[y^-] ⟶_[y] (Hom_Z(x,y)^op ⟶ Cat)
```

and add compact placeholder macros later.

### Exact Object-Level Display Under Opposite Binders

Inside:

```text
Π y :^n Z^op, ...
```

the canonical syntax should print `D[y^-]` for `D : Catd Z`.

In explanatory endpoint equations, it may sometimes be clearer to print:

```text
Hom_{E[y]}(E[f](u), FF[y](v))
```

after leaving the opposite-binder context. The documentation should be explicit
when it switches from canonical round-trip syntax to informal mathematical
reading.

## Near-Term `emdash3_2.lp` Comment Cleanup Plan

The next Lambdapi-file implementation pass should be documentation-only unless
a typechecking probe shows that a comment update exposes a missing assertion.
The intended scope is:

1. Replace canonical surface comments using `:^f` with `:^n`.
2. Update `Pi_cat` comments to say:

   ```text
   Pi_cat(E) = Π k :^n K, E[k]
             = (k :^n K) → 1 ⟶ E[k]
   ```

   where `1` is the terminal category/family source, not merely the object
   symbol `⋆`.

3. Update `Sigma_cat` comments to say:

   ```text
   Sigma_cat(E) = Σ k :^n K, E[k]
   ```

4. Update `Functor_catd` comments to use displayed category-family names:

   ```text
   Functor_catd(M,N)[z] = M[z^-] ⟶_[z] N[z]
   ```

5. Update `Transf_catd` comments to use displayed functor names:

   ```text
   Transf_catd(M,N,FF,GG)[z] = FF[z^-] ⇒_[z] GG[z]
   ```

6. Update `homd_int`, `Homd_target_*`, and related examples from
   `Π y :^f Z^op` to `Π y :^n Z^op`.
7. Do not introduce `Pid_cat` in this pass. Use
   `Pi_cat (Transf_catd M N FF GG)` for sections of mixed-variance transfor
   families unless a future computation needs a dedicated stable head.
8. Keep the kernel symbols and rewrite rules unchanged. This is a surface
   syntax/documentation consolidation, not a semantic rearchitecture.

Suggested verification after the comment cleanup:

```bash
rg ':\^f' emdash3_2.lp reports/REPORT_EMDASH_V3_FAITHFUL_SURFACE_SYNTAX_PLAN.md
timeout 60s lambdapi check -w emdash3_2.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

## Validation Strategy For The Future TypeScript Implementation

When the TypeScript implementation resumes, add tests in stages.

### Pretty-Printer Tests

For selected kernel terms, verify that pretty-printing produces the canonical
surface syntax.

Initial examples:

- `hom_int`;
- `fib_cov_int`;
- `homd_`;
- `homd_int`;
- `tapp1_int_func_transf`;
- `fapp1_int_transf`;
- `tdapp1_int_func_transfd`;
- `fdapp1_int_transfd`;
- `piapp1_func` / `piapp1_fapp0`;
- `Functor_catd`;
- `Transf_catd`;
- `Pi_cat`;
- `Sigma_cat`.

### Parser Tests

For canonical surface strings, verify that parsing produces the expected
surface AST, preserving:

- binder kind;
- base/opposite base;
- polarity flips;
- indexed arrows;
- ordinary arrows;
- placeholders.

Parser tests should not require full semantic correctness.

### Elaboration Tests

For parsed surface ASTs under typed contexts, verify elaboration to kernel
terms definitionally equal to the intended Lambdapi expressions.

The central test should be:

```text
parse(pretty(kernel_term)) ≡ kernel_term
```

for all initial examples.

### Negative Tests

Add negative tests where a string parses but fails elaboration, for example:

```text
Π y :^n Z^op,
  D[y] ⟶_[y] (Hom_Z(x,y)^op ⟶ Cat)
```

under a context where:

```text
D : Catd Z
```

The parser should accept the text as a surface AST. The elaborator should reject
or request correction because `D[y]` uses the wrong polarity under a `Z^op`
binder; canonical syntax should be `D[y^-]`.

## Summary

The faithful emdash surface syntax should default to mathematical syntax, not
kernel syntax.

The most important design commitments are:

- default surface printing expands important helper heads such as
  `Homd_target_catd` into dependent-hom notation;
- the pretty-printer is typed and polarity-aware;
- `z^-` means polarity inversion relative to the current binder;
- under `Π y :^n Z^op`, a family `D : Catd Z` is applied as `D[y^-]`;
- `⟶_[z]` and `⇒_[z]` distinguish mixed-variance family constructors from
  ordinary `⟶` and `⇒`;
- the parser creates a surface AST and leaves semantic correctness to
  elaboration;
- the long-term invariant is `parse(pretty(kernel_term)) ≡ kernel_term` up to
  definitional equality;
- near-term work should document this syntax in `emdash3_2.lp` and
  `reports/EMDASH_FOUNDATIONS.md` before implementing the TypeScript tooling.
