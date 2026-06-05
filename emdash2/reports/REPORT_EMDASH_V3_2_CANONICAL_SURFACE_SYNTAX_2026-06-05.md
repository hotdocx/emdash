# emdash v3.2 Canonical Surface Syntax

Date: 2026-06-05

Status: current notation authority for v3.2 comments, examples, and future
surface-syntax/parser planning.

Supersedes:

```text
reports/REPORT_EMDASH_V3_FAITHFUL_SURFACE_SYNTAX_PLAN.md
```

This report consolidates the notation settlement from:

```text
reports/REPORT_EMDASH_V3_2_FUNCTOR_STRUCTURAL_LOGIC_PRELIM_PLAN_2026-06-04.md
```

especially the postscript:

```text
Postscript 2026-06-05: Shaped Turnstile And Indexed Hom Notation
```

## Design Principles

The surface syntax should distinguish four roles:

- ordinary homs inside an ambient category;
- indexed/displayed homs inside an ambient displayed category;
- ordinary and shaped functor/program categories;
- section categories.

The operators are intentionally different:

```text
->      ordinary hom
->_     indexed/displayed hom
⊢       ordinary or shaped functor/program category
⊢_      mixed-variance displayed functor/program-family category
=>      transformation category
=>_     indexed/displayed transformation category
Π       terminal-shape section category
```

Subscripts carry displayed indices or future substitutions. Superscripts carry
ambient category or displayed-family annotations.

## Ordinary Homs

Canonical explicit form:

```text
a ->^C b
```

Kernel meaning:

```text
Hom_cat C a b
```

When the ambient category is clear:

```text
a -> b
```

Example:

```text
f :^n x -> z
```

means:

```text
f :^n Hom_cat Z x z
```

when `x z : Obj Z`.

Do not use `->_C` for ordinary homs. The operator `->_` is reserved for
indexed/displayed homs.

## Indexed Homs

Canonical explicit form:

```text
aa[z^-] ->_[z]^R bb[z]
```

Kernel meaning:

```text
Hom_catd R aa bb
```

where:

```text
R  : Catd Z
aa : Obj(Pi_cat (Op_catd R))
bb : Obj(Pi_cat R)
```

When `R` is clear:

```text
aa[z^-] ->_[z] bb[z]
```

The kernel fibre equation is:

```text
(Hom_catd R aa bb)[z]
  = aa[z^-] ->^(R[z]) bb[z]
```

or, in kernel notation:

```text
Fibre_cat (Hom_catd R aa bb) z
  = Hom_cat (R[z]) (aa[z^-]) (bb[z])
```

## Ordinary Functor Categories

Canonical form:

```text
A ⊢ B
```

Kernel meaning:

```text
Functor_cat A B
```

Equivalently:

```text
Hom_cat Cat_cat A B
```

with the existing kernel rewrite:

```text
Hom_cat Cat_cat A B ↪ Functor_cat A B
```

## Shaped Functor Categories

Canonical form:

```text
z :^n Z ; E[z] ⊢ D[z]
```

Kernel meaning:

```text
Functord_cat E D
```

where:

```text
E : Catd Z
D : Catd Z
```

This is a category expression. It may appear wherever a category is expected:

```text
C ⊢ (z :^n Z ; E[z] ⊢ D[z])
```

means:

```text
Functor_cat C (Functord_cat E D)
```

Do not write:

```text
z :^n Z ; e : E[z] ⊢ D[z]
```

for plain `Functord_cat E D`. The shape `E[z]` is part of the generalized
quantification; there is no object variable `e` available to the target family.
If the target depends on an actual object of `E[z]`, that is a different
dependent/telescopic construction, likely represented through `Sigma_cat E`.

## Section Categories

Canonical form:

```text
Π (z :^n Z), D[z]
```

Kernel meaning:

```text
Pi_cat D
```

Definitionally:

```text
Pi_cat D = Functord_cat (Terminal_catd Z) D
```

Do not make an Agda-style parenthesized binder-arrow form the primary section
syntax. The `Π` spelling should visibly signal the terminal-shape section
category.

## Mixed-Variance Displayed Functor Families

Canonical functor-category-flavoured form:

```text
A[z^-] ⊢_[z] B[z]
```

Kernel meaning:

```text
Functor_catd A B
```

where:

```text
A : Catd(Op_cat Z)
B : Catd Z
```

The operator `⊢_` is distinct from plain `⊢`. If the index is omitted in a
readability abbreviation, the operator remains `⊢_`, not `⊢`.

Generic indexed-hom explanation:

```text
A[z^-] ->_[z]^Cat B[z]
```

means:

```text
Hom_catd (Const_catd Z Cat_cat) A B
```

which reduces to:

```text
Functor_catd A B
```

The generic `->_[z]^Cat` reading is useful when emphasizing that
`Functor_catd` is the `Cat`-ambient instance of `Hom_catd`; the `⊢_[z]`
reading is preferred when emphasizing the functor/program-family type former.

## Transformations

Ordinary transformation category:

```text
F => G
```

Kernel meaning:

```text
Transf_cat F G
```

Equivalently:

```text
Hom_cat (Functor_cat A B) F G
```

Indexed transformation category:

```text
FF[z^-] =>_[z] GG[z]
```

Kernel meaning:

```text
Transf_catd A B FF GG
```

Generic indexed-hom explanation:

```text
FF[z^-] ->_[z]^(Functor_catd A B) GG[z]
```

means:

```text
Hom_catd (Functor_catd A B) FF GG
```

which reduces to:

```text
Transf_catd A B FF GG
```

## Nested Telescope Example

Canonical surface form:

```text
k :^n K ; C[k] ⊢ (z :^n Z ; E[k^-;z] ⊢ D[k;z])
```

Telescope order matters. `k;z` means first specialize in `k`, then specialize
the resulting `Z`-family in `z`. It is not a product-base pair `(k,z)`.

Morally:

```text
C : Catd K
E : K^op ⊢ Catd Z
D : K    ⊢ Catd Z
```

The inner expression:

```text
z :^n Z ; E[k^-;z] ⊢ D[k;z]
```

means:

```text
Functord_cat (E[k^-]) (D[k])
```

The family over `K` is represented by:

```text
Hom_catd (Const_catd K (Catd_cat Z)) Ebar Dbar
```

where:

```text
Ebar[k^-] = E[k^-; -] : Catd Z
Dbar[k]   = D[k; -]   : Catd Z
```

and the full category is:

```text
Functord_cat C (Hom_catd (Const_catd K (Catd_cat Z)) Ebar Dbar)
```

## Future Substitution Syntax

The indexed operators leave room for later pullback/substitution notation:

```text
A[z^-] ->_[z:=f]^R B[z]
A[z^-] ⊢_[z:=f] B[z]
```

These should mean that the corresponding displayed family over `Z` is pulled
back along:

```text
f : K ⊢ Z
```

approximately:

```text
Pullback_catd (Hom_catd R A B) f
Pullback_catd (Functor_catd A B) f
```

The exact syntax and elaboration should wait until substitution notation is
needed by an implementation task.

## Migration Policy

Active v3.2 comments and new reports should use this notation.

Historical dated reports may keep older notation behind an explicit warning
banner. Current active reports should either be updated in place or replaced by
a supersession pointer to this report.
