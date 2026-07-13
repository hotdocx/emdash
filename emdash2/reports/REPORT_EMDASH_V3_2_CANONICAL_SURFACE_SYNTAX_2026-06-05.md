# emdash v3.2 Canonical Surface Syntax

Date: 2026-06-05
Last reviewed: 2026-07-10

Status: current notation authority for v3.2 comments, examples, and future
surface-syntax/parser planning.

Notation in this report is immediately authoritative for mathematical comments
and examples. It becomes parser syntax only after a separate elaboration and
grammar implementation; no notation below should be read as an already active
Lambdapi parser extension.

Supersedes the older v3 faithful surface-syntax plan, which is no longer an
active report after the 2026-06-05 reports consolidation.

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

## Covariant And Contravariant Hom Actions

For an arrow:

```text
u : X ->^A Y
```

postcomposition by `u` is written with the standard lower-star action:

```text
u_* : (W ->^A X) ⊢ (W ->^A Y)
u_*(g) = u o g.
```

Kernel owners:

```text
hom_postcomp_func
hom_postcomp_fapp0.
```

Precomposition by `u` is written with the standard upper-star action:

```text
u^* : (Y ->^A Z) ⊢ (X ->^A Z)
u^*(h) = h o u.
```

Kernel owners:

```text
hom_precomp_along_func
hom_precomp_along_fapp0.
```

For a functor `F : B ⊢ A` and `p : X ->^B Y`, comments should expose the
actual arrow acting on the represented hom:

```text
(F[p])_*(g)
(F[p])^*(h).
```

Thus the preferred mathematical readings are:

```text
hom_postcomp_fapp0(F,p,g)       = (F[p])_*(g)
hom_precomp_along_fapp0(F,p,h)  = (F[p])^*(h).
```

When both endpoints move, use the hom-bifunctor action:

```text
Hom_A(g,f)[h] = f o h o g
              = f_*(g^*(h))
              = g^*(f_*(h)).
```

Kernel owners:

```text
Hom_func(g,f)
Hom_fapp0(g,f,h).
```

The equalities between the two factorizations and the rigid `Hom_*` value are
mathematical/proof-time comparisons in the current kernel. This notation does
not imply a runtime rewrite from post/precomposition syntax to `Hom_fapp0`.

Use `_*` and `^*` for represented hom actions, not for arbitrary functor
application. Ordinary functor application remains `F[x]` and `F[p]`.

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

Kernel comparison and runtime projections:

```text
Pi_cat D =proof-time Functord_cat (Terminal_catd Z) D
Obj(Pi_cat D) -> Obj(Functord_cat (Terminal_catd Z) D)
Hom_(Pi_cat D)(s,t) -> Transfd_cat(Terminal_catd Z,D,s,t)
```

`Pi_cat` is a stable section-category facade, not a transparent notation-only
alias. Special mathematical identifications, such as constant sections with
ordinary functors or Sigma-projection sections with displayed functors, are
direct proof-time comparisons.

The Pi-facing eliminators remain semantic surface names over the generic
displayed tower:

```text
piapp0_func(D,z)       : (Π (i :^n Z), D[i]) ⊢ D[z]
piapp0(s,z)            = s[z]
pi_hom_fapp0(eta,z)    = eta[z]
piapp1_func(s,x,y)[f]  = piapp1_fapp0(s,f) = s[f]
```

Their object, hom, and next-hom computations project through `tapp0_func`,
`tdapp0_func` / `tdapp0_fapp0`, and the generic displayed internal-hom action.
Do not read these names as additional primitive type formers merely because
`Pi_cat` itself is a stable primitive category facade.

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
