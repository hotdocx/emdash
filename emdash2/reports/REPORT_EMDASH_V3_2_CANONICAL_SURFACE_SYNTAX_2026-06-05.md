# emdash v3.2 Canonical Surface Syntax

Date: 2026-06-05
Last reviewed: 2026-08-01

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

Likewise, write displayed identity using the generic identity notation. The
compatibility name `id_transfd(FF)` is a transparent view of
`id_(Functord_cat(E,D))(FF)`, not a distinct constructor; no parallel
`id_transf` spelling is part of the canonical surface. At the ordinary/
displayed façade boundary, typed consumers may distinguish the stable
`Functord_cat(E,D)` and `Transf_cat(K,Cat,E,D)` category presentations even
though the mathematical identity notation is the same.

Write component composition mathematically as
`(eta ∘ epsilon)[z] = eta[z] ∘ epsilon[z]`. The active projection beta
uses that same left-to-right orientation for ordinary `tapp0_fapp0` and
displayed `tdapp0_fapp0`. This does not make `tdapp0_fapp0` a second
strict-functor composition owner: generic action cuts still contract as
`F[g] ∘ F[f] -> F[g ∘ f]`, while stable component projections expose a
composite pointwise. The two levels join through the documented
component-evaluation projection ladder.

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

### Constant-domain displayed evaluation

For `A : Cat` and `B : Catd K`, use the readable abbreviation:

```text
S(A,B) = Functor_catd(Const_catd(Op_cat K,A),B).
```

Its fibres are `S(A,B)[k] = Functor(A,B[k])`. The active coherent evaluator
is written:

```text
Eval_funcd(B) : P(S(A,B),Const_catd(K,A)) ⊢_K B
Eval_funcd(B)[k] = Eval_func(A,B[k]).
```

The source is the transparent displayed sibling product described below.
The constant-domain qualification is semantic, not merely notational: an
arbitrary `Catd(Op_cat K)` family cannot also serve as the covariant argument
family. Generic `fapp`/`tapp` owns the evaluator's identity, composition,
base-arrow action, and higher naturality; do not add constructor-specific
copies of those rules.

Displayed weakening to a fixed argument is:

```text
Terminal_funcd(E) : E ⊢_K Const_catd(K,Terminal_cat)
Terminal_funcd(E)[k] = Terminal_func(E[k]).
```

Compose it with `const_section_{K,A}(a)` to obtain a coherent constant
argument from any displayed source. Consequently a future convenient
categorical binder may present `F x` or `F a` without spelling the product,
pairing, or evaluator, while direct TypeScript construction may retain
explicit `apply` nodes. This notation does not select a text parser,
explicit bracket punctuation, arbitrary mixed-domain evaluation, or a
general dependent-chain lowering.

## Displayed Sibling Product Notation

For Cat-valued displayed families `B,C : Catd K`, write:

```text
P(B,C) : Catd K
```

for the transparent family:

```text
uncurry(Product_cat_func) o Struct_sigma(B,C).
```

`P` is mathematical and direct-TypeScript surface notation, not a
`Product_catd` kernel owner or an implemented string-parser token.

The fixed-base structural maps are written:

```text
projL_d(B,C) : P(B,C) ⊢_K B
projR_d(B,C) : P(B,C) ⊢_K C

FF : E ⊢_K B
GG : E ⊢_K C
pair_d(FF,GG) : E ⊢_K P(B,C).
```

Their active kernel owners are `Product_projL_funcd`,
`Product_projR_funcd`, and `Product_pair_funcd`. The derived structural maps
are:

```text
swap_d(B,C) = pair_d(projR_d(B,C),projL_d(B,C))
diag_d(B)   = pair_d(id_d(B),id_d(B)).
```

These express exchange and contraction of independent siblings over one
shared base. They do not license exchange across a genuine dependency edge.
The internalized arrow/cell action of pairing is written componentwise:

```text
cell(pair_d(FF,GG),p,u)
  = pair(cell(FF,p,u),cell(GG,p,u)).
```

The active owner is still `fdapp1_int_cell`; this notation does not introduce
a displayed-product cell owner.

The dependency-aware direct-TypeScript frontend uses the canonical
reindexing presentation:

```text
P(B,C)[F] = P(B[F],C[F]).
```

The right side means
`P(Pullback_catd(B,F),Pullback_catd(C,F))`. This spelling records frontend
Core selection only: the raw kernel term `Pullback_catd(P(B,C),F)` is not
currently definitionally equal to it, and no generic total-category pullback
is intended.

The bounded direct-TypeScript mixed telescope is:

```text
k : K;
a : A[k];
b : B[(k,a)], c : C[(k,a)];
d : D[((k,a),(b,c))].
```

It is constructed with `displayedDependentContextLambda` in the root-only
`fibred-displayed-chain-2a` profile. The middle sibling block is inferred from
the typed family bases; explicit `apply` and `fibrePair` nodes remain valid
direct-TypeScript syntax. This is not a string-parser grammar or a claim of
arbitrary `:^nd` telescope depth.

Constant-middle direct application may be written:

```text
F : C ⊢_K Functor_catd(A,Const_catd(K,X))
G : C ⊢_K Functor_catd(Const_catd(Op K,X),B)

lambda^n k. lambda^f c. lambda^f a. G[k](c)(F[k](c)(a))
  : Functord_cat C (Functor_catd A B).
```

The explicit kernel owner is `Functor_comp_pair_funcd`: pair `F` and `G`
over their common displayed source and apply that owner. The two occurrences
of `X` use opposite constant-family bases because `Functor_catd` is
contravariant in its source and covariant in its target; their fibres are
definitionally the same ordinary category. This notation is qualified to a
constant middle. It neither coerces a general positive family into a negative
one nor denotes mixed curry. The nested binders themselves remain the
fundamental introduction form, and the generic `fapp`/`tapp` calculus owns
the resulting object, arrow, base-arrow, and higher action.

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

## Walking-Endomorphism And Book Notation

For the selected walking-endomorphism development, introduce the mathematical
abbreviations once and then keep them distinct from kernel identifiers:

```text
W                  = WalkingEnd
*                  = walking base
ell : * ->^W *     = walking generator
BNat               = separate concrete one-object Nat-monoid model
```

`W` is opaque. Never write `W = BNat` or replace
`Hom_W(*,*)` definitionally by `Nat`. The checked result is
an equivalence of underlying carriers:

```text
Hom_W(*,*) ≃_Type Nat.
```

This notation corresponds to `walking_hom_nat_type_equiv`. Do not
omit the `Type` qualifier when the surrounding prose might suggest a
packaged monoid or hom-category equivalence.

The directed code and its two maps are written:

```text
Code : W ⊢ Cat
encode_x : Hom_W(*,x) -> Obj(Code[x])
power(0)       = id_*
power(succ n)  = ell o power(n)
decode_x : Obj(Code[x]) -> Hom_W(*,x).
```

Their active owners are `walking_Code_catd`,
`walking_encode`, `walking_power`, and the fibrewise
observation of `walking_directed_decode_funcd`. Ordinary functor
application notation remains appropriate for Code action:

```text
encode_x(p) = Code[p](0).
```

The normalization proof must retain its directed stage:

```text
norm_p : p ->^(Hom_W(*,x)) decode_x(encode_x(p))
path(norm_p) : p = decode_x(encode_x(p)).
```

The first line names the cell
`walking_directed_normalization_cell`. The second is equality
extracted by hom-discreteness and names
`walking_directed_normalization_path`. Comments and book prose must
present them in that order; `path(norm_p)` is mathematical notation,
not implemented parser syntax.

Use `Checked`, `Formal consequence`,
`Mathematical development`, and `Research boundary` for
book theorem status. These labels report evidence strength and do not alter
the formula notation above.

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
