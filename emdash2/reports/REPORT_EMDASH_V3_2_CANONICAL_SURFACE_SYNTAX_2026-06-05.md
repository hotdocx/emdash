# emdash v3.2 Canonical Surface Syntax

Date: 2026-06-05
Last reviewed: 2026-07-27

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

## Cat-Valued Presheaves

Canonical comment/formula notation:

```text
Psh_cat(K) = K^op ⊢ Cat
P :^n Psh(K)
F^* : Psh_cat(B) ⊢ Psh_cat(A)
F^*(P) = Pullback_catd(P,Op_func(F)).
y_K : K ⊢ Psh_cat(K)
y_K(U)[V] = Hom_K(V,U)
Into^-_K(U) = Sigma_(V : K^op) Hom_K(V,U)
K/U = Op_cat(Into^-_K(U)).
```

Kernel meanings:

```text
Psh_cat K
Psh K
Psh_pullback_func F
yoneda_psh_func K
yoneda_psh U
Into_restr_cat U
Slice_cat U
```

`Psh_cat(K)` is the category expression; `Psh(K)` is its decoded object/type
classifier. The equality with `K^op ⊢ Cat` is proof-time presentation
comparison plus explicit runtime object/hom projections, not a runtime
category-head rewrite. This notation currently means Cat-valued presheaves.
Do not use `Psh` or `stack` to silently claim pointwise discreteness or a
descent condition.

`Into^-_K(U)` is explicitly restriction-oriented; `K/U` is the conventional
slice and has the opposite direction. Cat-valued higher sieves use:

```text
HigherSieveClassifier(K)[U]
  = Catd_cat(Into^-_K(U))
  =proof-time Psh_cat(K/U)
maximal_higher_sieve(U) = Terminal_catd(Into^-_K(U)).
```

Kernel names are `HigherSieveClassifier K`, `HigherSieve_cat U`,
`HigherSieve U`, and `maximal_higher_sieve U`. The displayed second equality
uses the common proof-time `Catd_cat(Into_restr_cat U)` presentation; it is
not a direct runtime conversion. Write `higher sieve` or `Cat-valued higher
sieve` for this object.

The downstream ordinary specialization uses:

```text
Subterminal(C)
  := IsPropGrpd(Obj(C)) and IsGroupoidalCat(C)
OrdinarySieve(S)
  := forall f : Into^-_K(U), Subterminal(S[f])
Sieve_K(U)
  := { S : HigherSieve_K(U) | OrdinarySieve(S) }
p^*(R) := sieve_pullback(p,R).
```

Kernel names are `IsSubterminalCat C`, `IsOrdinarySieve S`, `Sieve U`, and
`sieve_pullback p R`. In prose, unqualified “sieve” means this ordinary
pointwise-subterminal package; say “higher sieve” explicitly for arbitrary
Cat-valued data. Do not write `Omega_K` as though it were active: the name
`Omega` remains reserved until sieve setness and contravariant family assembly
are checked. Pullback along an identity is not advertised as definitional
package eta because it reconstructs retained proposition evidence.

Direct sieve-topology notation is:

```text
f ∈ R                    := SieveMembership(R,f)
⊤_U                      := maximal_sieve(U)
J ⊩ R                    := Covers(J,R)
p^*R                     := sieve_pullback(p,R)
Topology(K)              := GrothTopology(K)
J_chaotic                := chaotic_groth_topology(K).
```

`f` denotes the full restriction-total pair `(V,f : V -> U)` where necessary;
do not suppress its domain when the local-character formula would become
ambiguous. The three checked topology laws may be written:

```text
J ⊩ ⊤_U
J ⊩ R -> J ⊩ p^*R
J ⊩ R -> (forall f ∈ R, J ⊩ f^*S) -> J ⊩ S.
```

Kernel names are `SieveCoverage K`, `Covers J R`, `GrothMaximal J`,
`GrothStable J`, `SieveLocalityPremise J R S`, `GrothLocal J`,
`IsGrothTopology J`, and `GrothTopology K`. Use
`groth_topology_cover_predicate`, `groth_topology_maximal`,
`groth_topology_pullback`, and `groth_topology_local_character` for named
package observations. “Coverage” here means a direct proposition-valued
predicate on sieves; a syntax/API for generating cover families is not yet
selected. `Omega`, free saturation, sheafification, and descent remain
separate names and gates.

Set-carrier commutative-ring notation is:

```text
R : CommRing
|R|                      := comm_ring_carrier(R)
0_R                      := comm_ring_zero(R)
1_R                      := comm_ring_one(R)
x +_R y                  := comm_ring_add(R,x,y)
-_R x                    := comm_ring_neg(R,x)
x *_R y                  := comm_ring_mul(R,x,y).

h : R ->_CRing S         := h : CommRingHom(R,S)
|h|                      := comm_ring_hom_function(R,S,h)
h(x)                     := comm_ring_hom_apply(R,S,h,x)
id^CRing_R               := comm_ring_hom_id(R)
id^pw_R                  := comm_ring_hom_id_pointwise(R)
g ∘_CRing f              := comm_ring_hom_comp(g,f).
g ∘_pw f                 := comm_ring_hom_comp_pointwise(g,f)

u : Unit_R(x)              := u : CommRingUnitEvidence(R,x)
u^-1                       := comm_ring_unit_inverse(R,x,u)
Loc_R(f)                   := CommRingLocalizationAt(R,f)
R[1/f]_ell                 := comm_ring_localization_target(R,f,ell)
iota_ell                   := comm_ring_localization_map(R,f,ell)
IterLoc_R(f,g)             := CommRingIteratedLocalizationAt(R,f,g)
CompLoc_R(f,g,m,p)         := CommRingIteratedLocalizationComparison(m,p).

O : CRingPsh(K)            := O : CommRingPsh(K)
O(U)                       := comm_ring_psh_value(O,U)
O[f]                       := comm_ring_psh_restriction_hom(O,f)
f^*_O(s)                   := comm_ring_psh_restrict(O,f,s)
D_O(s;f)                   := CommRingPshInvertibleAlong(O,s,f)
```

Subscripts may be omitted only when the ring is unambiguous.  The carrier is
not a bare meta-level `Type`: `comm_ring_carrier_package R` retains its
`SetU_grpd` package, and `comm_ring_carrier_is_set R` exposes its sethood
evidence.  Kernel constructors are `comm_ring_ops_intro`,
`comm_ring_laws_intro`, `comm_ring_structure_intro`, and `comm_ring_intro`;
the eight readable law projections are named `comm_ring_add_assoc_law`
through `comm_ring_left_distrib_law`.  `zero_comm_ring` denotes the checked
one-element zero ring, so notation must not suggest an implicit `0 != 1`
axiom.

Structured-map constructors use `comm_ring_hom_intro` and
`comm_ring_hom_laws_intro`. The retained witnesses have readable projections
`comm_ring_hom_zero_law`, `comm_ring_hom_one_law`,
`comm_ring_hom_add_law`, `comm_ring_hom_neg_law`, and
`comm_ring_hom_mul_law`. `CommRing_cat` is active with objects `CommRing` and
homs `Path_cat(CommRingHom(R,S))`; its whole identity/composition arrows retain
the generic category owners. Thus `h(x)` computes for explicit constructors,
but this notation must not imply an extra runtime equation reducing
`comm_ring_hom_apply(comm_ring_hom_id(R),x)` to `x`.

The selected `id^pw_R` notation is the rigid pointwise identity comparison
used by the empty-variable polynomial model. Its carrier application computes
to `x`, and `comm_ring_hom_id_pointwise_path` compares it at proof time with
`id^CRing_R`. Do not silently replace generic whole-arrow identity by this
pointwise view.

The selected `g ∘_pw f` notation is reserved for the rigid pointwise
composition comparison used by iterated localization. Its carrier application
computes to `g(f(x))`, and `comm_ring_hom_comp_pointwise_path` compares it at
proof time with `g ∘_CRing f`. Do not silently replace generic whole-arrow
composition by this pointwise view in comments or future surface elaboration.

`CommRingHomPointwisePath h k` is the canonical premise for
`comm_ring_hom_ext`; notation `h = k by ext x` may be used in prose only when
the displayed pointwise path is clear. `comm_ring_unit_evidence_is_prop`
records that explicit inverse evidence is a property.

For `ell : Loc_R(f)`, `R[1/f]_ell` and `iota_ell` always retain the chosen
package subscript. The library does not install a global canonical term named
`R[1/f]`, nor does it identify two chosen packages judgmentally. A factor
through `iota` is a term of `CommRingLocalizationFactor(iota,h)`, whose second
field is the pointwise triangle `k(iota(x)) = h(x)`. The localization property
states that this factor classifier is contractible whenever `h(f)` has
explicit unit evidence.

For `m : IterLoc_R(f,g)`, the first stage is a chosen localization at `f` and
the second is a chosen localization at the image of `g`; its stable composite
map sends `f*g` to a unit. For
`p : Loc_R(f*g)`, `CompLoc_R(f,g,m,p)` retains canonical forward and reverse
factors with pointwise triangles. No notation in this section claims that the
two maps are inverse or that the chosen targets are equal.

`CRingPsh(K)` is only comment/example notation for the transparent category
`Functor_cat(Op_cat(K),CommRing_cat)`; it does not denote a new rigid kernel
head. For `f : V -> U`, `O[f]` is contravariant and
`f^*_O(s) : |O(V)|`. The library supplies explicit paths
`id^*_O(s)=s` and `(f∘g)^*_O(s)=g^*_O(f^*_O(s))`; this notation must not be
read as adding carrier rewrites for generic `CommRing_cat` identity or
composition.

`D_O(s;f)` names the proposition that `f^*_O(s)` has explicit unit
evidence. The whole ordinary sieve is now
`comm_ring_psh_invertibility_sieve(K,O,U,s)`, so comments may write
`InvSieve_O(s)` or `D_O(s)` for that package and retain `D_O(s;f)` for its
literal-arrow membership classifier. A sheaf, topology, or locally ringed
structure is not implicit in `O : CRingPsh(K)`.

For the separately promoted finite-family layer, comments and examples may
write

```text
[]                       : FinFam(A,0)
x :: xs                  : FinFam(A,succ n)
All_P(xs)                : dependent evidence P(x_i) for every x_i
AllOver_Q(xs;ps)         : evidence Q(x_i,p_i) over selected p_i : P(x_i)
sum_R(xs)                : |R|
dot_R(a,f)               : |R|
Unimod_R(f; a, p)        : chosen data p : dot_R(a,f) = 1
ZarCover_R(n; f; a, p)   : finite algebraic cover presentation
LocFam_R(f; ell)         : selected localization ell_i at every f_i
ZarFamily_R(c; ell)      : algebraic cover c plus selected localizations
D_R(f;ell)               : affine arrow (R[1/f]_ell,iota_ell) into R
Members_Q(c;ell)         : each selected D_R(f_i;ell_i) belongs to Q
h_*ZarFamily(c;m)        : mapped cover with supplied target localizations m
h^*member                : membership of D_S(h(f);m) in h^*Q
ZarPresentationCovers_T(c): every sieve containing c covers in supplied T
ZarCompatible(T)         : T admits every selected finite Zariski presentation
```

The literal owners are `FiniteFamily`, `finite_family_nil/cons`,
`FiniteFamilyAll`, `FiniteFamilyAllOver`,
`finite_family_all_over_map`, `comm_ring_finite_sum`, `comm_ring_finite_dot`,
`CommRingUnimodularPresentation`, and
`CommRingZariskiCoverPresentation`. Presented geometric data additionally use
`CommRingLocalizationFamily`, `CommRingZariskiCoverFamily`,
`CommRingBasicOpenFamilyMembership`,
`CommRingZariskiCoverFamilyMembership`,
`comm_ring_zariski_cover_family_map`, `comm_ring_basic_open_arrow`, and
`comm_ring_basic_open_pullback_membership`. The supplied-topology boundary
additionally uses `CommRingZariskiPresentationCovers`,
`IsCommRingZariskiCompatibleTopology`, and
`CommRingZariskiCompatibleTopology`. The semicolon-separated cover
notation retains the coefficient family and equation; it must not be read as
a propositionally truncated existence statement. `ZarCover` alone names the
algebraic unit-ideal presentation; `ZarFamily` additionally retains selected
universal-property localization packages. Neither spelling denotes an
already constructed `Spec`, proposition-valued sieve coverage, or topology.
The base-change membership operation also requires explicit source and target
localization choices; no global localization choice is implicit. The generic
finite map owns arbitrary-length recursion. A specialized expanded Zariski
projection/recursion spelling is not canonical while it exceeds the bounded
elaboration budget; comments should use the generic owner plus the named
elementwise step rather than inventing a rigid membership head.
`ZarCompatible(T)` says only that `T` contains the selected Zariski cover
basis; it does not denote the least generated topology. The maintained
chaotic instance is a feasibility model, not canonical `Zar` syntax.

For the universal-property polynomial layer, comments and examples may write

```text
PolyAlg_R(X)             : chosen free commutative R-algebra package
R[X]_p                   : target ring of p : PolyAlg_R(X)
iota_p                   : R ->_CRing R[X]_p
var_p(x)                 : |R[X]_p|
Ext_p(h,v)               : contractible extension classifier
```

The literal owners are `CommRingPolynomialAlgebra`,
`comm_ring_polynomial_target`, `comm_ring_polynomial_base_map`,
`comm_ring_polynomial_variables`, and `CommRingPolynomialFactor`. The package
subscript `p` is mandatory: the library does not install a global chosen term
named `R[X]`. `Ext_p(h,v)` retains both pointwise equations
`k(iota_p(r)) = h(r)` and `k(var_p(x)) = v(x)`. The notation records only the
free-algebra universal property. It does not select monomials, coefficient
syntax, quotients, or a concrete positive-variable representation. The
reviewer equation `R[Empty] = R` is the current executable model.

No concrete fraction syntax, comparison equivalence, relative radical/power
interface, positive-variable polynomial representation, `Spec`, or
proposition-valued Zariski topology is implied. Those names remain reserved
for their separately gated layers.

No string-parser grammar is selected by this section. It records canonical
comments, examples, and direct TypeScript-AST intent only.

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
