# emdash v3.2 Canonical Surface Syntax

Date: 2026-06-05
Last reviewed: 2026-08-30

Status: current notation authority for v3.2 comments, examples, and future
surface-syntax/parser planning.

Critical variance qualification (2026-09-08): the current whole internal
`op : Cat → Cat` declaration is not a validated higher-categorical duality.
It participates in the checked empty-type derivation documented in the
[internal-op diagnostic](../../docs/TYPESCRIPT_EMDASH_INTERNAL_OP_VARIANCE_DIAGNOSTIC.md).
Future co/higher-duality notation is a repair proposal, not active syntax.
The [Sigma-Hom diagnostic](../../docs/TYPESCRIPT_EMDASH_SIGMA_HOM_VARIANCE_DIAGNOSTIC.md)
adds an independent constant-fibre direction defect. Its All/CoAll and
contravariant-totalization candidates are likewise not active surface syntax
or a claimed completed repair.

The [native-target polarity diagnostic](../../docs/TYPESCRIPT_EMDASH_HOMD_TARGET_POLARITY_DIAGNOSTIC.md)
records a further Empty route through the current Homd target section.
Its positive section over the opposite y-base supplies an invalid reverse
Hom action. Preserve native Hom notation/owners while correcting that
polarity and the coupled bases; the formulas below do not independently
certify the unrepaired encoding.

Notation in this report is immediately authoritative for mathematical comments
and examples. Most of it becomes parser syntax only after a separate
elaboration and grammar implementation. The bounded TypeScript categorical
binder profile identified below is already implemented; no notation here
should be read as an active Lambdapi parser extension.

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

## Implemented Bounded Categorical Binder Text

The root TypeScript text adapter implements one reviewed, first-order subset
of this mathematical surface. Intrinsic categorical variation is written on
the lambda, while the domain or family annotation is separate and may be
omitted when the expected type determines it:

```text
λ^f  x [: A]. body       ordinary functorial abstraction
λ^n  k [: K]. body       natural or indexed abstraction
λ^fd a [: E]. body       displayed-functorial abstraction
λ^nd a [: E]. body       displayed-natural abstraction
```

Whitespace application is neutral. The resolver uses inferred classifiers,
variation, and the expected result to select an existing object, arrow,
section, displayed, or higher-action owner; the parser does not attach an
owner-specific meaning to application punctuation.

Displayed contextual binders may group a canonical telescope:

```text
λ^fd (a : A; b : B, c : C; d : D). body
λ^nd (a : A; b : B, c : C; d : D). body
```

A semicolon advances one genuine dependency level. Commas group independent
siblings over the same preceding base. The implemented contextual compiler
accepts finite sequences of these canonical levels with finite sibling groups
for its reviewed displayed-functorial and displayed-natural constructions.
It also supports reviewed nested ordinary binders, qualified finite
Hom-category recursion, and finite rigid indexed-section chains. It does not
license arbitrary dependency or variance graphs, exchange across a dependency
edge, unrestricted mixed introduction/currying, or invented coherence.

The browser exposes twelve presets across the four modes, but the preset list
is evidence, not the grammar definition. Direct typed TypeScript construction
remains broader than the text adapter. Both routes lower to the same explicit
Core and generic checker, and unsupported routes fail with source-located
diagnostics.

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

For a higher arrow `alpha : h ==> k`, the capped precomposition action is
written by the same convention. Its stable kernel owner is
`hom_precomp_along_fapp1_fapp0(F,p,alpha)`. Proof-time it agrees with
`comp_prod_fapp1_fapp0(id_(F[p]),alpha)`, as exposed by
`hom_precomp_along_fapp1_comp_prod_path`; this is not a runtime rewrite.

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
its generic higher-component observation `tapp0_hom_fapp0`, the Cat-valued
`tdapp0_func` / `tdapp0_fapp0` specialization, and the generic displayed
internal-hom action.
Do not read these names as additional primitive type formers merely because
`Pi_cat` itself is a stable primitive category facade.

For `FF : Functord(E,D)` and `s : Pi_cat(E)`, the canonical postcomposition
surface is `section_postcomp_sec(FF,s)`.  It is the object action of
`Pi_func(K)` on `FF`, not an independent section-map semantics.  Its point
component is `FF[k](s[k])`; its base-arrow component is the existing
`fdapp1_int_hom_fapp0` action applied to `s[p]`, so a lax `FF` retains its
laxity cell rather than being silently treated as strict.

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

At the ordinary surface, write a higher component as
`Theta[Y] : eta[Y] -> eta'[Y]`; its stable kernel owner is
`tapp0_hom_fapp0(Y,Theta)`. Do not introduce a second Pi-specific or
Cat-specific spelling. When the target is `Cat_cat`, that owner computes to
the established displayed form `tdapp0_fapp0(Y,Theta)` while the whole hom
action remains `tdapp0_func(Y)`.

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
predicate on sieves. The direct sites module does not itself generate
coverhood or perform sheafification; the downstream generated-topology and
direct-cover constructions use the separate notation below. `Omega` remains
reserved and unbound.

For witness-rich generators and the constructed fixed-site Cat-valued
reflector, comments and examples may write:

```text
Gen_K(U,R)                 : retained presentations generating R on U
J_G                        : least Grothendieck topology accepting Gen
Gen ⊆ J_G                  : generator acceptance
J_G <= T                   : leastness against every accepting topology T

Match_P(R)                 : whole matching-family hom-category
Sect_P(U)                  : whole section hom-category
res_(P,R) : Sect_P(U) -> Match_P(R)
a_T(P)                     : direct cover completion of P
eta_P : P -> a_T(P)        : whole return/unit
glue                       : whole cover-indexed recursive glue
silent                     : glue o restriction = id on sections
a_T : Psh_Cat(K) ⇄ Sh_Cat(K,T) : i_T
a_T ⊣ i_T.
```

The literal generated-topology owners are `SieveGeneratorFamily`,
`GeneratedSieveCover`, `generated_groth_topology`,
`generated_groth_topology_accepts_generators`, and
`generated_groth_topology_least`. This is an impredicative/intersection
presentation of the least topology. It supplies no inductive derivation
syntax, cover normal form, or decision procedure.

The direct-cover owners include `DirectCoverMatching_cat`,
`DirectCoverSection_cat`, `DirectCoverSheafStructure`,
`DirectCoverCompletionPsh`, `direct_cover_completion_unit`,
`direct_cover_completion_glue_func`,
`direct_cover_sheafification_func`, and
`cat_valued_sheaf_include_psh_func`. The completion constructors are the
categorical-HIT boundary; locality, Hom universality, and the adjunction are
derived downstream. This notation is fixed-site and Cat-valued. It does not
name a CommRing-valued lift, left exactness, slice/base-change semantics, or a
constructed scheme structure sheaf.

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
R ×_CRing S              := comm_ring_product(R,S)
h ×_hom k                := comm_ring_product_map(h,k)
F2                        := f2_comm_ring

u : Unit_R(x)              := u : CommRingUnitEvidence(R,x)
u^-1                       := comm_ring_unit_inverse(R,x,u)
Loc_R(f)                   := CommRingLocalizationAt(R,f)
R[1/f]_ell                 := comm_ring_localization_target(R,f,ell)
iota_ell                   := comm_ring_localization_map(R,f,ell)
unit(1_R)                  := comm_ring_one_unit(R)
idLoc_R(f,u)               := comm_ring_unit_identity_localization(R,f,u)
idLoc_R(1_R)               := comm_ring_identity_localization_at_one(R)
zeroLoc_R                  := comm_ring_zero_localization(R)
eR                         := comm_ring_idempotent_image(R,e,e2)
idemLoc_R(e,e2)            := comm_ring_idempotent_image_localization(R,e,e2)
split_e(R,S)               := comm_ring_product_split_idempotent(R,S)
splitLoc(R,S)              := comm_ring_product_split_localization(R,S)
splitOpen(R,S)             := comm_ring_product_split_basic_open_arrow(R,S)
IterLoc_R(f,g)             := CommRingIteratedLocalizationAt(R,f,g)
CompLoc_R(f,g,m,p)         := CommRingIteratedLocalizationComparison(m,p)
OverlapAlong_R(f,g,m,p,c)  := comm_ring_iterated_localization_comparison_omega_equiv_along(c)
Overlap_R(f,g,m,p,c)       := comm_ring_iterated_localization_comparison_omega_equiv(c).

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

For a supplied path `e2 : e*_R e = e`, `eR` denotes the fixed-image ring
whose elements retain `(x,e*x=x)`, and `idemLoc_R(e,e2)` denotes its selected
localization package. Its structure-map observation is
`element(iota_e(x)) = e*x`. This notation does not assert that `e` is
nontrivial or that every localization is a fixed-image localization; a closed
nontrivial instance requires the separately gated product-ring consumer.

For `m : IterLoc_R(f,g)`, the first stage is a chosen localization at `f` and
the second is a chosen localization at the image of `g`; its stable composite
map sends `f*g` to a unit. For
`p : Loc_R(f*g)`, `CompLoc_R(f,g,m,p)` retains canonical forward and reverse
factors with pointwise triangles. `OverlapAlong_R(f,g,m,p,c)` explicitly
asserts that the forward factor has the reverse factor as both a left and
right inverse in `CommRing_cat`; `Overlap_R(f,g,m,p,c)` is its first-class
facade. Neither notation identifies the chosen targets or localization
packages judgmentally.

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
literal-arrow membership classifier. For a supplied topology `T`, comments
may write `Cover_T(D_O(s))` for
`CommRingPshInvertibilityCover(T,O,U,s)`. Given a chosen localization
`ell : Loc_{O(U)}(s)` and an actual member `m : D_O(s;f)`,
`factor_O(ell;f,m) : O(U)[1/s]_ell -> O(V)` denotes
`comm_ring_psh_localization_factor_map_at_member`; its canonical observation
is `factor_O(ell;f,m)(ell(x)) = f^*_O(x)`. Comments may write
`Elem(D_O(s))` for `CommRingPshInvertibilityElements_cat(O,U,s)` and
`factorCone_O(ell) : Const(O(U)[1/s]_ell) => O o dom` for
`comm_ring_psh_localization_factor_cone`; its literal component is
`factorCone_O(ell)[(V,f,m)] = factor_O(ell;f,m)`. This is a genuine internal
ordinary transformation, so generic `tapp1`—not an external square field—owns
naturality. For `g:W->V`, comments may still write the derived construction
audit
`factor_O(ell;f o g,g^*m) = g^*_O o factor_O(ell;f,m)`. None of this yet
identifies the cone as a limit or implies a descent theorem, sheaf, or locally
ringed structure.

The computational matching-family consumer may be written

```text
Matching_O(s) = Pi_(V,f,m in Elem(D_O(s))) Path_cat(|O(V)|)
restrict_ell : Path_cat(|O(U)[1/s]_ell|) -> Matching_O(s)
restrict_ell(x)[V,f,m] = factor_O(ell;f,m)(x).
```

The literal owners are `CommRingPshLocalizationMatching_cat`,
`comm_ring_psh_localization_matching_section`, and
`comm_ring_psh_localization_matching_restriction_func`. `Matching_O(s)` means
the internally coherent Pi section category, not a raw product of unrelated
elements. `restrict_ell` includes equality-path action through PathLift. Do
not add external naturality squares to this notation, and do not call it a
descent equivalence until a separately selected `glue_ell` and its laws have
been constructed from a real consumer.

The compatibility view of selected Cartier-locality glue may be written

```text
glue_ell : Matching_O(s) -> Path_cat(|O(U)[1/s]_ell|)
glue_ell(restrict_ell(x)) = x
factor_O(ell;f,m)(glue_ell(a)) = a[V,f,m].
```

The literal functor owner is
`comm_ring_psh_localization_glue_func`; its object action is
`comm_ring_psh_localization_glue`. The two observations are exposed by
`comm_ring_psh_localization_glue_restrict_path` and
`comm_ring_psh_localization_glue_at_member_path`. `glue_ell` is a complete
ordinary functor, so its action on arrows between matching families remains
with generic `fapp1`; the displayed equalities are retained paths, not new
rewrite rules or external naturality fields. This notation expresses selected
locality over the basic-open sieve `D_O(s)`, which need not cover `U`. It does
not by itself name ordinary sheaf descent, a generated topology, `Spec`, or a
scheme.

The stronger whole locality capability may be written

```text
LocLocal_O(s;ell)         : restrict_ell is a fixed-forward whole equivalence
glue^Loc_ell              : selected whole inverse functor
glue^Loc_ell o restrict_ell = id
restrict_ell o glue^Loc_ell = id.
```

The literal owners are `CommRingPshLocalizationLocality`,
`comm_ring_psh_localization_locality_glue_func`,
`comm_ring_psh_localization_locality_glue_restrict_functor_path`, and
`comm_ring_psh_localization_locality_restrict_glue_functor_path`. The
classifier is exactly `OmegaEquivAlong Cat_cat` with the existing restriction
functor fixed as its forward map. The transparent
`comm_ring_psh_localization_locality_legacy_glue` adapter derives the earlier
point/component package by evaluating the whole paths. Do not read
`LocLocal` as judgmental `DefIso`, ordinary covering-sieve descent, or a
stalk-local-ring condition; `D_O(s)` need not cover `U`.

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

For the downstream finite-presentation calculus, comments and examples may
write

```text
R^n                       : finite free vectors Vector_R(n)
Mat_R(r,c)                : column-oriented r-by-c matrices
A * v                     : matrix action R^c -> R^r
0_(r,c)                   : zero matrix
A o B                     : matrix composition
Agree_A(v,w;c,p)          : c with p : A*c = v-w
Syz_A(s)                  : equation A*s = 0
Chain0(A,B)               : equation A o B = 0.
```

The literal owners are `CommRingVector`, `CommRingMatrix`,
`comm_ring_matrix_apply`, `comm_ring_matrix_zero`,
`comm_ring_matrix_comp`, `CommRingPresentationAgreement`,
`CommRingMatrixSyzygy`, and `CommRingMatrixCompositeZero`. The first two are
transparent `FiniteFamily` aliases, and a matrix is a family of columns: the
shape `r,c` therefore means an action `R^c -> R^r`. `Agree`, `Syz`, and
`Chain0` retain explicit equality data; none is canonical syntax for equality
in a quotient module, an exact complex, or a formal Abelian category. There
are no matrix rewrite or unification rules beyond the inherited transparent
Nat/finite-family computation.

For fixed-ring presentation morphisms, comments and examples may write

```text
P = [R_P : R^r_P -> R^g_P]
F,W : P -> Q              : R_Q o W = F o R_P
F ~=_Q G via H            : R_Q o H = F-G
ChainSq(d,e;F0,F1)        : e o F1 = F0 o d.
```

The literal owners are `CommRingPresentation`,
`CommRingPresentationMorphism`,
`CommRingPresentationMorphismAgreement`, and `CommRingChainMapSquare`, with
the named presentation and morphism projections. The equation orientation is
deliberate: it matches the existing membership normal form `A*c = v`, so
assembling columnwise memberships needs no systematic equality symmetry.
`~=_Q` denotes retained coefficient data and a law, not kernel equality or a
path in a quotient module. `ChainSq` is computed from its four matrices; do
not describe it as a separately hand-written coherence field. This layer does
not introduce a formal category of presentations or a general complex.

For bounded free complexes and chain maps, comments and examples may write

```text
C = (C0 <-d1- C1 <-d2- ... <-dn- Cn)
d²_i                       : d_(i-1) o d_i = 0
F : C -> D                 : components F_i with e_i o F_i = F_(i-1) o d_i
Tail(d_i)                  : recursively typed higher terms and laws.
```

The literal owners are `CommRingFreeChainTail`,
`CommRingBoundedFreeComplex`, `CommRingFreeChainMapTail`, and
`CommRingBoundedFreeChainMap`, together with their nil/cons and selected
projection names. A zero-length complex retains one rank; a positive-length
complex stores `C0`, `C1`, `d1`, then the recursive tail, so there is no
spurious printed law `0 o d1 = 0`. Chain-map square fields are computed from
selected components and adopted as exact laws; they are not independent
hand-written coherence inputs. Do not describe these packages as complexes of
quotient modules, an Abelian category, exact resolutions, or homology.

For finite-free and Freyd presentation categories, comments and examples may
write

```text
Free_R                     : finite-free matrix category
[A : R^r -> R^g]           : presentation object
Agree(P,Q)                 : raw maps and target-factorization arrows
RawHom(P,Q)                : groupoidified agreement category
Hom_Freyd(P,Q)             : 0-truncated RawHom(P,Q)
El(P) = Hom_Freyd(R,P)     : representable element carrier.
PreAdd(Freyd_R)            : set-valued abelian Homs with bilinear composition
PreAdd(Free_R)             : the same structure on finite-free matrix Homs
Free_R^m ⊕ Free_R^n        : rank m+n with block-diagonal arrow action
π₁, π₂, ⟨f,g⟩             : canonical matrix projections/vertical pairing
0_Free                     : rank zero, both terminal and initial
Add(Free_R)                : selected finite-free additive-category structure
0_(P,Q), f+g, -f           : the selected Hom operations.
0_R                        : rank-zero presentation
P ⊕ Q                      : block-diagonal presentation direct sum
Add(Freyd_R)               : derived additive-category structure
ι_1 = <id,0>, ι_2 = <0,id> : biproduct injections
[f,g] = f o π_1 + g o π_2 : derived copairing.
Ann_α(T)                    : fibre of α o - over 0
WK(α) = (K,κ,factor)       : selected computational weak kernel
α o κ = 0                  : annihilation
κ o factor(τ,p) = τ        : selected nonunique factorization
Ker(α)                     : weak-kernel data plus contractible factor spaces
Coker(α)                   : dual coannihilator/contractible-colift data
lift_α(τ,p), colift_α(τ,p) : selected universal factors
PreAb(C)                   : additive C with selected kernels and cokernels
Mono(m), Epi(e)            : cancellation on incoming/outgoing Hom actions
Lift_m(τ), Colift_e(τ)    : selected normal factors of annihilated tests
Ab(C)                      : pre-Abelian C with normal mono/epi computation
Coim(f), Im(f)             : Coker(Ker(f)), Ker(Coker(f))
χ_f : Coim(f) -> Im(f)   : canonical comparison
f = i_f o χ_f o p_f       : selected image/coimage factorization
Bimor(h) -> Iso(h)          : normal-mono lift plus monic cancellation
WPB(α,γ)                   : WK([α,−γ]) with projected legs
lift_WPB(c)                : selected nonunique factor of an encoded cone
α o p = γ o q              : derived conventional WPB compatibility
cone(a,b,e)                : equalizing pair re-encoded as difference-zero
Coker_Freyd(f)             : target presentation with relation matrix [R_Q,F]
q_f                        : identity-data quotient projection
colift_f(h,H₀)             : colift consuming explicit zero agreement H₀
Ker_Freyd(f)               : presentation from two biased weak pullbacks
lift_f(τ,H₀)               : kernel lift using H₀ and τ's relation witness.
PreAb(Freyd_R)             : field-polynomial provider with all eight roles.
PreAbʷ(Freyd_R;W)          : formal witnessed surface from base capability W.
Ab(Freyd_R)                : operational provider with all normality/image roles.
Monoʷ(f), Liftʷ_f(τ,H₀) : formal kernel-zero witness and normal lift.
```

The literal owners are `CommRingFiniteFree_cat`,
`comm_ring_presentation_morphism_identity`,
`comm_ring_presentation_morphism_comp`,
`comm_ring_presentation_morphism_zero`,
`comm_ring_presentation_morphism_add`,
`comm_ring_presentation_agreement_refl`,
`comm_ring_presentation_agreement_trans`,
`comm_ring_freyd_comp`,
`comm_ring_freyd_add`,
`comm_ring_freyd_neg`,
`comm_ring_freyd_class_preadditive_evidence`,
`groupoidify_set_map_ext`,
`PreadditiveCategory`,
`comm_ring_finite_free_preadditive`,
`comm_ring_finite_free_binary_products`,
`comm_ring_finite_free_terminal_zero`,
`comm_ring_finite_free_cartesian`,
`comm_ring_finite_free_additive`,
`AdditiveCategory`,
`comm_ring_zero_presentation`,
`comm_ring_presentation_direct_sum`,
`comm_ring_freyd_direct_sum_func`,
`comm_ring_freyd_binary_products`,
`comm_ring_freyd_terminal_zero`,
`comm_ring_freyd_cartesian`,
`additive_inj1_fapp0`,
`additive_inj2_fapp0`,
`additive_copair_fapp0`,
`additive_biproduct_identity_path`,
`comm_ring_freyd_additive`,
`WeakKernelAnnihilator`,
`weak_kernel_annihilator_reindex_func`,
`ComputationalWeakKernel`,
`WeakKernel`,
`HasComputationalWeakKernels`,
`computational_weak_kernel_factor_fapp0`,
`computational_weak_kernel_factor_path`,
`KernelFactorSpace`,
`CokernelCoannihilator`,
`CokernelFactorSpace`,
`ComputationalKernel`,
`ComputationalCokernel`,
`computational_kernel_lift`,
`computational_kernel_lift_unique_path`,
`computational_cokernel_colift`,
`computational_cokernel_colift_unique_path`,
`HasComputationalKernels`,
`HasComputationalCokernels`,
`PreAbelianCategory`,
`IsMonic`,
`IsEpic`,
`NormalMonoLiftSpace`,
`NormalEpiColiftSpace`,
`HasLiftsAlongMonomorphisms`,
`HasColiftsAlongEpimorphisms`,
`lift_along_monomorphism`,
`colift_along_epimorphism`,
`ComputationalAbelianCategory`,
`computational_coimage`,
`computational_image`,
`computational_coimage_projection`,
`computational_image_embedding`,
`computational_coimage_annihilates_cone`,
`computational_image_coannihilates_cocone`,
`coimage_to_target`,
`coimage_image_comparison`,
`coimage_image_factorization_path`,
`AbelianCoimageImageComparisonBimorphism`,
`abelian_coimage_image_comparison_is_monic`,
`abelian_coimage_image_comparison_is_epic`,
`abelian_coimage_image_comparison_bimorphism`,
`AbelianSnakeTriple`,
`abelian_snake_gamma`,
`abelian_snake_alpha`,
`abelian_snake_fiber_product`,
`abelian_snake_pushout`,
`abelian_snake_p1_epic`,
`abelian_snake_q2_monic`,
`abelian_snake_p1_normal_epi_test`,
`abelian_snake_u`,
`abelian_snake_q2_normal_mono_test`,
`abelian_snake_connecting`,
`abelian_snake_ker_alpha_to_ker_beta`,
`abelian_snake_ker_beta_to_ker_gamma`,
`abelian_snake_coker_alpha_to_coker_beta`,
`abelian_snake_coker_beta_to_coker_gamma`,
`abelian_snake_connecting_after_kernel_map_zero_path`,
`abelian_snake_cokernel_map_after_connecting_zero_path`,
`ComputationalExactCoverWitness`,
`computational_exact_cover_intro`,
`HasComputationalExactCovers`,
`computational_exact_at_from_covers`,
`computational_exact_at_from_epic_factor_point`,
`abelian_canonical_kernel_exact`,
`abelian_canonical_cokernel_exact_explicit`,
`abelian_snake_exact_at_ker_beta`,
`abelian_snake_exact_at_ker_gamma`,
`AbelianSnakeSixTermResult`,
`abelian_snake_six_term_result`,
`abelian_snake_six_term_first_arrow`,
`abelian_snake_six_term_second_arrow`,
`abelian_snake_six_term_connecting_arrow`,
`abelian_snake_six_term_fourth_arrow`,
`abelian_snake_six_term_fifth_arrow`,
`AbelianSnakeConnectingResult`,
`abelian_snake_connecting_result`,
`CommRingFreydWitnessedSnakeConnecting`,
`comm_ring_freyd_snake_u_raw`,
`comm_ring_freyd_snake_u_reconstruction_path`,
`comm_ring_freyd_snake_connecting_raw`,
`comm_ring_freyd_snake_connecting_reconstruction_path`,
`comm_ring_freyd_witnessed_snake_connecting`,
`computational_abelian_bimorphism_inverse`,
`computational_abelian_bimorphism_iso`,
`computational_abelian_coimage_image_iso`,
`ComputationalChainPair`,
`ComputationalHomologyAt`,
`computational_homology_cycle_object`,
`computational_homology_cycle_embedding`,
`computational_homology_boundary`,
`computational_homology_object`,
`computational_homology_projection`,
`cokernel_composite_comparison`,
`cokernel_composite_comparison_path`,
`abelian_cokernel_composite_comparison_monic`,
`computational_homology_dnext_cokernel`,
`computational_homology_cokernel_inclusion`,
`abelian_homology_cokernel_inclusion_monic`,
`HomPostcompFactor`,
`HomPrecompFactor`,
`computational_kernel_map`,
`computational_kernel_maps_iso`,
`computational_cokernel_map`,
`computational_cokernel_maps_iso`,
`ComputationalChainPairMap`,
`computational_chain_pair_map_comp`,
`computational_homology_cycles_map`,
`computational_homology_map`,
`computational_homology_map_identity_path`,
`computational_homology_map_composition_path`,
`computational_homology_maps_iso`,
`chain_pair_map_snake_triple`,
`snake_row_gamma_comparison_path`,
`snake_row_alpha_comparison_path`,
`kernel_domain_comparison_iso`,
`cokernel_codomain_comparison_iso`,
`abelian_snake_row_source_cycle_iso`,
`abelian_snake_row_target_cokernel_iso`,
`normal_mono_test_from_epic_factor`,
`normal_mono_test_from_cycle_point`,
`snake_row_target_cokernel_from_projection_path`,
`snake_row_target_homology_normal_test`,
`snake_row_target_homology_factor`,
`hom_precomp_factor_paste_zero_path`,
`short_exact_row_chain_target_pair`,
`short_exact_row_chain_projection`,
`hom_postcomp_factor_trans`,
`hom_postcomp_factor_whisker`,
`hom_precomp_factor_postcomp_view`,
`kernel_domain_comparison_source_factor`,
`snake_row_source_cycle_factor`,
`snake_row_source_compared_boundary_factor`,
`annihilation_from_epic_factor`,
`covered_comparison_factor`,
`iso_evidence_to_is_monic`,
`abelian_snake_second_postcomp_path`,
`snake_row_source_compared_embedding_monic`,
`snake_row_source_second_comparison_path`,
`snake_row_source_upper_factor`,
`snake_row_source_boundary_covered_factor`,
`snake_row_source_boundary_zero_path`,
`monic_factor_prezero_path`,
`cokernel_descend_monic_factor`,
`short_exact_homology_connecting_factor`,
`short_exact_homology_connecting`,
`short_exact_homology_connecting_path`,
`ShortExactRowMap`,
`short_exact_row_map_snake_triple`,
`short_exact_row_source_cycle_iso`,
`short_exact_row_target_cokernel_iso`,
`weak_pullback_difference_fapp0`,
`ComputationalWeakPullback`,
`WeakPullbackCone`,
`computational_weak_pullback_proj1`,
`computational_weak_pullback_proj2`,
`computational_weak_pullback_lift`,
`HasComputationalWeakPullbacks`,
`computational_weak_pullback_compatibility_path`,
`weak_pullback_cone_intro`,
`comm_ring_freyd_cokernel_presentation`,
`comm_ring_freyd_cokernel_projection`,
`comm_ring_freyd_cokernel_annihilation_path`,
`comm_ring_freyd_cokernel_colift`,
`comm_ring_freyd_cokernel_reconstruction_path`,
`comm_ring_freyd_cokernel_uniqueness_path`,
`comm_ring_freyd_kernel_presentation`,
`comm_ring_freyd_kernel_embedding`,
`comm_ring_freyd_kernel_annihilation_path`,
`comm_ring_freyd_kernel_lift`,
`comm_ring_freyd_kernel_reconstruction_path`,
`comm_ring_freyd_kernel_uniqueness_path`,
`CommRingFreydWitnessedKernelUniversal`,
`CommRingFreydWitnessedCokernelUniversal`,
`HasCommRingFreydWitnessedKernels`,
`HasCommRingFreydWitnessedCokernels`,
`CommRingFreydWitnessedPreAbelian`,
`comm_ring_freyd_witnessed_preabelian`,
`CommRingFreydMonomorphismWitness`,
`CommRingFreydNormalMonoTestAgreement`,
`comm_ring_freyd_normal_mono_lift_raw`,
`comm_ring_freyd_normal_mono_reconstruction_path`,
`comm_ring_freyd_normal_mono_uniqueness_path`,
`CommRingFreydEpimorphismWitness`,
`CommRingFreydNormalEpiTestAgreement`,
`comm_ring_freyd_normal_epi_colift_raw`,
`comm_ring_freyd_normal_epi_reconstruction_path`,
`comm_ring_freyd_normal_epi_uniqueness_path`,
`CommRingFreydWitnessedNormalMonoUniversal`,
`CommRingFreydWitnessedNormalEpiUniversal`,
`CommRingFreydWitnessedAbelian`,
`comm_ring_freyd_witnessed_abelian`,
`CommRingFreydChainPair`,
`CommRingFreydWitnessedHomologyAt`,
`comm_ring_freyd_witnessed_homology_at`,
`comm_ring_freyd_homology_cycle_presentation`,
`comm_ring_freyd_homology_boundary_raw`,
`comm_ring_freyd_homology_presentation`,
`comm_ring_freyd_homology_projection_raw`,
`CommRingFreydExactnessAt`,
`CommRingFreydHomologyChainMap`,
`CommRingFreydHomologyCyclesZeroAgreement`,
`CommRingFreydHomologyBoundaryCompatibility`,
`CommRingFreydHomologyQuotientZeroAgreement`,
`CommRingFreydInducedHomologyData`,
`comm_ring_freyd_induced_homology_map`,
`CommRingFreydChainTail`,
`CommRingFreydBoundedComplex`,
`CommRingPresentationAgreementAtMatrices` (transparent literal-data alias),
`comm_ring_presentation_agreement_from_matrices`,
`comm_ring_freyd_chain_tail_first_homology`,
`CommRingFreydChainMapSquare` (transparent agreement alias),
`CommRingFreydChainMapTail`,
`CommRingFreydBoundedChainMap`,
`comm_ring_freyd_chain_map_first_homology`,
`CommRingFreydShortExactRow`,
`CommRingFreydShortExactTail`,
`CommRingFreydBoundedShortExactRows`,
`CommRingFreydBoundedShortExactSequence`,
`comm_ring_freyd_coimage_presentation`,
`comm_ring_freyd_image_presentation`,
`comm_ring_freyd_coimage_image_comparison_raw`,
`comm_ring_freyd_image_factorization_path`,
`CommRingFreydComparisonBimorphismWitness`,
`comm_ring_freyd_coimage_image_iso`,
`comm_ring_freyd_add_assoc_path`,
`comm_ring_freyd_comp_add_right_path`,
`comm_ring_freyd_comp_add_left_path`,
`comm_ring_freyd_preadditive`,
`comm_ring_freyd_identity_usability_path`,
`comm_ring_freyd_comp_usability_path`,
`CommRingPresentationAgreement_cat`, `CommRingFreydRawHomGroupoid`,
`CommRingFreydHomSet`, `CommRingFreydPresentation_cat`, and
`CommRingFreydElement`. Generic category identity/composition remain runtime
owners and compare with rigid finite-free matrix observations only at proof
time. `RawHom` retains agreement/syzygy paths; `Hom_Freyd` is its ordinary set
truncation. `El(P)` is a representable specialization rather than an
independent quotient-element type. `PreAdd(Freyd_R)` is a checked preadditive
package on arbitrary quotient points. `Add(Freyd_R)` additionally selects the
whole sum functor and terminal zero, then derives coproduct and zero-object
observations from products and preadditivity; it is not a parallel coproduct
grammar. `WK(α)` selects lifts without uniqueness; test-object action is
retained by the named reindexing functor, while naturality of the selected
factor choice is not asserted. Do not identify a weak kernel with a kernel or
strengthen the Freyd category merely because the generic `Ker`, `Coker`, and
`PreAb` classifiers now exist. `PreAbʷ(Freyd_R;W)` is the separately named
witness-enriched formal package: tests and competitors carry raw
zero/reconstruction agreements, from which the checked quotient paths follow.
It must not be printed as the stronger closed `PreAb(Freyd_R)` unless an
effective quotient-path decoder is actually supplied. The field-polynomial
runtime provider has all eight pre-Abelian roles, and `Ab(Freyd_R)` adds the
complete normality/image family plus a computed inverse to `χ_f`. `Ab(C)` is
the generic package of a selected pre-Abelian structure with contractible
normal lift/colift spaces. The concrete formal Freyd value remains witnessed
rather than closed until quotient effectiveness is supplied. None of these
Abelian surfaces should be printed as exactness or homology data.

For the separately promoted direct big-affine topology, comments and examples
may write

```text
AffBig(R)                 : conventional big affine slice over Spec(R)
Chart_R(h)                : literal chart h : R -> S
ChartLoc_R(h;ell)         : whole arrow Spec(S[1/f]_ell) -> Chart_R(h)
BigZarGen(R)              : witness-rich finite chart-cover generators
BigZar(R)                 : least topology on AffBig(R) accepting BigZarGen(R)
family ⊆ Q => covers(Q)   : selected-family inclusion in BigZar(R)
BigZar(R) <= T            : leastness against an accepting topology T
```

The literal owners are `AffineSpecBigSlice_cat`, `affine_spec_chart`,
`affine_spec_chart_localization_arrow`,
`AffineSpecBigZariskiGenerators`, `affine_spec_big_zariski_topology`,
`affine_spec_big_zariski_topology_covers`, and
`affine_spec_big_zariski_topology_least`. `ChartLoc` is a whole internal
slice arrow and coordinate restriction along it computes to the selected
whole localization map. `BigZar` names the promoted big-site topology; it
does not identify that site with the small poset of opens, construct a
reflector/sheafification, or denote a complete scheme.

For a global reflective CommRinged object with a selected cover, comments may
write

```text
RingedCover_K(A;X,R,c)    : reflective ringed object X with covering sieve R
Chart(P;V,f,m)            : selected member (V,f) of the covering sieve
f^*R                      : pulled-back cover on V
Cover(f^*R)               : coverhood derived by Grothendieck stability
```

The literal owners are `ReflectiveCommRingedSpaceCover`,
`reflective_comm_ringed_space_cover_intro`,
`ReflectiveCommRingedSpaceCoverChart`, and
`reflective_comm_ringed_space_cover_chart_pullback_covers`. A `Chart` here is
only an actual member of the selected covering sieve; the notation does not
assert affineness. Members of `f^*R` are the global-first overlap candidates,
so no independent overlap or cocycle field is implied. The package also does
not imply finiteness, locally-ringed support, a scheme, or effective gluing.

For whole restriction to a selected chart, comments may write

```text
pi_U : K/U -> K                    = slice_domain_func(U)
F^*O                               = comm_ring_psh_pullback(F,O)
O_X|_U                             = O_X o Op(pi_U)
SuppliedRingedSlice(A,U;B,i)       = B with i : include(O_B) ~=def O_A|_U
```

Here `~=_def` abbreviates the literal whole `DefIso` owner; it is not an
objectwise family of ring isomorphisms. At a literal slice arrow `(V,f)`,
`pi_U(V,f)` computes to `V`, while an arbitrary encoded-Sigma object remains
at the whole-functor evaluation endpoint rather than assuming package eta.
`SuppliedRingedSlice` visibly supplies the slice topology and reflector: the
notation does not assert that either was induced from the ambient site and
does not imply affineness, locally-ringed support, or a scheme.

For whole sheaf restriction and comparison along a selected basis functor,
comments may write

```text
i^*                            : whole presheaf restriction along i:A->B
i^*(P) = P o Op(i)             : proof-time path, not a runtime fold
SheafRestr(i;P)                : selected whole sheaf restriction
include_A o SheafRestr(i;P)
  ~= include_B o i^*           : whole IsoEvidence comparison
SheafBasis(i;Q)                : OmegaEquivAlong Cat_cat on SheafRestr(i;Q)
```

The literal owners are `psh_restriction_func`,
`psh_restriction_value_path`, `psh_restriction_value_iso`,
`SuppliedSheafRestrictionAlong`,
`supplied_sheaf_restriction_underlying_iso`, and
`SuppliedSheafBasisEquivalenceAlong`. The comparison sign denotes the whole
`IsoEvidence`; it is not a family of objectwise commutative squares. The
displayed value equation is the proof-time bridge from generic
precomposition's stable cut normal form to direct functor composition; it
does not install a runtime rewrite.
`SheafBasis` does not assert equivalence of `A` and `B`, construct a topology
or reflector, or retain a locally-exactness proof or Beck--Chevalley mate.

For a supplied affine reflective structure-sheaf presentation, comments and
examples may write

```text
AffStruct(R;P)            : supplied reflective structure-sheaf presentation
O_P                       : included whole CommRing-valued structure presheaf
i_P : O_P ~=def O_coord   : whole DefIso to the computing coordinate presheaf
i_P[U]                    : component of either whole comparison at U
```

The literal owners are `AffineStructureSheafPresentation`,
`affine_structure_sheaf_underlying_psh`,
`affine_structure_sheaf_coordinate_defiso`,
`affine_structure_sheaf_to_coordinate_at`, and
`affine_structure_sheaf_from_coordinate_at`. Here `~=def` is only display
notation for the existing `DefIso` classifier; it does not denote equality of
functor objects or invoke univalence. The two `i_P[U]` directions are
components projected from whole transformations, so their action and
naturality remain at the generic owners. This notation supplies neither a
construction of sheafification nor localization locality, a stalk-local-ring
condition, a small-site comparison, or a complete scheme.

For supplied whole locality of the computing affine coordinate presheaf,
comments and examples may write

```text
AffCoordLocal(R;L)        : whole coordinate-locality capability
L[U,s,ell]                : fixed-forward LocLocal at one selected localization
```

The literal owners are `AffineCoordinateLocalizationLocality` and
`affine_coordinate_localization_locality_at`. At a literal chart `R -> S`,
the value endpoint computes to `S` and the selected target to `S[1/s]_ell`.
`affine_coordinate_localization_legacy_glue` is only the compatibility view
for earlier component-glue consumers. This notation assumes the whole
locality capability; it does not construct one, choose localizations globally,
assert that `D(s)` covers the chart, impose stalk locality, identify the small
site, or package a scheme.

For the thin assumption-explicit affine-scheme presentation, comments and
examples may write

```text
AffScheme(R;P,L)          : affine presentation with structure P and locality L
O_AffScheme               : included whole structure presheaf
O_AffScheme ~= O_coord    : whole computational DefIso
L[U,s,ell]                : selected whole localization locality
```

The literal owners are `AffineSchemePresentation`, `affine_scheme_intro`,
`affine_scheme_underlying_psh`, `affine_scheme_coordinate_defiso`, and
`affine_scheme_locality_at`. `P` and `L` remain explicit supplied
capabilities. The base ring owns the generated topology and selected atlases
remain consumer data; do not read the notation as a second site, duplicated
cover/overlap structure, constructed sheafification/locality, general
non-affine gluing, small-site comparison, or a stalk-local-ring theorem.

For realization of an ambient chart by an existing affine presentation,
comments may write

```text
i : AffBig(R) -> K/U             : selected whole affine-basis functor
O_A|_i                           : ambient structure presheaf restricted by i
AffBasis(A,U,P,R,X,i;Q,b)        : sheaf-basis semantics Q and whole bridge b
b : O_A|_i ~=def O_X             : whole computational DefIso
O_A|_i ~=def O_coord(R)          : derived whole coordinate DefIso
```

The literal owners are `ambient_affine_basis_psh`,
`AffineBasisRealizationAlong`, `affine_basis_realization_semantics`,
`affine_basis_realization_bridge`, and
`affine_basis_realization_coordinate_defiso`. The sheaf-basis field and
presheaf bridge are whole internal objects; the notation supplies neither
component coherence nor a raw category equivalence. It does not construct
the basis, transport generic glue, define a general scheme, or assert a
stalk-local-ring condition.

For a global covering sieve generated by two selected affine charts, comments
may write

```text
q = c_b o h                    : factorization through chart b : Bool
Gen2_R(c0,c1)                  : c0 and c1 generate the retained sieve R
AffChart(P,c;Q)                : whole affine realization of selected chart c
BinAffCover(P;c0,c1,g,Q0,Q1)   : binary global-first affine-cover presentation
```

The literal owners are `CoverChartFactorization`,
`BinarySelectedCoverGeneration`, `AffineCoverChartRealization`, and
`BinaryAffineCoverPresentation`. Generation is witness-rich: for every member
`q` of `R`, it computes a Boolean branch, factor arrow, and triangle. Since
`c0` and `c1` are themselves retained members, the two branches generate
exactly `R`. Only the two selected generators carry affine realizations;
arbitrary refinements in the sieve are not asserted affine. Each realization
retains one whole `AffineBasisRealizationAlong`, so restriction action and
naturality remain at existing owners. `BinAffCover` supplies neither a
point-free locally-ringed certificate, open-immersion classifier, semantic
scheme, nor atlas-first gluing constructor.

For the derived CS-07 consumer, comments may write

```text
refine_Q(q) = (b,h,triangle)   : q factors through selected generator c_b
chart_Q(q)                     : the selected affine generator
realization_Q(q)               : its retained whole affine realization
coord_Q(q)                     : its coordinate ring
```

The literal owners are `binary_affine_cover_refinement_at`,
`binary_affine_cover_refinement_chart`,
`binary_affine_cover_refinement_realization`, and
`binary_affine_cover_refinement_ring`. The latter observations are derived
from the Boolean side; they are not fields of another refinement record.
`realization_Q(q)` keeps its canonical branch-indexed type for an open side,
and the notation does not claim that `q` itself is affine.

For topology-local local-ring computation, comments may write

```text
⊥_U                              : literal empty sieve on U
LocalBranch_O(s,t;q)              : selected Boolean unit branch at q
LocalCover_T,O(s,t)               : covering sieve with branches
LocalRing_T(O)                    : local nontriviality and unit splitting
WholeLocal(P)                     : local presentation on the supplied K/X
BinLocAffCover(P;L,Q)             : locally-ringed binary affine atlas
BinRelScheme_K(P;L,Q)             : total site-relative scheme presentation
```

The literal owners are `empty_sieve`, `CommRingPshLocalUnitBranch`,
`CommRingPshLocalUnitCover`, `CommRingPshTopologyLocalRingPresentation`,
`ReflectiveCommRingedWholeObjectLocalPresentation`, and
`BinaryLocallyRingedAffineCoverPresentation`. The final notation's literal
owner is `BinarySiteRelativeSchemePresentation`. An invertible sum returns an
actual covering sieve and an executable Boolean branch at every member; no raw
sieve join or propositional truncation is implied. `WholeLocal` uses the whole
computing ambient restriction on `K/X`, while the supplied reflective slice
retains sheaf semantics and its whole `DefIso`. `BinRelScheme` totals the
already-global cover with its dependent certificate. The supplied site
determines admissible chart geometry, and no overlap, transition, cocycle, or
gluing input is added. The notation does not claim a classical Zariski or
Zeuner compact-open comparison or a representation-independent `Scheme_cat`.

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

No concrete fraction syntax, relative radical/power interface,
positive-variable polynomial representation, small-site Zariski topology, or
complete scheme is implied. The direct big-affine topology is named only by
the `BigZar` block above; its sheaf and scheme consumers remain separately
gated.

This algebraic section adds no further parser tokens. It records canonical
comments, examples, and direct TypeScript-AST intent; the implemented textual
subset remains the bounded categorical binder profile stated above.

## Semisimplicial And Simplex Notation

The active semisimplicial index uses *vertex counts*. In comments, write

```text
alpha : p hook-> n              injective monotone face code
SemiDeltaPlus                   augmented injective simplex category
[n]_dir                         directed geometric n-simplex
Delta[n]                        representable semisimplicial n-simplex
X_n                             n-simplices of X
```

with literal owners

```text
alpha : FaceCode(p,n)
SemiDeltaPlus_cat
DirectedSimplex_cat(n)
StandardSimplex(succ n)
semisimplicial_grpd_level(X,succ n).
```

The successor in the last two lines is essential. An internal index object
`m` has `m` vertices: zero is the augmentation object, one is the ordinary
point, two the edge, and three the two-simplex. Thus the conventional
dimension notation `Delta[n]` is `StandardSimplex(succ n)`, not
`StandardSimplex(n)`. The ASCII spelling `hook->` is comment notation only;
no new parser token is active.

Face-code constructors and composition may be displayed as

```text
skip(alpha)                     : p hook-> succ n
keep(alpha)                     : succ p hook-> succ n
idFace(n)                       : n hook-> n
beta o_face alpha               : p hook-> r.
```

Their kernel owners are `face_skip`, `face_keep`, `face_identity`, and
`face_comp beta alpha`. Face-code composition, not an external family of
simplicial equations, owns the coface identities. For nonempty source and
target ordinals, write

```text
realize(alpha) : [p] -> [n]
```

for `face_realize_func alpha`. Its raw computation is
`realize(skip alpha) = inl o realize(alpha)` and
`realize(keep alpha) = join_map(realize(alpha),id_1)`. This is an
ambient-functor-valued decoder, not yet a whole functor from
`SemiDeltaPlus_cat` to `Cat_cat` and not generic strict-profile evidence:
identity and composition comparisons remain scoped join-uniqueness work.

For the recursive target-dependent reading, use

```text
Triangle_E((x,u),(y,v)) = (p,alpha)
Tetrahedron_E            = (kappa,lambda).
```

The literal classifiers are `DependentTriangle_catd` and
`DependentTriangle_cat`; the constructor names are `dependent_triangle` and
`dependent_tetrahedron`. `dependent_triangle_map(FF)` is the first hom action
of `Sigma(FF)`, and `dependent_tetrahedron_map(FF)` is its next hom action.
Do not expand these into a record of external face equations. On a visible
`(kappa,lambda)`, the dependent output remains the native
`fdapp1_int_hom_fapp0` projection.

For the two-sided cross-corner reading, comments may write

```text
Square_E(u,v)[a,b]
  = Hom_{E[x1][y2]}(E[x1][b](u),E[a^op][y2](v))

Square_C(u,v)[a,b]
  = Hom_{Hom_C(x1,y2)}(b o u,v o a)

SquareTotal_E(u,v) = (a,(b,alpha)).
```

The literal owners are `homdc_`, `homdc_fibre`, `homdc_square_func`,
`homdc_square_fibre`, `homdc_square_cat`, and `homdc_square_obj`. The variance
is part of the notation: `a` is covariant and `b` is contravariant. The whole
line observations are `homdc_square_top_func`,
`homdc_square_bottom_sec`, `homdc_square_left_func`, and
`homdc_square_right_func`. An arrow `theta` between two square objects has
ordinary source/target faces and the four observations
`homdc_cube_{top,bottom,left,right}_face`. In the current fixed-boundary total,
left and right compute to identities and bottom remains a dependent section
action. Do not read this notation as a fully varying `homdc_int`, a flat
cubical record, degeneracies/connections, Kan filling, or arbitrary-dimensional
cubical syntax. Fully varying notation belongs to the later derived owner:

```text
EdgeFamily_E[x1] = Sigma(x2:K2), E[x1][x2]
homdc_int(E)      = homd_int(id_(Op_catd(EdgeFamily_E)))
Total□(E)         = Op(Sigma(x1:K1^op),Op(EdgeFamily_E[x1])).
```

Its canonical projection order is target edge, source edge, then `a`; the
remaining Sigma-Hom object is `(b,alpha)`. The literal owners are
`homdc_edge_catd`, `homdc_op_edge_catd`, `homdc_int`, `homdc_at`, and
`homdc_total_cat`. `EdgeFamily_E` is prose for `homdc_edge_catd(E)` and must
not be confused with the unrelated older symbol `Edge_catd_func`.

For the first groupoidal source coherence, comments may write

```text
assoc_rep(f,g,h) : (h o g) o f = h o (g o f)
assoc_J(f,g,h)   : (h o g) o f = h o (g o f).
```

The literal owners are `path_represented_assoc` and
`path_assoc_J_forward`. The former is projected from the whole compositor of
`Rep_catd_func`; `represented_assoc_transfd` owns the whole displayed cell,
`represented_assoc_cell` is its point component, and
`represented_assoc_higher_func` retains the next action. The latter is path
symmetry applied to `path_cat_assoc_J`. Do not write either as a definitional
replacement for `comp_assoc`, and do not identify their proof terms. Formal
represented endpoints remain `represented_assoc_lhs` and
`represented_assoc_rhs`; their readable bracketing comparisons are
propositional. For arbitrary directed `Z`, the transported raw-endpoint cell
is `represented_assoc_readable_cell`; it is not a second primitive
associator.

For the constructor-visible dependent source, comments may write

```text
left3(p01,p12,p23)
right3(p01,p12,p23)
assoc3(p01,p12,p23) = (kappa,lambda)
map(FF,assoc3) = (kappa,fdapp1_int_hom_fapp0(FF,lambda)).
```

The literal owners are `dependent_spine3_left_triangle`,
`dependent_spine3_right_triangle`, `dependent_spine3_assoc_cell`,
`dependent_spine3_assoc_tetrahedron`, and `dependent_spine3_assoc_map`. The
`assoc_cell` is the represented directed cell; `assoc_tetrahedron` exposes its
native dependent-pair view. Do not infer a Sigma eta or a complete
dimension-three boundary package from this notation.

For the complete flagged finite tower, comments may write

```text
S0(C)
S1(C,x0)
S2(C,x0,e01)
S3(C,x0,e01,t012)
S_n(F) : S_n(C,flag) -> S_n(D,F(flag)).
```

The literal classifiers are `DependentSimplex0_cat` through
`DependentSimplex3_cat`; the whole actions are `dependent_simplex0_map`
through `dependent_simplex3_map`. Constructor notation uses
`dependent_simplex1`, `dependent_simplex2`, `dependent_simplex3`, and the
fully visible helpers `dependent_simplex2_visible` and
`dependent_simplex3_visible`. The final 123-face/filler split goes through
`dependent_simplex3_readable_cell` or its constructor-visible specialization,
not through a rewrite of the stable represented source. The `flag` arguments
are semantically essential: this notation does not denote one global category
of all simplices.

Dimension four continues with `DependentSimplex4_cat` and
`dependent_simplex4_map`. Write

```text
S4(C,x0,e01,t012,s0123)
readable4(alpha01234) = (face0234,residual1234).
```

The literal first split is `dependent_simplex4_visible_readable_cell`.
`sigma_Fst` reads face 0234; `sigma_Snd` is the retained frame containing face
1234 and the top filler. Do not write a second projection of that residual
unless its recursively readable lower endpoint views have been supplied.

For intrinsic flag codes write

```text
code0(C)
step(c,x) : Code(C,n+1,PathOut(decode(c),x))
decode(code4(C,x0,e01,t012,s0123)) = S4(C,x0,e01,t012,s0123)
view(c;formal,readable,p).
```

The literal owners are `DependentSimplexCode`,
`dependent_simplex_code_step`, `dependent_simplex_code_decode_cat`, and
`DependentSimplexEndpointView`. `DependentSimplexFaceRef(p,n)` is definitionally
the existing `FaceCode(succ p,succ n)`. Do not describe the code as syntax for
arbitrary categories: its decoded category is an intrinsic index.

For mapped decoding write

```text
mapCode(F,c) = (c',F_c)
mapView(F,c,v).
```

The literal owners are `dependent_simplex_code_map`, whose two Sigma
projections are `dependent_simplex_code_map_target` and
`dependent_simplex_code_map_func`, and
`dependent_simplex_endpoint_view_map`. At zero `F_c` is `F`; at successor it
is `pathout_map_func` of the recursively decoded map. Do not elaborate this
notation into a second recursive map record.

For nonempty face action write

```text
face(alpha,c) = (c_alpha,d_alpha)
d_alpha : decode(c) -> decode(c_alpha).
```

The literal owners are `dependent_simplex_face`,
`dependent_simplex_face_target`, and `dependent_simplex_face_func`; `alpha`
has the already-existing type `DependentSimplexFaceRef(p,n)`, definitionally
`FaceCode(succ p,succ n)`. Skip means a constant face of the fixed flag,
`keep(skip ...)` means recursive target projection, and `keep(keep ...)` means
`pathout_map_func`. Do not write a separate list of coface equations or imply
that direct and sequential opaque whole functors are judgmentally equal.

For the low-dimensional ordinal comparison write

```text
observe0(H)                 H[*]
observe1(H)                 (H[0],H[1],H[01])
triangleFiller(H)           the canonical dependent 2-cell
observe2(H).
```

The literal owners are `ordinal_simplex0_observe_func`,
`ordinal_dependent_simplex1_observe`,
`OrdinalDependentSimplex2CanonicalFiller`, and
`ordinal_dependent_simplex2_canonical_filler`, and
`ordinal_dependent_simplex2_observe_canonical`. The explicit owner
`ordinal_dependent_simplex2_observe(H,alpha)` remains available when a caller
supplies a noncanonical filler. Shared ordinal triangle vertices compute
through the generic join-eliminator point betas. Do not call the object-level
observation package a category or write an unqualified ordinal/dependent
equivalence.

For the constructed ordinal tetrahedron write

```text
tetrahedronSource             the one native Delta[3] source
observe3(H)                   map(H,tetrahedronSource)
faces(observe3(H))            (012,013,023,123)
top(observe3(H))              the dependent cell over face 023.
```

The literal whole owners are `ordinal_dependent_simplex3_source`,
`ordinal_dependent_simplex3_map`, and
`ordinal_dependent_simplex3_observation`. Their readable face projections are
`ordinal_dependent_simplex3_face012`, `...face013`, `...face023`, and
`...face123`; the final projections are
`ordinal_dependent_simplex3_theta_base` and
`ordinal_dependent_simplex3_top_component`. The construction is an object of
the existing flagged `DependentSimplex3_cat`, not a flat four-face record.
Do not print the typed represented-source reframe as a definitional endpoint
rewrite, and do not claim an unqualified all-dimensional equivalence.

For the constructed ordinal four-simplex write

```text
fourSimplexSource             the one native Delta[4] source
observe4(H)                   map(H,fourSimplexSource)
faces(observe4(H))            (0123,0124,0134,0234,1234)
top(observe4(H))              the recursive dependent component.
```

The literal owners are `ordinal_dependent_simplex4_source`,
`ordinal_dependent_simplex4_map`, and
`ordinal_dependent_simplex4_observation`. The five whole code-selected faces
are `ordinal_dependent_simplex4_face0123` through `...face1234`; the native
recursive projections include `...s0123`, `...s0124`, `...theta0134`,
`...readable_cell`, and `...top_component`. The successor is obtained by
iterating `pathout_transf_lift` over
`ordinal_join_pathout_transf`; do not print it as an opaque four-cell or
identify native and code-selected face presentations judgmentally.

For the variable-dimensional canonical source write

```text
source(n)                     canonical intrinsic Delta[n] source
observe(n,H)                  map the source under H : Delta[n] -> C
face(n,H,alpha)               selected nonempty FaceCode observation
successor(source(n))          source(n+1).
```

The literal owners are `OrdinalDependentSimplexSource`,
`ordinal_dependent_simplex_source`,
`ordinal_dependent_simplex_observation`, and
`ordinal_dependent_simplex_face`. The computational stage is
`OrdinalJoinLiftStage`; its canonical cell/action owners are
`ordinal_dependent_simplex_successor_cell` and
`ordinal_dependent_simplex_lift_next_action`. Describe the successor as
`step(d,F[s])` with object `(G[s],epsilon[s])`. Do not describe it as
generated source text, a primitive opaque filler, or a whole
`Functor(Delta[n],C)` equivalence.

For terminal-right normalization in a recursive join successor, write

```text
normalize_p : Hom(g o F[p],h) -> Hom(nativeSource[p],h)
Normalize   : nativeAction ->_K expectedAction.
```

The literal owners are `prof_terminal_expected_retained_source_transf` and
`prof_terminal_explicit_normalization_funcd`; their point projections are
`prof_terminal_retained_expected_source_fapp0_path` and
`prof_terminal_fibre_normalization_func`. The direction of `normalize_p` is
part of the normal-lax interface. Do not print it as an equality rewrite or
invert the section compositor. At dimension three the forward compositor is
followed by the 012-filler action; their composite is the formal top cell,
while the two factors remain separately observable.

When literal dependent-triangle endpoints are required, write

```text
visibleSource(p) = g o F[p]
reflag_p : Hom(expectedSource(p),h) -> Hom(visibleSource(p),h)
VisibleNormalize : expectedAction ->_K visibleAction.
```

The literal owners are `prof_terminal_visible_source_func`,
`prof_terminal_expected_visible_source_fapp0_path`, and
`prof_terminal_expected_visible_funcd`; the fibre projection is
`prof_terminal_expected_visible_fibre_func`. The expected and visible whole
source functors are not equal by definition. Use the displayed reflag when
higher action matters rather than applying an isolated endpoint path.

For the join higher-constructor computation write

```text
crossBeta(d) : observedCross(extend(d)) = primitiveCross(d)
crossCell(d) : observedCross(extend(d)) -> primitiveCross(d)
generatorBeta(F,G) : sourceCross(F[*],G[*]) = joinMap(F,G)[generator].
```

The literal owners are `join_map_extend_cross_beta` and its equality-induced
`join_map_extend_cross_cell`; shaped equality is
`join_map_extend_cross_shaped_beta`. Component and base-arrow action remain at
`tdapp0_fapp0` and `tdapp1_int_cell`. The literal whole generator owner is
`join_map_generator_beta`; its point projection is
`join_map_generator_at_beta`. Do not print either propositional beta as a
runtime reduction or replace the whole source filler by a handwritten
triangle equation.

For groupoid-valued diagrams write

```text
SemiSimplicial(Grpd)
X[alpha] : X_n -> X_p
PathRealize(X)
```

for `SemiSimplicialGrpd_cat`, `semisimplicial_grpd_face_map X alpha`, and
`semisimplicial_grpd_realize X`. The bracket expression is contravariant in
`alpha`. Its whole and higher action remain at the ordinary
functor/transformation owners; the notation must not be elaborated into a
record containing separate naturality proofs.

The selected two-dimensional sieve notation is

```text
boundary(Delta[2])              partial Delta[2]
horn(k,Delta[2])                Lambda^k[2],  k = 0,1,2
restrict(kind,X)                maps Delta[2] -> X to partial maps.
```

The literal owners are `simplex2_boundary_sieve`,
`simplex2_horn_zero_sieve`, `simplex2_horn_one_sieve`,
`simplex2_horn_two_sieve`, and `simplex2_partial_restrict`. These names refer
to ordinary sieves on the three-vertex object and their existing whole
extensions into `StandardSimplex(succ(succ(succ zero)))`. They do not denote
generic-dimensional boundary/horn families. The algebraic path-groupoid
fillers may be described as `fill_0`, `fill_1`, and `fill_2`, but their literal
owners remain the `path_nerve2_fill_*` functions; no all-dimensional `Kan`
notation is active.

For categorical decalage, write

```text
shift(m)      = succ m
shift(alpha)  = keep(alpha)
Dec(X)_n      = X_(n+1)
Cone_X(x;n)   = {sigma : X_n | finalVertex(sigma) = x}.
```

The corresponding owners are `semi_delta_shift_func`,
`semisimplicial_decalage`, and `SemisimplicialConeFibre X x n`. The last
kernel index follows the cardinal convention described above. Its base map is
the whole `semisimplicial_cone_base_func`; however, the collection of fibres
is not yet assembled into one displayed semisimplicial object. Accordingly,
there is no canonical surface notation identifying `Cone_X(x;-)` with a
`homd_` family, and no coinductive `SST` declaration syntax is active.

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

## Selected Kernel And Cokernel Presentations

The declaration-backed whole operations use the existing arrow-diagram
category and zero-arrow embeddings:

```text
J(A) = (A → t),       J ⊣ K
I(A) = (t → A),       Q ⊣ I
κ : K ⇒ domain
π : codomain ⇒ Q.
```

`KernelPresentation(S,T,W)` and `CokernelPresentation(S,Tᵒᵖ,W)` refer to
coherent presentations of the supplied original selection family W. They
are not automatic introductions from arbitrary old capabilities. Read the
following as proof-time usability, not runtime arrow rewrites:

```text
K[d] ≐ selected kernel object      κ[d] ≐ selected kernel embedding
Q[d] ≐ selected cokernel object    π[d] ≐ selected cokernel projection
K[η] ≐ existing kernel map         Q[η] ≐ existing cokernel map.
```

For ordinary targets, `one_cat_postcomp_adjunction` expresses
(F∘−)⊣(G∘−) at the existing postcomposition functors.
`one_cat_adjunction_family_transpose_func` and its `untranspose` companion
act on whole transformations. Their types retain native postcomposition
endpoints for inverse computation. The lift and ordinary functor-category
profile are explicit structural primitives, with whole unit/counit rules.
The optional `one_cat_adjunction_family_views` module now exposes
`one_cat_adjunction_family_transpose_agrees` and its inverse-direction
companion for the existing whole whiskering formulas. Their
`*_reconstruction` paths recover the entire input through the same native
inverse. These are equality witnesses using guarded proof-time
comparisons; raw-formula reconstruction is not a new judgmental cut.
The additional mixed-associativity view retains the native `(G∘F)∗X`
owner while comparing with `G∘(F∗X)` on the same data.

`diagram_family_evaluation_func(i)` evaluates whole diagram families and
their transformations at i. Its object observation is the existing
`diagram_family_at_func`; its map observation is
`sym_transf_tapp0_transf`. The ordinary composition path is derived from
generic functoriality. The normalizer now computes identity transformations
at both whole walking-arrow endpoints, with the old point route retained.
`one_cat_cokernel_unit_source_transf_path` and
`one_cat_kernel_counit_target_transf_path` identify the original normalized
input's whole observations with the universal diagram differential.

`one_cat_coimage_image_comparison` is the defined whole a:Coim⇒Im.
Its input is the internally constructed `one_cat_coimage_image_mate_input`;
the original native cokernel mate and inverse cuts own its computation.
Whole source-to-image annihilation and input-target recovery are derived
paths. `one_cat_coimage_image_factorization_value(b)` abbreviates the whole
observation E₀(unmate_P(E₁(transpose_Q(b)))); its `*_path` reconstructs ∂
and `*_unique` proves b=a from that whole condition. These names do not
introduce an opaque comparison, pointwise cone syntax or new factorization
runtime cut. The function in b is not separately packaged as an internal
functor. `OneCatAdjunctionNormality` is existing OmegaEquivAlong on this
actual a. `one_cat_coimage_image_inverse_transf` selects its supplied left
inverse; `one_cat_coimage_image_iso_evidence` derives both ordinary inverse
laws with literal a as forward arrow. Family restriction uses generic action
through `one_cat_adjunction_normality_family`, with the same inverse and
native precomposition endpoints. `OneCatAbelianAdjunctionStructure` stores
original P/Q and that fixed-a normality over an existing AdditiveCategory;
it does not infer normality or introduce a second equivalence grammar.

`one_cat_cokernel_family_input(D,Y,u,z)` forms the whole D⇒I∘Y at the
original D, where z is one whole u∘∂D=0 cell. Its introduced-diagram case
is `one_cat_cokernel_family_introduced_input`; canonical Coim⇒Im now shares
that constructor. `one_cat_cokernel_family_descent` applies the original
native mate to give Q∘D⇒Y, with `*_reconstruction` and `*_unique` as whole
path observations. The native inverse returns the full coherent input.
These names introduce no pointwise cone syntax or new runtime inverse law.

The corresponding kernel owners have the `kernel_presentation_*` and
`cokernel_presentation_*` prefixes. Defined reflexivity paths package these
agreements. Formal whole action remains the runtime owner for generic
functoriality and adjunction rectangles, and further Hom action is retained.
The semantic map receives an actual diagram transformation η and derives
its old factor-space input through the existing strict component-naturality
comparison. No new manual square syntax is introduced.

Whole `adjunction_transpose_func` and `adjunction_untranspose_func` are
evaluated views of the existing Hom-prof comparison; their inverses compute
both as whole functors and on points. The `kernel_presentation_lift_func`
and `cokernel_presentation_colift_func` specializations meet the original
selected factor operations through proof-time comparisons and defined paths.

For an already coherent family, the readable whole construction is:

```text
A:B→C,  D:B→Arr(C),  h:J∘A⇒D
cycles = K∘D
β = K(h)∘η_A : A⇒cycles
H = Q∘Arr(β) : B→C.
```

`homology_family_func` is a transparent definition. Its selected object/map
comparison paths do not change its runtime owner or reselect universals.
The native ordinary-target specialization uses `ZeroArrowCone_cat(C,T)`,
the existing represented homdc comma with objects (A,d,h:J(A)⇒d). Its whole
first/diagram projections and the profile-qualified
`zero_arrow_cone_universal_transf` supply the universal family above.
`zero_arrow_cone_homology_func` then defines global H on that native source.
No new strict category or manually supplied square/prism field is involved.

The profile is the existing `IsNCat (cat_succ cat_zero) C`, not mere sethood
of Obj(C). For the Freyd model, `freyd_zero_cone_universal_transf(R)` fills
that derived evidence internally. This is a model specialization, not a
generic truncation operator. The concrete retained-selection CAS replay and
the complete comparison with the older homology-map recipe remain further
implementation obligations.

For an original chain pair (e,d), the native entry is now the transparent
`chain_pair_zero_cone`: retain the original boundary beta and take its
inverse kernel mate to get (A,d,unmate(beta)). The raw Freyd specialization
is `freyd_raw_chain_zero_cone`; it consumes the existing raw agreement.
`freyd_zero_cone_homology_func` supplies the whole model-facing H, so its
application to that entry is ordinary functor application. Canonical
structural data are filled inside the alias; coherent P/Q capabilities stay
explicit. The separate `*_path` observations are compatibility theorems,
not additional runtime operations or caller-supplied square fields.

The ordinary-target realization is `one_cat_arrow_diagram_func(C1)` from
the existing native LaxArrow(C) to Arr(C). Its tautological transformation's
component is the stored arrow. Read point compatibility as proof-time:
`Arr(eta)[x] ≐ walking-arrow(eta[x])`; it is not a new runtime normalization.
`chain_pair_outgoing_diagram_map_func` realizes the old lower-square Hom
data with uncapped action, while `chain_pair_outgoing_diagram_map` is its
transparent point view. The auxiliary `zero_cone_map_from_lifts` derives
the native comparison cell from compatible mates. The complete
`chain_pair_zero_cone_map` now derives that compatibility from the old
chain-map data; `chain_pair_zero_cone_map_func` retains its whole fixed-pair
action. `freyd_raw_chain_zero_cone_map` specializes this to the original raw
Freyd agreements and fills the OneCat profile. Its three observations are
the original next/middle/prev quotient classes. Coherent model realization
in the actual CAS replay is still an explicit further boundary.

`FreydHomologyModel(R)` now packages the existing supplied coherent inputs;
`freyd_homology_model_func(M)` is their original whole H. The readable
`freyd_homology_model_object(M,e,d,chain)` is ordinary application of that H
to the original raw entry. Its first native point observation records an
explicit model-interpretation agreement with the retained presentation,
without an automatic model constructor, global rewrite or new equality axiom.
This is external trusted adoption in the working document, not `eq_refl`
or a claim that Lambdapi itself runs the CAS.

`freyd_homology_model_map(M,chainS,chainT,m)` is ordinary H action on the
original raw map. `freyd_homology_model_arrow_observation` and
`freyd_raw_arrow_observation` package complete arrows in the existing
Obj(LaxArrow(Freyd(R))) carrier. Read their adopted comparison as an explicit
model interpretation of both endpoints AND the arrow, not as a runtime
endpoint cast or a new normalization law. The matrix usability constructor
`comm_ring_freyd_chain_map_from_matrices` returns the existing chain-map
notion, preserving the seven morphisms and two original coefficient
witnesses; its equations use semantic matrix products, not an opaque map.

The bounded model consumer uses degree/role and interior-position labels
for those same observations. It preserves the actual replay and previous
adoption source; labels do not create new mathematical owners. Its induced
map observations cover inclusions/projections degreewise. Connecting arrows
keep their separate homology-owned meaning and are not written as H of an
ordinary degree-preserving chain map.

`freyd_homology_model_connecting_observation` observes that separate operation
at the two original model H inputs. It additionally takes supplied model
normality and model-side short-exact-row evidence; a raw chain-zero proof is
not a substitute. The bounded consumer explicitly interprets these rows and
the retained complete connecting arrows as trusted presentation semantics.
Its displayed arrow order is a view of the same observations and proofs, not
a new kernel operation or generic finite exactness theorem. Without supplied
normality, the point/map-only consumer reports that connecting interpretation
was not requested.

The direct record-level `homology_record_connecting` is read as
delta:Hs→Ht. Its retained factor reads delta∘qs = u, and its covered
reconstruction reads delta∘qs∘e = qt∘v. Here qs and qt are the actual
record projections, not newly selected quotients. Instantiating the records
at the whole-H interface gives literal H source/target observations.
These reconstruction equations are proved paths, not new runtime rewrites.
The whole counterpart is `homology_window_connecting_transf`, an actual
transformation between the two whole H-column functors. Its component
computes to the direct operation through `homology_window_connecting_at`;
generic transfor action retains naturality and higher action. The point
notation alone does not assert a generic bounded exactness theorem.

`chain_pair_homology_action_func` is the whole fixed-pair view of H action
after native map introduction; `chain_pair_homology_action` is its point
observation. It is still written H(m), not a second induced-map notation.
The whole structural transformations give κy∘Z(m) = middle(m)∘κx and
H(m)∘qx = qy∘Z(m). The three `homology_whole_window_*_pair` observations
are the overlapping pairs of H(A)→H(B)→H(C)→H(A')→H(B').
Their zero laws are proved paths, not added runtime rewrites. Do not print
this chain window as an already proved exact sequence.

`homology_whole_window_first_exact` is exactness at H(B), the first
interior of this same window. It inhabits the existing
`ComputationalExactAt` predicate, equivalently epicity of the actual
boundary lift used by that predicate. It does not assert exactness at
H(C) or H(A'), or denote a new homology object.

`homology_whole_window_second_exact` is the separate exactness witness
at H(C), immediately before delta, for the existing second window pair.
It uses that pair's actual selected boundary in `ComputationalExactAt`.
`homology_whole_window_third_exact` separately proves exactness at H(A'),
after delta. `HomologyWholeExactWindow` packages these three witnesses over
the existing window pairs, without duplicating its H objects or arrows.

Read `FiniteArrowTail(C,Q,n,A,B,f)` as n additional arrows after f:A→B,
with Q-data on each adjacent pair. Thus there are n+2 objects, n+1 arrows
and n annotated interior positions. `ComputationalExactArrowTail` chooses
the original zero/exactness annotation. Its constructor requires that
evidence; it does not prove exactness merely by forming a sequence.
The append operation shares one boundary arrow and is finite-data
concatenation, not ordinary categorical composition. In the checked
two-window consumer it retains the common H(i) and all original H inputs.
This notation does not by itself assert the full zero-padded bounded theorem
or replace the whole-complex/H/delta operations.

`HomologyRowTriple` is a sliding state of three whole row families, two
actual transformations and the middle-chain-zero datum. `HomologyRowSpan`
adds a finite number of coherent extensions; its remainder is indexed by
the shifted original state. These are not independently chosen windows
joined by object-equality proofs. `homology_whole_window_extend` prepends
the existing three exact pairs to an exact continuation at the same H(i).

`HomologyRowFieldSpan(n,R0,R1,R2,f,g,z)` keeps those original inputs
directly as indices. Its case operation eliminates one extension constructor.
`homology_row_field_span_exact_tail` iterates the same window construction;
n extensions give 3n annotated interiors, 3n+1 arrows and 3n+2 objects.
This is the finite assembler, not a new H or the completed zero-padded
long exact sequence. `finite_arrow_tail_arrows` observes complete arrows;
`finite_arrow_tail_init` removes the last arrow and its final annotation.
The packed-state generator comparison remains an unqualified convenience
interface, not an installed usability equation.

`homology_whole_middle_zero` states id_H = 0 from id_B = 0 for the original
middle term B. Its terminal-middle specialization uses the original
terminality evidence. Neither notation means H ↪ a newly selected zero
object, or a global runtime rule id_H ↪ 0.

## Whole Displayed Laxity Notation

For `FF : E ⊢_K D` and `p : x ->^K y`, write the active whole laxity
transformation as:

```text
laxity(FF,p) : D[p] o FF[x] => FF[y] o E[p]
laxity(FF,p)[u] = cell(FF,p,u).
```

The kernel owners are `functord_laxity_transf(FF,p)` and
`fdapp1_int_cell(FF,p,u)`. This notation reads a whole transformation already
extracted from `fdapp1_int_transfd(FF)` through a self-comma identity section;
it does not introduce a second square or law. For `h : u -> u'` in `E[x]`,
the expression `laxity(FF,p)[h]` means the retained generic `tapp1` action of
that same transformation.

For the selected structural instances, the readable notation is:

```text
action_p(Eval)(eta,q)        → eta[q]
action_p(⟨FF,GG⟩)(alpha)    → ⟨action_p(FF)(alpha), action_p(GG)(alpha)⟩
action_p(id)(alpha)          → alpha
cell(Eval,p,(U,i))           → id_(E[p](U[i])).
```

Here `action_p` denotes the existing `fdapp1_int_hom_func` and its
`fdapp1_int_hom_fapp0` projection, not a new surface constructor. Whole mixed
evaluation and further Hom action are retained. Ordinary and opposite
presentations compute at their actual typed Hom endpoints; neither notation
means reversing an arbitrary cell. Only leading-Eval composites are opened.
Constant-section/terminal specializations have whole, point and cell joins;
there is no general section eta syntax or law. The
[dedicated reviewer](../examples/displayed_evaluation.lp) checks both
projection orders and generic composition orientation. These computations do
not yet define a whole zero-complex category or homology functor.

For an ordinary `epsilon : F => G`, the two active fixed-object internal
actions may be written

```text
action(epsilon,X,-) : Hom_A(X,-) => Hom_B(F[X],G[-])
action(epsilon,-,Y) : Hom_A(-,Y) => Hom_B(F[-],G[Y]).
```

Their kernel owners are `tapp1_at_transf(epsilon,X)` and
`tapp1_con_at_transf(epsilon,Y)`. Both project at `(X,Y)` to
`tapp1_func(epsilon,X,Y)`; the second is a stable contravariant owner whose
opposite presentation compares proof-time, not a second square. Its internal
and identity-specialized companions are stable as well; whole projections
and identity specialization compute in that ladder. The active whole
ordinary notation is

```text
post_laxity(epsilon,X,g) : G[g] o epsilon[-] ==> epsilon[g o -]
pre_laxity(epsilon,Y,h)  : epsilon[-] o F[h] ==> epsilon[- o h]
```

with kernel owners `tapp1_post_laxity_transf` and
`tapp1_pre_laxity_transf`. Their components at `f` and `q` are
`tapp1_post_laxity_cell` and `tapp1_pre_laxity_cell`; these are projections of
the same `functord_laxity_transf`, not separately postulated squares. For the
identity transfor, write

```text
compositor(F,g,f) : F[g] o F[f] ==> F[g o f]
```

whose transparent kernel owner is `fapp1_compositor`.

For a raw map `h : A -> B` between groupoids and paths `p : x = y`,
`q : y = z`, the Path-realized specialization may be written

```text
compositor_Path(h,q,p)
  : ap(h,p) . ap(h,q) = ap(h,p . q)

compositor_Path(h,q,p)^-1
  : ap(h,p . q) = ap(h,p) . ap(h,q).
```

The public owners are `path_map_compositor_readable` and
`path_map_compositor_readable_inverse`. Here `.` denotes the ordered
`eq_trans` used by the displayed formula. Internally the generic compositor
retains `functord_transport_*_func` / represented-postcomposition endpoints;
`path_map_compositor_lhs_agrees_readable` and
`path_map_compositor_rhs_agrees_readable` compare them propositionally. This
notation must not be read as a runtime rewrite to `eq_trans`.

The whole owner `path_map_compositor_transf(h,x,q)` remains natural in `p`.
Its retained off-diagonal action is
`path_map_compositor_higher_func(h,q,p0,p1)`; the notation asserts no complete
simplicial or all-coherence interface.

## Profiled Gray Right-Closure Notation

Write semantic strictness and its package as

```text
IsStrictFunctor(F)
StrictFunctor(A,B) := Sigma F : Functor(A,B), IsStrictFunctor(F)
underlying(S) : Functor(A,B),
```

with kernel owners `IsStrictFunctor`, `StrictFunctor`,
`strict_functor_intro`, `strict_functor_underlying`, and
`strict_functor_evidence`. The stable ambient view is `strict_functor(S)`.
At a constructor-visible package its point and hom action computes to the
underlying carrier; an opaque package retains the stable head. Strictness
constrains the existing `fapp1_compositor` through `IsStrictCell`; it neither
supplies another compositor nor currently forces a literal identity normal
form. The global/profile-local strict-cut migration is separate.

The selected strict-object/lax-arrow internal Hom is written

```text
GrayHom_lax(A,B).
```

Its kernel head is the identically named `GrayHom_lax`; its whole inclusion
is `grayhom_lax_include_func`. There is no active `GrayHom_oplax`
compatibility spelling. The authoritative orientation is the displayed cell

```text
G[g] o epsilon[-]  ==>  epsilon[g o -],
```

called lax in this project. When external literature uses the opposite naming
convention, show the cell direction rather than silently changing the head.

For the selected right closure, mathematical prose may write

```text
A tensor_R B

curry_R   : GrayHom_lax(A tensor_R B,C)
              -> GrayHom_lax(A,GrayHom_lax(B,C))
uncurry_R : GrayHom_lax(A,GrayHom_lax(B,C))
              -> GrayHom_lax(A tensor_R B,C).
```

The kernel owners are `GrayTensor_R`, `gray_curry_R_func`, and
`gray_uncurry_R_func`; their whole beta/eta package is
`gray_right_closure_omega`. `tensor_R` is expository notation, not a declared
string-parser token.

Write the walking interval as `I = Join(1,1)`. For its tensor square, write

```text
interchanger_I :
  inner_target[g] o outer_source
    ==> outer_target o inner_source[g].
```

The kernel owner `gray_interchanger` is the identity component of
`gray_interchanger_transf`, itself the specialized
`tapp1_post_laxity_transf`; `gray_interchanger_next_func` retains the next
whole action. The readable raw composites do not license a new pointwise
endpoint rewrite: the formal component endpoints remain the stable
`functord_transport_*_func` owners.

After exchanging coordinate roles, write the iterable transformation graph as:

```text
Graph(ε) : B → Arr□(C)
Graph(ε)[y] = ε_y

Graph(ε)[g]
  : G[g] o ε_x  ==>  ε_y o F[g].
```

The kernel owners are `gray_transf_graph_func`,
`gray_transf_graph_obj_path`, `gray_transf_graph_source_side_path`,
`gray_transf_graph_target_side_path`, `gray_transf_graph_cell`, and
`gray_transf_graph_cell_projection_path`. The object and capped-arrow betas
compute to the displayed graph; `gray_transf_standard_cell` and
`gray_transf_standard_square` name its literal filler and arrow. The filler is
`tapp1_post_laxity_cell(epsilon,g,id_x)`, not a separately postulated
naturality square. Generic `fapp1_func` retains the next action.

At an identity arrow, this intended graph beta overlaps the historical global
strict-functor identity cut. Preserve the graph beta and record the warning;
the global cut is the temporary approximation that must later migrate to its
strict profile. `IsPseudoFunctor(F)` already names transparent coherent
evidence over an existing carrier but does not install or suppress runtime
carrier rules. Its fixed-forward fields are
`OmegaEquivAlong(readable_pseudo_post_cell(F,g,f))`; the readable endpoint
ladder compensates for the temporary global strict cut and must not be printed
as a noncollapse theorem. The selected strict graph package pairs
`gray_transf_graph_func` with supplied `IsStrictFunctor` evidence; its
underlying-carrier and evidence projections compute. It adds no graph-head
compositor or identity-filler rule. Do not print this as a new graph unit: the
readable `lax_square(id,id,id)` versus canonical nested-Sigma identity remains
a generic presentation comparison. No carrier path or `eq_ap`/`eq_apd`
observer is needed.

For positive right-Gray cubes and their native observation, write

```text
GrayCube⁺_R(0)       = I
GrayCube⁺_R(n+1)     = I tensor_R GrayCube⁺_R(n)

decode□_R(C,n)
  : StrictFunctor(GrayCube⁺_R(n),C) → Cub_{n+1}(C).
```

These denote `GrayCubePos_R` and `gray_cube_observation`. The index is the
predecessor of geometric dimension. Successor decoding uses right curry, the
walking generator, the strict graph package, recursion in `Arr□(C)`, and
`cubical_level_shift_path`. This notation describes one profiled right-closed
slice and must not be advertised as a tensor unit, alternate-bracketing
coherence, inverse decoder, mapping-category equivalence, or full Crans--Gray
monoidal structure.

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

The TypeScript mixed-telescope surface is:

```text
k : K;
a : A[k];
b : B[(k,a)], c : C[(k,a)];
d : D[((k,a),(b,c))].
```

It is constructed through `displayedDependentContextLambda` and the generic
contextual compiler. The middle sibling block is inferred from the typed
family bases; explicit `apply` and `fibrePair` nodes remain valid direct-
TypeScript syntax. The bounded text adapter implements the corresponding
semicolon/comma punctuation and finite canonical dependency levels for the
reviewed displayed modes. Neither surface licenses arbitrary dependency or
variance graphs.

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
one nor denotes the retired mixed-curry experiment. The nested binders
themselves remain the fundamental introduction form, and the generic
`fapp`/`tapp` calculus owns the resulting object, arrow, base-arrow, and higher
action.

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

## WalkingEnd--Circle Universality Notation

For the selected concrete groupoidification theorem, write

```text
Res_G : Hom(Circle,G) -> Functor(W,Path(G))
Ext_G : Functor(W,Path(G)) -> Hom(Circle,G)

Ext_G o Res_G = id
Res_G o Ext_G = id
Res_G : Hom(Circle,G) ~= Functor(W,Path(G)).
```

The kernel owners are `walking_circle_restrict_func`,
`walking_circle_extend_func`, and
`walking_circle_groupoidification_hom_omega`. The displayed equivalence is a
fixed-forward `OmegaEquivAlong Cat_cat`, not a claim that the two category
expressions are judgmentally equal. Base and generator readings use the
named `*_base_path` and `*_loop_pathover` projections; do not replace a
dependent generator `PathOver` by an untyped homogeneous equality.

For `e : A ~= A`, the universe-valued consumer may be written

```text
Mon_e : Circle -> Grpd
Mon_e(base) = A
ap(Mon_e,loop) = ua(e)
transport(Mon_e,loop,a) = e(a).
```

Here `ua(e)` denotes the selected `grpd_equiv_path(e)`, and the checked owners
are `walking_circle_monodromy_circle_family`,
`walking_circle_monodromy_loop_path`, and
`walking_circle_monodromy_transport_path`. Circle point beta and the dependent
constructor computation

```text
apd(circle_ind(D,b,ell),loop) == ell
```

are judgmental in the current kernel. The ordinary `ap(Mon_e,loop)` equation
and the displayed monodromy comparisons remain propositional. This monodromy
statement does not depend on the later generic `Groupoidify` construction.

## WalkingArrow--Interval Universality Notation

For the non-endomorphism free-inversion consumer, distinguish the directed
walking arrow from its groupoidal interval target:

```text
I_dir              = WalkingArrow
i0 i1 : I_grp
seg : i0 = i1
u_I : I_dir -> Path(I_grp).
```

The dependent interval computation is judgmental:

```text
apd(interval_ind(D,b0,b1,ell),seg) == ell.
```

Point computation at `i0` and `i1` is judgmental as well. The ordinary
constant-family equation `ap(interval_rec(...),seg) = ell` and the generator
equation for `u_I` remain propositional; use `=` rather than `==` for those
readings.

For every `G : Grpd`, write the checked whole mapping equivalence as

```text
Res^I_G : Hom(I_grp,G) -> Functor(I_dir,Path(G))
Ext^I_G : Functor(I_dir,Path(G)) -> Hom(I_grp,G)

Ext^I_G o Res^I_G = id
Res^I_G o Ext^I_G = id
Res^I_G : Hom(I_grp,G) ~= Functor(I_dir,Path(G)).
```

The kernel owners are `walking_interval_restrict_func`,
`walking_interval_extend_func`, and
`walking_interval_groupoidification_hom_omega`. Endpoint, segment, and source
generator readings use the named `*_i0_path`, `*_i1_path`, `*_seg_pathover`,
and `*_generator_pathover` projections. Do not flatten a dependent segment or
generator `PathOver` into a homogeneous equality. `I_grp` is expository
notation for `Interval_grpd`, not an implemented parser token. This theorem
handles the single WalkingArrow source and is recovered by the generic
construction below.

## Monad And Comonad Computation Notation

For `T : A -> A` and `M : Monad(T)`, comments and reviewer examples may write

```text
eta_M : id_A => T
mu_M  : T o T => T
f*    : T[X] -> T[Y]              for f : X -> T[Y]
KCut_M(g,f) = g* o f.
```

The structural and extension owners are `unit_monad_transf`,
`mult_monad_transf`, and
`kleisli_extend_func`/`kleisli_extend_fapp0`. Ordinary ambient composition owns
the selected runtime reductions:

```text
g* o eta^c(f) -> g o f
g* o f*       -> (g* o f)*
(eta_M[X])*   -> id_T[X]
mu_M[X]       -> (id_T[X])*.
```

`KCut_M(g,f)` may still be written for readability, but
`kleisli_cut_func`/`kleisli_cut_fapp0` are transparent notation for
`g* o f`, not primitive runtime owners or an explicit Kleisli category.

For `C : Comonad(D)`, write

```text
epsilon_C : D => id_A
delta_C   : D => D o D
Delta(f)  : D[X] -> D[Y]          for f : D[X] -> Y
CoKCut_C(f2,f1) = f2 o Delta(f1).
```

`Comonad_A(D)` is transparently `Monad_(A^op)(D^op)`. The computational owners
are stable `counit_comonad_transf`, `comult_comonad_transf`, and point
`cokleisli_extend_fapp0`, because these are the heads consumed by triangular
runtime rules. Whole `cokleisli_extend_func` is transparently the
endpoint-swapped `kleisli_extend_func` on the opposite category; generic
projection then folds to the stable point. This is a narrow computational
mirror, not a duplicated full comonad theory. Ambient composition computes

```text
epsilon^a(f2) o Delta(f1) -> f2 o f1
Delta(f2) o Delta(f1)     -> Delta(f2 o Delta(f1)).
```

`cokleisli_cut_func`/`cokleisli_cut_fapp0` are transparent notation. Whole
standard observations are stable and compute through `Op_transf` folds. No
opaque `_op_path`, `_fapp0_path`, or `_antecedent_path` comparison is part of
the selected surface.

For `J : Adjunction(F,G)`, use `adjunction_monad(J)` on `G o F` and
`adjunction_comonad(J)` on `F o G`; their multiplication and comultiplication
are `G epsilon F` and `F eta G`, respectively. This notation does not denote a
free-monad syntax or claim a global decision procedure. In computational
Monad terms, spell the unit through the canonical
`unit_monad_transf(adjunction_monad(J))`; the adjunction unit is its proof-time
usability endpoint and does not replace that head at runtime. Whole
`mult_monad_transf(adjunction_monad(J))` is semantic notation and computes to
the transparent `G epsilon F` construction. Its component-first triangular
endpoint and whole-first semantic component are joined by the derived
`adjunction_monad_mult_component_path`; this path does not alter runtime
preference. TypeScript declaration automation is deferred.

## Triangular Binary-Product And Terminal-Object Notation

After selecting

```text
P  : C × C -> C
BP : BinaryProducts(C,P),
```

write

```text
A ×_P B := P(A,B).
```

The shorter `A × B` is permitted when one `P` and `BP` are fixed and no
product-category ambiguity is present. `Product_cat(A,B)` continues to mean
the category of pairs and exists independently of `BinaryProducts(C,P)`; do
not use the same unqualified phrase for those two constructions.

The whole projections and their point components are written

```text
κ₁ : P => pr₁
κ₂ : P => pr₂

κ₁^{A,B} : A ×_P B -> A
κ₂^{A,B} : A ×_P B -> B.
```

The owners are `binary_products_proj1_transf`,
`binary_products_proj2_transf`, `binary_products_proj1_fapp0`, and
`binary_products_proj2_fapp0`. Their full off-diagonal `tapp1` projections are
the antecedential operations

```text
K₁ᵃ_A(f) := f o κ₁
K₂ᵃ_A(f) := f o κ₂.
```

Pairing is written

```text
<f,g> : X -> A ×_P B.
```

It is the point observation of the whole represented-family pairing transfor
`binary_products_pair_transf`; its component
`binary_products_pair_func(BP,X,A,B)` is a whole functor between Hom
categories and retains another hom action. Do not describe pairing as a capped
binary function when that retained action matters.

The selected runtime equations are

```text
h o K₁ᵃ(f)       == K₁ᵃ(h o f)
h o K₂ᵃ(f)       == K₂ᵃ(h o f)

K₁ᵃ(h) o <f,g>  == h o f
K₂ᵃ(h) o <f,g>  == h o g

<f,g> o k        == <f o k,g o k>
<κ₁,κ₂>          == id

<K₁ᵃ(f),K₁ᵃ(g)> == K₁ᵃ(<f,g>)
<K₂ᵃ(f),K₂ᵃ(g)> == K₂ᵃ(<f,g>).
```

Here `==` denotes runtime computation at the stable `K₁ᵃ`, `K₂ᵃ`, pairing,
or ambient-composition owner. The generic action of the selected whole product
functor remains a different runtime presentation. Write its agreement with
the triangular map as

```text
P[(f,g)] =proof-time <K₁ᵃ(f),K₂ᵃ(g)>.
```

The owner is the single direct map `unif_rule`; the typed first-class view is
`binary_products_map_path`. Do not print two projection-specific unifiers.
Their equality paths derive from this map path by ordinary congruence and the
runtime projection betas.

The transparent whole unpair functor may be written

```text
unpair(h) := (κ₁ o h,κ₂ o h).
```

Pointwise pair/unpair composites have internal equality paths. Do not promote
those paths to equality of whole functors or to `OmegaEquivAlong` unless a
separate whole assembly owner is supplied.

For a selected terminal object

```text
T : TerminalObject(C,t),
```

write its whole canonical-arrow transfor and components as

```text
!   : id_C => Const_t
!_A : A -> t.
```

The canonical terminal cut is runtime:

```text
!_B o h == !_A.
```

For arbitrary `f : A -> t`, write

```text
f = !_A
!_t = id_t
```

only as internal equality paths derived from
`terminal_hom_contr_at_arrow`. They are not runtime folds and not proof-time
bare-variable unifiers. In particular, do not print `!_t == id_t`.

The thin combined capability is

```text
CartesianCategory(C,P,t)
  := BinaryProducts(C,P) × TerminalObject(C,t).
```

It introduces no additional computational notation. The weighted comparison
surface remains assumption-explicit:

```text
W : BinaryProductsWeightedComp(BP).
```

Such a `W` carries a supplied strict weighted comparison and paths identifying
its two projections with `κ₁` and `κ₂`. It is not automatically constructed
from the triangular beta/eta equations, and it does not replace the direct
runtime calculus.

None of this notation asserts products or a terminal object for every
category, free Cartesian syntax, or a global commuting decision procedure.
It is canonical mathematical/comment/example notation only; the bounded
TypeScript text grammar does not acquire these forms automatically.

## Pullback And Slice Base-Change Notation

For `f : X → Y`, use distinct indexed slice notation

```text
Σ_f : C/X → C/Y
f^* : C/Y → C/X
Σ_f ⊣ f^*.
```

The owners are `slice_sigma_func`, `slice_base_change_func`, and
`slice_base_change_adjunction`. Write `f^*`, not the monadic postfix `f*`,
when ambiguity is possible. `SliceSigma_catd(C)` is the always-existing whole
covariant family; `SliceBaseChange_catd(PB)` is the selected whole
contravariant family supplied by `PB : PullbackStructure(C)`. Both have exact
fibre `C/X = Slice_cat(C,X)`.

For an arbitrary total object `q : Σ_k E[k]`, the kernel observations
`sigma_obj_base(q)` and `sigma_obj_fibre(q)` may be printed as `q.1` and
`q.2`. The generic arrow constructor `sigma_arrow_intro` may be written
`(p,α) : q → r`; its base and fibre observations compute. This is generic
Sigma syntax, not a pullback cone record. Composition in an opposite slice
reverses before using the forward Sigma constructor law.

For `g : Z → Y`, comments may write

```text
P        = dom(f^*(g))
π₁       : P → X
π₂       : P → Z
X ←π₁— P —π₂→ Z
```

for `pullback_domain`, `pullback_fst`, and `pullback_snd`. The directed square
owner is `pullback_square_readable_cell`, projected from the counit slice
arrow; it is not stored as a field. Do not print it as a strict equality in an
arbitrary emdash category.

For `a : Obj(C/X)`, use

```text
Cone_f(a,g) = Hom_{C/Y}(Σ_f(a),g)
lift_f      : Cone_f(a,g) → Hom_{C/X}(a,f^*(g))
cone_f      : Hom_{C/X}(a,f^*(g)) → Cone_f(a,g).
```

The whole owners are `pullback_cone_cat`, `pullback_lift_func`, and
`pullback_cone_of_lift_func`. Their selected point computations are

```text
cone_f(lift_f(h)) == h
lift_f(cone_f(k)) == k.
```

Here `==` is justified by the active stable adjunction-triangle rules. A
cone variable `h` is already an object of
`Hom_{C/Y}(Σ_f(a),g)`, hence already an internal commuting triangle. Do not
introduce or print a pullback-specific tuple `(a,b,α)` that stores a square;
the removed `pullback_cone_constructor` is not part of the surface.

For the full Došen `(ac)` calculus, write the off-diagonal actions of the
same whole unit and counit as

```text
γᶜ_f(k) := tapp1(unit_f,k)
φᵃ_f(h) := tapp1(counit_f,h).
```

The kernel owners are `slice_base_change_gamma` and
`slice_base_change_phi`. Their canonical rectangular cuts are

```text
φᵃ_f(h) ∘ Σ_f(γᶜ_f(k)) == h ∘ Σ_f(k)
f*(φᵃ_f(h)) ∘ γᶜ_f(k) == f*(h) ∘ k.
```

Here `==` is runtime computation at the selected post-opposite normal form.
At identities, `γᶜ_f` and `φᵃ_f` recover the ordinary unit/counit components,
and both component triangles compute to identity. The fully expanded
`f*[h]∘η` and `ε∘Σ_f[k]` mate implementations remain proof-time usability
views rather than competing runtime spellings. Generic composed-functor object
and functor-identity computation owns `(f*∘Σ_f)[a]`, `Σ_f(id)`, and
`f*(id)`; do not print or document pullback-specific rules for those cases.

The first ambient projection law is written

```text
π₁ ∘ lift_f(h) ⇒ a
```

and is owned by `pullback_lift_fst_cell`. Do not write
`π₁ ∘ lift_f(h) == a` or `π₂ ∘ lift_f(h) == b` without a locally
discrete/strict adapter: raw ambient composites deliberately remain runtime
distinct. The stable mate operations have propositional semantic paths to
`f^*[h] ∘ η` and `ε ∘ Σ_f[k]`; these paths are typed reflexivity
through proof-time usability rules, not opaque equality bridges. The stable
mate functors retain higher action. Canonical body-unfolded whole unifiers use
the `sigma_map_obj` form to compare them with the semantic functors, and exact
raw-Hom-guarded `Cat_cat` rules compute both whole composites to identity. The
generic `Adjunction_hom_prof_comparison` remains the varying-endpoint
profunctor presentation; do not print a second `OmegaEquivAlong` package.

Whole `Σ_f` action and `slice_sigma_obj` share the selected runtime point.
Its domain is definitionally the domain of `a`, and its structure arrow
computes to `f ∘ arrow(a)`; surface prose should not insert a recentering
path or equality transport between those presentations.

`Pullback_catd(E,F)` continues to mean substitution of a Cat-valued family
along `F`. It is not notation for categorical pullback objects or `f^*`.
Products-in-slices, weighted pullback notation, pushouts, Beck–Chevalley, and
Frobenius have no selected surface syntax yet.

For the separate additive binary universal constructions, mathematical prose
may write

```text
X ×_Y Z                    genuine fiber product of alpha:X->Y and gamma:Z->Y
X ⊔_Y Z                    genuine pushout of alpha:Y->X and gamma:Y->Z
```

The kernel owners are `ComputationalFiberProduct` and
`ComputationalPushout`. Their primary cones/cocones are the annihilator and
coannihilator fibres of the relevant biproduct difference map. They are not
records with manually entered squares, `Pullback_catd`, or the exact-slice
`PullbackStructure`. The ASCII formulas are explanatory notation only; no new
string-parser tokens are selected.

## Slice Dependent-Product Notation

Given `PB : PullbackStructure(C)` and
`DP : DependentProductStructure(C,PB)`, write

```text
Π_u : C/X → C/Y
Σ_u ⊣ u* ⊣ Π_u
```

for `slice_dependent_product_func(DP,u)` and the two existing indexed
adjunctions. Do not confuse this `Π_u` with `Pi_cat(E)` or the separately
proposed general `Pi_along_func(f)`.

Write the second unit/counit and their off-diagonal observations as

```text
ηΠ_u : id_(C/Y) ⇒ Π_u ∘ u*
εΠ_u : u* ∘ Π_u ⇒ id_(C/X)

γΠᶜ_u(k) := tapp1(ηΠ_u,k)
φΠᵃ_u(h) := tapp1(εΠ_u,h).
```

The corresponding runtime cuts are

```text
φΠᵃ_u(h) ∘ u*(γΠᶜ_u(k)) == h ∘ u*(k)
Π_u(φΠᵃ_u(h)) ∘ γΠᶜ_u(k) == Π_u(h) ∘ k.
```

The actual whole unit/counit use the generic adjunction symbols; the stable
`γΠᶜ`/`φΠᵃ` heads are their computing `tapp1` observations. Generic
functor composition and identity own composite points and identity action.
The transparent Hom mate functors may be printed as

```text
transposeΠ(h)   = Π_u(h) ∘ ηΠ_u(a)
untransposeΠ(k) = εΠ_u(b) ∘ u*(k).
```

Their whole semantic equivalence is the generic adjunction
`ProfComparison`; do not print an additional `OmegaEquivAlong` claim.
`SliceDependentProducts(C)` denotes the thin total pairing of the selected
pullback and dependent-product structures; reserve the stronger locally
cartesian closed category name for the later convention-sensitive package.

## Generic Groupoidification Notation

For a category `C`, write the checked category-indexed free inversion as

```text
Groupoidify(C) : Grpd
u_C : C -> Path(Groupoidify(C)).
```

For `F : C -> Path(G)`, use `Ext^C_G(F)` for
`groupoidify_extend_at C G F` and `Res^C_G(h)` for
`groupoidify_restrict_at C G h`. The selected computation and whole mapping
property are

```text
Ext^C_G(F)(u_C[x]) == F[x]
apd(Ext^C_G(F),u_C[f]) == const_pathover(F[f])

Ext^C_G o Res^C_G = id
Res^C_G o Ext^C_G = id
Res^C_G : Hom(Groupoidify(C),G) ~= Functor(C,Path(G)).
```

The first two equations are judgmental at the active `groupoidify_rec` and
`eq_apd` owners. Whole beta/eta are equality evidence packaged by
`groupoidification_hom_omega C G`; do not write them as runtime reductions.
For composable arrows use

```text
φ_u(g,f) : u_C[g] o u_C[f] ==> u_C[g o f]
```

for `groupoidify_unit_compositor C g f`. Its whole transformation and next
action are `groupoidify_unit_compositor_transf` and
`groupoidify_unit_compositor_next_func`. The explicit cell is not identity,
even where the prototype's historical strict cuts make its endpoints
convertible.

The checked recovery result is written

```text
Groupoidify(WalkingArrow) ~= Interval,
```

owned by `groupoidify_walking_interval_type_equiv`. This is a `TypeEquiv`, not
definitional equality. `Groupoidify(C)` is an active kernel constructor, but
surface parsing, source action `Groupoidify(H)`, the whole
`Groupoidify_func : Cat_cat -> Grpd_cat`, and its adjunction with
`Path_cat_func` remain future interfaces.

## Computational Truncation And Circle Notation

In mathematical comments and reviewer prose, write homotopy truncation as

```text
‖A‖_n                 the n-truncation of A
|a|_n : ‖A‖_n         its point constructor
```

The active kernel keeps the classified result distinct from its decoded
ambient carrier:

```text
Trunc_ntype(n,A)        : Obj(NType_cat(n))
Trunc_grpd(n,A)         = decoded carrier ‖A‖_n
trunc_intro(n,A,a)      = |a|_n.
```

Restricted elimination is written as induction or recursion out of `‖A‖_n`
into an explicitly `n`-truncated target. The kernel owners are `trunc_ind`,
`trunc_ind_ambient`, `trunc_rec`, and `trunc_rec_ambient`; the ambient forms
must display or infer the required same-level truncation evidence. Do not use
this notation to suggest unrestricted elimination.

The selected Circle consumer is written

```text
CircleConnected(x) := ‖base = x‖_-1
circle_connected   : Pi x:Circle, ‖base = x‖_-1
IsContr(‖Circle‖_0).
```

The final line corresponds to `circle_set_trunc_is_contr`. It is a theorem
carrying contractibility evidence, not notation for a judgmental equality
`‖Circle‖_0 = Unit`. None of the notation in this section extends the bounded
TypeScript text grammar automatically.

## Cubical Arrow And Semicubical Nerve Notation

For the intrinsic directed-square tower, write

```text
Arr□(C)              = LaxArrow_cat(C) = CubicalArrow_cat(C)
Cub_0(C)             = C
Cub_{n+1}(C)         = Arr□(Cub_n(C)).
```

The first equality is mathematical and computational: `LaxArrow_cat` is the
derived two-sided Sigma total, while `CubicalArrow_cat` is its transparent
readability/compatibility alias. Do not present `CubicalArrow_cat` as a
primitive category.

An object of `Arr□(C)` is an edge `u : x ->^C y`. An arrow from `u` to
`v : x' ->^C y'` is written

```text
(a,b,alpha) : u ==>□ v

a : x  ->^C x'
b : y  ->^C y'
alpha : b o u ==> v o a.
```

This is expository notation for `cubical_edge` and the nested-Sigma
`cubical_square(a,b,alpha) = (a,(b,alpha))`; it is not a new parser form.
`CubicalArrow_func(F,P)` requires the selected readable pseudo profile `P`.
Do not omit that qualification when the distinction between an arbitrary lax
carrier and a liftable coherent carrier matters. The profile supplies
fixed-forward `OmegaEquivAlong` for the readable reframe of the existing
`fapp1_compositor`; its selected inverse supplies the reverse square-boundary
adjustment, and it does not own a second compositor. The reframe compensates
for the documented temporary global strict cut.

Category identity and composition remain at the generic nested-Sigma owners.
The readable `cubical_square_id` and `cubical_square_comp` terms may illustrate
the old explicit whisker/paste presentation, but comments must not print them
as judgmental normal forms of `id` or `comp`.

For the augmented semicube category, use

```text
CubeFaceCode(p,n)     length-n word in {L,R,*} with p stars
L f                   cube_face_left(f)
R f                   cube_face_right(f)
* f                   cube_face_keep(f)
g o□ f                cube_face_comp(g,f)
□_+                   SemiCubePlus_cat.
```

The native restriction selected by a code is written `d_f : Cub_n(C) ->
Cub_p(C)`. Its recursive equations are

```text
d_{L f} = d_f o source
d_{R f} = d_f o target
d_{* f} = Arr□(d_f).
```

At arbitrary public truncation points these constructor readings are typed
paths; do not print them as judgmental `==` equations. The whole nerve is

```text
N□(C) : Functor(Op_cat(□_+),Cat_cat)
N□(C)[n] == Cub_n(C)
N□(C)[f] = d_f.
```

The object equation is judgmental. The arrow equation is propositional by
design: `N□(C)` retains generic functoriality, while `d_f` retains its recursive
profile history. Consequently

```text
d_{id_n} = id
d_{g o□ f} = d_f o d_g
```

For standard combinatorial semicubes, write

```text
□[n]                 = StandardSemicube(n) = Yoneda(n)
□[n][p]              = Hom_{□_+}(p,n)
decode_{p,n}           = standard_semicube_native_decode_func(p,n)
decode_{p,n}(f)        = d_f.
```

The level equation is judgmental. The final equation is the selected path
`standard_semicube_native_decode_path`, not a second runtime arrow beta. Its
whole Hom action remains available for higher representable paths.

For the direct Yoneda object slice, write

```text
yoneda□(X) : Hom_Psh(□[n],N□(C))
eval_id(η) = η[n](id_n)
eval_id(yoneda□(X)) = X.
```

The owners are `cubical_yoneda_section`, `cubical_yoneda_eval`, and
`cubical_yoneda_beta`. The last equation is a path derived from the whole
nerve identity law, not a judgmental beta or a full eta equivalence.

The `d`-equations above are whole equality paths, not face-specific rewrites.
The immediate boundary
of an `n`-cube is the recursive `2n`-entry family with the new `L/R` pair first
and all older faces star-lifted afterward. Degeneracy, connection, reversal,
permutation, and Kan-composition notation remains unselected.

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
