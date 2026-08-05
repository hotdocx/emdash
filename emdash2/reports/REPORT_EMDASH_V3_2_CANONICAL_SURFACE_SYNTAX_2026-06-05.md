# emdash v3.2 Canonical Surface Syntax

Date: 2026-06-05
Last reviewed: 2026-08-04

Status: current notation authority for v3.2 comments, examples, and future
surface-syntax/parser planning.

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
