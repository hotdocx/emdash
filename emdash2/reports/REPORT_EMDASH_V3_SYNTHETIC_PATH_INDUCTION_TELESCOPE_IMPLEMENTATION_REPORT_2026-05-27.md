# emdash v3.2 Synthetic Path Induction Telescope Implementation Report

Date: 2026-05-27.

This report records the implementation pass for
`reports/REPORT_EMDASH_V3_SYNTHETIC_PATH_INDUCTION_TELESCOPE_PLAN_2026-05-27.md`.

## Implemented

- Added the primary telescope theorem:

```text
PathInd_transfd(Z)
  : Transfd(PathOutReflEval_funcd(Z), PathOutPi_funcd(Z)).
```

- Added the component projection:

```text
PathInd_transfd(Z)[x] = PathInd_func(Z,x).
```

- Added focused computation checks:

```text
PathInd_transfd(Z)[x][E]    = path_ind_func_fapp0(Z,x,E)
PathInd_transfd(Z)[x][E](u) = path_ind_sec(Z,x,E,u)
```

- Rerouted the first fixed-`x` transitivity benchmark through
  `PathInd_transfd`.

- Added generic Sigma-total uncurrying:

```text
Sigma_transfd_funcd(eta)[(k,r)] = eta[k][r].
```

- Replaced `PathInd_funcd` as a primitive source of truth. It is now defined by:

```text
PathInd_funcd(Z) = Sigma_transfd_funcd(PathInd_transfd(Z)).
```

- Constructed:

```text
pathout_refl_arrow(Z,x,y,p)
```

from the generic Sigma transport arrow:

```text
sigma_transport_arrow(Rep_Z(x), p, id_x).
```

- Added the generic capped identity functor action rule:

```text
id_func[p] = p.
```

This was needed for the endpoint computation:

```text
Rep_Z(x)[p](id_x) = p.
```

- Promoted the Sigma hom characterization into the Sigma foundation section:

```text
Hom_Sigma(E)((x,u),(y,v))
  = Sigma (p : Hom_K(x,y)), Hom_{E[y]}(E[p](u),v).
```

- Added `sigma_arrow(E,u,v,p,alpha)` as the total-arrow constructor backed by
  that `Hom(Sigma)` characterization.

- Replaced the previously primitive-looking canonical total transport with the
  transparent definition:

```text
sigma_transport_arrow(E,p,u)
  = sigma_arrow(E,u,E[p](u),p,id_{E[p](u)}).
```

- Added global strict functoriality rules in the cut-elimination orientation:

```text
F[id_x] = id_{F[x]}
F[g] o F[f]  -->  F[g o f].
```

- Defined the generic Sigma-map action on canonical total transport arrows:

```text
Sigma(eta)[sigma_transport(E,p,u)]
  = sigma_map_transport_arrow(eta,p,u).
```

- Defined `Sigma_catd_transport_func(FF,p,r)` as the ordinary action of
  `Sigma_catd_functord_catd(FF)` on `sigma_transport_arrow(R,p,r)`, rather than
  as a primitive projection head.

- Added the first PathOut transport computations needed for rho coherence:

```text
PathOut_transport(p)[(z,q)] = (z,q o p)
PathOut_transport(p)[rho_{y,z,q}]
  = sigma_map_transport_arrow(precompose_p, q, id_y).
```

- Replaced the primitive rho-section by its path-induction-derived
  presentation:

```text
pathout_refl_arrow_sec(x)
  = path_ind_sec(Rep_{PathOut_Z(x)}((x,id_x)), id_{(x,id_x)}).
```

Its component computes to the same `pathout_refl_arrow(Z,x,y,p)`.

- Removed the old internalized-`x` transport-square layer:
  `functord_transport_transf`, `PathInd_transport_lhs_func`,
  `PathInd_transport_rhs_func`, and `PathInd_transport_transf`. These belonged
  to the earlier Sigma-total-primary design. The current source and target
  transport helpers are direct definitions:

```text
PathIndSrc_transport(p,E) = E[rho_{x,y,p}]
PathIndTgt_transport(p,E) = section_pullback(PathOut_transport(p),E).
```

## Design Notes

The old Sigma-total presentation is now derived from the telescope theorem. Its
component checks live after the generic `tdapp0_fapp0`/`Sigma_transfd_funcd`
projection layer, because a transparent derived `PathInd_funcd` unfolds before
the generic projection rule is available.

The `rho` construction is no longer an axiom. Full `rho` coherence, such as
compatibility with composition in `PathOut_transport`, remains deferred.

`sigma_transport_arrow`, `sigma_map_transport_arrow`, and
`Sigma_catd_transport_func` are no longer primitive mathematical assumptions.
They are transparent definitions over `sigma_arrow` and ordinary functor
action. This keeps `Hom(Sigma)` as the fundamental constructor layer.

The direct composite:

```text
PathOut_transport(p)[rho_{y,z,q}] o rho_{x,y,p}
```

was probed but does not yet reduce definitionally to `rho_{x,z,q o p}`. The
transparent `sigma_map_transport_arrow` exposes the transported-rho half; the
remaining missing piece is a clean Sigma-arrow composition rule, preferably at
the `sigma_arrow` constructor level rather than as a broad ad hoc
`comp_fapp0` rule.

`pathout_refl_arrow_sec` is now transparent. A focused probe showed that the
path-induction-derived definition checks once the old explicit
`tapp0_fapp0(pathout_refl_arrow_sec, Struct_sigma ...)` component rewrite rule
is removed. The earlier timeout came from that overlapping reduction path, not
from the component assertion itself.

Do not define `pathout_refl_arrow` itself as the component of
`pathout_refl_arrow_sec` in the current architecture. That section is defined
through `path_ind_sec`, and the component rule for `path_ind_sec` uses
`pathout_refl_arrow`; making `pathout_refl_arrow` unfold back to that component
would create a recursive computation path. The component equality is therefore
kept as an assertion rather than as the defining equation.

## Preliminary Findings For The Next Phase

The original transitivity benchmark has been achieved computationally in the
fixed-source form:

```text
path_ind_sec(Z,x,CompMotive_Z(x),id_{Rep_Z(x)}) = path_comp_sec(Z,x)
path_comp_sec(Z,x)[p][z](q) = q o p.
```

The redesigned internalized-source theorem also reaches this benchmark through
the telescope component:

```text
PathInd_transfd(Z)[x] = PathInd_func(Z,x)
PathInd_transfd(Z)[x][CompMotive_Z(x)](id_{Rep_Z(x)})
  = path_comp_sec(Z,x).
```

The file does not yet contain one fully expanded assertion spelling the whole
chain:

```text
PathInd_transfd(Z)[x][CompMotive_Z(x)](id)[(y,p)][z](q) = q o p.
```

Adding that assertion should be the first next implementation step. It is a
regression check for the achieved theorem, not new theory.

### Composition Packaging

Do not import the old `Product_cat`-based `comp_func` from `emdash2.lp` as the
first move. The better v3.2 form is the telescoped/internal composition
package:

```text
comp_func_tele(A,x,y,z)
  : Hom_A(y,z) -> (Hom_A(x,y) -> Hom_A(x,z)).
```

It should be definable from the existing internal hom infrastructure:

```text
comp_func_tele(A,x,y,z)
  := hom_(id_A,x)[on arrows y -> z]
```

or, in Lambdapi terms, morally:

```text
comp_func_tele(A,x,y,z)
  := fapp1_func(hom_ A A id_A x, y, z).
```

The pointwise beta behavior should be:

```text
comp_func_tele(A,x,y,z)[g][f] = g o f.
```

This gives the omega-friendly packaging of composition without requiring
`Product_cat` in v3.2.

### Do Not Reverse `comp_cat_fapp0` Globally Yet

Although cut-elimination often suggests the orientation:

```text
F(G(x)) -> (F o G)(x),
```

the current v3.2 kernel uses:

```text
(F o G)[x] -> F[G[x]].
```

Reversing this globally would be a high-risk rewrite-system change. It would
overlap with many constructor beta rules and could hide constructor-specific
normal forms currently used by assertions. For the immediate Sigma work, prefer
a narrow strict object-transport fold:

```text
E[q](E[p](u)) -> E[q o p](u).
```

This should be treated as the object-level projection of strict functoriality
for `E : K -> Cat`, not as a new mathematical axiom.

### Sigma-Arrow Composition

The intended Sigma-arrow composition computation is:

```text
(q,beta) o (p,alpha)
  -> (q o p, beta o E[q][alpha])
```

with:

```text
p     : Hom_K(x,y)
q     : Hom_K(y,z)
alpha : Hom_{E[y]}(E[p](u), v)
beta  : Hom_{E[z]}(E[q](v), w).
```

The fibre part:

```text
beta o E[q][alpha]
```

has the expected source only after the strict object-transport fold:

```text
E[q](E[p](u)) -> E[q o p](u).
```

Conceptual rule:

```text
comp_Sigma(
  sigma_arrow(E,v,w,q,beta),
  sigma_arrow(E,u,v,p,alpha))
  ->
sigma_arrow(E,u,w,q o p,beta o E[q][alpha]).
```

Operationally, since `sigma_arrow` is transparent and unfolds to the
`Struct_sigma` representation supplied by `Hom(Sigma)`, the robust Lambdapi rule
may need to match the reduced pair form rather than the readability head. The
mathematical comment should still present it as Sigma-arrow composition.

### Strict Naturality For Off-Diagonal Components

Full Sigma-map action on general Sigma arrows needs the strict naturality of
ordinary transfors. The useful v2 pattern is the off-diagonal component:

```text
tapp1_fapp0(epsilon,f) : F[x] -> G[y]
```

with cut-elimination rules:

```text
G[g] o epsilon[f] -> epsilon[g o f]
epsilon[f] o F[g] -> epsilon[f o g].
```

v3.2 already reserves `tapp1_fapp0`, but keeps it abstract. Porting the strict
v2 rules, carefully and with focused probes, would expose the naturality needed
for Cat-valued transfors and displayed functors:

```text
D[p] o eta[x] -> eta[p]
eta[y] o E[p] -> eta[p].
```

This is the missing ingredient for a fully general computation of:

```text
Sigma(eta)[sigma_arrow(E,p,alpha)].
```

### Rho Coherence Status

Full rho coherence:

```text
PathOut_transport(p)[rho_{y,z,q}] o rho_{x,y,p}
  -> rho_{x,z,q o p}
```

is no longer a blocker for `PathInd_transfd` or for the transitivity benchmark.
It remains useful future coherence for `PathOut`, generic Sigma maps, and
eventual global coherent motive families.

Recommended dependency order for the next implementation phase:

```text
1. Add the fully expanded PathInd_transfd transitivity assertion.
2. Add/probe comp_func_tele as transparent internal composition packaging.
3. Probe the strict object-transport fold E[q](E[p](u)) -> E[q o p](u).
4. Port/probe v2-style strict off-diagonal naturality for tapp1_fapp0.
5. Probe Sigma-map action on general sigma_arrow.
6. Probe Sigma-arrow composition.
7. Only then revisit full rho coherence.
```

## 2026-05-28 Implementation Update

The recommended dependency order above has now been implemented in
`emdash3_2.lp` and validated.

Added computational infrastructure:

- `comp_func_tele`, the telescoped internal composition package:
  `Hom(y,z) -> Hom(x,y) -> Hom(x,z)`.
- A fully expanded `PathInd_transfd` transitivity assertion showing that the
  synthetic/telescope theorem component computes to `q o p`.
- Strict object transport:
  `E[q](E[p](u)) -> E[q o p](u)`.
- Strict off-diagonal naturality for ordinary transfors:
  `G[g] o epsilon[f] -> epsilon[g o f]` and
  `epsilon[f] o F[g] -> epsilon[f o g]`.
- Cat-valued object-level naturality folds:
  `D[p](eta[x](u)) -> eta[p](u)` and
  `eta[y](E[p](u)) -> eta[p](u)`.
- General Sigma-map action on Sigma homs:
  `Sigma(eta)[(p,alpha)] -> (p, eta[y][alpha])`.
- General Sigma-arrow composition:
  `(q,beta) o (p,alpha) -> (q o p, beta o E[q][alpha])`.
- Regression assertions for `sigma_map_transport_arrow` and full rho
  coherence:
  `PathOut_transport(p)[rho_yz_q] o rho_xy_p -> rho_xz_(q o p)`.

Design notes:

- `sigma_arrow` remains a transparent readability constructor over the
  fundamental `Hom(Sigma)` pair characterization. Rules that must fire after
  unfolding match the reduced `Struct_sigma` pair form.
- The Sigma composition rule explicitly matches `Sigma_cat K E` as the actual
  discriminator needed to recover `K` and `E`; it avoids explicit `Hom_cat`
  source/target categories or reducible fibre-category expressions on the LHS.
- The old internalized-x transport theorem heads `functord_transport_transf`
  and `PathInd_transport_transf` remain deleted.

## 2026-05-28 Planning Note: Sigma Level, Product, And Uncurrying

### Capped Sigma Status

The current transitivity/composition theorem is a theorem about 1-arrows:

```text
PathInd_transfd(...)[...][...][...][(y,p)][z](q) -> q o p.
```

This uses the capped ordinary arrow action `fapp1_fapp0`, not the full
hom-functor action `fapp1_func` as an exposed omega-level API.

The recent Sigma infrastructure should be read the same way for now:

- `sigma_map_func` is a functor object.
- Its object action computes on `(k,u)`.
- Its capped arrow action computes on Sigma-hom pairs via `fapp1_fapp0`.
- Sigma-arrow composition computes via `comp_fapp0` in `Sigma_cat`.

What is not yet exposed:

```text
fapp1_func(sigma_map_func eta)
```

as a fully named/computational functor between Sigma hom-categories, with all
higher action data. The current rules are deliberately enough for 1-arrow/path
transitivity, Sigma transport, and rho coherence. They are not yet the final
full omega-functorial Sigma API.

### Product Before Further Dependent Uncurrying

`Product_cat` has now been reintroduced in v3.2. The foundations report
records the intended relation:

```text
Sigma_cat(Const_catd K A)  =  Product_cat K A.
```

Before expanding generic `Sigma_transfd_funcd` naturality, it is likely useful
to stage a smaller non-dependent product/curry-uncurry pass:

```text
Product_cat A B
Cat(A x B, C)  ~  Cat(A, Functor_cat B C).
```

Recommended approach:

1. Do not port the full emdash2 `Product_cat` block blindly.
2. Probe a minimal v3.2 product API in a temporary file:
   objects as pairs, homs as pairs, identity, composition, projections, and
   pairing.
3. Add ordinary curry/uncurry heads only after the product normal forms are
   stable.
4. Treat the dependent Sigma uncurrying layer as the dependent analogue of
   this ordinary product/curry story.

This staging should make later `Sigma_transfd_funcd` design less ad hoc.

### `Sigma_transfd_funcd` As Dependent Comprehension Action

`Sigma_catd_functord_catd` and `Sigma_transfd_funcd` are best understood as
dependent context-extension/curry-uncurry infrastructure.

For:

```text
FF : Functord R (Const_catd K Cat_cat)
```

the object:

```text
Sigma_catd_functord_catd(FF)
```

is the family over the context extension `Sigma K R`:

```text
(k,r) |-> FF[k][r].
```

For:

```text
eta : Transfd S T
```

the object:

```text
Sigma_transfd_funcd(eta)
```

is the uncurried/comprehension action:

```text
(k,r) |-> eta[k][r].
```

This is Grothendieck-like, but it is not literally the old emdash2
`Fibration_cov_fapp1_func`.

The emdash2 head had shape:

```text
Fibration_cov_fapp1_func :
  Transf(E,D) -> Functord(Fibration_cov_catd E, Fibration_cov_catd D).
```

That is the morphism-action of the Grothendieck construction on an ordinary
Cat-valued natural transformation. In contrast, `Sigma_transfd_funcd` acts on a
displayed transfor over a dependent telescope and produces a displayed functor
between families over the Sigma-total context. A good working description is:

```text
dependent Sigma-total/comprehension uncurrying
```

or, with care:

```text
dependent Grothendieck-style morphism action.
```

### Refined Next Implementation Order

1. Add comments/report text clarifying that the current Sigma computations are
   capped/1-arrow computations, not the final full `fapp1_func` API.
2. Probe a minimal `Product_cat` and ordinary curry/uncurry package.
3. Relate `Product_cat K A` definitionally against
   `Sigma_cat(Const_catd K A)`.
4. Return to `Sigma_transfd_funcd` and try to derive more of its action and
   naturality from the smaller ordinary and dependent infrastructure.
5. Keep global coherent motive families deferred until the generic uncurrying
   and comprehension action layer is stable.

## 2026-05-28 Implementation Update: Product Warm-Up

The first three items in the refined order above have now been implemented in
`emdash3_2.lp`.

Added comments near the Sigma definitions clarifying that the current Sigma
computation layer is capped/1-arrow level:

```text
fapp1_fapp0(sigma_map_func eta, (p,alpha))
```

is computational, while the full hom-functor package

```text
fapp1_func(sigma_map_func eta)
```

is not yet exposed as the final omega-level Sigma API.

Added a minimal ordinary product package:

```text
Product_cat(A,B)
Obj(A x B) = Sigma x : Obj(A), Obj(B)
Hom_{A x B}((x,u),(y,v)) = Hom_A(x,y) x Hom_B(u,v)
id_{(x,u)} = (id_x,id_u)
(g1,g2) o (f1,f2) = (g1 o f1, g2 o f2)
```

Also added the ordinary product universal-property heads at object/action
level:

```text
Product_pair_func(F,G)
Product_projL_func(H)
Product_projR_func(H)
```

with object and `fapp1_func` projection/pairing computations.

Added the ordinary curry/uncurry scaffold:

```text
curry(F)[x][y] = F[(x,y)]
uncurry(G)[(x,y)] = G[x][y]
uncurry(curry(F))[(x,y)] = F[(x,y)]
curry(uncurry(G))[x][y] = G[x][y]
```

The object-level heads remain stable projections of the more-internal functor
packages:

```text
curry_func_func[F]   = curry(F)
uncurry_func_func[G] = uncurry(G)
```

The first hom-action layer is now exposed:

```text
curry(F)[p][y] = F[(p,id_y)]
curry(F)[x][q] = F[(id_x,q)]
uncurry(G)[(p,q)] = G[x'][q] o G[p][y]
```

The functor-level action on transfors also computes componentwise:

```text
curry(eta)[x][y] = eta[(x,y)]
uncurry(theta)[(x,y)] = theta[x][y]
```

This is still not the final Product/Functor adjunction package. The remaining
work is adjunction-style packaging and coherence beyond these beta/action
laws.

The natural formula for `uncurry(G)[(f,g)]` uses both transfor components and
functor action:

```text
G[x'][g] o G[f][y].
```

Added the direct non-dependent Sigma/Product normal form:

```text
Sigma_cat(Const_catd K A) -> Product_cat K A
Hom_{Sigma(Const A)}((x,u),(y,v)) -> Hom_K(x,y) x Hom_A(u,v)
sigma_arrow(Const A,p,alpha) -> (p,alpha)
```

This replaces the temporary bridge-functor approach. The bridge heads
`Product_to_const_sigma_func` and `const_sigma_to_Product_func` were removed
instead of kept as undeclared functor symbols; constant-family Sigma now
inherits the Product object, hom, identity, and composition normal forms
directly.

The next natural implementation step is to return to more generic
`Sigma_transfd_funcd` action/naturality, unless Product/Functor adjunction
coherence becomes a more urgent downstream dependency.

## 2026-05-28 Superseded Probe: Sigma-Transfd Canonical Transport Action

Product/Functor adjunction coherence remains deferred. A route-specific
Sigma-total uncurrying step was probed for the canonical total transport case.

The probed helper was:

```text
Sigma_transfd_transport_func(eta,p,r)
  = Sigma_catd_transport(T,p,r) o Sigma_transfd(eta)[(x,r)]
```

for:

```text
eta : Transfd(S,T)
p   : Hom_K(x,y)
r   : R[x].
```

The exposed computation is:

```text
Sigma_transfd(eta)[sigma_transport(R,p,r)]
  -> Sigma_transfd_transport_func(eta,p,r)
```

where the left side is the heterogeneous `functord_transport_func`/`tapp1_fapp0`
action of the uncurried displayed functor over the Sigma-total base. The
rewrite rule deliberately matches the reduced Sigma-hom pair form
`(p,id)` rather than the transparent `sigma_transport_arrow` head, because
`sigma_transport_arrow` is a definition over `sigma_arrow`/`Struct_sigma` and
may unfold before the projection fires.

Also added an object-action regression:

```text
Sigma_transfd_transport_func(eta,p,r)[c]
  = Sigma_catd_transport(T,p,r)(eta[(x,r)](c)).
```

This probe typechecked, but it has now been retracted from `emdash3_2.lp`.

This is a narrow canonical-transport projection, not a full arbitrary
Sigma-arrow action for `Sigma_transfd_funcd`. The opposite route

```text
eta[(y,R[p]r)](Sigma_catd_transport(S,p,r)(c))
```

does not yet reduce definitionally to the same normal form; exposing that
requires a cleaner displayed-transfor naturality/comprehension rule and is left
for a later concrete downstream need.

## 2026-05-28 Reassessment: Internal Naturality Normal Form

After review, the preceding `Sigma_transfd_transport_func` direction is likely
the wrong long-term normal form. It chooses one external route around a
naturality square:

```text
T[p](eta[x](c))
```

but the internal/synthetic normal form should be the off-diagonal transfor
component itself:

```text
tapp1_fapp0(eta,p)(c).
```

For a canonical/cartesian Sigma arrow

```text
sigma_transport(R,p,r) : (x,r) -> (y,R[p]r),
```

the desired compiled Sigma-total computation is therefore:

```text
Sigma_transfd_funcd(eta)[sigma_transport(R,p,r)]
  -> tapp1_fapp0(Sigma_transfd_funcd(eta), sigma_transport(R,p,r))
```

or, more precisely, it should keep the existing `tapp1_fapp0` term as the
canonical internal off-diagonal component rather than folding it to a
route-specific helper.

The two external routes should, when they arise, accumulate toward that same
off-diagonal component:

```text
T[p](eta[x](c))       -> eta[p](c)
eta[y](S[p](c))       -> eta[p](c)
```

This follows the project design rule: if we are manually managing a naturality
square, the design is probably not internal/synthetic enough. The square is
data carried by the internal natural/displayed quantification.

Implementation consequence for the next turn:

- Treat the current rewrite from `tapp1_fapp0(Sigma_transfd_funcd eta, ...)` to
  `Sigma_transfd_transport_func` as suspect.
- Prefer removing that fold, or redefining the helper only as a readable alias
  that does not replace the `tapp1_fapp0` head.
- Do not introduce a new stable off-diagonal head unless a focused probe shows
  that `tapp1_fapp0` itself cannot serve.
- Probe diagonal naturality accumulation rules with `tapp0_fapp0` on the LHS,
  if needed, but orient them toward `tapp1_fapp0`, not toward a route-specific
  composite.

The corrected remaining target is not arbitrary Sigma-arrow action. It is only
canonical/cartesian Sigma-arrow computation, and even there the normal form
should remain internal:

```text
PathInd_funcd[canonical transport of (x,E)]
  -> PathInd_transfd's off-diagonal component over p,E.
```

Arbitrary Sigma arrows

```text
(p,alpha) : (x,r) -> (y,r')
```

remain outside the immediate milestone. Requiring them would recreate the old
Sigma-total-primary architecture that the telescope redesign intentionally
avoided.

## 2026-05-28 Implementation Update: Route-Specific Fold Removed

The reassessment above has now been applied to `emdash3_2.lp`.

Removed from the active file:

```text
Sigma_transfd_transport_func
tapp1_fapp0(Sigma_transfd_funcd eta, (p,id)) -> Sigma_transfd_transport_func(...)
```

and the two route-specific regression assertions that made
`Sigma_catd_transport(T,p,r) o eta[(x,r)]` the target normal form.

The active normal form for canonical/cartesian Sigma-total action is again the
existing internal off-diagonal component:

```text
functord_transport_func(Sigma_transfd_funcd eta, sigma_transport(R,p,r))
  = tapp1_fapp0(Sigma_transfd_funcd eta, sigma_transport(R,p,r)).
```

No new stable off-diagonal head was introduced. A probe of route-composite
assertions showed that explicit Sigma-total endpoints are still too brittle for
a clean theorem-style assertion there; adding a special rewrite would be the
wrong architectural response. Future work should only add a diagonal
`tapp0_fapp0` accumulation rule if a concrete downstream computation produces
that exact shape and the rule can be oriented toward `tapp1_fapp0`.

## 2026-05-28 Implementation Update: Generic Route Accumulation Assertions

The generic displayed-functor transport routes were checked at object level:

```text
D[p](FF[x](u)) -> FF[p](u)
FF[y](E[p](u)) -> FF[p](u)
```

In the file this is expressed as two regression assertions showing that
`functord_transport_lhs_func(FF,p)[u]` and
`functord_transport_rhs_func(FF,p)[u]` both compute to
`functord_transport_func(FF,p)[u]`.

No new rewrite rule was needed. The assertions are consequences of the existing
Cat-valued strict naturality rules:

```text
fapp0(D[p], fapp0(eta[x], u)) -> fapp0(eta[p], u)
fapp0(eta[y], fapp0(E[p], u)) -> fapp0(eta[p], u)
```

This confirms the desired internal normal form for route computations in the
generic displayed setting. The still-open Sigma-total question is narrower:
whether a downstream theorem exposes the same shape after the canonical
Sigma-total transport arrow has reduced far enough for these generic rules to
apply. We should not add a Sigma-specific route fold unless such a theorem
requires it.

## 2026-05-28 Implementation Update: Sigma-Total Transitivity Regression

The achieved transitivity theorem is now also checked through the derived
Sigma-total presentation:

```text
PathInd_funcd(Z)[(x,CompMotive_Z(x))](id_{Rep_Z(x)})
  -> path_comp_sec(Z,x)
```

and fully expanded:

```text
PathInd_funcd(Z)[(x,CompMotive_Z(x))](id)[(y,p)][z](q)
  -> q o p.
```

This is the Sigma-style regression for the already-derived theorem; it does
not require reintroducing the old Sigma-total-primary transport-square design.

A nearby probe tried to expose canonical transport for the `Pi_pullback_funcd`
specialization of `Sigma_catd_transport_func`, but that is adjacent target-side
transport coherence rather than part of the current transitivity computation.
It is deferred until a downstream theorem needs that exact transport
normal form.

## 2026-05-28 Planning Note: Canonical Pi-Pullback Transport

The deferred `Pi_pullback_funcd` transport computation should be implemented at
the lower semantic/projection layer, not by adding a rewrite rule to
`Sigma_catd_transport_func` and not by defining `section_pullback_func` from
Sigma transport.

The intended dependency direction is:

```text
Pi_int_funcd / Pi_pullback_funcd
  -> section_pullback_transf
  -> section_pullback_func
  -> Sigma_catd_functord_catd(Pi_pullback_funcd) canonical transport.
```

`section_pullback_func(F,E)` is the component of Pi naturality under base
pullback:

```text
section_pullback_transf(F)[E] -> section_pullback_func(F,E).
```

It is not conceptually a Sigma-total construction. The Sigma-total route should
project to this existing Pi-naturality component.

The desired future computation is:

```text
Sigma_catd_transport_func(Pi_pullback_funcd(G), p, E)
  -> tapp0_fapp0(section_pullback_transf(G[p]), E)
  -> section_pullback_func(G[p], E).
```

Since `Sigma_catd_transport_func` is a transparent definition, the future rule
or projection should target the unfolded constituent expression:

```text
fapp1_fapp0
  (Sigma_catd_functord_catd(Pi_pullback_funcd(G)))
  (sigma_transport_arrow(...,p,E))
```

or, if `sigma_transport_arrow` unfolds too early, the corresponding reduced
Sigma-hom pair form. The RHS should be the Pi-naturality component:

```text
tapp0_fapp0(section_pullback_transf(G[p]), E)
```

and the existing `section_pullback_transf` rule should finish the reduction to
`section_pullback_func(G[p],E)`.

Concrete path-induction specialization:

```text
Sigma_catd_transport_func(PathOutPi_funcd, p, E)
  -> PathIndTgt_transport_func(p,E).
```

This is needed for canonical-arrow naturality of the derived Sigma-total
presentation `PathInd_funcd`, but it is not needed for the transitivity theorem
already checked through both `PathInd_transfd` and `PathInd_funcd`.

Implementation recommendation for the next pass:

1. Probe the lower-level `fapp1_fapp0(Sigma_catd_functord_catd(...), ...)`
   rule in a temporary copy, with the endpoint-family arguments kept implicit
   unless they are true discriminators.
2. First target the RHS
   `tapp0_fapp0(section_pullback_transf(G[p]), E)`, not the fully reduced
   `section_pullback_func(G[p],E)`.
3. Add the generic assertion only if the path-specific assertion also reduces:
   `Sigma_catd_transport_func(PathOutPi_funcd,p,E) ≡ PathIndTgt_transport_func(p,E)`.
4. If the rule only works by matching a large explicit Sigma/Pi endpoint in an
   implicit LHS slot, reject it and leave the computation deferred.

## 2026-05-28 Implementation Probe: Pi-Pullback Transport Deferred

The canonical `Pi_pullback_funcd` transport rule was probed in temporary files
and was not promoted to `emdash3_2.lp`.

Findings:

- A rule matching on the transparent helper
  `sigma_transport_arrow(...)` is not robust, because the helper unfolds to the
  underlying `sigma_arrow`/`Struct_sigma` representation before the intended
  `fapp1_fapp0` projection necessarily sees that head.
- A reduced Sigma-pair rule with an unconstrained target object does not
  preserve typing: Lambdapi cannot infer that the target object is the canonical
  transported motive object required by the RHS.
- A diagnostic rule that explicitly matched the transported target object in
  the reduced pair form could be made to typecheck in isolation, but it relies
  on large compound endpoint expressions in positions that are implicit in the
  declared `fapp1_fapp0` interface. That is exactly the brittle pattern banned
  by the rewrite-rule SOP.
- Even with that diagnostic rule, the intended assertions through
  `Sigma_catd_transport_func(Pi_pullback_funcd(G),p,E)` did not reduce cleanly.

Conclusion: do not add a direct rule for this computation yet, and do not add a
rule directly on the transparent `Sigma_catd_transport_func` alias. The current
explicit target helper remains the correct stable surface:

```text
PathIndTgt_transport_func(p,E)
  = section_pullback_func(PathOut_transport_func(p),E).
```

The deferred computation should be revisited only after there is a stable,
more-internal source for the required endpoint information, likely a cleaner
Pi-naturality/comprehension package rather than a Sigma-specific rule. This
does not affect the already checked transitivity theorem through
`PathInd_transfd` and the derived `PathInd_funcd`.

## 2026-05-29 Design Note: Lax Coherence Via Sigma Totals

After reviewing the `emdash2.lp` lax-functor comments against the current v3.2
Sigma-total architecture, the cleaner interpretation is:

```text
lax coherence = image of a canonical/cartesian source triangle
                under the relevant total/Sigma action.
```

For an ordinary functor `F`, the computational reading of

```text
F[g] o F[f]  =>  F[g o f]
```

is not primarily a textbook composition equation. It is the image, under the
displayed/Grothendieck hom-action package, of the canonical source triangle
from `f` to `g o f` over `g`. If the functor is strict/cartesian-preserving,
that image triangle collapses to the canonical one; otherwise it is genuine
laxity data.

For a transfor `eta : F => G`, the same skew accumulation principle applies to
the fixed-`X` off-diagonal package:

```text
eta^X : Hom_A(X,-) -> Hom_B(F[X],G[-]).
```

In v3.2 this is clearer when totalized:

```text
Sigma(eta^X)
  : Sigma(Y : A, Hom_A(X,Y))
    -> Sigma(Y : A, Hom_B(F[X],G[Y])).
```

The source object is `(Y,f)`.  The canonical/cartesian source triangle over
`g : Y -> Z` is a Sigma arrow

```text
(Y,f) -> (Z,g o f)
```

whose fibre component is identity/canonical. Applying `Sigma(eta^X)` produces
a target Sigma arrow still over `g`, but with nontrivial fibre component. Its
ambient boundary is the lax naturality/accumulation cell:

```text
G[g] o eta_(f)  =>  eta_(g o f).
```

The dual skew variant

```text
eta_(f) o F[h]  =>  eta_(f o h)
```

is the analogous other-side accumulation. The direct textbook square comparing
`G[p] o eta[x]` and `eta[y] o F[p]` is semantically useful, but it should not be
the primary normalization driver. The computational orientation should go
through one chosen off-diagonal apex, in the spirit of the
antecedential/consequential naturality distinction.

### Pi Specialization

The Pi coherence should be understood as this same projected lax action, not as
an arbitrary Sigma-transport rule.

The internal Pi package is:

```text
Pi_int_funcd
  : Functord
      Catd_cat_func
      (Const_catd (Op_cat Cat_cat) Cat_cat).
```

For `F : Functor A B`, viewed as a base arrow `B -> A` in `Op_cat Cat_cat`, the
two Cat-valued routes are:

```text
D[F] o Pi_func(B)
Pi_func(A) o Pullback_catd_func(F)
```

where `D` is constant, so the first route reduces to `Pi_func(B)`. Therefore
the projected laxity/naturality arrow is exactly:

```text
section_pullback_transf(F)
  : Transf(
      Pi_func(B),
      Pi_func(A) o Pullback_catd_func(F)).
```

Its component at `E : Catd(B)` is:

```text
section_pullback_func(F,E).
```

For a pulled-back base family `G : K -> Op(Cat)`, the desired specialization is:

```text
functord_laxity_transf(Pi_pullback_funcd(G), p)
  -> section_pullback_transf(G[p])

tapp0_fapp0(functord_laxity_transf(Pi_pullback_funcd(G), p), E)
  -> section_pullback_func(G[p], E).
```

This is the likely solution to the deferred Pi-pullback transport issue. The
source of truth is the lax/coherence projection of `Pi_int_funcd` and its
pullbacks, not a direct rule on the transparent alias
`Sigma_catd_transport_func`.

### Implementation Recommendations

Recommended next implementation phase:

1. Introduce or probe a small stable projection for displayed-functor laxity,
   tentatively `functord_laxity_transf(FF,p)`, whose type expresses the skew
   comparison between the two routes
   `D[p] o FF[x]` and `FF[y] o E[p]`.
2. First add only the Pi specialization:
   `functord_laxity_transf(Pi_int_funcd,F) -> section_pullback_transf(F)`,
   or the pulled-back specialization
   `functord_laxity_transf(Pi_pullback_funcd(G),p) ->
   section_pullback_transf(G[p])`, whichever typechecks with cleaner implicit
   arguments.
3. Keep rewrite-rule LHSs on stable explicit discriminators such as
   `functord_laxity_transf`, `Pi_int_funcd`, or `Pi_pullback_funcd`. Do not
   match on transparent aliases such as `Sigma_catd_transport_func`, and do not
   place large reducible endpoint expressions in implicit argument slots.
4. Treat the Sigma-total action as the semantic explanation and eventual
   omega-friendly presentation: `Sigma(eta^X)` sends canonical/cartesian Sigma
   arrows to the lax-coherence Sigma arrows. Do not require arbitrary
   Sigma-arrow action to compute before the Pi coherence projection exists.
5. Leave the already achieved transitivity theorem unchanged. Both the
   telescope theorem and the derived Sigma-total regression already compute to
   `q o p`; this new phase is about canonical-arrow naturality/coherence of
   the Pi target transport.

## 2026-05-29 Implementation Update: Displayed-Functor Laxity Projection

The recommended projection was implemented in `emdash3_2.lp`.

New generic head:

```text
functord_laxity_transf(FF,p)
  : Transf(
      functord_transport_lhs_func(FF,p),
      functord_transport_rhs_func(FF,p)).
```

This records the skew coherence between the two route functors

```text
D[p] o FF[x]
FF[y] o E[p]
```

without forcing arbitrary Sigma-total transport to compute.

Pi specialization:

```text
functord_laxity_transf(Pi_int_funcd,F)
  -> section_pullback_transf(F)
```

where `F : A -> B` is read as a base arrow `B -> A` in `Op(Cat)`.

Pulled-back specialization:

```text
functord_laxity_transf(Pi_pullback_funcd(G),p)
  -> section_pullback_transf(G[p]).
```

Component extraction then computes as desired:

```text
tapp0_fapp0(functord_laxity_transf(Pi_pullback_funcd(G),p), E)
  -> section_pullback_func(G[p],E).
```

Path-specific regression:

```text
tapp0_fapp0(functord_laxity_transf(PathOutPi_funcd(Z),p), E)
  -> PathIndTgt_transport_func(p,E).
```

The probe showed that the Pi specialization needs ordinary identity folds for
the stable functor-composition head:

```text
comp_cat_fapp0(id, F) -> F
comp_cat_fapp0(F, id) -> F.
```

Without these rules, the source route for `Pi_int_funcd` remains syntactically
`id_Cat o Pi_func(B)`, and Lambdapi cannot prove subject reduction for the
specialization to `section_pullback_transf(F)`. These are ordinary
strict-functoriality rules for `comp_cat_fapp0`, not Sigma-specific transport
rules.

This update deliberately does not add a rule for
`Sigma_catd_transport_func(Pi_pullback_funcd(G),p,E)`. The computation now has
a clean source of truth at the displayed-laxity projection layer; the
Sigma-total presentation can later be connected to that projection by a
separate total-action theorem if a downstream theorem needs it.

## 2026-05-29 Correction: Laxity Projection Is Interim

Follow-up review clarified an important architectural issue: the newly added

```text
functord_laxity_transf(FF,p)
```

is currently a stable projection interface, not yet the intended derivation
from existing total/Sigma action. The long-term design remains:

```text
lax coherence = fibre component of the image of a canonical/cartesian
                 Sigma-total arrow under the relevant total action.
```

For a fixed-source off-diagonal package

```text
eta^X : Hom_A(X,-) -> Hom_B(F[X],G[-])
```

the intended extraction is:

```text
Sigma(eta^X)((Y,f) -> (Z,g o f))
```

and then project the fibre component of the resulting Sigma arrow. That fibre
component is the skew laxity cell:

```text
G[g] o eta_(f) => eta_(g o f).
```

The same principle should explain the Pi case:

```text
section_pullback_transf(F)
```

should be the extracted fibre component of the total action of `Pi_int_funcd`
along the canonical/cartesian total arrow over `F`, not merely a primitive
special case attached to `functord_laxity_transf`.

Immediate implementation target after this correction:

1. Probe a component-level extraction rule for the component of
   `functord_laxity_transf(FF,p)` at `u`.
2. The candidate RHS is the fibre component of the total action:

   ```text
   sigma_Snd(sigma_map_transport_arrow(FF,p,u))
   ```

   or a stable wrapper over that expression if the transparent Sigma term
   unfolds too early.
3. If the current `sigma_map_func` action strictifies canonical arrows and only
   produces identity/cartesian components, document that as a limitation of the
   present strict Sigma-map action. In that case, introduce a separate stable
   extraction head whose eventual definition is the full omega/Sigma action,
   and keep Pi-specific computation as a fold from that head.
4. Do not add more Pi-only primitive facts until the generic component
   extraction path has been probed.

## 2026-05-29 Implementation Update: Sigma-Total Fibre Extraction Helper

The first extraction-layer helper was implemented:

```text
sigma_map_transport_fibre_arrow(FF,p,u)
  := sigma_Snd(sigma_map_transport_arrow(FF,p,u)).
```

Its type is the component-level comparison between the two displayed route
objects:

```text
D[p](FF[x](u)) -> FF[y](E[p](u)).
```

Equivalently, it is the fibre component of the current total action
`Sigma(FF)` on the canonical total transport arrow:

```text
sigma_transport_arrow(E,p,u) : (x,u) -> (y,E[p](u)).
```

A focused regression assertion checks the definitional extraction:

```text
sigma_map_transport_fibre_arrow(FF,p,u)
  = sigma_Snd(sigma_map_transport_arrow(FF,p,u)).
```

Important probe result:

- A generic rewrite

  ```text
  tapp0_fapp0(functord_laxity_transf(FF,p),u)
    -> sigma_Snd(sigma_map_transport_arrow(FF,p,u))
  ```

  typechecked.
- However, the direct Pi/path specialization

  ```text
  sigma_Snd(sigma_map_transport_arrow(PathOutPi_funcd,p,E))
    = PathIndTgt_transport_func(p,E)
  ```

  did not reduce.

Therefore the generic rewrite was not promoted. Promoting it would make the
generic total-extraction normal form compete with the existing Pi-specific
`functord_laxity_transf` normal form without proving that the two join.

Interpretation: the current `sigma_map_func` action is still the strict/capped
total-map action. It can expose the fibre component of the image of a
canonical total arrow, but this is not yet the fuller lax/off-diagonal total
action needed to derive `section_pullback_transf(F)` for Pi. The next real
architecture step is to build that fuller action from the internal
off-diagonal packages (`tdapp1_int_*` / `fdapp1_int_transfd` style), then fold
its extracted component to `functord_laxity_transf`.

## 2026-05-29 Conceptual Settlement: Laxity, Sigma, And Internal Hom-Action

Follow-up review settled the conceptual architecture for laxity/coherence.
The short version is:

```text
conceptually settled, computationally not yet fully implemented.
```

There are two distinct layers which must not be confused.

First, `Sigma(FF)` is not the foundational source of laxity if its action is
itself defined using that laxity. Otherwise the design would be circular:

```text
Sigma(FF)(p,alpha) uses laxity(FF,p)
laxity(FF,p) is extracted from Sigma(FF)(canonical_arrow)
```

The non-circular architecture is:

```text
lower internal hom-action
  -> extracted laxity/coherence
  -> Sigma-map action consumes that laxity
  -> Sigma-total probes/benchmarks confirm the computation.
```

So the Sigma-total presentation remains important, but it is the
externalization/test surface where the laxity becomes visible as the second
component of a total arrow. It is not the primitive source of that same
laxity.

### Computational Shape

The computational primitive is not the textbook square directly. It is the
off-diagonal/skew accumulation idiom:

```text
action of g on eta_(f)  =>  eta_(action of g on f)
```

For an ordinary transfor

```text
eta : Transf(F,G)
eta_f := tapp1_fapp0(eta,f) : F[X] -> G[Y],
```

the codomain-side accumulation is:

```text
G[g] o eta_f  =>  eta_(g o f).
```

Here `G[g]` is implicit in the type of `eta`; it is recovered from the
codomain functor and the off-diagonal component. The textbook square

```text
G[p] o eta[x]  vs  eta[y] o F[p]
```

is semantically correct, but it is not the best normalization driver. The
normalization driver should be the skew/off-diagonal component and the chosen
accumulation convention.

For displayed/Cat-valued functors this specializes to:

```text
FF[p] := tapp1_fapp0(FF,p) : E[x] -> D[y]

D[p] o FF[x]      -- one accumulated route
FF[y] o E[p]      -- the other accumulated route
```

and the desired displayed laxity cell is:

```text
functord_laxity_transf(FF,p)
  : Transf(
      D[p] o FF[x],
      FF[y] o E[p]).
```

### The Failed Direct Sigma Extraction

The earlier generic component rewrite

```text
tapp0_fapp0(functord_laxity_transf(FF,p),u)
  -> sigma_Snd(sigma_map_transport_arrow(FF,p,u))
```

typechecked, but the Pi/path specialization did not reduce:

```text
sigma_Snd(sigma_map_transport_arrow(PathOutPi_funcd,p,E))
  != PathIndTgt_transport_func(p,E).
```

The reason is now clear. The current `sigma_map_func` action is the strict
Sigma-map action:

```text
Sigma(FF)(p,alpha) = (p, FF[y](alpha)).
```

For a canonical/cartesian total arrow, `alpha` is an identity. Therefore the
current action sees essentially:

```text
FF[y](id)
```

and any boundary mismatch has already been made convertible by existing
strict/object-level folds. This loses the nontrivial comparison

```text
D[p](FF[x](u)) -> FF[y](E[p](u)).
```

For the Pi/path case, the failed normal form was identity-like action on the
already transported motive, while the desired normal form is the actual
section pullback:

```text
section_pullback_func(PathOut_transport_func(p), E).
```

### Successful Cheap Probe

A disposable temporary-file probe tested the downstream design by assuming the
middle laxity object exists.

The probe changed the Sigma-map arrow action shape to:

```text
Sigma(eta)(p, alpha)
  -> (p, eta[y](alpha) o laxity(eta,p)[u])
```

instead of the current strict shape:

```text
Sigma(eta)(p, alpha)
  -> (p, eta[y](alpha)).
```

The probe then added the Pi-specific laxity fold:

```text
laxity(Pi_pullback_funcd(G), p)
  -> section_pullback_transf(G[p])
```

and a focused identity cleanup rule:

```text
Pi_func(K)[id_funcd(E)] -> id_func(Pi_cat(E)).
```

The identity cleanup is needed because generic strict functoriality matches
`@id`, while this file often keeps the stable displayed-identity head
`id_funcd` visible.

With these temporary changes, the target assertion passed:

```text
sigma_Snd(sigma_map_transport_arrow(PathOutPi_funcd,p,E))
  == PathIndTgt_transport_func(p,E).
```

Both sides computed to:

```text
section_pullback_func(PathOut_transport_func(p), E).
```

This confirms that the downstream Sigma/Pi computation is feasible once the
correct laxity component is available. The same probe also confirmed the cost:
old assertions that rely on all Sigma maps being strict/cartesian fail unless
the relevant constructors are separately marked strict. In particular, the
fixed-x path transitivity benchmarks through representable transport depend on
strict behavior and will need strict markers/folds for representable or
otherwise strict constructions.

### Non-Circular Source Of Displayed Laxity

The likely source of displayed functor laxity is the existing internal
displayed hom-action:

```text
fdapp1_int_transfd(FF)
  : Transfd(
      homd_int(id_E),
      homd_int(FF) o Op_funcd(FF)).
```

This is the v3.2 analogue of the emdash2 `fapp1_funcd` idea. It says that a
displayed functor acts on dependent homs/triangles. Applying this to a
canonical/cartesian source triangle should produce the non-cartesian target
triangle whose fibre component is exactly the displayed laxity/coherence cell.

Pseudo-sketch:

```text
canonical_triangle(E,p,u)
  : homd_int(id_E) ...
  -- represents E[p](u) from u over p

fdapp1_int_transfd(FF)(canonical_triangle(E,p,u))
  : homd_int(FF)(...)
  -- target triangle under FF

extract second/fibre component:
  D[p](FF[x](u)) -> FF[y](E[p](u)).
```

Then package this naturally in `u`:

```text
functord_laxity_transf(FF,p)
  : Transf(
      D[p] o FF[x],
      FF[y] o E[p]).
```

Only after that should Sigma action consume the laxity:

```text
Sigma(FF)(p,alpha)
  = (p, FF[y](alpha) o functord_laxity_transf(FF,p)[u]).
```

Current status:

```text
Implemented heads exist:
  fdapp1_int_transfd
  tdapp1_int_fapp0_transfd
  homd_int projection cascade

Missing:
  the focused projection rule/defined helper extracting
  functord_laxity_transf(FF,p) from fdapp1_int_transfd(FF).
```

Therefore the next real design task is not:

```text
extract laxity from Sigma map.
```

It is:

```text
extract laxity from internal displayed hom-action,
then let Sigma map consume that laxity.
```

### Ordinary Functors And Transfors

The same conceptual story is not restricted to `Cat_cat`.

For an ordinary functor

```text
F : Functor A B
```

the relevant package is the ordinary internal hom-action:

```text
fapp1_int_transf(F)
  : Transf(
      hom_int(id_A),
      hom_int(F) o Op_func(F)).
```

This is the Yoneda/hom-presheaf move: even if `B` is arbitrary, the homs of
`B` are categories, so `Cat_cat` appears after applying:

```text
Hom_B(FX, -) : B -> Cat.
```

Then lax functoriality is extracted by applying this internal action to
canonical triangles in the representable total:

```text
f : X -> Y
g : Y -> Z
canonical triangle: f -> g o f
```

and the image gives the cell:

```text
F[g] o F[f] => F[g o f].
```

For an ordinary transformation

```text
eta : Transf(F,G),
```

the relevant package is:

```text
tapp1_int_fapp0_transf(eta)
  : Transf(
      hom_int(id_A),
      hom_int(G) o Op_func(F)).
```

Its off-diagonal component is:

```text
eta_f : F[X] -> G[Y],
```

and its lax/naturality accumulation cells are:

```text
G[g] o eta_f => eta_(g o f)
eta_f o F[h] => eta_(f o h).
```

So ordinary laxness should be expressed through
`tapp1_int_*` / `fapp1_int_transf`, not primarily through the special
identification:

```text
Functord_cat = Transf_cat(_, Cat_cat, ...).
```

The terminal-base viewpoint remains useful but is not the foundational source
by itself. If an ordinary functor is viewed as a displayed functor over
`Terminal_cat`, the terminal base has no nontrivial base arrows. The
nontrivial data `f : X -> Y` and `g : Y -> Z` lives inside the fibre category
`A`, so the internal hom/Yoneda construction is still needed to expose it.
With enough `Lift_catd`/constant-family bridge rules, the terminal-base route
should recover the ordinary route, but v3.2 does not yet implement that bridge
fully.

For displayed functors, the analogue is:

```text
fdapp1_int_transfd(FF).
```

For displayed transformations, the analogue is:

```text
tdapp1_int_fapp0_transfd(epsilon).
```

Thus the current implementation gap is not that laxness is mathematically
unclear. The gap is:

```text
We have the internal action heads,
but we have not yet exposed the projection/extraction rules that turn them
into the concrete laxity cells needed by Sigma/Pi computation.
```

### Strictness Status And Future Split

The current v3.2 file still has global strict rewrite rules for ordinary
functoriality and ordinary transfor accumulation. These were useful temporary
conveniences for early normalization, but they collapse some coherence data too
early for the present Pi/internalized-family milestone.

The future architecture should follow the emdash2-style split:

```text
Functor / Transf                  general, possibly lax
StrictFunctor / StrictTransf      extra structure or marked projections
```

and similarly for displayed functors/transformations where needed. Strict
computation rules should move to strict projections or known strict
constructors. Pi supplies a genuinely nontrivial laxity component:

```text
section_pullback_transf(F).
```

Representable transport and other strict constructions should be explicitly
marked so their laxity collapses to identity/cartesian behaviour.

### Implementation SOP From This Settlement

When this architecture is implemented in `emdash3_2.lp`, the file itself must
carry self-contained comments explaining the settled mathematics and
normalization discipline. Future readers should not need this report to know:

- why laxity is extracted from internal hom-action rather than from Sigma
  action;
- why Sigma action consumes a laxity prefix;
- why Pi laxity computes to `section_pullback_transf`;
- why ordinary functor/transfor laxness is expressed through
  `fapp1_int_transf` / `tapp1_int_fapp0_transf`;
- why strict constructors need explicit markers/folds once global strictness is
  relaxed.

Concrete next implementation recommendations:

1. Add the internal-hom-action extraction helper/rule that produces
   `functord_laxity_transf(FF,p)` from `fdapp1_int_transfd(FF)`.
2. Keep `functord_laxity_transf` as an interface only until that extraction
   helper is stable; then make it defined or folded from the extraction path.
3. Revise Sigma-map arrow action to include the laxity prefix:

   ```text
   Sigma(FF)(p,alpha)
     = (p, FF[y](alpha) o functord_laxity_transf(FF,p)[u]).
   ```

4. Add focused strictness collapses for known strict constructions, especially
   representables/pathout transport, before replacing the current strict Sigma
   action globally.
5. Add the focused `Pi_func(id_funcd)` identity cleanup if the implementation
   keeps `id_funcd` visible in Pi action normal forms.
6. Keep arbitrary Sigma-arrow action and full omega `fapp1_func` Sigma
   coherence scoped to concrete downstream needs.

## Validation

The implementation was probed in a temporary copy before being applied to
`emdash3_2.lp`.

Commands run successfully:

```bash
timeout 60s lambdapi check -w emdash3_2.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
git diff --check
```

Documentation-only update after the conceptual-settlement review:

```bash
git diff --check
```

## Remaining Work

- Build the fuller lax/off-diagonal total-action extraction from the existing
  internal displayed hom-action packages (`tdapp1_int_*` /
  `fdapp1_int_transfd`). The target is a derived/folded path:

  ```text
  fdapp1_int_transfd(FF) applied to canonical_triangle(E,p,u)
    -> functord_laxity_transf(FF,p)[u].
  ```

  Once the Pi instance joins with `section_pullback_func(F,E)`, replace the
  current Pi-specific `functord_laxity_transf` folds by this derived path where
  feasible.
- Revise Sigma-map arrow action only after the extraction path is stable. The
  desired normal form is:

  ```text
  Sigma(FF)(p,alpha)
    = (p, FF[y](alpha) o functord_laxity_transf(FF,p)[u]).
  ```

  Add strict collapses for representables and other known strict constructors
  before enabling this normal form globally.
- Keep ordinary functor/transfor laxness aligned with the non-displayed
  internal hom-action packages:

  ```text
  fapp1_int_transf(F)
  tapp1_int_fapp0_transf(eta).
  ```

  Do not try to use the terminal-base encoding alone as the foundational source
  of ordinary functoriality/naturality laxity.
- If a downstream theorem requires it, connect canonical Sigma-total transport
  for `Sigma_catd_functord_catd(Pi_pullback_funcd(G))` to the new
  `functord_laxity_transf(Pi_pullback_funcd(G),p)` projection. Keep this as a
  separate total-action theorem rather than a direct rule on the transparent
  `Sigma_catd_transport_func` alias.
- Expose more of the generic `Sigma_transfd_funcd` action/naturality only when
  a concrete downstream theorem needs it. The route-specific canonical
  transport helper has been removed; arbitrary Sigma-arrow action remains
  outside the immediate milestone.
- Continue the ordinary curry/uncurry pass only if a downstream theorem needs
  explicit Product/Functor adjunction coherence beyond the current functor-level
  beta/action laws.
- Audit downstream uses of constant-family Sigma to ensure they rely on the
  direct `Product_cat` normal form rather than reintroducing bridge symbols.
- Continue the primitive-to-defined audit, especially around ordinary
  off-diagonal action (`tapp1_fapp0`) and any remaining internalized packages
  that can be derived cleanly from smaller semantic constructors.
- Add further Sigma-map/Sigma-composition regression assertions only when a
  downstream theorem exposes a missing computation.
- Keep global coherent motive families deferred; they are not the core
  path-induction constructor.
