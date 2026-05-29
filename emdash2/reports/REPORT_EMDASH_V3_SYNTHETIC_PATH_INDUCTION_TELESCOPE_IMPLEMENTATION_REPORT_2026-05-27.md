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

## 2026-05-29 Current Latest Design: Laxity, Sigma, And Internal Hom-Action

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

## 2026-05-29 Decision-Complete Implementation Order

This section records the current recommended implementation order. It
supersedes earlier rough ordering notes in this report where they conflict.

Key decisions before implementation:

- Do **not** start by deleting the current global strict functoriality or
  naturality rewrite rules. Keep them during the next probes. The successful
  cheap probe did not require deleting those rules.
- The strictness problem first becomes operational when the Sigma-map action is
  changed from the current strict/cartesian action to the lax-prefix action.
  Therefore strictness collapses for known strict constructors must be prepared
  **before** promoting the revised Sigma-map action, not after.
- The focused rule

  ```text
  Pi_func(K)[id_funcd(E)] -> id_func(Pi_cat(E))
  ```

  is not a new mathematical axiom. It is the stable-head version of strict
  identity preservation for `Pi_func`. The generic strict functoriality rule
  matches an input written as `@id`; after normalization this file often keeps
  the displayed identity as the stable head `id_funcd`, so a focused bridge is
  needed unless `id_funcd` is redesigned to unfold differently.
- `functord_laxity_transf` should ultimately be defined or folded from the
  internal-hom extraction path. It should remain an interface only while that
  extraction is being stabilized.
- The future emdash2-style strict/lax split remains important, but it is not
  the first implementation move. First prove that the explicit laxity
  extraction and Pi/Sigma computation work locally.

Recommended phases:

1. **Document The Settlement In Code**

   Add a compact, self-contained comment block in `emdash3_2.lp` near the
   internal hom-action / `functord_laxity_transf` area. It should state the
   current design:

   ```text
   internal hom-action -> extracted laxity -> Sigma action consumes laxity
   ```

   It should also say that the current global strict rules are temporary and
   that strict constructors will be marked/folded explicitly as the lax layer
   is promoted.

2. **Add The Stable Identity Cleanup**

   Probe and then add the focused Pi identity bridge:

   ```text
   fapp1_fapp0(Pi_func(K), id_funcd(E)) -> id_func(Pi_cat(E)).
   ```

   This is low risk and was required by the successful cheap probe. Treat it as
   a strictness bridge for the visible `id_funcd` normal form.

3. **Build A Focused Internal-Hom Extraction Probe**

   In a temporary copy, introduce only stable helper heads needed to express the
   component extracted from:

   ```text
   fdapp1_int_transfd(FF)
   ```

   applied to a canonical/cartesian source triangle:

   ```text
   canonical_triangle(E,p,u).
   ```

   The target component is:

   ```text
   D[p](FF[x](u)) -> FF[y](E[p](u)).
   ```

   Do not revise Sigma action in this phase. The purpose is to isolate whether
   the existing `homd_int` projection cascade and `fdapp1_int_transfd` heads are
   sufficient to expose the desired component.

4. **Package The Extracted Component As Laxity**

   Once the component extraction typechecks, package it as the whole transfor:

   ```text
   functord_laxity_transf(FF,p)
     : Transf(D[p] o FF[x], FF[y] o E[p]).
   ```

   Preferred endpoint:

   ```text
   functord_laxity_transf(FF,p) := extracted_internal_hom_laxity(FF,p).
   ```

   If Lambdapi cannot yet build the whole `Transf` term directly, keep
   `functord_laxity_transf` as a stable head and add a focused projection/fold
   from the extracted internal-hom helper. Record the reason in comments.

5. **Make Pi Laxity Join Through The Extraction Path**

   Replace or justify the current Pi-specific folds by proving that the
   extracted route computes to:

   ```text
   functord_laxity_transf(Pi_pullback_funcd(G),p)
     -> section_pullback_transf(G[p]).
   ```

   Required regression:

   ```text
   tapp0_fapp0(functord_laxity_transf(PathOutPi_funcd,p),E)
     -> PathIndTgt_transport_func(p,E).
   ```

   Keep the existing Pi-specific fold temporarily until the extracted route
   joins, then either remove it or document it as a shortcut to the extracted
   normal form.

6. **Prepare Strict Constructor Collapses Before Sigma Revision**

   Before changing the Sigma-map action globally, add focused strict collapses
   for known strict constructions that old benchmarks rely on. The first likely
   targets are representable/pathout transport and any strict constructor used
   by fixed-x path transitivity.

   The goal is that for strict `FF`:

   ```text
   functord_laxity_transf(FF,p)[u]
     -> identity/cartesian component.
   ```

   This phase addresses the cheap-probe failure where old strict Sigma/path
   assertions broke after adding the laxity prefix.

7. **Revise Sigma-Map Arrow Action In A Temp Probe**

   Only after phases 4-6, change the Sigma-map action in a temporary file to:

   ```text
   Sigma(FF)(p,alpha)
     = (p, FF[y](alpha) o functord_laxity_transf(FF,p)[u]).
   ```

   Required probe assertions:

   ```text
   sigma_Snd(sigma_map_transport_arrow(PathOutPi_funcd,p,E))
     == PathIndTgt_transport_func(p,E)
   ```

   and the fixed-x strict transitivity/pathout assertions still join through
   the strict collapses from phase 6.

8. **Promote Sigma Revision And Regressions**

   Promote the revised Sigma-map action only after the temp probe passes.
   Add focused assertions for:

   ```text
   Pi/path laxity -> PathIndTgt_transport_func
   Sigma action with Pi -> section_pullback_func
   strict representable Sigma action -> old cartesian normal form
   ```

9. **Defer The Global Strict/Lax Split**

   After the above is stable, start a separate phase to move global strict
   functoriality/naturality rules behind explicit strict wrappers or strict
   constructor folds, following the emdash2-style design:

   ```text
   StrictFunctor_cat / sfunc_func
   Strict displayed functor/transfor variants
   ```

   This is deliberately not a prerequisite for the next implementation turn.
   The next turn should focus on the internal-hom extraction and local
   Sigma/Pi computation.

## 2026-05-29 Implementation Update: First Internal-Hom Extraction Stage

Implementation has started according to the decision-complete order above.

Completed in `emdash3_2.lp`:

- Added self-contained code comments near the internal displayed hom-action
  declarations documenting the current/latest architecture:

  ```text
  internal hom-action -> extracted laxity -> Sigma action consumes laxity.
  ```

- Added the focused stable displayed-identity bridge for Pi:

  ```text
  fapp1_fapp0(Pi_func(K), id_funcd(E))
    -> id_func(Pi_cat(E)).
  ```

  This was first probed in a temporary copy. It typechecked and was then
  promoted with a regression assertion. This rule is the visible-`id_funcd`
  form of strict identity preservation for `Pi_func`, not an additional
  mathematical axiom.

- Added the first concrete helper in the non-circular laxity extraction path:

  ```text
  functord_laxity_fdapp1_section_arrow(FF,x,u)
  ```

  Its definition is the component of:

  ```text
  fdapp1_int_transfd(FF)
  ```

  at the represented source `x` and source fibre object `u`, via
  `Fibre_transf_app`. Its type is an arrow in:

  ```text
  Fibre_cat(Homd_target_catd(E), x)
  ```

  from the identity dependent-hom section:

  ```text
  homd_src_sec(id_E,x,u)
  ```

  to the section obtained by first applying `FF[x]` to `u` and then using
  `homd_int(FF)`:

  ```text
  homd_src_sec(FF,x,FF[x](u)).
  ```

  This is not yet the whole laxity component

  ```text
  D[p](FF[x](u)) -> FF[y](E[p](u)).
  ```

  It is the first stable projection layer from which that component should be
  obtained by further projections at `y`, at `E[p](u)`, and at `p`.

Focused temporary probes:

- The first helper above typechecked quickly and was promoted.
- A second-stage helper that immediately projected at `y` while forcing fully
  reduced endpoint names timed out under a 60s Lambdapi check.
- A revised second-stage helper using less-reduced/raw endpoint terms also
  timed out under a 60s Lambdapi check.

Interpretation: the next extraction step should introduce additional stable
projection heads for the section-at-`y` and terminal-object evaluation layers,
rather than asking Lambdapi to solve the whole
`Pi_cat`/`Homd_target_section_catd`/terminal-source conversion in one
definition. This matches the standing SOP: use semantic definitions first, but
add stable heads when a focused probe shows real discrimination or performance
need.

## 2026-05-29 Implementation Update: Readable Section Projection Stack

Follow-up implementation tightened the first extraction stage and advanced one
projection layer.

Changes promoted to `emdash3_2.lp`:

- Rewrote the first internal-hom extraction helper in readable form. The active
  definition now uses small semantic aliases instead of fully explicit kernel
  applications:

  ```text
  homd_id_src_sec(E,x,u)
    = homd_int(id_E)[x](u)

  homd_ff_src_sec(FF,x,u)
    = homd_int(FF)[x](FF[x](u))

  functord_laxity_fdapp1_section_arrow(FF,x,u)
    = fdapp1_int(FF)[x,u]
  ```

- Added a semantic section-arrow component helper:

  ```text
  pi_hom_fapp0(eta,k) = eta[k] : s[k] -> t[k].
  ```

  This is a definition through the existing displayed component projection:

  ```text
  tapp0_fapp0(Terminal_obj, tdapp0_fapp0(k,eta)).
  ```

  No rewrite rule was added for `piapp0_func`. A temp probe with such a rule
  was rejected: `piapp0_func` is definable, and the rule both violated the SOP
  against definable LHS discriminators and led to timeout behavior.

- Added the second projection stage:

  ```text
  functord_laxity_fdapp1_tgt_arrow(FF,x,u,y)
    = fdapp1_int(FF)[x,u][y]
    : Homd_E(x,u,y,—)
        -> Homd_D(x,FF[x](u),y,FF[y](—)).
  ```

  This is still not the full laxity cell. It stops before choosing the fibre
  object `E[p](u)` and base arrow `p`.

- Added the third projection stage:

  ```text
  functord_laxity_fdapp1_presheaf_arrow(FF,x,u,y,v)
    = fdapp1_int(FF)[x,u][y][v]
    : Hom_E(E[-](u),v)
        -> Hom_D(D[-](FF[x](u)),FF[y](v)).
  ```

  This is still one step before the desired laxity component: the remaining
  projection must choose `v := E[p](u)` and then evaluate at the base arrow
  `p` and the canonical source triangle/identity.

Probe results:

- The readable first-stage helper and the second-stage `y` projection
  typechecked quickly in a temporary copy and were promoted.
- Initial third-stage attempts timed out or failed because the type used the
  readable-looking expression:

  ```text
  HomPresheaf_catd_func K
  ```

  But `K` is an implicit parameter of `HomPresheaf_catd_func`. Without `@`,
  Lambdapi parsed this as an explicit application and inferred the malformed
  head:

  ```text
  @HomPresheaf_catd_func ?K K
  ```

  A `type` query on the candidate body exposed this mismatch.
- The corrected ambient category is:

  ```text
  Fibre_cat(fapp0(@HomPresheaf_catd_func K,x),y).
  ```

  With this correction, and with the body written as an explicit
  `@tapp0_fapp0` application, the third-stage helper typechecked quickly and
  was promoted.

Current interpretation: the presheaf/object evaluation stage is no longer the
bottleneck. The actual next missing layer is the final canonical-triangle
evaluation:

```text
fdapp1_int(FF)[x,u][y,E[p](u)][p]
  : D[p](FF[x](u)) -> FF[y](E[p](u)).
```

This should again be probed with `type` queries first, because the corrected
`HomPresheaf_catd_func` issue shows that implicit-argument placement can easily
masquerade as a mathematical design problem.

## 2026-05-29 Implementation Update: Canonical Homd Endpoint Projection

Further review corrected the diagnosis above. The `@HomPresheaf_catd_func K`
implicit-argument issue was real, but the deeper root cause was architectural:
the extraction path crossed between two convertible views of the same category:

```text
Fibre_cat(HomPresheaf_Z(x), y)
```

and its canonical endpoint form:

```text
Functor_cat(Op_cat(Hom_cat K x y), Cat_cat).
```

Using the first view in the projection stack made later stages repeatedly ask
Lambdapi to rediscover the whole `HomPresheaf` classifier pipeline. Several
probes confirmed that adding rewrite rules against `HomPresheaf_catd_func` or
bridging from the fibre view to a `Transf` view is the wrong direction:

- direct bridge helpers from `Fibre_cat(HomPresheaf_Z(x),y)` to `Transf`
  timed out;
- a focused projection rule for `Presheaf_catd_func` would have required
  compound expressions in rewrite-rule source/target slots and still timed out;
- an evaluation functor

  ```text
  HomPresheaf_Z(x)[y] -> Cat
  ```

  typechecked by itself, but combining it with the third-stage arrow again
  forced large endpoint conversions.

The better design is to expose the canonical category earlier. This was probed
and promoted:

```text
homd_tgt_func(FF,x,u,y)
  : Fibre_cat(D,y) -> Functor_cat(Op_cat(Hom_cat K x y), Cat_cat)
```

instead of the older target:

```text
Fibre_cat(D,y) -> Fibre_cat(HomPresheaf_Z(x), y).
```

The readable aliases were then reordered and retargeted so that the stack from
the `y` projection onward stays in canonical functor-category form:

```text
homd_id_tgt_func(E,x,u,y)
  : E[y] -> ((x -> y)^op -> Cat)

homd_ff_tgt_func(FF,x,u,y)
  : E[y] -> ((x -> y)^op -> Cat)

functord_laxity_fdapp1_tgt_arrow(FF,x,u,y)
  : homd_id_tgt_func(E,x,u,y)
      -> homd_ff_tgt_func(FF,x,u,y)

functord_laxity_fdapp1_presheaf_arrow(FF,x,u,y,v)
  : homd_id_tgt_func(E,x,u,y)[v]
      -> homd_ff_tgt_func(FF,x,u,y)[v]
```

The fourth projection now typechecks quickly when its endpoints are written
through the stable endpoint constructor `homd_`:

```text
functord_laxity_fdapp1_hom_func(FF,p,u,v)
  : homd_(id_E,x,u,y,v)[p]
      -> homd_(FF,x,FF[x](u),y,v)[p].
```

This is the right normal form for this layer. It avoids forcing the simplified
fibre-hom category too early:

```text
Hom_{D[y]}(D[p](FF[x](u)), FF[y](v)).
```

That simplification remains valid but should be exposed by focused endpoint
assertions/folds only where a downstream theorem needs it.

A canonical source triangle was also promoted:

```text
homd_id_canonical_triangle(E,p,u)
  : homd_(id_E,x,u,y,E[p](u))[p]
```

with body:

```text
id_{E[p](u)}.
```

Important non-promotion:

```text
fapp0(
  functord_laxity_fdapp1_hom_func(FF,p,u,E[p](u)),
  homd_id_canonical_triangle(E,p,u))
```

still timed out when promoted as the raw cell. This shows the next missing
surface is not `HomPresheaf` normalization anymore; it is the object-action
surface for the fourth projection, or a staged endpoint/action helper that does
not unfold the whole fourth-stage definition during application.

Current next recommendation:

1. Keep the promoted canonical `homd_tgt_func` and fourth-stage hom functor.
2. Do not add rewrite rules on `HomPresheaf_catd_func` or other definable
   classifier pipelines.
3. Next probe a stable object-action layer for
   `functord_laxity_fdapp1_hom_func`, preferably still typed at the direct
   `homd_` endpoint.
4. Only after that object-action layer typechecks quickly, fold/package it as
   the component of `functord_laxity_transf(FF,p)`.

## 2026-05-30 Corrected Status: Stable Projection Ladder Toward Laxity

The latest review corrected the implementation diagnosis again. The canonical
`homd_tgt_func` endpoint change remains good, but the current promoted
`functord_laxity_fdapp1_*` helpers are still too definitional for the final
extraction architecture. In particular, trying to compute:

```text
fapp0(
  functord_laxity_fdapp1_hom_func(FF,p,u,E[p](u)),
  homd_id_canonical_triangle(E,p,u))
```

asks Lambdapi to unfold the fourth-stage helper and re-solve the whole
projection stack during object application. That is the wrong computational
surface. It explains the timeout and matches the older successful patterns:

```text
fib_cov_int -> fib_cov_src_func -> fib_cov_transf -> fib_cov_tapp0_func
homd_int    -> homd_src_func    -> homd_src_sec   -> homd_tgt_func -> homd_
```

Those developments use stable projection heads at each layer, with small folds
from the lower internal package toward the next normal-form head. The corrected
laxity extraction should follow the same SOP. The final head to reach is not a
large defined expression; it is the stable interface:

```text
functord_laxity_transf(FF,p)
  : D[p] o FF[x] => FF[y] o E[p].
```

Therefore the desired projection ladder is:

```text
fdapp1_int_transfd(FF)
  -> fdapp1/lax section component at (x,u)
  -> fdapp1/lax y-component
  -> fdapp1/lax v-component
  -> fdapp1/lax p-action
  -> component of functord_laxity_transf(FF,p) at u.
```

In current names, the intended normal-form sequence is:

```text
fdapp1_int_transfd(FF)
  -> functord_laxity_fdapp1_section_arrow(FF,x,u)
  -> functord_laxity_fdapp1_tgt_arrow(FF,x,u,y)
  -> functord_laxity_fdapp1_presheaf_arrow(FF,x,u,y,v)
  -> functord_laxity_fdapp1_hom_func(FF,p,u,v)
  -> tapp0_fapp0(functord_laxity_transf(FF,p),u).
```

The last step is only well-typed at the canonical choice:

```text
v := E[p](u),
source triangle := homd_id_canonical_triangle(E,p,u).
```

The orientation is important:

```text
extracted internal-hom action
  -> component of functord_laxity_transf(FF,p)
```

not:

```text
functord_laxity_transf(FF,p)
  -> giant internal-hom expression.
```

This keeps `functord_laxity_transf` as the stable normal form consumed by Pi
and Sigma rules. Pi-specific computation can then be stated as a small fold on
that stable head:

```text
functord_laxity_transf(Pi_pullback_funcd(G),p)
  -> section_pullback_transf(G[p]).
```

### Corrected Implementation Order

1. Keep `functord_laxity_transf` primitive/stable for now. Do not make it a
   transparent definition by the full internal-hom expression.
2. Refactor the current `functord_laxity_fdapp1_*` extraction path toward
   stable projection heads. Readable semantic aliases are acceptable for
   comments and assertions, but rewrite-rule discriminators should be stable
   lower-level heads (`tdapp0_fapp0`, `tapp0_fapp0`, `fapp1_fapp0`, etc.) and
   should fold toward the named projection heads.
3. Avoid rewrite rules whose left-hand side depends on definable helper heads
   or compound expressions in inferred source/target slots. This is the same
   rule hygiene used by the `homd_int` and `fib_cov_int` cascades.
4. Add a final stable object-action fold from the canonical-triangle
   application of the fourth-stage projection to:

   ```text
   tapp0_fapp0(functord_laxity_transf(FF,p),u).
   ```

   If the direct fold still times out, insert one more stable head for the raw
   canonical-triangle cell, then fold that raw cell to the laxity component.
5. Only after the generic component fold is stable, revisit the Pi-specific
   `section_pullback_transf` rules and the later Sigma-map lax-prefix action.
   The Sigma action must consume `functord_laxity_transf`; it must not be used
   as the source from which `functord_laxity_transf` is extracted.

Immediate implementation status after this correction:

- The current file typechecks.
- The canonical `homd_tgt_func` endpoint form should be kept.
- The `functord_laxity_fdapp1_*` projection heads should be promoted as stable
  heads along the same route instead of pushing large defined expressions
  further.
- The next validation target is a small assertion that the canonical-triangle
  projection folds to:

  ```text
  tapp0_fapp0(functord_laxity_transf(FF,p),u).
  ```

## 2026-05-30 Implementation Update: Component-To-Cell Orientation

The first corrected implementation step after the review has been promoted to
`emdash3_2.lp`.

Important correction to the previous section: the final generic fold should be
oriented from the `functord_laxity_transf` component to the extracted
internal-hom cell, not from the extracted cell back to the interface component.
The active normal form is now:

```text
tapp0_fapp0(functord_laxity_transf(FF,p),u)
  -> functord_laxity_fdapp1_cell(FF,p,u).
```

The extracted cell is a stable head:

```text
functord_laxity_fdapp1_cell(FF,p,u)
  : D[p](FF[x](u)) -> FF[y](E[p](u)).
```

It represents the canonical-triangle application of the fourth internal-hom
projection:

```text
fdapp1_int(FF)[x,u][y,E[p]u][p](id).
```

The first attempt deliberately did **not** add a rewrite whose left-hand side
matched either `homd_id_canonical_triangle(E,p,u)` or an explicit identity
term. At that time `homd_id_canonical_triangle` was still a transparent alias,
and a compute probe showed that the alias normalized generically to:

```text
id(E[y], E[p](u)).
```

However, rules keyed on a concrete `id` shape still produced slow conversion in
temporary probes, because the surrounding fourth-stage hom-action endpoint
forces Lambdapi to compare several reducible presentations of the same homd
object. Therefore the safe promoted step is to expose the stable cell head and
make the transfor component reduce to that head.

Pi-specific cell folds were added after `section_pullback_func` is declared:

```text
functord_laxity_fdapp1_cell(Pi_int_funcd,F,E)
  -> section_pullback_func(F,E)

functord_laxity_fdapp1_cell(Pi_pullback_funcd(G),p,E)
  -> section_pullback_func(G[p],E).
```

This preserves the existing Pi/path computations because:

```text
tapp0_fapp0(functord_laxity_transf(Pi_pullback_funcd(G),p),E)
  -> functord_laxity_fdapp1_cell(Pi_pullback_funcd(G),p,E)
  -> section_pullback_func(G[p],E).
```

Validation assertions added:

```text
tapp0_fapp0(functord_laxity_transf(FF,p),u)
  == functord_laxity_fdapp1_cell(FF,p,u)

functord_laxity_fdapp1_cell(Pi_int_funcd,F,E)
  == section_pullback_func(F,E)

functord_laxity_fdapp1_cell(Pi_pullback_funcd(G),p,E)
  == section_pullback_func(G[p],E).
```

Follow-up implementation added exactly that smaller stable identity API. The
symbol:

```text
homd_id_canonical_triangle(E,p,u)
  : homd_(id_E,x,u,y,E[p]u)[p]
```

is now a primitive stable head, analogous in role to `id_func` and `id_funcd`.
The first implementation avoided a global rewrite from plain
`id(E[y],E[p]u)` to this head, because an overly explicit probe changed an
existing Sigma-map transport assertion. A later SOP-clean probe found the
correct narrow left-hand side:

```text
id(E[y], fapp0(E[p],u))
  -> homd_id_canonical_triangle(E,p,u)
```

where the kernel shape leaves the source/target arguments of the inner
transport-object application implicit:

```text
rule @id
      (@fapp0 $K Cat_cat $E $y)
      (fapp0 (@fapp1_fapp0 $K Cat_cat $E $x $y $p) $u)
  -> homd_id_canonical_triangle(E,p,u).
```

This is not a rewrite for every identity in every fibre category. It is a
specific fold for the primitive projection normal form of the transported
object `E[p](u)`.

The fdapp1 fourth-stage action consumes this stable head:

```text
fapp0(
  functord_laxity_fdapp1_hom_func(FF,p,u,_),
  homd_id_canonical_triangle(E,p,u))
  -> functord_laxity_fdapp1_cell(FF,p,u).
```

This keeps the canonical triangle available as a real rewrite discriminator
without perturbing unrelated plain identity computations. The direct local
fdapp1 fallback rule on the explicit plain `id` was removed; the active route is
now:

```text
id(E[y],E[p]u)
  -> homd_id_canonical_triangle(E,p,u)
  -> functord_laxity_fdapp1_cell(FF,p,u)
```

The same probe clarified that the old assertion

```text
sigma_map_transport_arrow(eta,p,u)
  == sigma_transport_arrow(D,p,eta[x](u))
```

was not a harmless computation test. It asserted strict/cartesian preservation
of canonical transport by an arbitrary displayed functor. In the lax design that
is false in general: the image of the canonical source triangle should expose
the image of `homd_id_canonical_triangle`, and eventually the laxity cell.

The active assertion has therefore been replaced by the weaker and correct
normal form:

```text
sigma_map_transport_arrow(eta,p,u)
  == sigma_arrow(
       p,
       eta[y][homd_id_canonical_triangle(E,p,u)])
```

where the source/target object mismatch is handled by the existing Cat-valued
object-level naturality folds.

The corresponding fibre-component sanity assertion now also checks:

```text
sigma_map_transport_fibre_arrow(FF,p,u)
  == FF[y][homd_id_canonical_triangle(E,p,u)].
```

The stable projection-head refactor for the earlier fdapp1 stages was then
promoted as well:

```text
tdapp0/tapp0 projections of fdapp1_int_transfd(FF)
  -> functord_laxity_fdapp1_section_arrow
  -> functord_laxity_fdapp1_tgt_arrow
  -> functord_laxity_fdapp1_presheaf_arrow
  -> functord_laxity_fdapp1_hom_func.
```

The active final extraction route is now:

```text
fapp0(
  functord_laxity_fdapp1_hom_func(FF,p,u,_),
  homd_id_canonical_triangle(E,p,u))
  -> functord_laxity_fdapp1_cell(FF,p,u)

tapp0_fapp0(functord_laxity_transf(FF,p),u)
  -> functord_laxity_fdapp1_cell(FF,p,u)
```

This completes the currently scoped generic component extraction surface without
installing a broad global bridge from arbitrary plain `id` terms to the
homd-specific canonical triangle.

Follow-up identity probe:

The earlier failed `id` probe was too explicit: it used `Fibre_cat` /
`catd_transport_func` or explicit source/target arguments for the nested
transport-object application. A corrected SOP-clean probe succeeded by matching
the primitive projection shape directly:

```text
fapp0(
  functord_laxity_fdapp1_hom_func(FF,p,u, fapp0(E[p],u)),
  id(E[y], fapp0(E[p],u)))
  -> functord_laxity_fdapp1_cell(FF,p,u).
```

In kernel shape, the nested object action leaves source/target inference
implicit:

```text
fapp0 (@fapp1_fapp0 K Cat_cat E x y p) u
```

not:

```text
@fapp0 (E[x]) (E[y]) (@fapp1_fapp0 K Cat_cat E x y p) u.
```

This was later generalized one step: the same SOP-clean identity shape now
folds directly to `homd_id_canonical_triangle`, and the fdapp1 fourth-stage
context reaches the extracted laxity cell through that canonical head.

Identity-normal-form caveat:

The fold above handles the primitive `@id` normal form whose category is still
visible as `fapp0(K,Cat_cat,E,y)` and whose object is still visible as
`fapp0(E[p],u)`. It does not settle every identity presentation that can arise
after further computation. Depending on the family and endpoint category,
ordinary identities may reduce to specialized heads such as:

```text
id_func
id_funcd
id_transfd          (future/when present)
```

or to constructor-specific identity forms for `Cat_cat`, `Catd_cat`,
`Functor_cat`, `Transf_cat`, and related classifiers. If a future projection
appears not to consume the canonical triangle, check first whether the source
triangle has normalized past the primitive `@id` shape into one of these
specialized identity heads.

The preferred repair is not a broad global rewrite from every specialized
identity back to `homd_id_canonical_triangle`. Use a focused probe and add a
narrow consumer-local simulation/fold rule only where the expected endpoint is
the transported dependent-hom source shape:

```text
homd_(id_E,x,u,y,E[p]u)[p].
```

This keeps identity bridges typed by the local semantic context and avoids
perturbing unrelated identity computations.

## 2026-05-30 Implementation Update: Internal-Hom Extraction Regressions

The displayed internal-hom extraction path is now guarded by focused
stage-by-stage assertions in `emdash3_2.lp`.

The checked ladder is:

```text
Fibre_transf_app(fdapp1_int_transfd(FF),x,u)
  == functord_laxity_fdapp1_section_arrow(FF,x,u)

tapp0_fapp0(
  tdapp0_fapp0(y, functord_laxity_fdapp1_section_arrow(FF,x,u)),
  *)
  == functord_laxity_fdapp1_tgt_arrow(FF,x,u,y)

tapp0_fapp0(
  functord_laxity_fdapp1_tgt_arrow(FF,x,u,y),
  v)
  == functord_laxity_fdapp1_presheaf_arrow(FF,x,u,y,v)

fapp1_fapp0(
  fapp0_func(p),
  functord_laxity_fdapp1_presheaf_arrow(FF,x,u,y,v))
  == functord_laxity_fdapp1_hom_func(FF,p,u,v)
```

At the canonical transported endpoint, the extracted internal-hom action now
joins with the displayed-laxity component:

```text
fapp0(
  functord_laxity_fdapp1_hom_func(FF,p,u,E[p]u),
  homd_id_canonical_triangle(E,p,u))
  == tapp0_fapp0(functord_laxity_transf(FF,p),u)
```

Both sides reduce to the stable cell:

```text
functord_laxity_fdapp1_cell(FF,p,u).
```

This is not yet a constructor/eta principle for the whole transfor
`functord_laxity_transf(FF,p)`, but it gives the intended computational bridge
at the component level: the lower internal hom-action and the public laxity
interface now have a checked common normal form.

Probe note:

The readable assertion

```text
tapp0_fapp0 v (functord_laxity_fdapp1_tgt_arrow ...)
```

timed out. The issue was not mathematical: Lambdapi had to reconstruct too many
implicit projection parameters. A follow-up probe confirmed that the
`functord_laxity_fdapp1_tgt_arrow` head itself should be typed in the reduced
consumer-facing form:

```text
Transf(
  homd_id_tgt_func(E,x,u,y),
  homd_ff_tgt_func(FF,x,u,y)).
```

That change was promoted. However, the fully readable assertion can still time
out, so the promoted regression fixes the source category, target category, and
endpoint functors explicitly in canonical form:

```text
tapp0_fapp0
  (Fibre_cat E y)
  (Functor_cat (Op_cat (Hom_cat K x y)) Cat_cat)
  (homd_id_tgt_func(E,x,u,y))
  (homd_ff_tgt_func(FF,x,u,y))
  v
  (functord_laxity_fdapp1_tgt_arrow(FF,x,u,y)).
```

This follows the SOP distinction: rewrite-rule LHSs should avoid brittle
compound source/target slots, but focused assertions may spell out canonical
source/target slots to prevent conversion search from exploding.

The same probe also tested changing `functord_laxity_fdapp1_presheaf_arrow` to
the reduced `Transf` spelling. That was not promoted: the file timed out,
because the next consumer of that head is the evaluation functor action
`fapp1_fapp0(fapp0_func(p), ...)`, where the `Hom(Functor_cat(...),...)`
surface is the better computational interface. The guideline is therefore:
write intermediate symbol types in the reduced/computer form expected by their
next projection consumer, but do not globally reduce every `Hom(Functor_cat)`
presentation.

## 2026-05-30 Implementation Update: Pi Laxity Keeps Whole Transfors

A cleanup probe briefly removed the whole-transfor Pi-specific folds:

```text
functord_laxity_transf(Pi_int_funcd,F)
  -> section_pullback_transf(F)

functord_laxity_transf(Pi_pullback_funcd(G),p)
  -> section_pullback_transf(G[p]).
```

The file still typechecked after also removing the old whole-transfor
assertions, because the Pi/path transport computations already go through the
generic component route:

```text
tapp0_fapp0(functord_laxity_transf(Pi_int_funcd,F),E)
  -> functord_laxity_fdapp1_cell(Pi_int_funcd,F,E)
  -> section_pullback_func(F,E)

tapp0_fapp0(functord_laxity_transf(Pi_pullback_funcd(G),p),E)
  -> functord_laxity_fdapp1_cell(Pi_pullback_funcd(G),p,E)
  -> section_pullback_func(G[p],E).
```

However, the removal was not promoted. For Pi, the whole-transfor fold is the
better architectural normal form: it records the full naturality/coherence
transfor, not only its object component. The active file therefore keeps both
levels:

```text
functord_laxity_transf(Pi_int_funcd,F)
  -> section_pullback_transf(F)

functord_laxity_transf(Pi_pullback_funcd(G),p)
  -> section_pullback_transf(G[p])

tapp0_fapp0(functord_laxity_transf(...),E)
  -> functord_laxity_fdapp1_cell(...)
  -> section_pullback_func(...,E).
```

The whole folds preserve functoriality/naturality structure. The component/cell
assertions remain useful regressions showing that the internal hom-action route
and the public Pi laxity transfor have the same component normal form.

## 2026-05-29 Implementation Update: Lax Sigma-Map Arrow Action

The Sigma-map arrow action has now been revised from the old strict/cartesian
shape to the lax-prefix shape:

```text
Sigma(FF)(p,alpha)
  = (p, FF[y](alpha) o functord_laxity_transf(FF,p)[u]).
```

The direct rule with the full raw composite
`comp_fapp0(FF[y](alpha), laxity(FF,p)[u])` in the RHS was probed first. It is
mathematically the intended formula, but it timed out under a bounded
Lambdapi check. The promoted implementation therefore factors the fibre
component through a stable head:

```text
sigma_map_fibre_arrow(FF,p,u,alpha)
```

with surface reading:

```text
FF[y][alpha] o laxity(FF,p)[u].
```

The capped Sigma-map rule now constructs:

```text
sigma_arrow(p, sigma_map_fibre_arrow(FF,p,u,alpha)).
```

For the canonical transport case, the stable fibre action reduces to the
already checked displayed-laxity cell:

```text
sigma_map_transport_fibre_arrow(FF,p,u)
  == functord_laxity_fdapp1_cell(FF,p,u).
```

A diagnostic `compute` probe showed that representable transport normalizes
past the readable `Rep_catd_func` / `Rep_catd` aliases to the internal
`hom_int(id)` / `hom_` presentation. Rather than matching that raw normalized
shape in later rules, the implementation now introduces a stable
representable-transport head:

```text
Rep_transport_func(p) : Rep_Z(y) -> Rep_Z(x)
Rep_transport_func(p)[z][q] = q o p.
```

The normalized internal hom-action folds to this head, and its fibre component
folds to `hom_precomp_func`. Strict/cartesian representable behaviour is then
recorded by focused rules keyed on `Rep_transport_func`, with family slots left
implicit. This avoids rewrite rules with large compound expressions in
implicit argument positions.

The fixed PathOut/rho regression still computes: the image of the canonical
rho transport under representable precomposition reduces to the identity at
the composite arrow:

```text
id_{q o p} : Hom_Z(x,z)(q o p, q o p).
```

Successful probe and promotion checks:

```bash
timeout 60s lambdapi check -w tmp/emdash3_2_sigma_probe.lp
timeout 60s lambdapi check -w emdash3_2.lp
```

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

- Continue from the now-checked component-level bridge from internal hom-action
  to displayed laxity. The currently promoted policy is: keep whole-transfor
  folds when they express real constructor-level naturality/coherence, and keep
  component/cell assertions to verify their object-level normal forms:

  ```text
  fdapp1_int_transfd(FF) applied to canonical_triangle(E,p,u)
    == functord_laxity_transf(FF,p)[u]
    == functord_laxity_fdapp1_cell(FF,p,u).
  ```

  The Pi-specific whole-`functord_laxity_transf` folds are kept because they
  expose the full `section_pullback_transf` naturality object.
- Sigma-map arrow action has been revised to the stable lax-prefix normal form:

  ```text
  Sigma(FF)(p,alpha)
    = (p, FF[y](alpha) o functord_laxity_transf(FF,p)[u]).
  ```

  Continue adding focused strict collapses for other known strict constructors
  only when downstream regressions expose a missing computation. The first
  representable/pathout collapse is now keyed on `Rep_transport_func`.
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
