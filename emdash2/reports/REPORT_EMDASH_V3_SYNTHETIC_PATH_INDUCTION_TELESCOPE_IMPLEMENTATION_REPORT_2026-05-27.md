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

`Product_cat` is not currently reintroduced in v3.2. The foundations report
already records the intended relation:

```text
Sigma_cat(Const_catd K A)  ~  Product_cat K A.
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
3. Relate or at least document `Product_cat K A` against
   `Sigma_cat(Const_catd K A)`.
4. Return to `Sigma_transfd_funcd` and try to derive more of its action and
   naturality from the smaller ordinary and dependent infrastructure.
5. Keep global coherent motive families deferred until the generic uncurrying
   and comprehension action layer is stable.

## 2026-05-28 Implementation Update: Product Warm-Up

The first two items in the refined order above have now been implemented in
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

Added an object-level ordinary curry/uncurry scaffold:

```text
curry(F)[x][y] = F[(x,y)]
uncurry(G)[(x,y)] = G[x][y]
uncurry(curry(F))[(x,y)] = F[(x,y)]
curry(uncurry(G))[x][y] = G[x][y]
```

This is intentionally not the final most-internal product/functor adjunction
package. In particular, the full omega-action:

```text
fapp1_func(curry(F))
fapp1_func(uncurry(G))
```

is not implemented yet. The current scaffold only validates object-level beta
behavior and the two object-level round trips.

The curry/uncurry arrow-action laws should be probed later as a focused pass,
because the natural formula for `uncurry(G)[(f,g)]` uses both transfor
components and functor action:

```text
G[x'][g] o G[f][y].
```

Added bridge functors between ordinary products and constant-family Sigma
totals:

```text
Product_to_const_sigma_func    : Product_cat K A -> Sigma_cat(Const_catd K A)
const_sigma_to_Product_func    : Sigma_cat(Const_catd K A) -> Product_cat K A
```

These compute on objects and capped 1-arrow actions. They are intentionally not
a definitional identification between `Product_cat K A` and
`Sigma_cat(Const_catd K A)`.

The next natural implementation step is to probe the full `fapp1_func` action
for ordinary curry/uncurry, then return to more generic `Sigma_transfd_funcd`
action/naturality.

## Validation

The implementation was probed in a temporary copy before being applied to
`emdash3_2.lp`.

Commands run successfully:

```bash
timeout 60s lambdapi check -w emdash3_2.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
git diff --check
```

## Remaining Work

- Expose more of the generic `Sigma_transfd_funcd` action/naturality only when
  a concrete downstream theorem needs it.
- Continue the ordinary curry/uncurry pass by probing the missing full
  `fapp1_func` action laws and a more-internal adjunction-style packaging.
- Strengthen the product/Sigma constant-family bridge only if a downstream
  theorem requires more than the current object and capped-arrow bridge
  functors.
- Continue the primitive-to-defined audit, especially around ordinary
  off-diagonal action (`tapp1_fapp0`) and any remaining internalized packages
  that can be derived cleanly from smaller semantic constructors.
- Add further Sigma-map/Sigma-composition regression assertions only when a
  downstream theorem exposes a missing computation.
- Keep global coherent motive families deferred; they are not the core
  path-induction constructor.
