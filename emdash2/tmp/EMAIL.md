I would like to announce an expanded v3.2 draft of **emdash**, a Lambdapi formalization and prototype proof assistant aimed at functorial programming with strict/lax higher ω-categorical structure (fully internalized and computational, in the style of Kosta Došen's cut-elimination techniques). I believe it points to a high-stakes research programme at the intersection of dependent type theory and category theory, potentially on a scale comparable to homotopy type theory:

https://github.com/hotdocx/emdash/blob/main/docs/emdash3_2.pdf
https://github.com/hotdocx/emdash/blob/main/emdash2/emdash3_2.lp

The basic construction underneath the draft is the directed dependent hom. For a category-valued family

```
E : K ⊢ Cat
```

where `⊢` denotes a functor category, and fixed data `x : K`, `u : E[x]`, emdash forms a functorial object

```
homd_E(x,u)
  : Π(y : K^op), E[y^-] ⊢_[y] (Hom_K(x,y)^op ⊢ Cat)
```

Here `⊢_[y]` is the mixed-variance displayed version of `⊢`, and `y^-` marks that the `E`-argument occurs contravariantly. Its value at `y`, `v : E[y]`, and `f : x → y` is

```
Hom_{E[y]}(E[f](u),v).
```

This is also what organizes arrows in Sigma totals:

```
Hom_{ΣE}((x,u),(y,v))
  = Σ(f : x → y), Hom_{E[y]}(E[f](u),v).
```

The motivating example is the familiar shape of path induction in dependent type theory. For a category `Z` and an object `x : Z`, replace paths out of `x` by the outgoing-arrow category, i.e. the coslice/undercategory

```
x ↓ Z = Σ(y : Z), Hom_Z(x,y).
```

The object `(x,id_x)` is initial in `(x ↓ Z)`. For `a = (y,p)`, the canonical arrow `(x,id_x) → a` is `p` itself. Thus, for a motive

```
E : (x ↓ Z) ⊢ Cat
```

and `u : E((x,id_x))`, fixed-source directed induction has the expected section

```
Ind_x(E,u) : Π(a : (x ↓ Z)), E(a)

Ind_x(E,u)(y,p) = E(p)(u).
```

Write `Rep_Z(t)` for the covariant representable `Hom_Z(t,-)`. For the composition motive

```
E[(y,p)] ≔ Rep_Z(y) ⊢ Rep_Z(x)
```

with initial datum `id : Rep_Z(x) ⊢ Rep_Z(x)`, this computes to ordinary composition: for `p : x → y` and `q : y → z`,

```
Ind_x(E,id)[(y,p)][z][q] ↝ q ∘ p.
```

In the current kernel the runtime owner for this reduction is the hom-action cut

```
hom_postcomp_fapp0(id_Z,q,p),
```

while the ordinary composition presentation remains available as the typed proof-time view

```
comp_fapp0(q,p).
```

The new phenomenon appears when the source object `x` itself is internalized. For an arrow `r : x → y`, precomposition gives

```
r^* : (y ↓ Z) ⊢ (x ↓ Z)

r^*(z,q : y → z) = (z,q ∘ r).
```

Once induction is internalized as a construction varying in `x`, the target `Π`/section-taking construction

```
x ↦ (E ↦ Π(a : (x ↓ Z)), E(a))
```

is itself a displayed construction over the moving source object `x`. Its transport/comparison along `r` is not the identity; it is the section-pullback functor

```
Π(a : (x ↓ Z)), E(a)
  ⊢
Π(b : (y ↓ Z)), E(r^*(b))
```

sending `s` to `b ↦ s(r^*(b))`.

The expanded draft now also contains checked slices of a larger profunctor calculus. A Cat-valued profunctor is represented as

```
Prof(A,B) = A^op × B ⊢ Cat.
```

The kernel includes representables `Hom_prof_along(F,G)`, reindexing, shaped profunctor cells, a symbolic tensor `Prof_tensor`, fixed tensor action `Prof_tensor_func`, co-Yoneda maps, and covariant/contravariant internal homs with eval/lambda cancellation. Weighted limits are expressed as profunctor representability:

```
WeightedLimit_cov(F,W,L)
  = ProfComparison(Prof_imply_cov(Hom_prof(F),W), Hom_prof(L)).
```

With that interface, right adjoints preserve weighted limits by composing three checked profunctor comparisons: inverse adjunction mate, reindexing of the given limit comparison along the left adjoint, and the mate at the candidate limit. The dual theorem that left adjoints preserve weighted colimits is obtained by opposite normalization, not by duplicating the proof. There is also a primitive directed-inductive join category with two inclusions and one internally natural cross cell.

The supporting MathOps/DevOps layer has grown as well: the repository now has a check catalog, warning summaries, health reports, rewrite-LHS audits, and an "Infinity Codex" final-response archive used only as recovery evidence after interruptions or context compaction.

This is the lax naturality / functoriality layer exposed by the internalized formulation of directed path induction, now connected to a checked profunctor, tensor, weighted-limit, duality, and join calculus in `emdash` v3.2. I would be very interested to know whether this phenomenon has an established name or prior formulation in categorical logic, HoTT, or higher category theory.
