I would like to announce a new v3.2 draft of **emdash**, a Lambdapi formalization and prototype proof assistant aimed at functorial programming with lax higher ω-categorical structure (fully internalized and computational, in the style of Kosta Došen's cut-elimination techniques). I believe it points to a high-stakes research programme at the intersection of dependent type theory and category theory, potentially on a scale comparable to homotopy type theory:

https://github.com/hotdocx/emdash/blob/main/docs/emdash3_2.pdf
https://github.com/hotdocx/emdash/blob/main/emdash2/emdash3_2.lp

The basic construction underneath the draft is the directed dependent hom. For a category-valued family

```
E : K → Cat
```

and fixed data `x : K`, `u : E[x]`, emdash forms a functorial object

```
homd_E(x,u)
  : Π(y : K^op), E[y^-] ⊢ (Hom_K(x,y)^op ⊢ Cat)
```

whose value at `y`, `v : E[y]`, and `f : x → y` is

```
Hom_{E[y]}(E[f](u),v).
```

This is also what organizes arrows in Sigma totals:

```
Hom_{ΣE}((x,u),(y,v))
  = Σ(f : x → y), Hom_{E[y]}(E[f](u),v).
```

The same normalization-first architecture also covers product/curry structure, computational adjunctions, structural operations such as weakening/symmetry/contraction, and vertical/horizontal composition, whiskering, interchange, and stacking of higher cells; sheaves and schemes are feasible too.

The motivating example is the familiar shape of path induction in dependent type theory. For a category `Z` and an object `x : Z`, replace paths out of `x` by the outgoing-arrow category

```
Out_Z(x) = Σ(y : Z), Hom_Z(x,y).
```

Its distinguished object is

```
ι_x = (x,id_x),
```

and every object `a = (y,p) : Out_Z(x)` has a canonical arrow

```
ρ^x_a : ι_x → a.
```

Thus, for a motive

```
E : Out_Z(x) → Cat
```

and `u : E(ι_x)`, fixed-source directed induction has the expected section

```
Ind_x(E,u) : Π(a : Out_Z(x)), E(a)

Ind_x(E,u)(a) = E(ρ^x_a)(u).
```

Write `Rep_Z(t)` for the covariant representable `Hom_Z(t,-)`. For the composition motive

```
E[(y,p)] ≔ Rep_Z(y) ⊢ Rep_Z(x),
```

with initial datum `id : Rep_Z(x) ⊢ Rep_Z(x)`, this computes to ordinary composition: for `p : x → y` and `q : y → z`,

```
Ind_x(E,id)[(y,p)][z][q] ↝ q ∘ p.
```

The new phenomenon appears when the source object `x` itself is internalized. For an arrow `r : x → y`, precomposition gives

```
Out_Z(r) : Out_Z(y) → Out_Z(x)

Out_Z(r)(z,q : y → z) = (z,q ∘ r).
```

Once induction is internalized as a construction varying in `x`, the target `Π`/section-taking construction

```
(x,E) ↦ Π(q : Out_Z(x)), E(q)
```

is itself a displayed construction over the moving source object `x`. Its transport/comparison along `r` is not the identity; it is the section-pullback functor

```
Π(a : Out_Z(x)), E(a)
  →
Π(b : Out_Z(y)), E(Out_Z(r)(b)),
```

sending `s` to `b ↦ s(Out_Z(r)(b))`.

This is the lax naturality / functoriality layer exposed by the internalized formulation of directed path induction, in `emdash` v3.2. I would be very interested to know whether this phenomenon has an established name or prior formulation in categorical logic, HoTT, or higher category theory.
