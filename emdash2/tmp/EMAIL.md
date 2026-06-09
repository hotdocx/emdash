I would like to announce a new v3.2 draft of **emdash**, a Lambdapi formalization and prototype proof assistant aimed at functorial programming with higher lax ω-categorical structure (fully internalized and computational, in the style of Kosta Dosen's cut-elimination techniques):

https://github.com/hotdocx/emdash/blob/main/docs/emdash3_2.pdf
https://github.com/hotdocx/emdash/blob/main/emdash2/emdash3_2.lp

The motivating example is the familiar shape of path induction in dependent type theory. For a category `Z` and an object `x : Z`, replace paths out of `x` by the outgoing-arrow category

```
Out_Z(x) = Σ(y : Z), Hom_Z(x,y).
```

Its distinguished object is

```
ι_x = (x,id_x),
```

and every object `q = (y,p) : Out_Z(x)` has a canonical arrow

```
ρ^x_q : ι_x → q.
```

Thus, for a motive

```
E : Out_Z(x) → Cat
```

and `u : E(ι_x)`, fixed-source directed induction has the expected section

```
Ind_x(E,u) : Π(q : Out_Z(x)), E(q)

Ind_x(E,u)(q) = E(ρ^x_q)(u).
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
Π(b : Out_Z(y)), E(Out_Z(r)(b)).
```

This is the lax naturality / functoriality layer exposed by the internalized formulation of directed path induction, in `emdash` v3.2. I would be very interested to know whether this phenomenon has an established name or prior formulation in categorical logic, HoTT, directed type theory, or higher category theory.

