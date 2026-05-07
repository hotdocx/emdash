---

RESPONSE ID: 1003

Yes: by “hom action induced by total-introduction” I meant essentially `Total_intro_func_func`.

More precisely, for a future:

```text
Totald_func Z : Functor (Catd_cat Z) Cat_cat
```

we want:

```text
fapp0 (Totald_func Z) H
  ↪ Sigma_cat H
```

and on a displayed functor `FF : Functord H K`:

```text
fapp1_fapp0 (Totald_func Z) FF
  ↪ Total_intro_func (id_func Z) FF
```

or, at the packaged functor level:

```text
fapp1_func (Totald_func Z) H K
  ↪ Total_intro_func_func (id_func Z)
```

This likely needs the identity-pullback rule:

```text
Pullback_catd K (id_func Z) ↪ K
```

so that the domain of `Total_intro_func_func (id_func Z)` is definitionally `Functord_cat H K`.

On the Sigma/Total point: yes, the plan is sloppy there. In `emdash3.lp`, `Total_cat E ≔ Sigma_cat E`, so the formula is not mathematically wrong, but it reads badly. We should choose one canonical name in the plan. For v3 I would use `Sigma_cat` in the Sigma hom section:

```text
Hom_cat (Sigma_cat E) (Struct_sigma x u) (Struct_sigma y v)
  ↪ Op_cat (Sigma_cat (...))
```

Now the more important point: I agree we should try not to make `SigmaHom_catd` a new primitive hom former. But `Hom_catd` alone is not enough unless we also construct the two sections whose pointwise hom it compares.

The shape should be:

```text
Axy := Op_cat (Hom_cat Z x y)

Ey := Pullback_catd E (const_y : Axy -> Z)

transport_u : Obj (Pi_cat Ey)
const_v     : Obj (Pi_cat Ey)

Sigma hom fibre over f
  := Hom_catd Ey transport_u const_v
```

So the Sigma hom classifier should be expressible as:

```text
Hom_catd Ey transport_u const_v
```

where:
- `const_v` is the constant section at `v : E[y]`;
- `transport_u` is the hard part: the internally constructed “transport of u along the varying base arrow f”.

For Grothendieck `E = Fibration_cov_catd M`, `transport_u[f]` computes to:

```text
fib_cov_tapp0_fapp0 M f u
```

For general `E : Catd Z`, this transport section is exactly where `homd_curry` / `homd_int` enters. So the corrected design is:

- do not make `SigmaHom_catd` a primitive hom concept;
- express the hom part with `Hom_catd`;
- introduce only the necessary internal section/projection machinery that produces the varying left endpoint from `homd_curry`;
- if a `SigmaHom_catd` head is kept, it should be a derived stable alias/normal form for that `Hom_catd` expression, not a new primitive with independent meaning.

So I would revise the plan’s Sigma section to say:

```text
Sigma hom is not primitive.
It is:
  Op_cat (Sigma_cat (Hom_catd Ey transport_u const_v))
where Ey is E pulled back to the arrow context x -> y.
```

The actual feasibility question becomes: can we define `transport_u` from the current `homd_curry` target cleanly, or do we first need a small stable projection head for “transport section extracted from homd”? That is the next thing to assess before making the plan decision-complete.

---

RESPONSE ID: 1004

I think you are right. I was conflating two layers.

For Sigma hom, the primitive should be a directed transport / induction operation for displayed categories, analogous to HoTT transport. It should not be extracted from `homd_curry` first.

A plausible core primitive is:

```text
transportd_sec E x u y
  : Obj (Pi_cat (Const_catd (Hom_cat Z x y) (Fibre_cat E y)))
```

Meaning:

```text
f : Hom_Z(x,y) ⊢ transportd_sec(E,x,u,y)[f] : E[y]
```

For a general `E : Catd Z`, this is primitive/abstract. For a Grothendieck fibration it computes:

```text
piapp0 (transportd_sec (Fibration_cov_catd M) x u y) f
  ↪ fib_cov_tapp0_fapp0 M f u
```

So yes: this is the directed analogue of HoTT’s `transport`, with Groth/functor families giving the computational beta rule.

Then Sigma hom should be expressed using `Hom_catd`, not as a new primitive `SigmaHom_catd`. We also need a constant section:

```text
const_section A B v
  : Obj (Pi_cat (Const_catd A B))

piapp0 (const_section A B v) a ↪ v
```

Then the fibre-hom family for Sigma arrows is:

```text
Hom_catd
  (Const_catd (Hom_cat Z x y) (Fibre_cat E y))
  (transportd_sec E x u y)
  (const_section (Hom_cat Z x y) (Fibre_cat E y) v)
```

and the Sigma hom rule should be phrased using `Sigma_cat` consistently, roughly:

```text
Hom_cat (Sigma_cat E) (Struct_sigma x u) (Struct_sigma y v)
  ↪ Op_cat (Sigma_cat (...the Hom_catd expression...))
```

There is still an orientation check to do: whether the internal base should be `Hom_cat Z x y` or `Op_cat (Hom_cat Z x y)` depends on the chosen convention for the final outer `Op_cat`. But conceptually, the ingredients should be:

1. `transportd_sec`: primitive displayed transport/induction.
2. `const_section`: constant section into a constant displayed category.
3. `Hom_catd`: fibrewise hom between the transported source and constant target.
4. `Sigma_cat`: totalization of that displayed hom family.

Then `homd_curry` / `homd_int` is not the source of transport. It is the higher/off-diagonal packaging that should be related later to this transport-plus-`Hom_catd` story, especially for iteration and naturality.