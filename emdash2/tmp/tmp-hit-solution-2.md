Yes—your `Catd`/`homd_` formulation is the idiomatic Emdash eliminator, and it should be preferred over my category-over arrow-package probe.

The exact interface is:

```text
E  : Catd(W)
e  : Obj(E[base])

ℓᴰ : homd_E(base,e,base,e)[loop]
   ≡ Hom_{E[base]}(E[loop](e),e)

ind_W(E,e,ℓᴰ) : Obj(Pi_cat(E))
```

with judgmental rules:

```text
ind_W(E,e,ℓᴰ)[base] ↪ e
ind_W(E,e,ℓᴰ)[loop] ↪ ℓᴰ
```

This was already successfully tested in [wehit_opaque_rewrite_loop_beta.lp](/home/user1/emdash1/emdash2/tmp/probes/wehit_opaque_rewrite_loop_beta.lp:19), including the strict loop rule through `fdapp1_int_cell`. So nothing fundamentally failed in this formulation. The failures came later, when trying to fit the decoder motive into an ordinary covariant `Catd`.

## What `Catd(W)` means

In the active kernel:

```text
Catd(W) ≡ Functor(W,Cat).
```

It already includes directed transport:

```text
E[p] : E[x] → E[y]
```

for every `p : x → y`. The corresponding section action is:

```text
s[p] : E[p](s[x]) → s[y].
```

Therefore your proposed `ℓᴰ` is exactly the existing dependent-hom idiom.

Replacing it with:

```text
Functor(Core(W),Cat)
```

would not work for the walking endomorphism:

- `Core(W)` retains only object paths/equivalences;
- the directed `loop` need not belong to `Core(W)`;
- consequently one could not state the required computation over `loop`;
- `Functor(Core(W),Core(Cat))` would be even too restrictive, since `Succ : ℕ̂ → ℕ̂` is not invertible.

## Where the naïve decoder family fails

Let:

```text
Code : Catd(W)

H(x) ≔ Core(Hom_W(base,x))
H[p](q) ≔ p ∘ q.
```

The saved outline proposed fibre objects:

```text
Dec(x) ≔ Functor(Code(x),H(x)).
```

For `p : x → y`, to make this a `Catd(W)` we would need:

```text
Dec[p] :
  Functor(Code(x),H(x))
  →
  Functor(Code(y),H(y)).
```

Given `d : Code(x) → H(x)`, the available operations only produce:

```text
H[p] ∘ d       : Code(x) → H(y)
d' ∘ Code[p]   : Code(x) → H(y).
```

They do not produce a functor:

```text
Code(y) → H(y).
```

That would require either:

```text
Code[p]⁻¹
```

or a selected Kan-extension operation along `Code[p]`. At `loop`:

```text
Code[loop] = Succ,
```

and `Succ` is noninvertible. This is precisely why the pointwise decoder-candidate family is not canonically a covariant `Catd(W)`.

In the groupoidal Circle proof the problem is invisible because transport is invertible.

## Better Emdash-native decoder design

We should not form `Dec(x)` as another `Catd`. The decoder itself should directly be a natural family morphism:

```text
decode : Functord(Code,H).
```

Its existing Emdash projections are exactly what the proof needs:

```text
decode[x] : Functor(Code(x),H(x))
```

and, for `p : x → y` and `n : Code(x)`:

```text
fdapp1_int_cell(decode,p,n) :
  H[p](decode[x](n))
  →
  decode[y](Code[p](n)).
```

Because `H(y)` is a core/path category, this arrow is an equality:

```text
p ∘ decode[x](n)
=
decode[y](Code[p](n)).
```

Thus the appropriate whole-HIT principle is the contextual/parameterized form:

```text
R D : Catd(W)

u : Functor(R[base],D[base])

σ : D[loop] ∘ u ⇒ u ∘ R[loop]

indᵈ_W(R,D,u,σ) : Functord(R,D).
```

with judgmental computations:

```text
indᵈ_W(R,D,u,σ)[base] ↪ u

fdapp1_int_cell(indᵈ_W(R,D,u,σ),loop,r)
  ↪ σ[r].
```

The ordinary `Pi_cat` eliminator is its terminal-parameter specialization:

```text
R ≔ Terminal_catd(W).
```

So this is not a separate Hom or 1-cell eliminator. It is the same whole-HIT dependent elimination principle, but usable in an open dependent context.

## Application to the ℕ proof

Take:

```text
R ≔ Code
D ≔ H
u ≔ power : ℕ̂ → H(base)
```

and the spiral:

```text
σ(n) :
  loop ∘ power(n)
  =
  power(Succ(n)).
```

With:

```text
power(0)     ↪ id
power(n + 1) ↪ loop ∘ power(n),
```

the spiral component reduces to reflexivity.

Define:

```text
decode ≔ indᵈ_W(Code,H,power,σ).
```

Then for arbitrary `p : base → x`, its generic `Functord` action at zero gives:

```text
p ∘ power(0)
=
decode[x](Code[p](0)).
```

Hence:

```text
p = decode[x](encodeₓ(p)).
```

For `x ≔ base`, the base computation gives `decode[base] ↪ power`, so:

```text
p = power(encode(p)).
```

The other inverse remains ordinary ℕ-induction.

Therefore the likely best design is:

```text
simple HIT elimination       : ind_W into Pi_cat(E)
contextual HIT elimination   : indᵈ_W into Functord(R,D)
decoder                      : Functord(Code,H)
arbitrary-arrow theorem      : generic fdapp1_int_cell
```

The next probe should test this parameterized `Functord` eliminator at `Fibre_func` and `fdapp1_int_cell`. That is substantially more native than the category-over arrow-package probe and avoids `DecTotal`, word induction, and a special Hom eliminator.