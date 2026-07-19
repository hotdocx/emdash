## Verdict

No remaining opaque sentinel has the same semantic defect as the rejected

```text
Core_cat(Hom_cat(W,base,−)).
```

With the directed-first correction, the core Hom–Nat argument is computationally feasible. The one substantial unprobed implementation gate is constructing the spiral as an actual structured `Transf`, including naturality and higher action—not merely declaring its pointwise components.

### Sentinel-by-sentinel assessment

| Former probe sentinel | Replacement | Feasibility |
|---|---|---|
| `Code` | `rec_W(Cat,Path_cat(ℕ),NatSucc_func)` | High |
| `H` | Existing `Rep_catd(base)` | Already foundationally available |
| `zero` | Ordinary Nat `zero` after Code base β | Trivial |
| `power` object map | Nat recursion into `Hom(W,base,base)` | High |
| `power_func` | `Core_incl_func ∘ Path_map(power)` | High, with reusable `Path_map` infrastructure |
| `spiral` | Structured transfor with component `loop ∘ power(n) ⇒ power(succ n)` | Moderate; main remaining gate |
| `decodeᵈ` | Contextual eliminator applied to the concrete preceding data | High |
| hard equality | `hom_to_path(walking_end_is_one_cat(base,x),νₚ)` | High, conditional on the explicit truncation evidence |

## Why `Path_map` does not repeat the Core problem

A reusable construction can be introduced as:

```text
Path_int : Functor(Grpd_cat,Cat_cat)

Path_int[A] ≔ Path_cat(A)
Path_int[f] ≔ Path_map(f).
```

This is semantically sound because an arrow of `Grpd_cat` is an ordinary function:

```text
f : A → B,
```

and its action on paths is genuinely available:

```text
Path_map(f)(p) ≔ ap(f,p).
```

Higher arrows in `Grpd_cat` are themselves equalities between functions, so their action is obtained by equality induction. No directed arrow is being reflected into equality. This is categorically different from attempting a functor:

```text
Core_cat : Cat_cat → Cat_cat,
```

whose action on a directed natural transformation would require an unavailable equality between component objects.

Therefore:

```text
NatSucc_func ≔ Path_map(succ)
```

is a reusable foundational construction, not an ad hoc WalkingEnd assumption.

## `Code` is feasible

Once `NatSucc_func` exists:

```text
Code ≔ rec_W(
  Cat_cat,
  Path_cat(ℕ),
  NatSucc_func
).
```

The existing constant-section/Functor comparison makes the result usable as:

```text
Code : Catd(W).
```

The expected observations are:

```text
Code(base) ≃ Path_cat(ℕ)
Code[loop] = NatSucc_func.
```

The second may initially be a transparent equality theorem assembled from contextual loop β and the terminal-source comparison, rather than a direct runtime reduction. That is enough for all subsequent proofs.

The retained terminal `tapp0_fapp0` warning affects the one-step normal form of this recursor presentation, but not its mathematical formation. It remains an engineering/normal-form issue rather than a conceptual blocker.

## `power_func` is feasible

Define the carrier function by Nat recursion:

```text
power(0)       ↪ id
power(succ n)  ↪ loop ∘ power(n).
```

Then put:

```text
C ≔ Hom_cat(W,base,base)

power_core : Functor(Path_cat(ℕ),Core_cat(C))
power_core ≔ Path_map(power)

power_func : Functor(Path_cat(ℕ),C)
power_func ≔ Core_incl_func(C) ∘ power_core.
```

This uses equality only to transport equality of natural numbers through the ordinary function `power`; it does not assume equality of arbitrary directed walking cells.

## The spiral is the main remaining gate

Pointwise, it is elementary:

```text
ρₙ : loop ∘ power(n) = power(succ n)
ρₙ ≔ refl

σₙ : loop ∘ power(n) ⇒ power(succ n)
σₙ ≔ path_to_hom(ρₙ).
```

Because the power successor equation computes, `σₙ` reduces to the identity 2-cell.

But the eliminator needs the whole structured object:

```text
σ :
  Rep(base)[loop] ∘ power_func
  ⇒
  power_func ∘ NatSucc_func.
```

The implementation must supply:

- every component `σₙ`;
- naturality for `p : n = m`;
- the iterable higher action.

Naturality is mathematically straightforward: equality induction on `p` reduces it to the reflexive case, where generic functor identity laws and `σₙ ≔ id` close the diagram. Nat sethood handles the subsequent proof coherence.

The active kernel does not appear to have an immediately reusable transparent constructor that packages such pointwise data into an arbitrary `Transf`. Thus the goal should treat one of these as an early reusable prerequisite:

```text
Path_source_transf(...)
```

or an equivalent action of `Path_int` on function homotopies, with component and higher-action computations.

This is not a variance or semantic obstruction like `Core_catd`. It is a missing structured-introduction interface. A bodyless WalkingEnd-specific:

```text
constant symbol walking_spiral : Transf(...)
```

would not be acceptable.

I recommend probing this packaging immediately after `Path_map`, before destructively removing the old walking implementation.

## Directed decoder and hard equality are feasible afterward

Once the spiral exists:

```text
decodeᵈ ≔ indᵈ_W(
  Code,
  Rep_catd(base),
  power_func,
  spiral
).
```

For `p : base → x`, generic `fdapp1_int_cell` gives:

```text
Rep(base)[p](decodeᵈ[base](0))
  ⇒
decodeᵈ[x](Code[p](0)).
```

The existing representable computation reduces the source through:

```text
Rep(base)[p](id)
  ↪ p ∘ id
  ↪ p.
```

Hence:

```text
νₚ : p ⇒ decodeᵈ[x](encodeₓ(p)).
```

The selected truncation evidence then gives:

```text
dₓ ≔ walking_end_is_one_cat(base,x)
   : IsDiscreteCat(Hom_cat(W,base,x))

hom_to_path(dₓ,νₚ)
  : p = decodeᵈ[x](encodeₓ(p)).
```

Equality symmetry gives the exported orientation, and at `x ≔ base`, contextual base β yields:

```text
power(encode(p)) = p.
```

There is no remaining typing mystery in this part.

One computational caveat is that `walking_end_is_one_cat` is intentionally opaque signature evidence. Therefore `hom_to_path(dₓ,νₚ)` will generally be a stuck but valid equality proof, not judgmentally `refl`. That is acceptable for the propositional inverse theorem. If judgmental computation of that equality proof were demanded, the explicit truncation axiom would need a richer computational interface.

## The Nat inverse is feasible

Nat induction proves:

```text
encode(power(n)) = n.
```

The successor calculation is:

```text
encode(power(succ n))
= Code[loop ∘ power(n)](0)
= Code[loop](Code[power(n)](0))
= succ(encode(power(n)))
= succ(n).
```

Because generic functoriality is oriented toward action on the composite, this will likely be expressed as an equality chain rather than runtime expansion of `Code[loop ∘ power(n)]`. The kernel already has the necessary `eq_ap`, `eq_trans`, Nat induction, strict functoriality, and loop-β theorem.

## Downstream packaging

The carrier result

```text
Hom(W,base,base) ≃ ℕ
```

is high-feasibility once both inverses exist.

Two later structured claims have additional packaging work:

- A concrete functor `BNat → W` whose hom action is `power_func`.
- A full structured equivalence
  `Hom_cat(W,base,base) ≃ Path_cat(ℕ)`.

Neither has a semantic obstruction. They may require a reusable one-object-functor constructor or further structured functor/transfor packaging. They should remain downstream of the carrier result, as the plan currently says.

## Minor plan corrections

I found one stale phrase in the current authoritative section: [the plan](/home/user1/emdash1/emdash2/reports/REPORT_EMDASH_V3_2_WALKING_ENDOMORPHISM_DIRECTED_HIT_PLAN_2026-07-17.md:172) still says:

```text
R ≔ Code
D ≔ H
```

It should say:

```text
R ≔ Code
D ≔ Rep_catd(base).
```

More substantively, G2/G4 should treat “structured Path-source transfor/spiral packaging” as an explicit feasibility gate, not merely say that function/path extensionality supplies the spiral.

Overall:

- Directed normalization MVP: high feasibility.
- Carrier Hom–Nat equivalence with explicit OneCat evidence: high feasibility, contingent mainly on structured spiral packaging.
- Full structured Hom-category/`BNat` equivalence: moderate-to-high feasibility, with further packaging work.
- Deriving OneCat evidence instead of assuming it: still open and correctly outside the MVP.

No files were changed during this review.