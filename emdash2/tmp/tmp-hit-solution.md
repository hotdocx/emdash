Yes. There is a clean Circle-style solution, and it does not require a WalkingEnd-specific “1-cell eliminator.”

The crucial correction is that the whole-HIT eliminator must eliminate into an arbitrary displayed category/category over `WalkingEnd`, not merely into a pre-existing split `Catd(WalkingEnd)`. That broader eliminator exposes both the object and arrow components of one section. Its arrow component supplies the hard roundtrip.

## 1. What the Circle proof actually does

The Coq/Agda Circle interface is abstract:

```text
S¹   : Type
base : S¹
loop : base = base
```

with whole-HIT induction:

```text
indS¹(P,b,ℓ) : Π x:S¹, P(x)

indS¹(P,b,ℓ)(base)     ↪ b
apd(indS¹(P,b,ℓ),loop) ↪ ℓ
```

The correspondence with integers then uses:

```text
Code(base) ≔ ℤ
Code[loop] ≔ successor equivalence

encode(p) ≔ transport Code p 0
decode    ≔ Circle induction with the spiral coherence
```

Finally:

```text
encode(decode(n)) = n
```

is integer induction, while:

```text
decode(encode(p)) = p
```

uses ordinary equality `J` on `p`.

The relevant references are [Coq Circle.v](/tmp/emdash-review-vendor-20260718/HoTT/theories/Spaces/Circle.v:17) and [Cubical Agda Base.agda](/tmp/emdash-review-vendor-20260718/cubical/Cubical/HITs/S1/Base.agda:22).

## 2. The directed walking HIT

Declare only:

```text
WalkingEnd : Cat
base       : Obj(WalkingEnd)
loop       : Hom_WalkingEnd(base,base)
```

There must be no rules exposing:

```text
Obj(WalkingEnd)
Hom_WalkingEnd(x,y)
id_WalkingEnd
composition_WalkingEnd
```

as Unit, words, Nat, or any other concrete datatype.

## 3. The correct whole-HIT dependent eliminator

Use a displayed category `𝔇` over `WalkingEnd`. It has:

```text
𝔇₀(x)           displayed objects over x
𝔇₁(p;u,v)       displayed arrows over p : x → y
```

together with displayed identities, composition, and higher structure.

Given:

```text
u  : 𝔇₀(base)
ℓᴰ : 𝔇₁(loop;u,u)
```

the single whole-HIT eliminator returns a displayed section:

```text
ind_W(𝔇,u,ℓᴰ) : Section(𝔇).
```

Writing its object and arrow components as `s₀` and `s₁`, its constructor β-rules must compute:

```text
s₀(base) ↪ u
s₁(loop) ↪ ℓᴰ
```

The loop rule is therefore judgmental—a rewrite at the stable arrow-component owner.

Identity and composition are supplied by the generic section/functor calculus:

```text
s₁(id)    ↪ idᴰ
s₁(q ∘ p) ↪ s₁(q) ∘ᴰ s₁(p).
```

They are not WalkingEnd-specific rules.

Equivalently, in category-over notation, for:

```text
π : E → WalkingEnd
e : Obj(E),             π(e) = base
ℓ̃ : Hom_E(e,e),         π(ℓ̃) = loop
```

the eliminator gives:

```text
ind_W(E,π,e,ℓ̃) : WalkingEnd → E
π ∘ ind_W(E,π,e,ℓ̃) ↪ id_WalkingEnd
```

with definitional computation on `base` and `loop`.

This is the direct categorical counterpart of Circle induction. It is not a full functor-category initiality theorem, although such an initiality theorem could later be derived from it.

## 4. Code and encode

Let:

```text
ℕ̂ ≔ Path_cat(ℕ)
```

and construct the successor functor:

```text
Succ : ℕ̂ → ℕ̂
Succ(n) ↪ n + 1.
```

Its action on equality paths is ordinary congruence.

Define Code by the nondependent specialization of the whole-HIT eliminator:

```text
Code ≔ rec_W(Cat,ℕ̂,Succ) : WalkingEnd → Cat
```

with judgmental rules:

```text
Code(base) ↪ ℕ̂
Code[loop] ↪ Succ.
```

For any based arrow:

```text
p : Hom_WalkingEnd(base,x)
```

define:

```text
encodeₓ(p) ≔ Code[p](0) : Obj(Code(x)).
```

In particular:

```text
encode : Hom_WalkingEnd(base,base) → ℕ.
```

This is action of the whole-HIT-defined Code functor—not elimination on Hom.

## 5. Powers

Define at the base by Nat recursion:

```text
power(0)     ↪ id
power(n + 1) ↪ loop ∘ power(n).
```

Viewed categorically:

```text
power : ℕ̂ → Core(Hom_WalkingEnd(base,base)).
```

Using `Core(Hom)` is useful: arrows in the target are actual equalities between walking arrows, while the objects remain directed arrows.

## 6. The directed decoder displayed category

This is the central construction.

For each `x : WalkingEnd`, a displayed object is a decoder candidate:

```text
Dec₀(x)
  ≔ Functor(Code(x), Core(Hom_WalkingEnd(base,x))).
```

For `p : x → y`, a displayed arrow from `d : Dec₀(x)` to `e : Dec₀(y)` is the strict directed naturality equation:

```text
Dec₁(p;d,e)
  ≔ Π n : Code(x),
       e(Code[p](n)) = p ∘ d(n).
```

This is the directed counterpart of the dependent-function transport equation in the Circle decoder.

Displayed identity follows from:

```text
Code[id](n) = n
id ∘ d(n)  = d(n).
```

Displayed composition follows from:

```text
e_z(Code[q ∘ p](n))
  = e_z(Code[q](Code[p](n)))
  = q ∘ e_y(Code[p](n))
  = q ∘ (p ∘ d_x(n))
  = (q ∘ p) ∘ d_x(n).
```

Thus `Dec` is closed under the generic identity and composition structure without assuming that arbitrary walking arrows already have normal forms.

A concrete category-over presentation is also possible:

```text
Obj(DecTotal)
  ≔ Σ x : Obj(WalkingEnd), Dec₀(x)

Obj(Hom_DecTotal((x,d),(y,e)))
  ≔ Σ p : Obj(Hom_WalkingEnd(x,y)), Dec₁(p;d,e).
```

Above this first proof-bearing level, the displayed tail can simply retain the underlying higher cells of `WalkingEnd`, ignoring the equality witness. This avoids assuming local discreteness while constructing the 1-arrow normalization proof.

## 7. The spiral datum

At `base`, choose:

```text
power : Dec₀(base).
```

The displayed lift over `loop` is:

```text
spiral(n) :
  power(Code[loop](n)) = loop ∘ power(n).
```

It computes:

```text
power(Code[loop](n))
  ↪ power(n + 1)
  ↪ loop ∘ power(n).
```

Therefore the pointwise spiral can be reflexivity after reduction:

```text
spiral(n) ↪ refl.
```

Naturality in equality paths of `ℕ̂` is handled by equality `J`; `nat_is_set` closes the higher proof coherence.

This is the directed analogue of Coq’s spiral and Agda’s `decodeSquare`. Unlike the groupoidal Circle, successor need not be invertible because the displayed equation is oriented forward.

## 8. Whole-HIT construction of decode

Apply the one whole-HIT eliminator:

```text
decodeSection ≔ ind_W(Dec,power,spiral).
```

Its object components give:

```text
decodeₓ : Code(x) → Hom_WalkingEnd(base,x)
```

with judgmental base computation:

```text
decode_base(n) ↪ power(n).
```

Its arrow component at every `p : x → y` gives:

```text
decode_naturality(p,n) :
  decode_y(Code[p](n)) = p ∘ decode_x(n).
```

At the constructor `loop`, this computes judgmentally to the supplied spiral:

```text
decode_naturality(loop,n) ↪ spiral(n).
```

This arrow component is the directed replacement for the Circle proof’s dependent action on paths. No separate Hom induction is involved.

## 9. The hard inverse

For:

```text
p : Hom_WalkingEnd(base,y)
```

evaluate decoder naturality at zero:

```text
decode_y(encodeₓ(p))
  ≔ decode_y(Code[p](0))
  = p ∘ decode_base(0)
  ↪ p ∘ power(0)
  ↪ p ∘ id
  ↪ p.
```

Hence:

```text
decode_y(encodeₓ(p)) = p.
```

For an endomorphism `p : Hom(base,base)`:

```text
power(encode(p)) = p.
```

This proof materially uses:

1. whole-HIT Code elimination;
2. whole-HIT dependent decoder elimination;
3. the decoder section’s arrow component;
4. judgmental loop β and the spiral.

It does not assume a word carrier, direct Hom eliminator, bodyless motive, or initiality theorem.

## 10. The easy inverse

Prove by Nat induction:

```text
encode(power(0))
  ↪ encode(id)
  ↪ 0.
```

For the successor:

```text
encode(power(n + 1))
  ↪ encode(loop ∘ power(n))
  = Succ(encode(power(n)))
  = Succ(n)
  ↪ n + 1.
```

The middle equality is generic Code functoriality plus judgmental `Code[loop] ↪ Succ`.

Thus:

```text
encode(power(n)) = n.
```

Together:

```text
Hom-arrow objects at (base,base)  ≃  ℕ.
```

This can be packaged as:

```text
TypeEquiv(Obj(Hom_WalkingEnd(base,base)),ℕ)
```

and as an equivalence:

```text
Core(Hom_WalkingEnd(base,base)) ≃ ℕ̂.
```

Showing that the entire directed Hom category has no additional nonidentity higher cells is the next-dimensional/local-discreteness theorem. It should be derived by iterating the same whole displayed-elimination architecture, not by exposing Hom as words.

## 11. Role of `PathOut`

`PathOut_W(base)` remains useful:

```text
PathOut_W(base) ≔ Σ x : Obj(W), Hom_W(base,x).
```

It provides the natural global parameter `(x,p)` for:

```text
encodeₓ(p)
decodeₓ(encodeₓ(p))
hard(x,p) : decodeₓ(encodeₓ(p)) = p.
```

It can package the completed decoder naturality theorem and its reflexive computation.

But `path_ind_sec` should not be asked to manufacture the equality motive from nothing. Its motive must already have a functorial action. The decoder displayed section constructs precisely that missing arrow-level equality. Thus:

```text
whole-HIT displayed induction  → constructs decoder and strict naturality
PathOut                         → packages/evaluates the resulting based-arrow theorem
```

That is the clean division of responsibilities.

## Feasibility conclusion

The design is computationally feasible. The apparent roadblock came from trying to put decoder candidates into an ordinary covariant `Catd` fibre:

```text
Code(x) → Hom(base,x).
```

Because `Code[loop]=Succ` is noninvertible, such functions cannot be transported forward merely by precomposition. The Circle hides this issue because transport along equality is always invertible.

The solution is not a special 1-cell eliminator. It is to use the correct whole categorical dependent eliminator into a displayed category/category over `WalkingEnd`, where:

- objects are local decoder candidates;
- arrows are their strict naturality equations;
- the loop arrow is the spiral;
- the section’s arrow component proves the hard inverse.

Existing `Functord`, `homd_int`, `Core_cat`, equality action, Sigma/category-over, and PathOut machinery should supply most of the implementation. If the current `Catd` interface cannot express this non-split displayed category, the reusable missing foundation is a general `DisplayedCat`/category-over section eliminator—not any WalkingEnd-specific Hom principle.