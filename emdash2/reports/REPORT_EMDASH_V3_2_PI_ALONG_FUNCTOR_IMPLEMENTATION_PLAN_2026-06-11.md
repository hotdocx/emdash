# EMDASH v3.2 Pi Along Functor Implementation Plan

Date: 2026-06-11

Status: proposed implementation plan. No `Pi_f` implementation from this
report has been attempted in `emdash3_2.lp` yet.

## Scope

This report consolidates the design discussion around dependent products along
an ordinary functor:

```text
f : A ⊢ B
Π_f : Catd(A) ⊢ Catd(B)
```

The immediate motivation is the projection case:

```text
π_K : Sigma_cat(K) ⊢ L
Π_K := Π_{π_K}
```

where `K : Catd(L)`. This is also tied to split/native presentations of
families over displayed categories, such as:

```text
E : Obj(Pi_cat(Catd_catd_con K))
E : Obj(Pi_cat(Op_catd(Catd_catd_con K)))
E : Catd(Sigma_cat K)
```

The settled design direction is to implement the general `Pi_f` first, using a
comma/outgoing category formula. Fibrewise/split presentations should then be
bridges or facades over this general owner, not the primitive definition.

## Current Kernel Context

Relevant existing infrastructure in `emdash3_2.lp`:

```text
Catd_cat(K)              = K ⊢ Cat
Pullback_catd(E,F)       = E ∘ F
Pullback_catd_func(F)    : Catd(B) ⊢ Catd(A)
Pi_cat(E)                = sections of E
Pi_func(K)               : Catd(K) ⊢ Cat
Pi_int_funcd             : K :^n Cat^op ; Catd(K) ⊢ Cat
Pi_pullback_funcd(G)     : x :^n X ; Catd(G[x]) ⊢ Cat
section_pullback_func(F,E)
                         : Pi(E) ⊢ Pi(F^*E)
Sigma_cat(E)             = total category
Sigma_func(K)            : Catd(K) ⊢ Cat
Sigma_proj1_func(E)      : Sigma_cat(E) ⊢ K
sigma_map_func(eta)      : Sigma_cat(E) ⊢ Sigma_cat(D)
hom_(F,W)[a]             = Hom(W,F[a])
hom_int(F)[W]            = hom_(F,W)
```

The current `Pi` infrastructure already knows how to pull sections backward
along a functor. It does not yet provide a right adjoint/direct image
operation along an arbitrary functor. That missing direct image is the proposed
`Pi_along_func`.

## Settled Semantic Owner

The semantic owner should be:

```text
Pi_along_func(f) : Catd(A) ⊢ Catd(B)
```

for:

```text
f : A ⊢ B
```

The intended reading is right Kan/dependent product along `f`.

The fibre at `b : Obj(B)` is not merely a strict fibre of `f`. In a directed
category it is the section category over the outgoing comma category:

```text
CommaOut(f,b) := Σ (a :^n A), b ->^B f[a]
```

The hom-family part should be read through the existing `hom_int` idiom:

```text
hom_int B A f : Op_cat B ⊢ Catd_cat A
hom_int(f)[b][a] = Hom_B(b,f[a])
```

This is not just notation. It gives the pre/postcomposition action a semantic
owner before any raw `comp_cat*` pipeline is introduced, which is the normal
cut-elimination style used elsewhere in v3.2.

Then:

```text
(Pi_along_func(f)[E])[b]
  = Pi_cat(Pullback_catd(E, CommaOut_proj(f,b)))
```

where:

```text
CommaOut_proj(f,b) : CommaOut(f,b) ⊢ A
```

This formula defines `Pi_f` for any ordinary functor `f : A ⊢ B`. No
fibration or opfibration hypothesis should be required for the kernel
definition.

## Arrow Action

The object-level fibre formula is not enough. For:

```text
h : b ->^B b'
```

there is a canonical precomposition functor:

```text
CommaOut_precomp(f,h)
  : CommaOut(f,b') ⊢ CommaOut(f,b)
```

on objects:

```text
(a, q : b' -> f[a])
  ↦ (a, q o h : b -> f[a])
```

It satisfies the projection equation:

```text
CommaOut_proj(f,b) o CommaOut_precomp(f,h)
  = CommaOut_proj(f,b')
```

Therefore the base-arrow action of `Pi_f` should be:

```text
(Pi_along_func(f)[E])[h]
  =
section_pullback_func(
  CommaOut_precomp(f,h),
  Pullback_catd(E, CommaOut_proj(f,b)))
```

After the projection equation folds, its target is:

```text
Pi_cat(Pullback_catd(E, CommaOut_proj(f,b')))
```

So the direction is correct:

```text
(Pi_f E)[b] ⊢ (Pi_f E)[b']
```

This arrow-action formula is the main reason `Pi_f` should be implemented via
stable comma heads. If Lambdapi has to rediscover the comma projection
equation through raw Sigma, hom, and composition reductions, conversion is
likely to become brittle.

## No Restriction On `f` For Kernel Definition

The general comma formula is meaningful for every ordinary functor:

```text
f : A ⊢ B
```

Fibration, opfibration, cartesian, or opcartesian hypotheses should not be
kernel prerequisites for defining `Pi_f`.

Those hypotheses become relevant for comparison theorems, for example:

- comparing `Π_{π_K}` with a strict fibrewise formula;
- relating a split presentation to a total-category presentation;
- proving Beck-Chevalley, adjunction, or exactness properties;
- replacing a comma category by a strict fibre in a special case.

In particular, for:

```text
π_K : Sigma_cat(K) ⊢ L
```

the general definition gives:

```text
(Π_{π_K} E)[l]
  =
Pi_cat(Pullback_catd(E, CommaOut_proj(π_K,l)))
```

This is not definitionally the strict-fibre formula:

```text
Pi_cat(E[l])
```

unless a later comparison theorem or additional split/cartesian structure
justifies that replacement.

## Split Family Classifier

The useful classifier for fibrewise category families over a displayed base is
contravariant:

```text
Catd_catd_con(K) : Catd(Op_cat L)
Catd_catd_con(K)[l] = Catd_cat(K[l])
```

It should be semantically routed through existing internal constructors:

```text
Catd_catd_con(K)
  := Catd_cat_func o Op_func(K)
```

where:

```text
K              : L ⊢ Cat
Op_func(K)    : L^op ⊢ Cat^op
Catd_cat_func : Cat^op ⊢ Cat
```

Thus along:

```text
p : x ->^L y
```

the action is pullback:

```text
Catd_catd_con(K)[p^op]
  = Pullback_catd_func(K[p])
  : Catd(K[y]) ⊢ Catd(K[x])
```

Implementation note, 2026-06-11: this classifier is now present in
`emdash3_2.lp` as a derived semantic alias:

```text
Catd_catd_con(K) := Catd_cat_func o Op_func(K)
```

It was deliberately not added as an independent primitive. The active checks
cover its fibre law and its opposite-base arrow action as pullback.

There are two important section readings:

```text
E : Obj(Pi_cat(Catd_catd_con K))
```

unpacks as contravariant split data:

```text
E[x] : Catd(K[x])
K[p]^* E[y] ⊢ E[x]
```

while:

```text
E : Obj(Pi_cat(Op_catd(Catd_catd_con K)))
```

unpacks, in ordinary non-op fibre direction, as:

```text
E[x] ⊢ K[p]^* E[y]
```

The latter is closer to the ordinary displayed-over-displayed `K` reading, but
its fibrewise dependent product along `K[p]` requires the real `Pi_f`.

Therefore this report recommends:

1. implement general `Pi_along_func(f)`;
2. use it to define projection/direct-image operations;
3. only then add split-to-total or split-to-fibrewise comparison bridges.

## Comma Infrastructure

### Fixed Object Comma

Add stable heads:

```text
CommaOut_cat(f,b) : Cat
CommaOut_proj_func(f,b) : CommaOut_cat(f,b) ⊢ A
```

with semantic body or fold:

```text
CommaOut_cat(f,b)
  = Sigma_cat(hom_(f,b))

CommaOut_proj_func(f,b)
  = Sigma_proj1_func(hom_(f,b))
```

where:

```text
hom_(f,b)[a] = b ->^B f[a]
```

Expected object computation:

```text
Obj(CommaOut_cat(f,b))
  = Σ (a : Obj(A)), Obj(Hom_B(b,f[a]))
```

Expected projection computation:

```text
CommaOut_proj_func(f,b)[(a,q)] = a
```

### Precomposition Between Commas

Add stable heads:

```text
CommaOut_precomp_func(f,h)
  : CommaOut_cat(f,b') ⊢ CommaOut_cat(f,b)
```

for:

```text
h : b ->^B b'
```

Object rule:

```text
CommaOut_precomp_func(f,h)[(a,q)]
  =
(a, q o h)
```

using the existing ordinary precomposition head:

```text
hom_precomp_func(h)[q] = q o h
```

Projection fold:

```text
CommaOut_proj_func(f,b) o CommaOut_precomp_func(f,h)
  ↪ CommaOut_proj_func(f,b')
```

Identity and composition folds:

```text
CommaOut_precomp_func(f,id_b)
  ↪ id_func(CommaOut_cat(f,b))

CommaOut_precomp_func(f,h' o h)
  ↪ CommaOut_precomp_func(f,h) o CommaOut_precomp_func(f,h')
```

The composition orientation should be probed carefully. The intended
normalization should make section-pullback actions compose by cut elimination,
not expand into raw Sigma arrows.

### Internal Family Of Comma Categories

The functor in `b` is morally:

```text
b ↦ Σ (a :^n A), b ->^B f[a]
```

That is:

```text
CommaOut_catd(f) : Catd(Op_cat B)
```

with:

```text
CommaOut_catd(f)[b] = CommaOut_cat(f,b)
CommaOut_catd(f)[h^op] = CommaOut_precomp_func(f,h)
```

There is also a semantic internal expression:

```text
Sigma_func(A) o hom_int(f)
```

more explicitly:

```text
comp_cat_fapp0
  (Op_cat B)
  (Catd_cat A)
  Cat_cat
  (Sigma_func A)
  (hom_int B A f)
```

This expression sends:

```text
b ↦ Sigma_cat(hom_(f,b))
```

It is preferred over expanding `b ->^B f[-]` as a hand-built composition of
endpoint functors. The `hom_int` package is the owner of the hom-family action;
`CommaOut_catd(f)` should only become a stable owner after a probe shows that
the Sigma/hom pipeline needs a fold for conversion or performance.

A stable fold should be considered:

```text
Sigma_func(A) o hom_int(f)
  ↪ CommaOut_catd(f)
```

This is the interaction/folding rule needed for the surface expression:

```text
Σ (a :^n A), - ->^B f[a]
```

to land in the stable comma package.

Do not install the fold blindly. Probe it with:

```text
CommaOut_catd(f)[b] = CommaOut_cat(f,b)
CommaOut_catd(f)[h^op] = CommaOut_precomp_func(f,h)
```

and with downstream `Pi_along_func` fibre and arrow-action assertions. If the
fold overlaps badly with generic composition or Sigma action, keep
`CommaOut_catd(f)` as the primitive stable owner and define only one-way
readability aliases for the semantic expression.

## `Pi_along_func`

### Stable Heads

Add:

```text
Pi_along_func(f) : Catd(A) ⊢ Catd(B)
Pi_along_catd(f,E) : Catd(B)
Pi_along_transport_func(f,E,h)
  : (Pi_along_catd(f,E))[b] ⊢ (Pi_along_catd(f,E))[b']
```

Rules:

```text
Pi_along_func(f)[E]
  ↪ Pi_along_catd(f,E)

Pi_along_catd(f,E)[b]
  ↪ Pi_cat(Pullback_catd(E, CommaOut_proj_func(f,b)))

Pi_along_catd(f,E)[h]
  ↪ Pi_along_transport_func(f,E,h)
```

Transport body:

```text
Pi_along_transport_func(f,E,h)
  :=
section_pullback_func(
  CommaOut_precomp_func(f,h),
  Pullback_catd(E, CommaOut_proj_func(f,b)))
```

The target reduces by the projection fold:

```text
Pullback_catd(
  Pullback_catd(E, CommaOut_proj_func(f,b)),
  CommaOut_precomp_func(f,h))

↪ Pullback_catd(E, CommaOut_proj_func(f,b'))
```

This target fold should probably be its own stable rule, rather than relying
on generic associativity of composition plus projection reduction.

### Action On Displayed Functors

For:

```text
eta : Functord(E,D)
```

eventually add:

```text
Pi_along_map_funcd(f,eta)
  : Functord(Pi_along_catd(f,E), Pi_along_catd(f,D))
```

with:

```text
Pi_along_func(f)[eta] ↪ Pi_along_map_funcd(f,eta)
```

At each `b`, this should be the section-level action induced by pulling `eta`
back along:

```text
CommaOut_proj_func(f,b)
```

This can be deferred in the first implementation pass if the object and
base-arrow action of `Pi_along_catd` can be validated independently. However,
the final `Pi_along_func` API should not stop at object action forever: later
structural logic and adjunction comparisons will need functorial action in
`E`.

## Projection Case

For:

```text
K : Catd(L)
π_K := Sigma_proj1_func(K) : Sigma_cat(K) ⊢ L
```

define:

```text
Pi_proj_func(K) := Pi_along_func(Sigma_proj1_func K)
```

or keep a stable alias:

```text
Pi_proj_func(K) : Catd(Sigma_cat K) ⊢ Catd(L)
```

with:

```text
Pi_proj_func(K)[E]
  ↪ Pi_along_catd(Sigma_proj1_func K,E)
```

The general fibre law is:

```text
Pi_proj_func(K)[E][l]
  =
Pi_cat(Pullback_catd(
  E,
  CommaOut_proj_func(Sigma_proj1_func K,l)))
```

Do not rewrite this globally to:

```text
Pi_cat(E[l])
```

That strict-fibre formula should be a later comparison theorem or specialized
bridge, not the primitive definition.

## Relation To Split Presentations

The total-category presentation:

```text
E : Catd(Sigma_cat K)
```

is the native input to:

```text
Pi_proj_func(K)
```

The split presentation:

```text
E : Obj(Pi_cat(Op_catd(Catd_catd_con K)))
```

is better for a surface reading of displayed-over-displayed `K`, but it should
not replace the total presentation until there is a bridge:

```text
split_to_total_catd(K,E) : Catd(Sigma_cat K)
```

Expected object law:

```text
split_to_total_catd(K,E)[(l,u)] = E[l][u]
```

Expected action over a total arrow:

```text
(p : l -> l', alpha : K[p](u) -> v)
```

should combine:

1. the split base action `E[l] ⊢ K[p]^* E[l']`;
2. evaluation at `u`;
3. fibre action along `alpha` inside `E[l']`.

This is real structure, not just notation. It should be planned after the
general `Pi_f` owner exists.

The contravariant split presentation:

```text
E : Obj(Pi_cat(Catd_catd_con K))
```

is useful for fibrewise right-action formulas already supported by
`Pi_pullback_funcd`, but it is not the primary displayed-over-displayed shape.

## Sigma Sketch

The analogous dependent sum along a functor should be a left Kan/direct image:

```text
Sigma_along_func(f) : Catd(A) ⊢ Catd(B)
```

Its fibre likely uses an incoming comma category:

```text
CommaIn(f,b) := Σ (a :^n A), f[a] ->^B b
```

with:

```text
(Sigma_f E)[b]
  = Sigma_cat(Pullback_catd(E, CommaIn_proj(f,b)))
```

For projection functors of Sigma totals, operational Sigma may be easier than
Pi because total maps and `sigma_map_func` are already well developed.
However, this report recommends letting `Pi_f` drive the architecture first:
it forces the comma and section-pullback structure that later comparison
theorems will need anyway.

## Proposed Implementation Order

### Phase 0: Probe Setup

Use a temporary copy:

```bash
cp emdash3_2.lp tmp_pi_along_probe.lp
timeout 60s lambdapi check -w tmp_pi_along_probe.lp
```

Keep every nontrivial rule behind a focused assertion before moving it to the
active file.

### Phase 1: Fixed Comma Heads

Implement:

```text
CommaOut_cat(f,b)
CommaOut_proj_func(f,b)
CommaOut_precomp_func(f,h)
```

Probe:

```text
CommaOut_proj_func(f,b)[(a,q)] = a
CommaOut_precomp_func(f,h)[(a,q)] = (a,q o h)
CommaOut_proj(f,b) o CommaOut_precomp(f,h) = CommaOut_proj(f,b')
```

Do not over-specify reducible Sigma endpoints on rule LHSs.

### Phase 2: Internal Comma Family

Implement:

```text
CommaOut_catd(f) : Catd(Op_cat B)
```

Probe:

```text
CommaOut_catd(f)[b] = CommaOut_cat(f,b)
CommaOut_catd(f)[h^op] = CommaOut_precomp_func(f,h)
```

Then probe the semantic fold:

```text
Sigma_func(A) o hom_int(f) ↪ CommaOut_catd(f)
```

Keep the fold only if downstream assertions remain fast and stable.

### Phase 3: `Pi_along_catd`

Implement:

```text
Pi_along_func(f)
Pi_along_catd(f,E)
Pi_along_transport_func(f,E,h)
```

Probe:

```text
Pi_along_func(f)[E] = Pi_along_catd(f,E)
Pi_along_catd(f,E)[b]
  = Pi_cat(Pullback_catd(E, CommaOut_proj(f,b)))
Pi_along_catd(f,E)[h] = Pi_along_transport_func(f,E,h)
```

Also probe a section-level object action:

```text
Pi_along_transport_func(f,E,h)(s)
  =
section_pullback_func(CommaOut_precomp_func(f,h), ...)(s)
```

### Phase 4: Projection Alias

Implement:

```text
Pi_proj_func(K)
  := Pi_along_func(Sigma_proj1_func K)
```

or as a stable alias if probes show a need.

Probe only the general comma fibre law first. Do not force strict-fibre
comparison.

### Phase 5: Action In The Family Argument

Implement:

```text
Pi_along_map_funcd(f,eta)
```

with object components induced by the pulled-back displayed functor along each
comma projection.

This phase may require a small section-map helper if the existing `Pi_func`
hom-action is too abstract for useful normal forms.

### Phase 6: Split Bridges

Implement only after `Pi_along_func` is stable:

```text
Catd_catd_con(K)
split_to_total_catd(K,E)
```

Then define and compare split projection Pi surfaces through:

```text
Pi_proj_func(K)(split_to_total_catd(K,E))
```

Comparison with strict fibrewise `Pi_cat(E[l])` should remain theorem-level or
specialized, not a broad kernel rewrite.

## Rewrite Hygiene Notes

- Prefer semantic definitions first, but introduce stable comma heads where
  projection equations are computationally important.
- Keep implicit source/target slots minimal on rule LHSs.
- Avoid broad rewrites equating comma categories with strict fibres.
- Avoid making `Pi_id`, `Pi_terminal`, or `Pi_projection` collapse globally
  before the relevant comparison theorem is available.
- Treat `CommaOut_catd(f)` as the owner of the functor
  `b ↦ Σ(a), b -> f[a]`; use a fold from the internal expression only after a
  focused probe.
- Keep object-law, arrow-action-law, and family-argument-action-law probes
  separate. A rule that works at object level may still be too expensive at
  arrow-action level.

## Validation Targets

Minimum checks before moving from probe to active file:

```bash
timeout 60s lambdapi check -w tmp_pi_along_probe.lp
timeout 60s lambdapi check -w emdash3_2.lp
timeout 60s lambdapi check -w emdash3_2_checks.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

Add focused assertions to `emdash3_2_checks.lp` for each accepted normal form.

## Current Recommendation

Implement `Pi_f` as the general comma/right-Kan type former:

```text
Pi_along_func(f) : Catd(A) ⊢ Catd(B)
```

with object and arrow action owned by:

```text
CommaOut_cat(f,b)
CommaOut_precomp_func(f,h)
section_pullback_func
```

Then treat:

```text
Pi_proj_func(K)
Catd_catd_con(K)
split_to_total_catd(K,E)
```

as derived layers over the general owner. This keeps the kernel coherent,
avoids premature fibration restrictions, and leaves strict-fibre formulas to
comparison theorems instead of broad definitional rewrites.
