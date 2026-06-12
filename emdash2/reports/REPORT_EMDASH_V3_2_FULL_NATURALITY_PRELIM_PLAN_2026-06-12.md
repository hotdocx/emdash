# EMDASH v3.2 Full Naturality Preliminary Plan

Date: 2026-06-12

Status: preliminary design note. No implementation has landed from this plan
yet.

## Scope

This note consolidates the current review of strict functoriality, strict
naturality, and the planned port of the v2 "exchange law" check, now better
called the interchange law.

The immediate design issue is that v3.2 currently has useful capped
computation rules:

```text
F[g] o F[f]          -> F[g o f]
G[g] o eta[f]        -> eta[g o f]
eta[f] o F[h]        -> eta[f o h]
```

but the omega-friendly owners should be full hom-action functors:

```text
fapp1_func F
tapp1_func eta
```

The capped heads `fapp1_fapp0` and `tapp1_fapp0` should remain as projection
and performance surfaces, but they should not be the only formulation of
functoriality and naturality.

## Current State

Functor action:

```text
fapp1_func F X Y : Hom_A(X,Y) -> Hom_B(F[X],F[Y])
fapp1_fapp0 F f  : F[X] -> F[Y]
```

The generic strict functoriality rule is currently capped:

```text
F[g] o F[f] -> F[g o f]
```

There are also later full hom-action rules for identity and composition of
ordinary functors in `Cat_cat`:

```text
fapp1_func(id_A) -> id_(Hom_A)
fapp1_func(F o G) -> fapp1_func(F) o fapp1_func(G)
```

The composition rule expands the hom-action of the composite functor `F o G`
into the composite of the hom-actions of `F` and `G`. This is the full
hom-action counterpart of the existing object/capped-arrow computation for
ordinary functor composition, and there is no present reason to remove it unless
a focused probe later exposes an actual overlap or orientation problem.

This rule is separate from strict functoriality of an arbitrary single functor
`F` with respect to composition inside its source category. The redesign needs
strict functoriality rules in addition to strict naturality rules; that
single-functor strict functoriality problem is the one still to formulate at
the full `fapp1_func` level.

Transformation action:

```text
tapp1_func eta X Y : Hom_A(X,Y) -> Hom_B(F[X],G[Y])
tapp1_fapp0 eta f  : F[X] -> G[Y]
```

The current strict naturality rules are capped:

```text
G[g] o eta[f] -> eta[g o f]
eta[f] o F[h] -> eta[f o h]
```

For now, ordinary `Transf` may continue to mean strict natural transformation:
both accumulation directions are installed as rewrite rules. Later lax/skew
variants should not inherit both rules automatically. For a lax or skew
transfor, one side should become explicit higher data: the image under
`tapp1_func` or a nearby projection of a canonical/cartesian comparison arrow
need not be identity or cartesian.

## Hom-Action Asymmetry

The covariant postcomposition API is currently owned by `hom_`:

```text
hom_(F,W)[Y] = Hom(W,F[Y])

hom_postcomp_tele_func(F,W,X,Y)
  = fapp1_func(hom_(F,W), X, Y)

hom_postcomp_func(F,W,X,Y,f)
  = hom_postcomp_tele_func(F,W,X,Y)[f]

hom_postcomp_func(F,W,X,Y,f)[g]
  = F[f] o g
```

The contravariant precomposition API is less uniform:

```text
hom_precomp_func(A,X,Y,Z,f)[g] = g o f
```

This is currently a standalone stable head. It is morally the identity-functor
case of a precomposition action owned by `hom_con`, but `hom_con` is only a
defined alias:

```text
hom_con(W,F)
  := hom_(Op(A), Op(B), Op(F), W)
```

This alias was intentional: duplicating a full `hom_con` theory parallel to
`hom_` would create a second presentation of the same hom action. Before adding
full naturality rules, this asymmetry should be reassessed.

## Precomposition Design Options

### Option A: Projection Through Existing `hom_` Over Opposites

Keep `hom_con` as a definition. Introduce the generalized precomposition
projection by routing through:

```text
hom_(Op(B), Op(A), Op(F), Z)
```

Conceptual head:

```text
hom_precomp_along_func(F,Z,h)[g] = g o F[h]
```

where:

```text
F : A -> B
h : W -> X in A
Z : Obj(B)

hom_precomp_along_func(F,Z,h)
  : Hom_B(F[X],Z) -> Hom_B(F[W],Z)
```

This option avoids making `hom_con` a second primitive owner.

### Option B: Add A Narrow Fold To `hom_con`

Add a fold such as:

```text
hom_(Op(A), Op(B), Op(F), W) -> hom_con(W,F)
```

This may improve readability and make the projection path explicit, but it
could introduce an overlapping normal form with existing `hom_` projection
rules. It should be tried only in a temporary probe with focused assertions.

### Option C: Primitive `hom_con` Theory

Make `hom_con` a primitive/stable owner with its own projection rules. This is
the most symmetric surface, but it duplicates the `hom_` theory. The cost may
be acceptable if conversion through opposites is too brittle, but this should
be justified by a failed probe, not by aesthetics.

Initial recommendation: start with Option A. Add a stable projection head only
if the direct `hom_`-over-opposites route is too brittle or expensive.

## Full Strict Naturality

Let:

```text
A B : Cat
F G : A -> B
eta : F => G
X Y Z W : Obj(A)
g : Y -> Z
h : W -> X
```

### Post/Left Accumulation

Full functor-level rule:

```text
hom_postcomp_func(G, F[X], g) o tapp1_func(eta, X, Y)
  ->
tapp1_func(eta, X, Z) o hom_postcomp_func(id_A, X, g)
```

Both sides have type:

```text
Hom_A(X,Y) -> Hom_B(F[X],G[Z])
```

Capping at `f : X -> Y` gives the current strict rule:

```text
G[g] o eta[f] -> eta[g o f]
```

### Pre/Right Accumulation

After adding the generalized precomposition projection:

```text
hom_precomp_along_func(F, G[Y], h) o tapp1_func(eta, X, Y)
  ->
tapp1_func(eta, W, Y) o hom_precomp_func(A,W,X,Y,h)
```

Both sides have type:

```text
Hom_A(X,Y) -> Hom_B(F[W],G[Y])
```

Capping at `f : X -> Y` gives the current strict rule:

```text
eta[f] o F[h] -> eta[f o h]
```

## Full Strict Functoriality

Morally, strict functoriality is the identity-transfor instance of strict
naturality:

```text
tapp1_func(id_F, X, Y) -> fapp1_func(F,X,Y)
```

The code already has this identity specialization. However, implementation
still needs strict functoriality rules as first-class rules, not merely as an
informal consequence of strict naturality. The identity-transfor viewpoint is a
design guide and a consistency check, but implementation should provide the
functoriality rules explicitly when the naturality head is not present or has
already reduced away. This is the full-functor-level analogue of the existing
"identity-silent" issue for capped rules.

This is distinct from the existing rule for the hom-action of a composite
functor:

```text
fapp1_func(F o G) -> fapp1_func(F) o fapp1_func(G)
```

That rule concerns functor composition as an arrow of `Cat_cat`; it should stay
unless implementation probes discover a concrete conflict. It does not solve,
and should not be confused with, the strict functoriality rule for a single
functor's action on composable arrows in its source.

## v1 Inspiration

The old `emdash.lp` architecture is obsolete, but it is useful for naming the
Dosen-style accumulation pattern.

It had separate direct and accumulated rewrite forms:

```text
naturality direct
naturality with accumulated context
functoriality direct
functoriality with accumulated context
associativity accumulation
```

The old comments also distinguish actor/data positions and relate them to
antecedent/consequent variants. That matches the intended strict/lax/skew
reading here: in strict mode both sides are cut-elimination rewrites; in lax or
skew mode one side remains a nontrivial higher comparison.

## Interchange Law Port

The v2 "exchange law" check near the Cat-valued representable `hom_` should be
renamed to "interchange law".

It is not structural exchange (`sym_func_func`). It is the whiskering /
interchange computation:

```text
(g * beta) o epsilon[alpha] = epsilon[beta o alpha]
```

where `epsilon` is induced by functoriality of the representable
postcomposition action.

Recommended order:

1. Settle the generalized precomposition projection.
2. Add/probe full `tapp1_func` strict naturality rules.
3. Keep or adjust capped `tapp1_fapp0` strict rules as projection shortcuts.
4. Add full/capped strict functoriality checks.
5. Port the v2 representable check as an interchange regression.
6. Add no interchange-specific primitive unless the existing hom-action owners
   cannot normalize the regression after focused probing.

## Validation Plan

Use temporary probes before editing the active file:

```bash
cp emdash3_2.lp tmp_full_naturality_probe.lp
timeout 60s lambdapi check -w tmp_full_naturality_probe.lp
```

Each candidate rule should have a focused assertion showing:

```text
full functor-level normal form
capped projection normal form
agreement with the existing capped strict rule
```

Final validation after implementation:

```bash
EMDASH_TYPECHECK_TIMEOUT=60s make check
```
