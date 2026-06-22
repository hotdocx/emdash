# EMDASH v3.2 Full Naturality Preliminary Plan

Date: 2026-06-12
Last reviewed: 2026-06-22

Status: first implementation slice landed in `emdash3_2.lp` and
`emdash3_2_checks.lp` on 2026-06-12.

## 2026-06-22 Generic-Owner Correction

This report records historical implementation steps that introduced local
identity laws for `comp_cat_cov_transf`, `comp_cat_con_transf`, and related
specialized actions. Do not copy or extend those laws without reassessing their
owner and reduction role. Ordinary identity, composition, and naturality
should be inherited from the operation's internalized `Functor`/`Transf` owner
and the global `fapp*`/`tapp*` calculus. A specialized rule may nevertheless
remain when a focused audit establishes that it is an intentional projection
or normal-form bridge, rather than a duplicate assertion of the generic law.

The Cat-specialized heads may remain as readable projection points for genuine
component and off-diagonal transfor structure. Before adding another ordinary
law to them, resume side task `INT-COMP` from the `Deferred Internalization
Side-Task Ledger` in
`REPORT_EMDASH_V3_2_PROFUNCTOR_REPRESENTABILITY_REDESIGN_PRELIM_PLAN_2026-06-19.md`.
Its completion criterion is a generic-owner route with object, full/capped
action, identity, and composition diagnostics, plus warning comparison. This
correction supersedes the later historical recommendation in this report to
add constructor-local “semantic identity reductions.” Direct Došen-style
beta/eta or cut-elimination laws remain admissible only when they express
structure beyond generic functoriality or naturality.

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

The former contravariant precomposition API was less uniform:

```text
hom_precomp_along_func(id_A,Z,f)[g] = g o f
```

This was originally represented by a standalone stable head. It is really the
identity-functor case of a precomposition action owned by `hom_con`, but
`hom_con` is only a defined alias:

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
tapp1_func(eta, W, Y) o hom_precomp_along_func(id_A, Y, h)
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

## Implementation Notes 2026-06-12

The first slice implements Option A for generalized precomposition:

```text
fapp1_fapp0(hom_(Op(B),Op(A),Op(F),Z), h)
  -> hom_precomp_along_func(F,Z,h)
```

The stable projection computes as intended:

```text
hom_precomp_along_func(F,Z,h)[g] = g o F[h]
```

The full strict naturality and strict functoriality rules were added at the
`comp_cat_fapp0`/`tapp1_func`/`fapp1_func` level. The pre/right rules now
discriminate on the stable projection head:

```text
hom_precomp_along_func(F,Z,h)
```

The raw `hom_`-over-opposites owner folds to this head, so the public
accumulation rules do not expose the brittle normalized `hom_`/`Op_func`
expression. A temporary probe also confirmed that making
`hom_precomp_along_func` a reducible alias is the weaker choice: it typechecks,
but then rules either have to match the raw owner or risk a rewrite cycle if a
fold is added back to the alias.

One focused probe found that the post/left rules must not hard-code the fixed
source endpoint as syntactic `F[X]` on the LHS. Representable postcomposition
can reduce `F[X]` to a composite before the rule sees it. The implemented rule
therefore keeps that endpoint as an inferred pattern variable; typing still
forces it to be the correct endpoint.

The v2 "exchange law" check was ported as a v3.2 full-owner interchange
regression. It uses `hom_postcomp_func(...) o tapp1_func(...)` rather than the
old pointwise `fapp1_fapp0 postcomp_g beta` spelling, because the latter now
reduces through the specialized hom-postcomposition projection ladder before
generic capped naturality can match.

## Implementation Notes 2026-06-15

The generalized precomposition head still needs the same projection ladder as
the postcomposition head. Right now it has the object action:

```text
hom_precomp_along_func(F,Z,h)[g] = g o F[h]
```

but it does not yet have the arrow-action analogue:

```text
hom_precomp_along_func(F,Z,h)[alpha]
  : Hom(g,k) -> Hom(g o F[h], k o F[h])
```

So it should get projection heads parallel to `hom_postcomp_func`:

```text
hom_precomp_along_fapp1_func(F,Z,h,g,k)
hom_precomp_along_fapp1_fapp0(F,Z,h,g,k,alpha)
```

with rules:

```text
fapp1_func(hom_precomp_along_func(F,Z,h), g, k)
  -> hom_precomp_along_fapp1_func(...)

fapp0(hom_precomp_along_fapp1_func(...), alpha)
  -> hom_precomp_along_fapp1_fapp0(...)

fapp1_fapp0(hom_precomp_along_func(F,Z,h), g, k, alpha)
  -> hom_precomp_along_fapp1_fapp0(...)
```

It should also get the higher tele projection, fully parallel to
`hom_postcomp_tele_func`:

```text
hom_precomp_along_tele_func(F,Z,W,X)
  : Hom_A(W,X) -> Functor(Hom_B(F[X],Z), Hom_B(F[W],Z))
```

so that the raw `hom_`-over-opposites full action can fold to it, and then the
object action of the tele head gives `hom_precomp_along_func`.

Replacing the old identity-specialized precomposition heads was staged rather
than done in one large migration. The recommended phase at that point was:

1. Add the missing `hom_precomp_along_*` projection ladder.
2. Add Cat-specific folds analogous to the existing postcomp folds, so
   generalized precomposition in `Cat_cat` folds to `comp_cat_con_func`, and its
   arrow action folds to `comp_cat_con_fapp1_func` / `comp_cat_con_transf`.
3. Keep the old heads initially as the identity-functor specialization for
   compatibility.
4. After checks pass, migrate the old heads to either fold into
   `hom_precomp_along_func(id_A,Z,h)`, if the generalized head should be
   canonical, or remain as identity-specialized stable aliases if that proves
   less brittle.

Thus, that implementation was a good first slice, but not the final symmetric
architecture. The full `hom_precomp_along_func` projection ladder was built
first, and the older identity-specialized heads were then retired after a
focused probe.

### Implementation Result

The generalized precomposition ladder has now been added in `emdash3_2.lp`:

```text
hom_precomp_along_tele_func(F,Z,W,X)
hom_precomp_along_func(F,Z,h)
hom_precomp_along_fapp1_func(F,Z,h,g,k)
hom_precomp_along_fapp1_fapp0(F,Z,h,g,k,alpha)
```

The raw contravariant representable owner folds at both the full and capped
levels:

```text
fapp1_func(hom_(Op(B),Op(A),Op(F),Z), X, W)
  -> hom_precomp_along_tele_func(F,Z,W,X)

fapp1_fapp0(hom_(Op(B),Op(A),Op(F),Z), X, W, h)
  -> hom_precomp_along_func(F,Z,h)
```

The Cat-valued specialization now folds generalized precomposition along
`F[h]` to the existing `comp_cat_con_*` heads:

```text
hom_precomp_along_func(F,Z,h)
  -> comp_cat_con_func(F[h])

hom_precomp_along_fapp1_func(F,Z,h,G,H)
  -> comp_cat_con_fapp1_func(F[h],G,H)

hom_precomp_along_fapp1_fapp0(F,Z,h,G,H,eta)
  -> comp_cat_con_transf(F[h],G,H,eta)
```

Follow-up probing chose the generalized head as canonical. The old
identity-specialized heads were removed from `emdash3_2.lp`; ordinary
represented-object precomposition is now expressed as:

```text
hom_precomp_along_func(id_A,Z,h)
hom_precomp_along_fapp1_func(id_A,Z,h,g,k)
hom_precomp_along_fapp1_fapp0(id_A,Z,h,g,k,alpha)
```

The internal-hom component, representable transport component, and strict
pre/right naturality and functoriality RHSs now use this identity-specialized
generalized form directly.

Probe note: a standalone assertion equating the raw full
`fapp1_func(hom_(Op(B),Op(A),Op(F),Z),X,W)` with
`hom_precomp_along_tele_func(F,Z,W,X)` was unnecessarily brittle because the
assertion forced type conversion across unreduced `Op_cat` endpoints. The rule
itself typechecks, and the diagnostics assert the downstream stable behavior:
tele object projection, capped raw fold, full arrow-action projection, capped
arrow-action projection, and Cat-valued folds.

### Opposite-Postcomp Bridge Decision

The `hom_precomp_along_*` ladder intentionally duplicates the postcomposition
projection/action story at the variance boundary. We should not wait until final
`comp_fapp0` projection for opposite-specialized postcomposition to meet
precomposition: the full functor-level owners matter for later strict
naturality, functoriality, and higher projection rules.

The canonical orientation should be:

```text
hom_postcomp_* over opposites  ->  hom_precomp_along_*
```

not the symmetric inverse. The inverse would reintroduce two canonical normal
forms and create unnecessary overlap/cycle risk. The directed bridge makes the
general postcomposition route join the specialized contravariant route.

The bridge rules to probe and implement are:

```text
hom_postcomp_tele_func(Op(B), Op(A), Op(F), Z, X, W)
  -> hom_precomp_along_tele_func(F,Z,W,X)

hom_postcomp_func(Op(B), Op(A), Op(F), Z, X, W, h)
  -> hom_precomp_along_func(F,Z,W,X,h)

hom_postcomp_fapp1_func(Op(B), Op(A), Op(F), Z, X, W, h, g, k)
  -> hom_precomp_along_fapp1_func(F,Z,W,X,h,g,k)

hom_postcomp_fapp1_fapp0(Op(B), Op(A), Op(F), Z, X, W, h, g, k, alpha)
  -> hom_precomp_along_fapp1_fapp0(F,Z,W,X,h,g,k,alpha)
```

These rules do not make `hom_con` primitive. They only ensure that when the
existing `hom_` owner is seen through opposites and already projected into a
postcomposition stable head, it normalizes back to the contravariant
`hom_precomp_along_*` stable head rather than surviving as a second normal
form.

Implementation result: the four directed bridge rules were added to
`emdash3_2.lp`. Focused diagnostics were added at the projected surfaces:

```text
fapp0(hom_postcomp_tele_func(Op(B),Op(A),Op(F),Z,X,W), h)
  -> hom_precomp_along_func(F,Z,W,X,h)

fapp0(hom_postcomp_func(Op(B),Op(A),Op(F),Z,X,W,h), g)
  -> g o F[h]

fapp0(hom_postcomp_fapp1_func(Op(B),Op(A),Op(F),Z,X,W,h,g,k), alpha)
  -> hom_precomp_along_fapp1_fapp0(F,Z,W,X,h,g,k,alpha)
```

Direct assertions equating the unreduced opposite `hom_postcomp_*` functor
heads with the corresponding `hom_precomp_along_*` heads were deliberately not
used as diagnostics: they ask Lambdapi to solve brittle type conversion across
`Op_cat` endpoints before the projected computation has a chance to expose the
canonical stable head. The rules themselves pass subject reduction; the
projected assertions are the robust regression surface.

### Direct Opposite-Hom Rule Cleanup

After adding the directed opposite-postcomp bridge, the earlier direct
opposite-specific raw `hom_` rules should be simplified away. The full rule:

```text
fapp1_func(hom_(Op(B),Op(A),Op(F),Z), X, W)
  -> hom_precomp_along_tele_func(F,Z,W,X)
```

is derivable through the general postcomposition route:

```text
fapp1_func(hom_(Op(B),Op(A),Op(F),Z), X, W)
  -> hom_postcomp_tele_func(Op(B),Op(A),Op(F),Z,X,W)
  -> hom_precomp_along_tele_func(F,Z,W,X)
```

The capped direct rule is not derivable unless the general capped
postcomposition fold exists:

```text
fapp1_fapp0(hom_(A,B,F,W), X, Y, f)
  -> hom_postcomp_func(A,B,F,W,X,Y,f)
```

Focused probing showed the correct cleanup sequence:

1. Add the general capped postcomposition fold above.
2. Remove both direct opposite-specific raw `hom_ -> hom_precomp_along_*`
   rules.
3. Keep the directed bridge
   `hom_postcomp_* over opposites -> hom_precomp_along_*`.

This makes the architecture cleaner:

```text
hom_ projection -> hom_postcomp_*
opposite-specialized hom_postcomp_* -> hom_precomp_along_*
```

rather than having `hom_` sometimes bypass `hom_postcomp_*` directly into
`hom_precomp_along_*`.

Implementation also needs the identity-on-higher-arrows companions for the
stable post/precomposition projection heads. Once capped `hom_` action folds to
`hom_postcomp_func`, generic identity functoriality no longer sees the raw
`fapp1_fapp0` head; it sees:

```text
hom_postcomp_fapp1_fapp0(..., g, g, id_g)
hom_precomp_along_fapp1_fapp0(..., g, g, id_g)
```

These must reduce to the identity at the accumulated 1-cell. The diagnostic
that exposed this was the PathOut transitivity computation: the composite first
normalized to a Sigma pair whose fibre component was
`hom_postcomp_fapp1_fapp0(id_Z, q, p, p, id_p)` instead of `id_(q o p)`.

### Generalized `Cat_cat` Postcomposition Exits

The first implementation kept the semantic postcomposition exits too narrow:

```text
hom_postcomp_fapp1_func(Cat,Cat,id_Cat, ...)
hom_postcomp_fapp1_fapp0(Cat,Cat,id_Cat, ...)
```

These are only the special case where the varying endpoint functor is the
identity endofunctor on `Cat_cat`. The intended generalized exits parallel the
already-general precomposition exits:

```text
hom_postcomp_func(Cat,Cat,E,W,X,Y,f)
  -> comp_cat_cov_func(W, E[X], E[Y], E[f])

hom_postcomp_fapp1_func(Cat,Cat,E,W,X,Y,f,G,H)
  -> comp_cat_cov_fapp1_func(W, E[X], E[Y], E[f], G, H)

hom_postcomp_fapp1_fapp0(Cat,Cat,E,W,X,Y,f,G,H,eta)
  -> comp_cat_cov_transf(W, E[X], E[Y], E[f], G, H, eta)
```

This generalization should replace the identity-only `hom_postcomp_func`
special case rather than coexist with it.

The confluence-sensitive overlap is not primarily the opposite bridge:
`hom_postcomp_* (Op(B), Op(A), Op(F), ...)` does not directly overlap
`Cat_cat Cat_cat E` because `Op_cat Cat_cat` is not currently reduced to
`Cat_cat`. The real overlap is with identity-on-higher-arrow rules. To make the
semantic exits join, add the semantic identity reductions:

```text
comp_cat_cov_transf(G,F,F,id_F) -> id_(G o F)
comp_cat_con_transf(F,G,G,id_G) -> id_(G o F)
```

Focused probing of these generalized exits plus the semantic identity rules
typechecked and preserved the diagnostic suite.

### Generalized Tele-Level `Cat_cat` Exits

The remaining identity-only tele rule:

```text
hom_postcomp_tele_func(Cat,Cat,id_Cat,X,Y,Z)
  -> comp_cat_cov_func_func(X,Y,Z)
```

is the special case of a general semantic fold. For an arbitrary endofunctor
`E : Cat -> Cat`, the tele-level postcomposition action factors through the
arrow action of `E`:

```text
hom_postcomp_tele_func(Cat,Cat,E,W,X,Y)
  -> comp_cat_cov_func_func(W,E[X],E[Y]) o E[X,Y]
```

where `E[X,Y]` is `fapp1_func(E,X,Y)`.

The matching precomposition tele-level fold needs the object-level package:

```text
comp_cat_con_func_func(X,Y,Z)[F] = comp_cat_con_func(F)
```

Then the generalized precomposition tele fold is:

```text
hom_precomp_along_tele_func(Cat,Cat,E,Z,W,X)
  -> comp_cat_con_func_func(E[W],E[X],Z) o E[W,X]
```

Focused probing showed that the generalized postcomp tele rule, the minimal
`comp_cat_con_func_func` package, and the generalized precomp tele rule all
typecheck and preserve the diagnostic suite. Higher-arrow action for
`comp_cat_con_func_func` can be considered later if a concrete computation
needs it; the tele fold only needs the object action above.

### Cat-Specialized Semantic Heads And Tele Higher Action

The Cat-specialized heads are not all equally forced by mathematics. In
principle, some rules currently attached to heads such as
`comp_cat_cov_func` or `comp_cat_cov_fapp1_func` could be written directly on
long Cat-specialized `hom_postcomp_*` left-hand sides. The first heads that are
strongly justified by extra exposed structure are:

```text
comp_cat_cov_transf
comp_cat_con_transf
```

Their results are transfors in `Cat_cat`, so they support the additional
transfor projections:

```text
tapp0_fapp0(...)
tapp1_func(...)
tapp1_fapp0(...)
```

Those projections do not make sense on a completely generic
`hom_postcomp_fapp1_fapp0` or `hom_precomp_along_fapp1_fapp0`, whose result is
only an arrow in an arbitrary hom category. They could be attached directly to
Cat-specialized hom-action patterns, but the patterns would be long and brittle.
The practical convention is therefore:

```text
Cat-specialized semantic heads package extra structure exposed only when the
ambient category is Cat_cat.
```

The parent Cat-specialized heads remain useful as a coherent projection ladder
and readable normal form, even if the strongest theoretical need starts at the
transfor-producing level.

For the tele layer, the remaining uniformity gap is the higher action of:

```text
hom_postcomp_tele_func(F,W,X,Y)
```

Add stable projection heads:

```text
hom_postcomp_tele_fapp1_func(F,W,X,Y,f,g)
hom_postcomp_tele_fapp1_fapp0(F,W,X,Y,f,g,alpha)
```

with projection rules:

```text
fapp1_func(hom_postcomp_tele_func(F,W,X,Y), f, g)
  -> hom_postcomp_tele_fapp1_func(F,W,X,Y,f,g)

fapp0(hom_postcomp_tele_fapp1_func(F,W,X,Y,f,g), alpha)
  -> hom_postcomp_tele_fapp1_fapp0(F,W,X,Y,f,g,alpha)

fapp1_fapp0(hom_postcomp_tele_func(F,W,X,Y), f, g, alpha)
  -> hom_postcomp_tele_fapp1_fapp0(F,W,X,Y,f,g,alpha)
```

The identity-Cat specialization should join the existing object-level tele
fold:

```text
hom_postcomp_tele_func(Cat,Cat,id_Cat,X,Y,Z)
  -> comp_cat_cov_func_func(X,Y,Z)
```

so its higher action should fold to:

```text
hom_postcomp_tele_fapp1_func(Cat,Cat,id_Cat,X,Y,Z,G,H)
  -> comp_cat_cov_func_func_fapp1_func(X,Y,Z,G,H)

hom_postcomp_tele_fapp1_fapp0(Cat,Cat,id_Cat,X,Y,Z,G,H,eta)
  -> comp_cat_cov_func_func_transf(X,Y,Z,G,H,eta)
```

For arbitrary `E : Cat -> Cat`, the object-level tele head now folds through a
composite:

```text
hom_postcomp_tele_func(Cat,Cat,E,W,X,Y)
  -> comp_cat_cov_func_func(W,E[X],E[Y]) o E[X,Y]
```

so the higher action has a confluence-sensitive overlap with the generic
`fapp1_func` / `fapp1_fapp0` rules for `comp_cat_fapp0`. Focused probing chose
to install explicit arbitrary-`E` Cat folds oriented through that same composite
route:

```text
hom_postcomp_tele_fapp1_func(Cat,Cat,E,W,X,Y,L,M)
  -> fapp1_func(comp_cat_cov_func_func(W,E[X],E[Y]) o E[X,Y], L, M)

hom_postcomp_tele_fapp1_fapp0(Cat,Cat,E,W,X,Y,L,M,alpha)
  -> fapp1_fapp0(comp_cat_cov_func_func(W,E[X],E[Y]) o E[X,Y], L, M, alpha)
```

The semantic content of the capped arbitrary-`E` case is postcomposition by the
transfor `E[alpha]`, i.e. a `comp_cat_cov_func_func_transf` whose transfor
argument is the capped arrow action of `fapp1_func(E,X,Y)` on `alpha`. The
implemented diagnostics check that this semantic normal form is reached:

```text
hom_postcomp_tele_fapp1_fapp0(Cat,Cat,E,W,X,Y,L,M,alpha)
  -> comp_cat_cov_func_func_transf(W,E[X],E[Y],E[L],E[M],E[alpha])
```

where:

```text
E[alpha] = fapp1_fapp0(fapp1_func(E,X,Y), L, M, alpha)
```

The identity-Cat instance then computes as a consequence:

```text
hom_postcomp_tele_fapp1_func(Cat,Cat,id_Cat,W,X,Y,G,H)
  -> comp_cat_cov_func_func_fapp1_func(W,X,Y,G,H)

hom_postcomp_tele_fapp1_fapp0(Cat,Cat,id_Cat,W,X,Y,G,H,eta)
  -> comp_cat_cov_func_func_transf(W,X,Y,G,H,eta)
```

### Precomposition Tele Higher Action Follow-Up

The contravariant tele head should receive the same higher-action treatment:

```text
hom_precomp_along_tele_fapp1_func(F,Z,W,X,h,k)
hom_precomp_along_tele_fapp1_fapp0(F,Z,W,X,h,k,alpha)
```

For the Cat-specialized arbitrary-`E` case, the existing tele object fold is:

```text
hom_precomp_along_tele_func(Cat,Cat,E,Z,W,X)
  -> comp_cat_con_func_func(E[W],E[X],Z) o E[W,X]
```

Therefore the higher action should join the same composite route:

```text
hom_precomp_along_tele_fapp1_fapp0(Cat,Cat,E,Z,W,X,L,M,alpha)
  -> fapp1_fapp0(
       comp_cat_con_func_func(E[W],E[X],Z) o E[W,X],
       L,M,alpha)
```

To expose the semantic normal form, `comp_cat_con_func_func` also needs the
matching higher-action projection heads:

```text
comp_cat_con_func_func_fapp1_func(X,Y,Z,F,K)
comp_cat_con_func_func_transf(X,Y,Z,F,K,alpha)
```

with object component:

```text
comp_cat_con_func_func_transf(F,K,alpha)[G]
  = comp_cat_cov_transf(G,F,K,alpha)
```

The expected arbitrary-`E` capped tele normal form is then:

```text
hom_precomp_along_tele_fapp1_fapp0(Cat,Cat,E,Z,W,X,L,M,alpha)
  -> comp_cat_con_func_func_transf(E[W],E[X],Z,E[L],E[M],E[alpha])
```

Implementation result: focused probing typechecked this mirror slice and the
rules were added to `emdash3_2.lp`. The opposite-postcomposition bridge was
extended too:

```text
hom_postcomp_tele_fapp1_func(Op(B),Op(A),Op(F),Z,X,W,h,k)
  -> hom_precomp_along_tele_fapp1_func(F,Z,W,X,h,k)

hom_postcomp_tele_fapp1_fapp0(Op(B),Op(A),Op(F),Z,X,W,h,k,alpha)
  -> hom_precomp_along_tele_fapp1_fapp0(F,Z,W,X,h,k,alpha)
```

The diagnostics check generic precomp tele projection, the opposite bridge, the
`comp_cat_con_func_func` higher-action projection, its object component

```text
comp_cat_con_func_func_transf(F,K,alpha)[G]
  -> comp_cat_cov_transf(G,F,K,alpha)
```

and both arbitrary-`E` and identity-Cat normal forms.
