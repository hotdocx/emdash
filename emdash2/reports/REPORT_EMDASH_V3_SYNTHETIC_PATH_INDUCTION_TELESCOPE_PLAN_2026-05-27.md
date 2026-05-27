# emdash v3.2 Synthetic Path Induction Telescope Plan

Draft status: replacement-forward plan for the internalized path-induction
work. This report is intended to supersede, for future planning, the older
reports:

- `reports/REPORT_EMDASH_V3_INTERNALIZED_PATH_INDUCTION_PLAN.md`
- `reports/REPORT_EMDASH_V3_INTERNALIZED_PATH_INDUCTION_IMPLEMENTATION_REPORT_2026-05-26.md`

Those older reports remain useful as historical implementation records. The
active recommendation below is different: the primary internalized-`x` theorem
should be formulated as a displayed transformation (`Transfd`) over the
varying motive category, not primarily as a displayed functor over the Sigma
total category of pairs `(x,E)`.

Date: 2026-05-27.

## Executive Summary

The current `emdash3_2.lp` implementation successfully reached a meaningful
outer-`x` package:

```text
PathInd_funcd(Z)
  : Functord(PathIndSrc_Z, PathIndTgt_Z)
```

over the total category:

```text
Sigma x : Z, PathOutMotives_Z[x]
```

where:

```text
PathOutMotives_Z[x] = Catd(PathOut_Z(x)).
```

This type is accepted and its component at `(x,E)` computes to the fixed-`x`
path-induction functor:

```text
PathInd_funcd(Z)[(x,E)] = path_ind_func_fapp0(Z,x,E).
```

However, subsequent review showed that this Sigma-total formulation is not the
best primary architecture. It compresses a telescope:

```text
x : Z
E : Catd(PathOut_Z(x))
```

into one total object `(x,E)`, and then the theorem appears to require
naturality for arbitrary total arrows:

```text
(p, alpha) : (x,E) -> (y,E')
```

This is stronger and less synthetic than the intended sequential theorem.

The better primary formulation is:

```text
PathInd_transfd(Z)
  : Transfd(PathOutReflEval_funcd(Z), PathOutPi_funcd(Z)).
```

In surface syntax:

```text
PathInd_transfd(Z) :
  (x :^n Z) ->
    PathInd_src(Z,x) => PathInd_tgt(Z,x)
```

where:

```text
PathInd_src(Z,x)[E] = E[(x,id_x)]
PathInd_tgt(Z,x)[E] = Pi q : PathOut_Z(x), E[q].
```

The component should compute as:

```text
PathInd_transfd(Z)[x] = PathInd_func(Z,x)
PathInd_transfd(Z)[x][E](u) = path_ind_sec(Z,x,E,u).
```

This is the synthetic/telescope form of internalized path induction. The
current Sigma-total `PathInd_funcd` should eventually become a derived
uncurrying of `PathInd_transfd`, not the primary theorem.

## Current Implemented Baseline

The current file `emdash3_2.lp` already contains the necessary foundation for
the new plan.

### Fixed-`x` Motive Domain

For a category `Z` and object `x : Obj(Z)`:

```text
Rep_Z(x)[y] = Hom_Z(x,y)
PathOut_Z(x) = Sigma y : Z, Hom_Z(x,y).
```

The fixed-`x` motive is:

```text
E : Catd(PathOut_Z(x)).
```

This is the correct computational categorical-semantics form. A surface
language may print it in curried form:

```text
E : Pi y : Z, Hom_Z(x,y) -> Cat
```

but the kernel should keep the compiled categorical form:

```text
E : Catd(Sigma y, Hom_Z(x,y)).
```

### Fixed-`x` Path Induction

The fixed-`x` constructor is:

```text
path_ind_sec(Z,x,E,u)
  : Pi q : PathOut_Z(x), E[q]
```

with:

```text
u : E[(x,id_x)].
```

It is packaged as:

```text
PathInd_func(Z,x)
  : Functord(PathInd_src(Z,x), PathInd_tgt(Z,x))
```

where:

```text
PathInd_src(Z,x)[E] = E[(x,id_x)]
PathInd_tgt(Z,x)[E] = Pi q : PathOut_Z(x), E[q].
```

This remains foundational. It corresponds to ordinary DTT/HoTT-style path
induction in a context containing `x`.

### Varying Motive Category

The implemented varying-base package is:

```text
PathOutMotives_Z : Z -> Cat
PathOutMotives_Z[x] = Catd(PathOut_Z(x)).
```

It is implemented as a true directed family:

```text
PathOutMotives_catd(Z) : Catd(Z).
```

For `p : x -> y`, the action is reindexing along:

```text
PathOut_transport(p) : PathOut_Z(y) -> PathOut_Z(x).
```

Thus:

```text
PathOutMotives_Z[p](E) = p_*E
  = PathOut_transport(p)^* E.
```

### Internal Source And Target Packages

The source-side and target-side fixed-`x` functors have already been
internalized over `x`:

```text
PathOutReflEval_funcd(Z)
  : Functord(PathOutMotives_Z, Const_Z(Cat))

PathOutPi_funcd(Z)
  : Functord(PathOutMotives_Z, Const_Z(Cat)).
```

Their components are:

```text
PathOutReflEval_funcd(Z)[x] = PathInd_src(Z,x)
PathOutPi_funcd(Z)[x]       = PathInd_tgt(Z,x).
```

This is the key observation behind the revised plan. These two objects are
already the source and target needed for a displayed transformation over `Z`.

### Current Sigma-Total Package

The implementation also contains:

```text
PathIndSrc_Z[(x,E)] = E[(x,id_x)]
PathIndTgt_Z[(x,E)] = Pi q : PathOut_Z(x), E[q]

PathInd_funcd(Z)
  : Functord(PathIndSrc_Z, PathIndTgt_Z)
```

over:

```text
Sigma x : Z, PathOutMotives_Z[x].
```

This package should be reinterpreted as an uncurried/compiled presentation. It
is useful, but it should no longer be the main design target.

## Conversation History And Design Lessons

This section records the reasoning that led to the new plan. It is intentionally
included so future iterations do not repeat the same false starts.

### 1. Fixed-`x` vs Internalized-`x`

Early discussion asked whether the implementation was still in a fixed-`x`
phase or had reached an internalized-`x` phase. The answer was: both were
present.

The fixed-`x` theorem existed as:

```text
PathInd_func(Z,x).
```

The first outer-`x` package existed as:

```text
PathInd_funcd(Z)
```

over the Sigma total category of `(x,E)`.

At that point, the outer-`x` package was coherent enough to typecheck, but the
component-level coherence projections were still not cheap.

### 2. Internalization Must Be Synthetic, Not Object-Level

Several review rounds stressed that object-level formulas are not enough. For
example:

```text
PathInd_tgt(Z,x)[E] = Pi(E)
```

is only prose unless it is represented by an actual functor/displayed functor
whose projections compute.

This led to the implementation of real internal packages:

```text
Catd_cat_func
Pullback_catd_func
Pi_int_funcd
Pi_pullback_funcd
PathOut_cat_func
PathOutMotives_catd
PathOutPi_funcd
PathOutReflEval_funcd
```

The standing SOP remains important:

- keep rewrite-rule LHS endpoint family slots implicit unless they are true
  discriminators;
- avoid reducible compound expressions in implicit arguments on rule LHSs;
- prefer semantic definitions first;
- add stable heads only when projection, discrimination, or performance needs
  justify them.

### 3. `Pi_int_funcd` And Varying Bases

A major prerequisite was realizing that Pi over varying bases must be
contravariant in the base:

```text
Pi_int_funcd
  : Functord(Catd_cat_func, Const_{Cat^op}(Cat)).
```

At a base `K`:

```text
Pi_int_funcd[K] = Pi_func(K).
```

For a functor `F : A -> B`, section pullback has direction:

```text
Pi_B(E) -> Pi_A(F^*E).
```

This led to the stable fold:

```text
Pi_pullback_funcd(G)[x] = Pi_func(G[x]).
```

This infrastructure is still correct and is reused by `PathOutPi_funcd`.

### 4. The Transitivity Benchmark Corrected The Stable-Head Diagnosis

The fixed-`x` transitivity/composition benchmark initially looked like it might
need primitive path-specific stable heads. Further review showed that the
semantic presentation was viable:

```text
CompTarget_Z(x)[y] = Functord(Rep_Z(y), Rep_Z(x)).
```

The blockers were narrower:

- a missing capped `fapp1_fapp0` rule for `Op_func`;
- assertions using reducible fibre expressions in explicit source/target slots
  instead of canonical endpoint forms.

After those corrections, the fixed-`x` benchmark computes:

```text
path_comp_sec(x)[p][z](q) = q o p.
```

This remains the main regression test for any redesigned path-induction
architecture.

### 5. Current Remaining Blockers Were Symptoms Of The Wrong Primary Shape

The earlier assessment listed blockers:

```text
1. component-level coherence for PathInd_transport_transf
2. generic component API for functord_transport_transf
3. naturality of the Sigma-total PathInd_funcd
4. construction/coherence of rho
5. arbitrary Sigma-total arrows vs canonical transported-motive arrows
```

The later review clarified that blockers 1, 2, 3, and 5 are largely symptoms of
using the Sigma-total presentation as the primary theorem. That presentation
asks for behavior along arbitrary total arrows:

```text
(p, alpha) : (x,E) -> (y,E').
```

The implementation now follows this diagnosis: `functord_transport_transf` and
the derived `PathInd_transport_transf` transport-square layer have been removed
from the active file. Source and target transport for path induction are direct
definitions, while the primary theorem remains the telescope-shaped
`PathInd_transfd`.

The intended telescope theorem first internalizes `x` in the source and target
functors:

```text
PathOutReflEval_funcd(Z), PathOutPi_funcd(Z)
```

and then gives a displayed transformation between them:

```text
PathInd_transfd(Z).
```

The naturality square is then part of the `Transfd` structure, not a separate
manually stated theorem.

### 6. Core/Discrete Discussion

We considered a weaker theorem where the variation in `x` is over a core or
discrete groupoid. In retrospect, this is close to the existing fixed-`x`
theorem in a Lambdapi context:

```text
x : Obj(Z)
E : Catd(PathOut_Z(x))
u : E[(x,id_x)]
```

This is useful as intuition, but it is not the right replacement for the
directed internalized theorem. The directed theorem remains feasible if
expressed synthetically.

### 7. Discrete Fibration vs Cartesian/Cleavage Restriction

The current Sigma-total formulation has a useful canonical arrow:

```text
sigma_{p,E} : (x,E) -> (y,p_*E).
```

It is tempting to say that only those arrows should exist, making the motive
family "discrete" over `Z`. More accurately, the full fibre

```text
PathOutMotives_Z[x] = Catd(PathOut_Z(x))
```

is not discrete. What we want is to separate:

```text
x-direction: canonical reindexing E |-> p_*E
E-direction: ordinary motive morphisms inside Catd(PathOut_Z(x)).
```

The Sigma-total category fuses these directions. The telescope/`Transfd`
formulation keeps them conceptually separate.

### 8. The Two Sigmas

Two Sigma constructions were discussed:

```text
PathOut_Z(x) = Sigma y, Hom_Z(x,y)
```

and:

```text
Sigma x, PathOutMotives_Z[x].
```

The first Sigma is mathematically and computationally appropriate. It is the
categorical-semantics compilation of a curried motive:

```text
E : Pi y : Z, Hom_Z(x,y) -> Cat.
```

The second Sigma is a compiled context/telescope representation. It should not
be removed from the kernel entirely, but it should not be the primary theorem
surface. The primary theorem should use the sequential/telescope form
represented by `Transfd`.

### 9. Global Coherent Motive Families Are Deferred

Another possible theorem shape is:

```text
M : Obj(Pi_cat(PathOutMotives_Z))
u : Pi x, M[x][(x,id_x)]
--------------------------------
Pi x, Pi q : PathOut_Z(x), M[x][q].
```

This is meaningful, but it is not the core path-induction theorem. It is a
global section theorem for a coherent family of motives varying in `x`.

It should be deferred. The immediate target is the internal telescope theorem:

```text
PathInd_transfd(Z)
  : Transfd(PathOutReflEval_funcd(Z), PathOutPi_funcd(Z)).
```

### 10. `rho` Is Elementary But Still A Construction Task

The arrow:

```text
rho_{x,y,p} : (x,id_x) -> (y,p) in PathOut_Z(x)
```

is mathematically elementary:

```text
rho_{x,y,p} = (p, id_p).
```

Equivalently, it should be obtained from:

```text
sigma_transport_arrow(Rep_Z(x), p, id_x)
```

once the endpoint:

```text
Rep_Z(x)[p](id_x) = p
```

computes cleanly by:

```text
p o id_x = p.
```

The construction of `rho` is not the central design blocker. It remains an
important cleanup task and should eventually remove the current
`pathout_refl_arrow` constant.

## Revised Design Thesis

The correct active theorem is the telescope/displayed-transformation theorem:

```text
PathInd_transfd(Z)
  : Transfd(PathOutReflEval_funcd(Z), PathOutPi_funcd(Z)).
```

Expanded:

```text
PathInd_transfd(Z)
  : Transfd
      (PathOutReflEval_funcd Z)
      (PathOutPi_funcd Z)
```

where both endpoints are displayed functors:

```text
PathOutReflEval_funcd(Z),
PathOutPi_funcd(Z)
  : Functord(PathOutMotives_Z, Const_Z(Cat)).
```

At each `x`, the component is an ordinary transformation between functors:

```text
PathInd_transfd(Z)[x]
  : PathOutReflEval_funcd(Z)[x] => PathOutPi_funcd(Z)[x].
```

Since Cat-valued transformations reduce to displayed functors, this component
is exactly:

```text
PathInd_func(Z,x)
  : Functord(PathInd_src(Z,x), PathInd_tgt(Z,x)).
```

Then:

```text
PathInd_transfd(Z)[x][E]
  : E[(x,id_x)] -> Pi q : PathOut_Z(x), E[q]

PathInd_transfd(Z)[x][E](u)
  = path_ind_sec(Z,x,E,u).
```

This matches the `_int*` design pattern:

- define a semantically correct internal object;
- expose stable projection heads;
- keep endpoint/source/target family slots implicit in rules where possible;
- use assertions to document mathematical component equations.

## Ported SOP And Design Hygiene

This section ports forward the implementation discipline from the older
path-induction plan and implementation report. Future work should treat these
rules as part of the replacement plan, not as historical notes.

### Rewrite LHS Hygiene

Rewrite rules should match the smallest stable discriminator that actually
matters. In particular:

- keep inferred source/target categories, endpoint families, and similar
  reconstructible arguments implicit on rule LHSs unless they are the real
  discriminator;
- avoid explicit compound or reducible expressions in implicit-argument
  positions on rule LHSs;
- do not match against readability aliases when the canonical unfolded head is
  the one Lambdapi will see after reduction;
- probe nontrivial rules in a temporary copy with a focused assertion before
  committing them to `emdash3_2.lp`;
- prefer narrow rules over broad `tapp0_fapp0`, `tdapp0_fapp0`,
  `Pullback_catd`, or arbitrary transfor projection rules.

The failure mode to avoid is a rule that is mathematically right but
operationally brittle because its LHS contains a large normalized pullback,
Sigma, or hom expression in a slot that Lambdapi should have inferred.

### Canonical Endpoint Spelling

When an assertion or helper type must spell source/target categories
explicitly, prefer canonical endpoint forms over reducible fibre wrappers.

Examples:

```text
Hom_cat Z x y
Functord_cat Z (Rep_catd Z y) (Rep_catd Z x)
```

are usually better explicit endpoints than:

```text
Fibre_cat (CompTarget_catd Z x) y
```

unless the assertion is specifically testing that fibre reduction. This was the
root cause of several false blockers in the fixed-`x` transitivity benchmark.

### Stable Heads Policy

The default path is:

```text
semantic definition first, stable head only after a focused probe justifies it.
```

A stable head is justified when it is a real projection, discrimination, or
performance boundary. It is not justified merely because a formula is easier to
read under a shorter name.

Many good stable heads are projections from a more internalized construction,
but they should be introduced only when a focused probe shows an actual
projection or performance boundary. Current active Sigma transport now prefers
transparent definitions through the fundamental Sigma-arrow constructor:

```text
Pi_pullback_funcd(G)[x] = Pi_func(G[x])
sigma_transport_arrow(E,p,u) = sigma_arrow(E,u,E[p](u),p,id)
Sigma_catd_transport_func(...) = Sigma_catd_functord_catd(...)[sigma_transport_arrow(...)]
PathInd_transfd(Z)[x] = PathInd_func(Z,x)
```

This pattern preserves the internal/synthetic object while exposing the
component that rewrite search needs. Helper aliases should route through the
semantic constructor rather than duplicating semantic bodies.

### Object-Level vs Arrow-Action-Level

Object-level formulas are not enough for internalized infrastructure. A package
such as:

```text
PathOutMotives_Z[x] = Catd(PathOut_Z(x))
```

must also have the correct action on arrows:

```text
p : x -> y
E : Catd(PathOut_Z(y))
--------------------------------
p^*E : Catd(PathOut_Z(x))
```

and its projections must compute in the contexts where later packages use it.
The same warning applies to `PathOutReflEval_funcd`, `PathOutPi_funcd`,
`PathInd_transfd`, and any future uncurrying construction.

If an implementation step starts requiring manually written naturality squares,
check whether the missing object should instead be a displayed functor or
displayed transformation whose action/naturality is synthetic. Manual squares
may be useful as projected lemmas, but they should not become the primary
architecture when an internal `_int*` package is the intended concept.

### Capped Action vs Full Hom/Omega Action

The file often needs both:

```text
fapp1_fapp0 F p
```

and:

```text
fapp1_func F a b
```

The first is the capped action of a functor on one displayed arrow/object-level
component. The second is the full hom-action functor. They are related, but
neither should be treated as a complete substitute for the other.

The transitivity benchmark exposed the typical issue: `Op_func` had a full
hom-action rule, but the semantic `hom_con` route needed the capped rule:

```text
fapp1_fapp0(Op_func F, p) = fapp1_fapp0(F, p) with endpoints reversed.
```

Adding that narrow capped rule was correct. Replacing the full synthetic action
with capped object-only reasoning would not have been correct. Future work
should check which level is needed before adding a helper or rule.

### Assertion Placement And Documentation

Assertions/checks with mathematical content should live near the symbols they
explain, not in a generic diagnostic block. Examples include component laws
such as:

```text
PathInd_transfd(Z)[x] = PathInd_func(Z,x)
PathInd_transfd(Z)[x][E](u) = path_ind_sec(Z,x,E,u)
path_comp_sec(Z,x)[(y,p)][z](q) = q o p
```

Diagnostic checks that only probe Lambdapi normalization or a temporary
regression can remain in a dedicated debug/diagnostic section, but theorem-like
assertions should be documented as formulas and kept with their motivation.

When feasible, each nontrivial symbol and theorem-style assertion should have a
nearby header comment giving the mathematical notation and/or faithful surface
syntax from
`reports/REPORT_EMDASH_V3_FAITHFUL_SURFACE_SYNTAX_PLAN.md`. The Lambdapi term
may still use explicit canonical endpoints when that improves checking
stability.

### Validation Workflow

For implementation turns touching `emdash3_2.lp`, validate incrementally:

```bash
timeout 60s lambdapi check -w emdash3_2.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
git diff --check
```

If a bounded check times out after a rewrite/projection change, treat it as a
rewrite/unification regression until a focused probe says otherwise. Inspect
the rule LHS before redesigning the mathematical architecture.

## Proposed New Symbols

### `PathInd_transfd`

Candidate declaration:

```lambdapi
constant symbol PathInd_transfd [Z : Cat]
  : τ (@Transfd
      Z
      (@PathOutMotives_catd Z)
      (@Const_catd Z Cat_cat)
      (@PathOutReflEval_funcd Z)
      (@PathOutPi_funcd Z));
```

Intended component rule:

```text
tdapp0_fapp0(PathInd_transfd(Z), x) = PathInd_func(Z,x).
```

Approximate Lambdapi shape:

```lambdapi
rule @tdapp0_fapp0
      $Z
      _
      _
      _
      _
      $x
      (@PathInd_transfd $Z)
  ↪ @PathInd_func $Z $x;
```

The actual rule must be probed. The discriminator should be the stable head
`PathInd_transfd`; reducible endpoint family expressions should stay implicit.

Expected checks:

```text
PathInd_transfd(Z)[x] == PathInd_func(Z,x)

PathInd_transfd(Z)[x][E] == path_ind_func_fapp0(Z,x,E)

PathInd_transfd(Z)[x][E](u) == path_ind_sec(Z,x,E,u).
```

### `Sigma_transfd_funcd` Or Equivalent Uncurrying

After `PathInd_transfd` works, the existing Sigma-total theorem should be
derivable by a generic uncurrying construction.

For:

```text
R : Catd(K)
S,T : Functord(R, Const_K(Cat))
eta : Transfd(S,T)
```

define:

```text
Sigma_transfd_funcd(eta)
  : Functord(Sigma_catd_functord_catd(S),
             Sigma_catd_functord_catd(T)).
```

At a total object `(k,r)`:

```text
Sigma_transfd_funcd(eta)[(k,r)]
  = eta[k][r].
```

Then the current Sigma-total path-induction package should become:

```text
PathInd_funcd(Z)
  = Sigma_transfd_funcd(PathInd_transfd(Z)).
```

This is the right direction because it turns the old Sigma-total formulation
into a compiled theorem derived from the more synthetic telescope theorem.

This generic uncurrying construction may need stable projection heads only
after a concrete downstream theorem justifies them, especially for action along
canonical total arrows:

```text
sigma_transport_arrow(R,p,r).
```

But those projections should be consequences of the generic uncurrying
architecture, not path-specific ad hoc rules.

## Implementation Plan

### Phase 0: Reclassify The Existing Sigma Package

Do not delete `PathInd_funcd` immediately. Reclassify it in comments/docs as:

```text
uncurried Sigma-total presentation, to be made derived later
```

rather than:

```text
primary final internalized-x theorem.
```

This avoids breaking existing assertions while the new telescope theorem is
introduced.

### Phase 1: Add `PathInd_transfd`

Add:

```text
PathInd_transfd(Z)
  : Transfd(PathOutReflEval_funcd(Z), PathOutPi_funcd(Z)).
```

Add the component projection:

```text
PathInd_transfd(Z)[x] = PathInd_func(Z,x).
```

Then add focused assertions:

```text
tdapp0_fapp0(PathInd_transfd(Z),x)
  == PathInd_func(Z,x)

tdapp0_fapp0(PathInd_transfd(Z),x)[E]
  == path_ind_func_fapp0(Z,x,E)

tdapp0_fapp0(PathInd_transfd(Z),x)[E](u)
  == path_ind_sec(Z,x,E,u).
```

Use canonical endpoint forms in assertions if Lambdapi struggles with reducible
aliases.

### Phase 2: Reroute The Transitivity Benchmark Through `PathInd_transfd`

The fixed-`x` transitivity motive remains:

```text
CompMotive_Z(x)[(y,p)]
  = Functord(Rep_Z(y), Rep_Z(x)).
```

The test should be expressible through the new component:

```text
PathInd_transfd(Z)[x][CompMotive_Z(x)](id_{Rep_Z(x)})
  = path_comp_sec(Z,x)
```

and:

```text
PathInd_transfd(Z)[x][CompMotive_Z(x)](id_{Rep_Z(x)})[(y,p)][z](q)
  = q o p.
```

This is the main check that the new theorem is not merely better-looking, but
still computes correctly for the benchmark.

### Phase 3: Design `Sigma_transfd_funcd`

Only after `PathInd_transfd` is stable, introduce a generic uncurrying helper:

```text
Sigma_transfd_funcd(eta)
```

for:

```text
eta : Transfd(S,T).
```

The initial goal is object-component computation:

```text
Sigma_transfd_funcd(eta)[(k,r)] = eta[k][r].
```

Then specialize:

```text
PathInd_funcd(Z) = Sigma_transfd_funcd(PathInd_transfd(Z)).
```

This may require keeping the existing `PathInd_funcd` constant temporarily
while adding assertions that its behavior matches the derived presentation.

### Phase 4: Construct `rho`

Replace or bridge:

```text
pathout_refl_arrow(Z,x,y,p)
```

with the generic Sigma transport arrow:

```text
sigma_transport_arrow(Rep_Z(x), p, id_x).
```

The key endpoint computation is:

```text
Rep_Z(x)[p](id_x) = p.
```

This phase is independent enough to be done before or after Phase 3, but it is
not required to validate `PathInd_transfd` as a type-theoretic architecture.

### Phase 5: Surface Syntax Documentation

Document the faithful surface syntax:

```text
PathOut_Z(x) = Sigma y : Z, Hom_Z(x,y)
E : Catd(PathOut_Z(x))
```

with an optional curried display:

```text
E(y,p)
```

for:

```text
E[(y,p)].
```

Do not make the curried form the primary kernel representation in v3.2. It is
a surface/Fubini notation for the same categorical semantics.

## Deferred Work

### Global Coherent Motive Families

The theorem:

```text
M : Obj(Pi_cat(PathOutMotives_Z))
u : Pi x, M[x][(x,id_x)]
--------------------------------
Pi x, Pi q : PathOut_Z(x), M[x][q]
```

is deferred. It is a useful global-section theorem, but not the core
path-induction constructor.

### Arbitrary Sigma-Total Naturality

Naturality along arbitrary total arrows:

```text
(p, alpha) : (x,E) -> (y,E')
```

should be derived from:

```text
PathInd_transfd
```

plus a generic uncurrying/comprehension theorem, not hand-coded as the primary
path-induction theorem.

### Curried Kernel Motives

A kernel-level curried motive type:

```text
Pi y : Z, Hom_Z(x,y) -> Cat
```

may eventually be useful, especially for user-facing elaboration. For the
current computational categorical-semantics kernel, keep:

```text
Catd(PathOut_Z(x)).
```

### Full `rho` Coherence

The law:

```text
rho_{x,z,q o p}
  =
PathOut_transport(p)(rho_{y,z,q}) o rho_{x,y,p}
```

is meaningful and likely follows from Sigma transport, associativity, and unit
laws once `rho` is constructed. It is not the immediate next blocker for the
`PathInd_transfd` type.

## Recommended Next Turn

The next implementation turn should do only the first narrow step:

1. Add `PathInd_transfd`.
2. Add its component projection to `PathInd_func`.
3. Add assertions for the component at `x`, at `E`, and at `u`.
4. Run:

```bash
timeout 60s lambdapi check -w emdash3_2.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

If that succeeds, reroute one transitivity assertion through
`PathInd_transfd`. Do not yet implement `Sigma_transfd_funcd` or construct
`rho` in the same turn unless the first step is completely stable.

## Summary Of The New Active Plan

The previous active target was:

```text
PathInd_funcd
  : Functord(PathIndSrc_Z, PathIndTgt_Z)
```

over:

```text
Sigma x, PathOutMotives_Z[x].
```

The new active target is:

```text
PathInd_transfd
  : Transfd(PathOutReflEval_funcd(Z), PathOutPi_funcd(Z)).
```

This is the synthetic telescope theorem:

```text
(x :^n Z) ->
  (E :^n Catd(PathOut_Z(x))) ->
    E[(x,id_x)] -> Pi q : PathOut_Z(x), E[q].
```

The Sigma-total theorem should become a derived uncurrying, not the primitive
source of truth.
