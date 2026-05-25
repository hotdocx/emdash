# emdash v3.2 Pi Alias, Projection Pullback, And Directed Induction Plan

Draft status: proposed implementation plan. As of 2026-05-25, the main kernel
parts of this plan have been implemented in `emdash3_2.lp`; see
`reports/REPORT_EMDASH_V3_PI_ALIAS_SIGMA_PROJ1_IMPLEMENTATION_REPORT_2026-05-25.md`.

Date: 2026-05-25.

## Scope

This plan proposes a focused redesign of the current dependent-product
architecture in `emdash3_2.lp`.

The main recommendation is:

```text
Pi_cat E
  should be a defined alias for
Functord_cat (Const_catd K Terminal_cat) E
```

with a separate stable constructor for the important comprehension/pullback
case:

```text
Sigma_proj1_pullback_catd R D
  ~= pullback of D along Sigma_proj1_func R
```

This plan also recommends demoting the current `piapp1_*` projection chain from
foundational kernel structure to surface/derived notation wherever possible.
Section action should be recovered from the general displayed-functor and
displayed-transformation machinery.

## Motivation

The current file treats `Pi_cat E` as a stable primitive category head:

```lambdapi
injective symbol Pi_cat [K : Cat] (E : τ (Catd K)) : Cat;

rule @Functord_cat $K (@Const_catd $K Terminal_cat) $E
  ↪ @Pi_cat $K $E;
```

This made `Pi_cat` convenient for user-facing section categories, but it also
introduced a second kernel normal form for the same mathematical object:

```text
sections of E
  = displayed functors Const_K(1) -> E
```

That duplication then required bridges such as:

```lambdapi
rule Hom_cat (@Pi_cat $K $E) $s $t
  ↪ @Transfd_cat $K (@Const_catd $K Terminal_cat) $E $s $t;
```

and a separate terminal-source section-action chain:

```text
fdapp1_int_transfd
  -> piapp1_int
  -> piapp1_int_src_transf
  -> piapp1_int_src_app
  -> piapp1_int_tgt_transf
  -> piapp1_func
```

Those heads solved real typing and normalization problems in the current
architecture, but the problems are partly caused by keeping `Pi_cat` as an
independent kernel head.

If `Pi_cat` is just notation for terminal-source `Functord_cat`, then:

```text
s : Obj(Pi_cat E)
```

is definitionally:

```text
s : Obj(Functord_cat (Const_catd K Terminal_cat) E)
```

and ordinary displayed projection/action infrastructure can be used directly.

## Design Thesis

The kernel should have one canonical representation for section categories:

```text
Functord_cat (Const_catd K Terminal_cat) E
```

`Pi_cat E` should remain as mathematical notation and as a user-facing surface
constructor, but not as a separate rewrite discriminator.

The kernel should still introduce stable heads where a real computational
construction needs one. The important example here is not general
`Pullback_catd`, but the special pullback along a Sigma projection:

```text
Sigma_proj1_pullback_catd R D
```

This constructor supports the dependent-Yoneda/comprehension conversion:

```text
Pi_{(k,r):Sigma R} D[k]
  ~= Functord(R,D)
```

which is needed for directed/path-dependent induction.

## Current Architecture Summary

The current `emdash3_2.lp` has:

```lambdapi
symbol Fibre_cat [K : Cat] (E : τ (Catd K)) (k : τ (Obj K)) : Cat
≔ @fapp0 K Cat_cat E k;

symbol Pullback_catd [A B : Cat] (E : τ (Catd B)) (F : τ (Functor A B))
  : τ (Catd A)
≔ @comp_cat_fapp0 A B Cat_cat E F;

injective symbol Pi_cat [K : Cat] (E : τ (Catd K)) : Cat;
rule @Functord_cat $K (@Const_catd $K Terminal_cat) $E
  ↪ @Pi_cat $K $E;
rule @Pi_cat $K (@Const_catd $K $A) ↪ Functor_cat $K $A;

unif_rule Obj (@Pi_cat $K $E) ≡ Obj (@Pi_cat $K' $E')
  ↪ [ $K ≡ $K'; $E ≡ $E' ];

rule Hom_cat (@Pi_cat $K $E) $s $t
  ↪ @Transfd_cat $K (@Const_catd $K Terminal_cat) $E $s $t;
```

The current `piapp0` is already a defined surface/projection form:

```lambdapi
symbol piapp0_func [K : Cat] (E : τ (Catd K)) (k : τ (Obj K))
  : τ (Functor (Pi_cat E) (Fibre_cat E k))
≔ comp_cat_fapp0
     (@fapp0_func Terminal_cat (Fibre_cat E k) Terminal_obj)
     (@tapp0_func K Cat_cat (@Const_catd K Terminal_cat) E k);

symbol piapp0 : Π [K : Cat], Π [E : τ (Catd K)],
  Π (s : τ (Obj (Pi_cat E))),
  Π (k : τ (Obj K)),
  τ (Obj (Fibre_cat E k))
≔ λ K E s k, @fapp0 (Pi_cat E) (Fibre_cat E k) (@piapp0_func K E k) s;
```

This part is aligned with the proposed direction. The issue is not `piapp0`
itself; it is the independent `Pi_cat` category head and the extra `piapp1_*`
kernel chain built around it.

## Probe Evidence

Temporary local probes were run during discussion. They were removed afterward;
no changes were made to `emdash3_2.lp`.

### Probe A: Naive Pi Alias

The naive change:

```lambdapi
symbol Pi_cat [K : Cat] (E : τ (Catd K)) : Cat
≔ @Functord_cat K (@Const_catd K Terminal_cat) E;
```

without other edits fails immediately because Lambdapi does not allow rewrite
rules to be added to a symbol already defined with `≔`.

This only rules out a drop-in alias.

### Probe B: Deeper Pi Alias Migration

A deeper temporary migration typechecked after:

1. replacing primitive `Pi_cat` by a defined alias;
2. moving constant-family collapse to `Functord_cat`;
3. removing the `Obj(Pi_cat ...)` unification helper;
4. removing the `Hom_cat(Pi_cat ...)` bridge rule;
5. unfolding `Pi_cat` in `pi_eval_transf` declarations/rules;
6. unfolding `Pi_cat` in `section_pullback_func` and
   `section_pullback_sec` declarations/rules.

The essential temporary diff was:

```lambdapi
symbol Pi_cat [K : Cat] (E : τ (Catd K)) : Cat
≔ @Functord_cat K (@Const_catd K Terminal_cat) E;

rule @Functord_cat $K (@Const_catd $K Terminal_cat) (@Const_catd $K $A)
  ↪ Functor_cat $K $A;
```

and the `pi_eval_transf` source family was made explicit:

```lambdapi
injective symbol pi_eval_transf [K : Cat] (E : τ (Catd K))
  : τ (Functord
      (@Const_catd K (@Functord_cat K (@Const_catd K Terminal_cat) E))
      E);

rule @tapp0_fapp0
      $K Cat_cat
      (@Const_catd $K (@Functord_cat $K (@Const_catd $K Terminal_cat) $E))
      $E $k
      (@pi_eval_transf $K $E)
  ↪ @piapp0_func $K $E $k;
```

Likewise, `section_pullback_func` was given its canonical source and target:

```lambdapi
symbol section_pullback_func [A B : Cat]
  (F : τ (Functor A B)) (E : τ (Catd B))
  : τ (Functor
      (@Functord_cat B (@Const_catd B Terminal_cat) E)
      (@Functord_cat A (@Const_catd A Terminal_cat) (@Pullback_catd A B E F)));
```

This probe suggests the Pi-alias architecture is feasible with a focused
migration.

### Probe C: Projection Pullback Bridge

A separate temporary probe introduced:

```lambdapi
injective symbol Sigma_proj1_pullback_catd [K : Cat]
  (R D : τ (Catd K))
  : τ (Catd (@Sigma_cat K R));
```

with rules:

```lambdapi
rule @comp_cat_fapp0
      (@Sigma_cat $K $R)
      $K
      Cat_cat
      $D
      (@Sigma_proj1_func $K $R)
  ↪ @Sigma_proj1_pullback_catd $K $R $D;

rule @fapp0
      (@Sigma_cat $K $R)
      Cat_cat
      (@Sigma_proj1_pullback_catd $K $R $D)
      (Struct_sigma $k $r)
  ↪ @Fibre_cat $K $D $k;
```

In the current primitive-`Pi_cat` architecture, this bridge typechecked:

```lambdapi
rule @Pi_cat
      (@Sigma_cat $K $R)
      (@Sigma_proj1_pullback_catd $K $R $D)
  ↪ @Functord_cat $K $R $D;
```

In the Pi-alias architecture, the corresponding bridge also typechecked:

```lambdapi
rule @Functord_cat
      (@Sigma_cat $K $R)
      (@Const_catd (@Sigma_cat $K $R) Terminal_cat)
      (@Sigma_proj1_pullback_catd $K $R $D)
  ↪ @Functord_cat $K $R $D;
```

Assertions also typechecked:

```lambdapi
assert [K : Cat] (R D : τ (Catd K))
  (k : τ (Obj K)) (r : τ (Obj (Fibre_cat R k))) ⊢
  Fibre_cat (@Sigma_proj1_pullback_catd K R D) (Struct_sigma k r)
    ≡ Fibre_cat D k;

assert [K : Cat] (R D : τ (Catd K)) ⊢
  @Pi_cat (@Sigma_cat K R) (@Sigma_proj1_pullback_catd K R D)
    ≡ @Functord_cat K R D;

assert [K : Cat] (R D : τ (Catd K))
  (s t : τ (Obj (@Pi_cat (@Sigma_cat K R)
    (@Sigma_proj1_pullback_catd K R D)))) ⊢
  Hom_cat (@Pi_cat (@Sigma_cat K R)
    (@Sigma_proj1_pullback_catd K R D)) s t
    ≡ @Transfd_cat K R D s t;
```

This suggests the projection-pullback technique is useful independently of the
Pi representation choice.

## Recommended Target Architecture

### Canonical Section Category

Use `Functord_cat` as the canonical kernel normal form:

```text
Pi_cat E
  := Functord_cat (Const_catd K Terminal_cat) E
```

Consequences:

- `Pi_cat` is not injective.
- `Pi_cat` has no rewrite rules.
- `Pi_cat` has no `Obj` unification helper.
- `Hom_cat (Pi_cat E) s t` reduces through the general `Functord_cat` hom rule.
- Section morphisms are just displayed transformations from the terminal source.

### Constant-Family Collapse

Move the constant-family section collapse to the canonical head:

```lambdapi
rule @Functord_cat $K (@Const_catd $K Terminal_cat) (@Const_catd $K $A)
  ↪ Functor_cat $K $A;
```

This keeps:

```text
Pi_cat (Const_catd K A)
  ~= Functor_cat K A
```

by unfolding `Pi_cat`.

### Section Evaluation

Keep `piapp0_func` and `piapp0` as defined surface notation. They are useful
and already conceptually correct.

However, update declarations and rule left-hand sides that need stable matching
to use the canonical `Functord_cat` expression instead of matching on `Pi_cat`.

### Section Action

Demote `piapp1_*` from foundational kernel structure.

The current names:

```text
piapp1_src_obj
piapp1_func
piapp1_fapp0
piapp1_int
piapp1_int_src_transf
piapp1_int_src_app
piapp1_int_tgt_transf
```

were useful in the primitive-`Pi_cat` architecture because they provided a
stable terminal-source path from displayed internal action to surface section
action.

In the target architecture, section action should be derived from:

```text
tdapp0 / tdapp1 / fdapp1 / Transfd
```

applied to:

```text
s : Functord(Const_K(1), E)
```

Surface notation such as:

```text
s[f]
```

can remain, but it should elaborate to the general displayed-action projection,
not to an independent Pi-action kernel pipeline.

## Migration Plan

### Phase 0: Baseline And Probe Discipline

Before edits:

```bash
timeout 60s lambdapi check -w emdash3_2.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

Make migration changes in a temporary copy first:

```bash
cp emdash3_2.lp tmp_pi_alias_migration.lp
timeout 30s lambdapi check -w tmp_pi_alias_migration.lp
```

Do not keep temporary probe files.

### Phase 1: Convert `Pi_cat` To A Defined Alias

Replace:

```lambdapi
injective symbol Pi_cat [K : Cat] (E : τ (Catd K)) : Cat;

rule @Functord_cat $K (@Const_catd $K Terminal_cat) $E
  ↪ @Pi_cat $K $E;
rule @Pi_cat $K (@Const_catd $K $A) ↪ Functor_cat $K $A;

unif_rule Obj (@Pi_cat $K $E) ≡ Obj (@Pi_cat $K' $E')
  ↪ [ $K ≡ $K'; $E ≡ $E' ];

rule Hom_cat (@Pi_cat $K $E) $s $t
  ↪ @Transfd_cat $K (@Const_catd $K Terminal_cat) $E $s $t;
```

with:

```lambdapi
symbol Pi_cat [K : Cat] (E : τ (Catd K)) : Cat
≔ @Functord_cat K (@Const_catd K Terminal_cat) E;

rule @Functord_cat $K (@Const_catd $K Terminal_cat) (@Const_catd $K $A)
  ↪ Functor_cat $K $A;
```

Expected assertion changes:

```lambdapi
assert [K : Cat] (E : τ (Catd K)) ⊢
  @Functord_cat K (@Terminal_catd K) E ≡ Pi_cat E;
```

should continue to hold by unfolding `Terminal_catd` and `Pi_cat`.

```lambdapi
assert [K : Cat] (A : Cat) ⊢
  Pi_cat (Const_catd K A) ≡ Functor_cat K A;
```

should continue to hold through the new `Functord_cat` constant-family rule.

```lambdapi
assert [K : Cat] (E : τ (Catd K)) (s t : τ (Obj (Pi_cat E))) ⊢
  Hom_cat (Pi_cat E) s t
    ≡ @Transfd_cat K (@Const_catd K Terminal_cat) E s t;
```

should continue to hold through the general:

```lambdapi
rule Hom_cat (@Functord_cat $K $E $D) $FF $GG
  ↪ @Transfd_cat $K $E $D $FF $GG;
```

### Phase 2: Update `pi_eval_transf`

Current declaration:

```lambdapi
injective symbol pi_eval_transf [K : Cat] (E : τ (Catd K))
  : τ (Functord (@Const_catd K (@Pi_cat K E)) E);
```

Recommended canonical declaration:

```lambdapi
injective symbol pi_eval_transf [K : Cat] (E : τ (Catd K))
  : τ (Functord
      (@Const_catd K (@Functord_cat K (@Const_catd K Terminal_cat) E))
      E);
```

Current rule:

```lambdapi
rule @tapp0_fapp0
      $K Cat_cat (@Const_catd $K (@Pi_cat $K $E)) $E $k
      (@pi_eval_transf $K $E)
  ↪ @piapp0_func $K $E $k;
```

Recommended canonical rule:

```lambdapi
rule @tapp0_fapp0
      $K Cat_cat
      (@Const_catd $K (@Functord_cat $K (@Const_catd $K Terminal_cat) $E))
      $E $k
      (@pi_eval_transf $K $E)
  ↪ @piapp0_func $K $E $k;
```

Rationale: after `Pi_cat` becomes defined notation, matching through
`@Pi_cat` in inferred family slots can become brittle. The stable form is the
canonical `Functord_cat` expression.

### Phase 3: Update `section_pullback_func`

Current declarations:

```lambdapi
symbol section_pullback_func [A B : Cat]
  (F : τ (Functor A B)) (E : τ (Catd B))
  : τ (Functor (@Pi_cat B E) (@Pi_cat A (@Pullback_catd A B E F)));

symbol section_pullback_sec [A B : Cat]
  (F : τ (Functor A B)) (E : τ (Catd B))
  (s : τ (Obj (@Pi_cat B E)))
  : τ (Obj (@Pi_cat A (@Pullback_catd A B E F)));
```

Recommended canonical declarations:

```lambdapi
symbol section_pullback_func [A B : Cat]
  (F : τ (Functor A B)) (E : τ (Catd B))
  : τ (Functor
      (@Functord_cat B (@Const_catd B Terminal_cat) E)
      (@Functord_cat A (@Const_catd A Terminal_cat)
        (@Pullback_catd A B E F)));

symbol section_pullback_sec [A B : Cat]
  (F : τ (Functor A B)) (E : τ (Catd B))
  (s : τ (Obj (@Functord_cat B (@Const_catd B Terminal_cat) E)))
  : τ (Obj (@Functord_cat A (@Const_catd A Terminal_cat)
        (@Pullback_catd A B E F)));
```

Current rule:

```lambdapi
rule @fapp0 (@Pi_cat $B $E) _ (@section_pullback_func $A $B $F $E) $s
  ↪ @section_pullback_sec $A $B $F $E $s;
```

Recommended canonical rule:

```lambdapi
rule @fapp0
      (@Functord_cat $B (@Const_catd $B Terminal_cat) $E)
      _
      (@section_pullback_func $A $B $F $E)
      $s
  ↪ @section_pullback_sec $A $B $F $E $s;
```

### Phase 4: Revalidate Existing Assertions

Run:

```bash
timeout 60s lambdapi check -w emdash3_2.lp
```

Expected fragile assertion zones:

- assertions around `pi_eval_transf`;
- assertions around `const_section_func`;
- assertions around `section_pullback_func`;
- assertions mentioning `Hom_cat (Pi_cat E)`;
- later `piapp1_*` assertions.

Do not delete assertions merely because the spelling changes. Prefer changing
the surface spelling to the canonical expression if needed.

### Phase 5: Introduce `Sigma_proj1_pullback_catd`

Add a special stable constructor:

```lambdapi
injective symbol Sigma_proj1_pullback_catd [K : Cat]
  (R D : τ (Catd K))
  : τ (Catd (@Sigma_cat K R));
```

Add a fold from the specific composition:

```lambdapi
rule @comp_cat_fapp0
      (@Sigma_cat $K $R)
      $K
      Cat_cat
      $D
      (@Sigma_proj1_func $K $R)
  ↪ @Sigma_proj1_pullback_catd $K $R $D;
```

Add fibre computation:

```lambdapi
rule @fapp0
      (@Sigma_cat $K $R)
      Cat_cat
      (@Sigma_proj1_pullback_catd $K $R $D)
      (Struct_sigma $k $r)
  ↪ @Fibre_cat $K $D $k;
```

Add the comprehension bridge in the Pi-alias architecture:

```lambdapi
rule @Functord_cat
      (@Sigma_cat $K $R)
      (@Const_catd (@Sigma_cat $K $R) Terminal_cat)
      (@Sigma_proj1_pullback_catd $K $R $D)
  ↪ @Functord_cat $K $R $D;
```

This is the kernel form of:

```text
sections over Sigma R of D pulled back along pi1
  = displayed functors R -> D
```

Add regression assertions:

```lambdapi
assert [K : Cat] (R D : τ (Catd K))
  (k : τ (Obj K)) (r : τ (Obj (Fibre_cat R k))) ⊢
  Fibre_cat (@Sigma_proj1_pullback_catd K R D) (Struct_sigma k r)
    ≡ Fibre_cat D k;

assert [K : Cat] (R D : τ (Catd K)) ⊢
  @Pi_cat (@Sigma_cat K R) (@Sigma_proj1_pullback_catd K R D)
    ≡ @Functord_cat K R D;

assert [K : Cat] (R D : τ (Catd K))
  (s t : τ (Obj (@Pi_cat (@Sigma_cat K R)
    (@Sigma_proj1_pullback_catd K R D)))) ⊢
  Hom_cat (@Pi_cat (@Sigma_cat K R)
    (@Sigma_proj1_pullback_catd K R D)) s t
    ≡ @Transfd_cat K R D s t;
```

### Phase 6: Audit `piapp1_*`

Do not delete `piapp1_*` immediately. First classify each symbol:

```text
piapp1_src_obj              likely keep as defined surface helper
piapp1_func                 candidate for removal or defined alias
piapp1_fapp0                likely keep only as surface notation
piapp1_int                  candidate for removal
piapp1_int_src_transf       candidate for removal
piapp1_int_src_app          candidate for removal
piapp1_int_tgt_transf       candidate for removal
```

The target should be:

```text
s[f]
```

elaborates through the general displayed-action stack:

```text
s : Functord(Const_K(1), E)
id_transfd s : Transfd s s
fdapp1_int_transfd s
tdapp0_fapp0 / tapp0_fapp0 projections
```

rather than through a separate Pi-specific internal chain.

Recommended audit procedure:

1. Keep `tdapp1_int_func_transfd`, `tdapp1_int_fapp0_transfd`,
   `tdapp1_int_fapp1_func_transfd`, and `fdapp1_int_transfd`.
2. Temporarily remove only the `piapp1_int_*` projection chain in a copy.
3. Keep `piapp1_src_obj` and `piapp1_fapp0` as definitions if they remain
   useful for surface assertions.
4. Run a bounded check.
5. For each failure, decide whether the assertion should be rewritten through
   the general displayed projection path instead of restoring the Pi-specific
   head.

Likely end state:

```text
piapp1_fapp0
```

is a surface alias, not a kernel rewrite target.

### Phase 7: Directed/Path-Dependent Motives

The path/arrow-dependent motive problem should be handled by changing the base
category, not by inventing a wholly separate transport primitive.

For a fixed object:

```text
x : Obj Z
```

define the raw covariant representable:

```text
Rep_Z(x)[y] = Hom_Z(x,y)
```

Do not use `Edge_catd_func` for this covariant transport. Current
`Edge_catd_func` is pointwise opposite:

```text
Edge_Z(x)[y] = Hom_Z(x,y)^op
```

The raw representable can be written through existing `hom_int`:

```text
Rep_Z(x) := fapp0 (hom_int Z Z (id_func Z)) x
```

Then define the outgoing-arrow total category:

```text
PathOut_Z(x) := Sigma_cat (Rep_Z(x))
```

A path/arrow-dependent motive is:

```text
E : Catd (PathOut_Z(x))
```

The source point is:

```text
(x, id_x) : Obj(PathOut_Z(x))
```

The essential missing kernel ingredient is a canonical arrow:

```text
pathout_refl_arrow Z x y p
  : Hom_{PathOut_Z(x)} (x,id_x) (y,p)
```

This arrow is the categorical analogue of the HoTT path-induction path from
`refl_x` to an arbitrary `p : x = y`.

Then directed induction can be represented as a section:

```text
path_ind_sec Z x E u : Obj (Pi_cat E)
```

with evaluation:

```text
piapp0 (path_ind_sec Z x E u) (Struct_sigma y p)
  ~= fapp0
       (fib_cov_tapp0_func
          E
          (Struct_sigma x (id x))
          (Struct_sigma y p)
          u)
       (pathout_refl_arrow Z x y p)
```

This uses existing `fib_cov_tapp0_func`, just over the base
`PathOut_Z(x)`.

### Phase 8: Specialization To Ordinary Transport

For:

```text
D : Catd Z
R := Rep_Z(x)
E := Sigma_proj1_pullback_catd R D
```

the new bridge gives:

```text
Pi_cat E
  ~= Functord_cat R D
```

The directed induction section should specialize to the current ordinary
transport package:

```text
fib_cov_transf D x u : Functord R D
```

The desired assertion shape is:

```lambdapi
assert [Z : Cat] (D : τ (Catd Z)) (x : τ (Obj Z))
  (u : τ (Obj (Fibre_cat D x))) ⊢
  path_ind_sec Z x (@Sigma_proj1_pullback_catd Z (Rep_Z x) D) u
    ≡ @fib_cov_transf Z D x u;
```

Exact syntax will depend on how `Rep_Z x`, `PathOut_Z x`, and
`path_ind_sec` are named.

## Internalized Constructor Audit

This migration also clarifies a broader rule:

```text
Only internalize constructors when a parameter genuinely varies under a binder.
Pick the variance from the mathematical action, not from the syntactic arity.
```

Already present:

```text
Cat_cat
Functor_cat_func
Functor_cat_fapp0_func
Op_catd_func
Sigma_func
Pi_func
Functor_catd_func
Functor_catd_fapp0_func
Edge_catd_func
Presheaf_catd_func
HomPresheaf_catd_func
hom_int
homd_int
fib_cov_int
```

Likely additions:

```text
Raw representable package for y |-> Hom_Z(x,y)
PathOut/Sigma representable package
Sigma_proj1_pullback_catd
possibly a functorial package for Sigma_proj1_pullback_catd
```

Do not add internalized constructors merely for symmetry. For example, broad
general internalization of `Pullback_catd` may create more rewrite overlap than
it solves. The special `Sigma_proj1_pullback_catd` is preferred because it is a
real comprehension rule.

## Risks

### Risk 1: Losing Useful Pi Unification

Removing:

```lambdapi
unif_rule Obj (@Pi_cat $K $E) ≡ Obj (@Pi_cat $K' $E')
```

may expose inference failures that were previously hidden.

Mitigation:

- use canonical `Functord_cat` forms in declarations that need inference;
- only add new unification helpers for canonical stable heads;
- do not reintroduce a unification helper for `Pi_cat` once it is defined.

### Risk 2: Reintroducing Terminal-Source Loops

The implementation report already warns not to add a broad rule:

```text
tapp0_fapp0 (Const_catd K Terminal_cat) E k s
  -> Obj_func ... (piapp0 s k)
```

because `piapp0` is itself defined through the same projection path.

Mitigation:

- keep exact stable-head folds;
- prefer canonical `Functord_cat` declarations;
- avoid recursive rules involving `piapp0`.

### Risk 3: Over-Broad Pullback Rules

Making all `Pullback_catd` cases injective or giving it broad computation
rules may interfere with existing composition normalization.

Mitigation:

- add only `Sigma_proj1_pullback_catd`;
- fold only the exact composition with `Sigma_proj1_func`;
- postpone any general `Pullback_catd` redesign.

### Risk 4: Removing `piapp1_*` Too Early

The current `piapp1_*` chain encodes successful hard-won normal forms. Removing
it before equivalent displayed-action assertions exist may lose test coverage.

Mitigation:

- first migrate `Pi_cat`;
- then add equivalent assertions through general `fdapp1_int_transfd`;
- only then retire Pi-specific heads.

## Validation Strategy

Minimum validation after each phase:

```bash
timeout 30s lambdapi check -w emdash3_2.lp
```

Full validation:

```bash
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

Suggested focused assertions:

```text
Pi_cat E
  == Functord_cat ConstTerminal E

Pi_cat Const(A)
  == Functor_cat K A

Hom_cat (Pi_cat E) s t
  == Transfd_cat ConstTerminal E s t

piapp0 F k for Const_catd
  == fapp0 F k

pi_eval_transf E at k
  == piapp0_func E k

section_pullback_func F E applied to s, then evaluated at a
  == s(F a)

Pi_cat (Sigma_proj1_pullback_catd R D)
  == Functord_cat R D

Hom_cat (Pi_cat (Sigma_proj1_pullback_catd R D)) s t
  == Transfd_cat R D s t
```

For directed induction:

```text
path_ind_sec x E u at (x,id_x)
  == u

path_ind_sec x (Sigma_proj1_pullback_catd Rep_x D) u
  == fib_cov_transf D x u
```

The last two are future targets and may require adding a canonical arrow in the
Sigma representable category first.

## Proposed Implementation Order

1. Convert `Pi_cat` to a defined alias.
2. Move constant-family section collapse to `Functord_cat`.
3. Update `pi_eval_transf`.
4. Update `section_pullback_func` and `section_pullback_sec`.
5. Revalidate all existing assertions.
6. Add `Sigma_proj1_pullback_catd`.
7. Add projection-pullback assertions.
8. Audit and simplify `piapp1_*`.
9. Add raw representable notation distinct from `Edge_catd_func`.
10. Add `PathOut`/outgoing-arrow total category notation.
11. Add canonical arrow from `(x,id_x)` to `(y,p)`.
12. Add directed induction section.
13. Prove specialization to existing `fib_cov_transf`.

## Acceptance Criteria

The migration is successful if:

- `emdash3_2.lp` typechecks with `Pi_cat` as a defined alias.
- No rewrite rule has `Pi_cat` as its defined head.
- Existing section evaluation behavior still works.
- Constant-family sections still reduce to ordinary functors.
- `Hom_cat (Pi_cat E)` reduces through the general `Functord_cat` route.
- `Sigma_proj1_pullback_catd` supports the comprehension conversion to
  `Functord_cat R D`.
- The remaining `piapp1_*` names, if any, are clearly marked as surface or
  compatibility aliases rather than primitive kernel structure.

## Open Questions

1. Should `Pi_func` remain an injective functor package if `Pi_cat` is defined?

   Tentative answer: yes. `Pi_func` internalizes the operation
   `E |-> Pi_cat E`; it may still be useful as a stable package even if its
   object action unfolds to `Functord_cat ConstTerminal E`.

2. Should `piapp1_fapp0` remain as a named surface helper?

   Tentative answer: yes, but only as a definition/elaboration target. It
   should not drive kernel normalization.

3. Should there be a general `Pullback_catd` injective constructor?

   Tentative answer: no, not yet. The projection-pullback case is special and
   semantically justified.

4. Should raw representables get a named constructor distinct from
   `Edge_catd_func`?

   Tentative answer: yes. `Edge_catd_func` is pointwise opposite and is correct
   for presheaf/dependent-hom contravariance. Directed induction needs the raw
   covariant representable.

5. Is the canonical arrow in `Sigma_cat (Rep_x)` definable from existing Sigma
   hom rules?

   Tentative answer: maybe, but it should likely be introduced as a stable head
   first, then connected to the Sigma hom normal form by assertions. This avoids
   requiring too much from the still-developing Sigma hom infrastructure.

## Summary

The recommended foundation is:

```text
Pi_cat E
  = notation for Functord_cat ConstTerminal E

section action
  = general displayed action specialized to terminal source

Sigma_proj1_pullback_catd R D
  = stable comprehension pullback along Sigma projection

Pi_cat (Sigma_proj1_pullback_catd R D)
  = Functord_cat R D

directed/path-dependent induction
  = existing fib_cov transport over Sigma of a raw representable
```

This should reduce kernel duplication, make section categories part of the
general displayed-functor calculus, and provide the right foundation for motives
that depend on an arrow/path argument.
