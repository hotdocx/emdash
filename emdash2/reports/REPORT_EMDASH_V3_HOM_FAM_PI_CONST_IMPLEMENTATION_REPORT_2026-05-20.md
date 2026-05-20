# emdash v3.2 Hom/Fam/Pi/Const Implementation Report

Date: 2026-05-20

## Scope

This report records the first implementation pass of
`REPORT_EMDASH_V3_HOM_FAM_PI_CONST_PLAN.md` into the new v3.2 fork
`emdash3_2.lp`.

The preserved baseline `emdash3_1.lp` was left unchanged. The new file
`emdash3_2.lp` was created as a fork of `emdash3_1.lp` and now carries the
initial Catd/Hom/Pi/constant-family migration.

## Validation Status

The current state typechecks.

Commands run:

```bash
timeout 30s lambdapi check -w emdash3_2.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

`make check` now checks:

```text
emdash2.lp
emdash3_1.lp
emdash3_2.lp
```

Continuation update: the 2026-05-20 follow-up pass also typechecks with the
same two commands after adding the internal `fib_cov_int` package, internal
object/hom action packagings, and the first `piapp1*` declarations.

Second continuation update: a later 2026-05-20 pass also typechecks after
adding the generalized endpoint/projection path for `homd_int FF` and the
derived `tdapp0` component notation.

Third continuation update: the next 2026-05-20 pass also typechecks after
adding derived fibre-level projections and derived fibre projections of
`fdapp1_int_transfd`.

Fourth continuation update: the next 2026-05-20 pass also typechecks after
adding the pointwise `Op_funcd` fibre projection, extra `Fibre_func` /
`homd_int` source-projection assertions, and the `piapp1_src_obj` helper. A
displayed-composition fibre projection was probed but remains deferred after a
timeout on the lower-level rule shape; a narrower `homd_int FF ∘ Op_funcd FF`
probe was also removed because an exact assertion did not reduce.

Correction update 2026-05-21: the displayed-composition probe above was
overstated. The failed probe did not follow the plan's rewrite SOP because it
spelled compound/reducible source and target families in inferred LHS slots of
`tapp0_fapp0`. The result should be treated as inconclusive evidence about that
particular bad rule shape, not as evidence that the planned projection is
impossible. The next code pass should retry with the source/target functor
arguments kept implicit (`_ _`), using the explicit data argument
`comp_fapp0 (Catd_cat K) ...` or another stable head as the discriminator. The
same review applies to the retained `Op_funcd` fibre-projection rule: it should
be re-probed with implicit source/target family slots.

Follow-up correction update 2026-05-21: the retained `Op_funcd` projection was
corrected to keep the source/target family slots implicit and the file still
typechecks. The displayed-composition projection was then retried with those
same implicit slots, both as a standalone `tapp0_fapp0` rule and as a `with`
sibling of the ordinary natural-transformation composition rule. Both
SOP-compliant forms still timed out in bounded checking, so the next route is no
longer another broad `tapp0_fapp0` pattern over unfolded
`comp_fapp0 (Catd_cat K) ...`; it is to promote `comp_catd_fapp0` from a
definitional alias into a stable displayed-composition head, with small fold and
identity rules attached to that head. That stable-head promotion typechecks.
However, a broad fibre projection attached to `comp_catd_fapp0`, and then a
narrow `homd_int FF ∘ Op_funcd FF` specialization attached to the same stable
head, both still timed out in bounded checking and were not kept. A subsequent
attempt to attach the projection to the derived `Fibre_func` notation was also
not viable because `Fibre_func` is a defined symbol, and Lambdapi rejected adding
rewrite rules to it.

Fifth continuation update: the 2026-05-21 pass typechecks after the
`Op_funcd` LHS correction, the stable `comp_catd_fapp0` promotion, and new
assertions covering displayed composition folding and identity reductions.

## Files Changed

- `emdash3_2.lp`: new v3.2 implementation fork.
- `scripts/check.sh`: now checks `emdash3_2.lp`.
- `Makefile`: check target comment updated.
- `README.md`: v3.2 file and direct check command documented.
- `AGENTS.md`: local SOP updated to treat `emdash3_2.lp` as the active v3.2 fork while keeping `emdash3_1.lp` as the preserved baseline.

## Implemented Successfully

### Baseline Fork And Canonical Spine

- Created `emdash3_2.lp` from `emdash3_1.lp`.
- Preserved the canonical directed-family spine:
  - `Functor_cat K Cat_cat -> Catd_cat K`
  - `Hom_cat (Catd_cat K) E D -> Functord_cat E D`
  - `@Transf_cat K Cat_cat E D -> Functord_cat E D`
  - `Hom_cat (Functord_cat E D) FF GG -> Transfd_cat FF GG`
- Promoted `comp_catd_fapp0` from a definitional alias into a stable displayed
  composition head:
  - `comp_fapp0 (Catd_cat K) E D C FF GG -> comp_catd_fapp0 FF GG`
  - `comp_catd_fapp0 FF (id_funcd E) -> FF`
  - `comp_catd_fapp0 (id_funcd D) GG -> GG`
- Did not reintroduce `Fam_*` vocabulary.
- Did not import the v2 `StrictFunctor_cat` / `sfunc_func` layer.

### Constant And Terminal Families

- Added the constant-functor calculus needed by the indirect cascades:
  - `fapp1_func (Const_func A B b) x y`
  - `fapp1_fapp0 (Const_func A B b) f`
  - `Op_func (Const_func A B b)`
  - composition with constant functors
  - `hom_ A B (Const_func B A u) w`
- Kept `Const_catd K A` as the stable constructor.
- Changed `Terminal_catd K` into a definitional alias:

```text
Terminal_catd K := Const_catd K Terminal_cat
```

- Removed separate terminal-specific `fapp0`, `fapp1_func`, `fapp1_fapp0`, and `Op_catd` rules from the v3.2 operational path.
- Added regression assertions for terminal-as-constant and terminal fibres.

### Pi And Section Evaluation

- Kept `Pi_cat E` as a primitive stable section category.
- Routed the necessary terminal-source join through the unfolded constant-terminal source:

```text
Functord_cat (Const_catd K Terminal_cat) E -> Pi_cat E
```

- Preserved non-dependent Pi:

```text
Pi_cat (Const_catd K A) -> Functor_cat K A
```

- Replaced primitive `piapp0` behavior with defined notation through `piapp0_func`.
- Moved the old `piapp0`-headed homd projection fold down to a lower-level `tapp0_fapp0` rule returning `Obj_func ...`.
- Added the constant-family `tapp0_fapp0` rule so:

```text
piapp0 F k -> fapp0 F k
```

for constant families.

### Mixed-Variance Constructors

The already-present v3.1 mixed-variance constructors were preserved in v3.2:

- `Functor_catd`
- `Functor_catd_mix_func`
- `Hom_catd`
- `Transf_catd`
- bridges:
  - `Hom_catd (Const_catd K Cat_cat) X Y -> Functor_catd ...`
  - `Hom_catd (Functor_catd A B) FF GG -> Transf_catd ...`

### Reordered Fibre Transport

- Kept `fib_cov_tapp0_func` as a defined semantic helper based on:

```text
comp_cat_fapp0 (fapp0_func u) (fapp1_func E x y)
```

- Added external `fib_cov_transf E x u`.
- Added its component fold:

```text
tapp0_fapp0 y (fib_cov_transf E x u) -> fib_cov_tapp0_func E x y u
```

- Converted `fib_cov_tapp0_fapp0` from the v3.1 primitive strict-transport head into a defined object projection:

```text
fib_cov_tapp0_fapp0 E x y f u :=
  fapp0 (fib_cov_tapp0_func E x y u) f
```

- Removed the old generic strict identity/composition transport rules for arbitrary `E`.
- Added constant-family regression assertions:
  - `fib_cov_tapp0_func (Const_catd K A) x y u -> Const_func ... A u`
  - `fib_cov_tapp0_fapp0 (Const_catd K A) x y f u -> u`

### Most-Internal `fib_cov` Package

- Added the internal fibre-transport package requested by the plan:
  - `FibCov_target_catd`
  - `FibCov_cat`
  - `FibCov`
  - `fib_cov_int`
  - `fib_cov_src_func`
- Added projection folds:

```text
tapp0_fapp0 x (fib_cov_int E) -> fib_cov_src_func E x
fapp0 (fib_cov_src_func E x) u -> fib_cov_transf E x u
```

- Added assertions showing that `FibCov_target_catd E` has fibres
  `Transf_cat (hom_ (id_func K) x) E`, and that the internal projection path
  reaches the already-existing external `fib_cov_transf` and component
  `fib_cov_tapp0_func`.

### Endpoint `homd_`

- Deleted `homd_semantic_func` as a permanent symbol.
- Made endpoint `homd_` a definition through the semantic `hom_con` body:

```text
homd_ E x u y v :=
  hom_con
    (Fibre_cat E y)
    v
    (Hom_cat K x y)
    (fib_cov_tapp0_func E x y u)
```

- Removed direct endpoint simulation rules:
  - `fapp0 (homd_ ...) -> ... homd_semantic_func ...`
  - `fapp1_func (homd_ ...) -> ... homd_semantic_func ...`
  - `fapp1_fapp0 (homd_ ...) -> ... homd_semantic_func ...`
- Removed direct endpoint rewrite rules for:
  - `homd_ (Const_catd K A) ...`
  - `homd_ (Terminal_catd K) ...`
- Preserved those normal forms as assertions reached by the indirect cascade.

### Generalized Endpoint `homd_funcd_`

- Added the explicit-displayed-functor endpoint:

```text
homd_funcd_ [D E] (FF : Functord D E) x u y v
```

where `u : E[x]` and `v : D[y]`. Its target object is computed by the fibre
component of `FF` at `y`, while transport still uses the ambient target family
`E`.

- Generalized the internal projection path:
  - `homd_src_funcd`
  - `homd_src_secd`
  - `homd_tgt_funcd`
- Changed the `homd_int` first projection rule to target the generalized
  `homd_src_funcd` head.
- Kept the old identity-only heads as stable compatibility normal forms:
  - `homd_src_func`
  - `homd_src_sec`
  - `homd_tgt_func`
  - `homd_`
- Added the displayed identity component fold:

```text
tapp0_fapp0 y (id_funcd E) -> id_func (E[y])
```

- Added assertions that:
  - `homd_int FF` projects to `homd_src_funcd FF`,
  - `homd_src_funcd FF` projects to `homd_src_secd FF`,
  - `piapp0 (homd_src_secd FF) y` projects to `homd_tgt_funcd FF`,
  - `fapp0 (homd_tgt_funcd FF) v` projects to `homd_funcd_ FF`,
  - the identity specialization `homd_funcd_ (id_funcd E)` joins the old
    `homd_ E` endpoint.

### Generalized `homd_int` And Displayed Internal Action

- Generalized `homd_int` to carry an explicit family morphism argument:

```text
homd_int [K] [D E : Catd K] (FF : Functord D E)
  : Functord (Op_catd E) (Homd_target_catd D)
```

- Updated the existing identity-specialization projection path to use:

```text
homd_int (id_funcd E)
```

- Added `Op_funcd`.
- Added `Op_funcd (id_funcd E) -> id_funcd (Op_catd E)`.
- Added the involution rule for nested `Op_funcd`.
- Added internal displayed action heads:
  - `tdapp1_int_func_transfd`
  - `tdapp1_int_fapp0_transfd`
  - `tdapp1_int_fapp1_func_transfd`
  - `fdapp1_int_transfd`
- Added the same internal object/hom action packaging for the ordinary
  `tapp1_int_func_transf` head:
  - `tapp1_int_fapp0_transf`
  - `tapp1_int_fapp1_func_transf`
- Routed identity folds through the object-action stable heads:

```text
tdapp1_int_fapp0_transfd FF FF (id (Functord_cat E D) FF)
  -> fdapp1_int_transfd FF

tapp1_int_fapp0_transf F F (id (Functor_cat A B) F)
  -> fapp1_int_transf F
```

No external surface `fdapp1_*` or `tdapp1_*` heads were added in this pass.

### Derived Displayed Components `tdapp0*`

- Added derived component notation:

```text
tdapp0_func z := fapp1_func (tapp0_func z)
tdapp0_fapp0 z ϵ := fapp0 (tdapp0_func z) ϵ
```

- This follows the plan's decision that `tdapp0` is not primitive kernel
  structure; it is ordinary hom-action of component evaluation through the
  canonical `Transfd_cat` spine.
- Added an assertion that `fapp0 (tdapp0_func z) ϵ` computes to
  `tdapp0_fapp0 z ϵ`.

### Derived Fibre-Level Projections

- Added notation-only fibre projections:

```text
Fibre_func FF z := tapp0_fapp0 z FF
Fibre_transf ϵ z := tdapp0_fapp0 z ϵ
Fibre_transf_app ϵ z u := tapp0_fapp0 u (Fibre_transf ϵ z)
```

- Added assertions that these unfold through the canonical `tapp0` /
  `tdapp0` projection path.
- Added derived projections of the internal displayed hom-action:

```text
fdapp1_int_fibre_transf FF x
fdapp1_int_fibre_app FF x u
```

These are projections of `fdapp1_int_transfd`; they are not external
`fdapp1_*` surface heads.

### Pointwise Opposite And `homd_int` Fibre Source Projections

- Added the pointwise displayed-opposite projection:

```text
tapp0_fapp0 x (Op_funcd FF)
  -> Op_func (tapp0_fapp0 x FF)
```

- Added assertions that:
  - `Fibre_func (id_funcd E) z` computes to `id_func (Fibre_cat E z)`,
  - `Fibre_func (Op_funcd FF) z` computes to `Op_func (Fibre_func FF z)`,
  - object action of the opposite fibre functor computes back to object action
    of `Fibre_func FF z`.
- Added assertions exposing the first fibre projection of generalized
  `homd_int`:

```text
Fibre_func (homd_int FF) x -> homd_src_funcd FF x
fapp0 (Fibre_func (homd_int FF) x) u -> homd_src_secd FF x u
```

- Probed the analogous displayed-composition projection, but the probe is now
  classified as non-conclusive because it over-specified inferred LHS slots.
  A rule headed by `comp_catd_fapp0` typechecked but did not give the desired
  assertion because Lambdapi unfolds the alias before matching. Moving the rule
  to the unfolded `comp_fapp0 (Catd_cat K)` shape caused `lambdapi check` to
  time out, but that attempted rule still explicitly pinned the source/target
  family arguments of `tapp0_fapp0`. A narrower rule for the
  `homd_int FF ∘ Op_funcd FF` target composite also typechecked, but an exact
  assertion did not reduce; it had the same LHS-shape problem and was not kept.
  The corrected recommendation is to retry the projection with the
  `tapp0_fapp0` source/target family slots written as `_ _`, following the
  `homd_int` projection style.

### Section Action `piapp1*`

- Added the planned section-level action head:

```text
piapp1_func E s x y
  : Obj (Pi_cat (homd_ E x (piapp0 s x) y (piapp0 s y)))
```

- Added the capped component as a definition by section evaluation:

```text
piapp1_fapp0 E s f
  := piapp0 (piapp1_func E s x y) f
```

- Added the source object of the dependent hom component:

```text
piapp1_src_obj E s f
  := fib_cov_tapp0_fapp0 E f (piapp0 s x)
```

- Added assertions that the endpoint category of `piapp1_fapp0` unfolds to:

```text
Hom_cat (Fibre_cat E y) (piapp1_src_obj E s f) (piapp0 s y)
```

- Added the constant-family sanity assertion:

```text
piapp1_src_obj (Const_catd K A) s f -> fapp0 s x
```

- Added an assertion for this definitional projection.
- The terminal-specialization fold from displayed internal action to
  `piapp1_func` remains deferred.

## Remaining Gaps And Divergences

### 1. Terminal-Specialization Fold To `piapp1_func` Is Still Missing

The plan expects full homd-valued section action only after the internal
dependent-action layer is settled. The current v3.2 file now defines:

- `piapp1_func`
- `piapp1_fapp0`
- `piapp1_src_obj`

It does not yet define the terminal-specialization fold from displayed
dependent action to `piapp1_func`. That fold remains the most important next
implementation target for making `piapp1*` computational rather than only a
typed stable package plus definitional projection. The new `piapp1_src_obj`
helper clarifies the endpoint hom category, but it is not the missing packaged
section fold.

### 2. General Endpoint Exists, But Surface Arity Is Still A Design Choice

The current old endpoint remains:

```text
homd_ E x u y v
```

The generalized endpoint now exists under the explicit name:

```text
homd_funcd_ FF x u y v
```

where `FF : Functord D E`. The remaining design choice is whether to keep both
names permanently, rename/promote `homd_funcd_` to the main surface `homd_`
arity, or continue treating `homd_ E x u y v` as the identity-specialized
notation used by Sigma homs and `piapp1*`.

### 3. Most-Internal `fib_cov` Package Is Now Implemented

This gap is closed in the follow-up pass. The internal package
`fib_cov_int E` projects to `fib_cov_src_func E x`, then to the existing
external `fib_cov_transf E x u`, and then to `fib_cov_tapp0_func E x y u`.

Remaining work in this area is not the package itself, but possible future
integration with richer displayed action folds.

### 4. No Constant/Terminal Whole-Family `homd_int` Normal Forms Yet

The endpoint `homd_` has constant and terminal assertions by cascade. The first
fibre projection of generalized `homd_int` is now exposed through
`Fibre_func`, but the internal package does not yet have whole-family constant
or terminal normal forms. The plan says to add these only after checking they
join with the defined endpoint and constant-functor cascade.

### 5. `piapp0` Replacement LHS Is More Explicit Than The Plan Sketch

The plan sketches a highly implicit replacement:

```text
rule @tapp0_fapp0 _ Cat_cat _ _ y (homd_src_sec ...)
  -> Obj_func ...
```

The implementation needed a more explicit source base and terminal source for
Lambdapi subject reduction:

```text
rule @tapp0_fapp0
      (Op_cat Z)
      Cat_cat
      (Const_catd (Op_cat Z) Terminal_cat)
      _
      y
      (homd_src_sec Z E x u)
  -> Obj_func ...
```

This still follows the unfolded `Const_catd` discipline, but it is a minor
operational divergence and should be watched for matching brittleness.

### 6. `Hom_cat (Pi_cat E) s t` Remains Deferred

No rule was added for:

```text
Hom_cat (Pi_cat E) s t
```

The plan explicitly defers this, with `Transfd_cat s t` as the likely joining
direction. This remains open.

### 7. External Surface Heads Remain Deferred

The following were intentionally not introduced:

- external `fdapp1_*`
- external `tdapp1_*`

The internal object/hom action packagings from v2 have now been introduced for
both ordinary and displayed internal heads. The plan still says to promote
less-internal external heads only after the internal layer is better understood.
The derived `fdapp1_int_fibre_*` names added later remain internal projection
notation and do not settle the external API question.

### 8. Displayed Composition Stable Head Added; Fibre Projection Deferred

The desired rule shape is:

```text
Fibre_func (comp_catd_fapp0 FF GG) x
  -> comp_cat_fapp0 (Fibre_func FF x) (Fibre_func GG x)
```

This pass did not keep such a rule. The first probes should not be treated as a
real blocker because they violated the local rewrite hygiene rule: they
explicitly wrote compound/reducible source and target family expressions in the
inferred slots of `tapp0_fapp0`. The correct next probe should keep those slots
implicit and discriminate on the explicit composed morphism argument, as in the
existing `homd_int` projection rule:

```text
rule @tapp0_fapp0 K Cat_cat _ _ x
      (comp_fapp0 (Catd_cat K) E D C FF GG)
  -> comp_cat_fapp0 (Fibre_func FF x) (Fibre_func GG x)
```

This continuation promoted `comp_catd_fapp0` into that smaller stable head and
added fold/identity rules for displayed composition. That part typechecks and is
now validated by assertions.

The fibre projection itself still remains deferred. A broad rule over the new
stable `comp_catd_fapp0` head still timed out. A narrower rule for the concrete
`homd_int FF ∘ Op_funcd FF` composite, using only explicit morphism arguments
as discriminators, also timed out once placed after the `homd_int` projection
heads. Both rules were removed. A rule headed by `Fibre_func` is not available
while `Fibre_func` remains defined notation over `tapp0_fapp0`: Lambdapi rejects
rules on symbols already defined with `≔`. The next attempt should therefore
either introduce a fresh primitive fibre-level composition/projection head, or
refactor `Fibre_func` itself from defined notation into a primitive projection
head with carefully staged rules.

## Assessment

The first implementation pass is successful as a typechecked core migration. It
implements the main architecture changes:

- `Terminal_catd` as a `Const_catd` alias.
- `piapp0` as defined notation.
- `fib_cov_tapp0_fapp0` as a defined projection.
- most-internal `fib_cov_int` projection package.
- endpoint `homd_` as a defined `hom_con` endpoint.
- generalized endpoint/projection path `homd_funcd_`.
- generalized `homd_int`.
- internal ordinary/displayed object and hom action heads.
- derived `tdapp0_func` / `tdapp0_fapp0` notation.
- derived `Fibre_func` / `Fibre_transf` / `Fibre_transf_app` notation.
- pointwise `Op_funcd` fibre projection and related `Fibre_func` assertions.
- `Fibre_func (homd_int FF)` source-projection assertions.
- derived `fdapp1_int_fibre_transf` / `fdapp1_int_fibre_app` projections.
- initial `piapp1_func` / `piapp1_fapp0` stable package plus
  `piapp1_src_obj`.

It does not complete the full plan. The next work should focus on the unresolved
arity and action questions, especially:

1. whether to promote/rename `homd_funcd_` as the main surface `homd_` arity,
2. how to derive the terminal-specialization fold to `piapp1_func`,
3. how to expose displayed-composition fibre projections without a timeout,
4. whether constant/terminal whole-family `homd_int` normal forms are now safe
   to add.
