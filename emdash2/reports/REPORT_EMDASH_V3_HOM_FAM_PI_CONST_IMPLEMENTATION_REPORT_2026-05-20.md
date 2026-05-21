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
`homd_int` source-projection assertions, and the `piapp1_src_obj` helper. The
initial displayed-composition fibre projection probes were inconclusive and were
revisited later; no displayed-composition fibre projection rule is currently
kept.

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
typechecks. The displayed-composition projection was first retried with those
same implicit outer slots and timed out. The later proposed explicit outer
`D`/`C` rule:

```text
tapp0_fapp0 K Cat_cat D C x (comp_catd_fapp0 E D C FF GG)
  -> comp_cat_fapp0
       (Fibre_cat E x) (Fibre_cat D x) (Fibre_cat C x)
       (tapp0_fapp0 K Cat_cat D C x FF)
       (tapp0_fapp0 K Cat_cat E D x GG)
```

was accepted as a raw rewrite command in a focused test, but it is not the
intended fibre projection: the standalone assertion with that LHS is not typable
for general `E,D,C` because the component should be an `E[x] -> C[x]` functor,
not a `D[x] -> C[x]` one. The semantically aligned `E`/`C` outer-slot version is
the correct rule shape. It timed out when inserted early near the other
projection rules, but it typechecked quickly when appended at the end of the
file, together with the intended `Fibre_func (comp_catd_fapp0 FF GG)` assertion.
Therefore no displayed-composition fibre projection rule is currently retained:
it should be added only when a concrete later use justifies choosing a safe
insertion point. The useful SOP is narrower: when adding explicit outer slots to
recover variables hidden inside non-injective subterms, those slots must still be
the actual source/target slots of the head being projected, and rule placement
can materially affect bounded checking.

Fifth continuation update: the 2026-05-21 pass typechecks after the
`Op_funcd` LHS correction, the stable `comp_catd_fapp0` promotion, and new
assertions covering displayed composition folding and identity reductions.

Review correction update 2026-05-21: the displayed-composition fibre-projection
probes should be treated as exploratory and premature, not as plan-critical
blockers. The plan's generalized `homd_int` requirement is already the simpler
stable-head projection:

```text
tapp0_fapp0 x (homd_int D E FF) -> homd_src_funcd D E FF x
```

The attempted rule for the composite
`comp_catd_fapp0 (homd_int FF) (Op_funcd FF)` was only trying to expose a later
fibrewise convenience normal form for the target of `fdapp1_int_transfd`; it is
not needed to implement the generalized `homd_int` design. Also, `Fibre_func`
is deliberately defined notation over `tapp0_fapp0`, so computations involving
`Fibre_func` should happen by unfolding and by indirect rules on primitive or
stable heads, not by making `Fibre_func` a new primitive head. Finally,
`homd_funcd_` should be considered a migration artifact: the cleaner next step
is to refactor toward the plan's generalized endpoint arity by making `homd_`
itself carry the displayed functor argument, with the old one-family endpoint as
the identity-specialized form.

Sixth continuation update: the `homd_funcd_` migration artifact has now been
removed from `emdash3_2.lp`. The endpoint `homd_` itself carries the generalized
displayed-functor argument, and old one-family endpoint uses have been rewritten
as identity-specialized uses of `homd_ E E (id_funcd E) ...`. The focused
`lambdapi check -w emdash3_2.lp` pass and the full bounded `make check` pass
succeed after this refactor.

Seventh continuation update: the 2026-05-21 pass also typechecks after adding
the stable displayed identity `id_transfd`, routing the `tdapp1_int` identity
fold through that head, and adding focused terminal-source probes for the
`piapp0`/`homd_` cascade needed by the eventual fold to `piapp1_func`. A direct
general terminal-source `tapp0_fapp0` rule returning `piapp0` was tested and
removed because it recursed through the definition of `piapp0` and timed out.
The focused `timeout 30s lambdapi check -w emdash3_2.lp` pass and full
`EMDASH_TYPECHECK_TIMEOUT=60s make check` pass succeed.

Clarification update 2026-05-21: the next implementation step should introduce
`piapp1_int` as the terminal-source specialization of the whole internal action
witness `fdapp1_int_transfd`, not as a replacement for only the target displayed
functor inside that witness. Since the section `s` is the specialized external
`FF` argument of `fdapp1_int_transfd`, the fully applied version is preferred:

```text
piapp1_int [K] (E : Catd K) (s : Obj (Pi_cat E))
  : Transfd
      (homd_int (id_funcd (Const_catd K Terminal_cat)))
      (comp_catd_fapp0
        (homd_int s)
        (Op_funcd s))
```

with the actual Lambdapi type written explicitly/readably enough for
typechecking, and with implicit arguments omitted in use where local style
allows.

Follow-up clarification 2026-05-21: the fold from
`fdapp1_int_transfd K (Const_catd K Terminal_cat) E s` to `piapp1_int E s`
does not require a terminal/constant whole-family `homd_int` normal form,
because `piapp1_int E s` will be declared with the same type as that specialized
internal witness. A later projection from `piapp1_int E s` to `piapp1_func E s x
y` may require the planned terminal/constant `homd_int` normal forms, or an
equivalent projected cascade, to expose the desired `Pi_cat` target. Therefore
that projection should be deferred until the later phase that handles the
inter-related `homd_int` rules for `Const_catd` / `Terminal_catd`.

Eighth continuation update: `piapp1_int` has now been added to `emdash3_2.lp` as
the fully applied terminal-source specialization of the internal displayed
hom-action witness. The fold
`fdapp1_int_transfd K (Const_catd K Terminal_cat) E s -> piapp1_int E s`
typechecks, with focused assertions for both the direct `fdapp1_int_transfd`
path and the `tdapp1_int` identity-specialization path through `id_transfd`.
Projection from `piapp1_int` to `piapp1_func` remains intentionally deferred to
the later constant/terminal `homd_int` phase.

Ninth continuation update: the terminal/constant `homd_int` phase has started
with narrow projected terminal-source normal forms, not a broad whole-family
rewrite for `homd_int`. The new rules expose
`homd_src_func (Const_catd K Terminal_cat) x` as the object functor at
`homd_src_sec ... Terminal_obj`, and expose
`homd_tgt_func (Const_catd K Terminal_cat) x Terminal_obj y` as the object
functor at `Terminal_catd (Op_cat (Hom_cat K x y))`. Focused assertions confirm
that `Fibre_func (homd_int (id_funcd (Const_catd K Terminal_cat))) x` reduces
through the first normal form and that applying the inner endpoint functor at
`Terminal_obj` reaches the terminal displayed family. No direct endpoint
`homd_` terminal rule and no broad `homd_int -> ...` whole-family rule were
introduced.

Tenth correction update: the earlier named terminal-source `piapp1_int_*`
projection definitions and the purpose-built capped bridge were removed from
`emdash3_2.lp`. They were not part of the original plan, introduced extra
defined-symbol vocabulary around `piapp1_int`, and encoded a bad architectural
shape by matching a composite/cut subterm inside a capped projection. A later
displayed-composition projection probe clarified another issue: the raw `D`/`C`
outer-slot rule can be accepted as a command, but it is not the intended general
`E[x] -> C[x]` fibre projection. The semantic `E`/`C` rule is correct and
validated when appended at the end of the file with the intended fibre assertion,
but early insertion timed out. No displayed-composition fibre rule is currently
retained. The direct
`piapp1_int -> piapp1_func` fold remains deferred; it should resume only through
the planned terminal / constant `homd_int` and Pi-hom projection phase, not
through ad hoc `piapp1_int_*` aliases.

Latest validation update 2026-05-21: after removing the premature
`piapp1_int_*` aliases, removing the capped bridge, and leaving the
displayed-composition fibre projection deferred, both
`timeout 30s lambdapi check -w emdash3_2.lp` and
`EMDASH_TYPECHECK_TIMEOUT=60s make check` pass. `git diff --check` also passes.

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

### Generalized Endpoint `homd_`

- Added the explicit-displayed-functor endpoint. It was initially introduced as
  the migration name:

```text
homd_funcd_ [D E] (FF : Functord D E) x u y v
```

and has now been promoted to the intended generalized endpoint:

```text
homd_ [D E] (FF : Functord D E) x u y v
```

where `u : E[x]` and `v : D[y]`. Its target object is computed by the fibre
component of `FF` at `y`, while transport still uses the ambient target family
`E`.

Correction implemented: the separate `homd_funcd_` name is no longer present in
`emdash3_2.lp`. The old `homd_ E x u y v` shape is represented as the
identity-specialized case:

```text
homd_ E E (id_funcd E) x u y v
```

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
  - `fapp0 (homd_tgt_funcd FF) v` projects to generalized `homd_ FF`,
  - the identity specialization `homd_ (id_funcd E)` unfolds to the old endpoint
    body.

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
- Added the stable displayed identity head:

```text
id_transfd FF : Transfd FF FF
id (Functord_cat E D) FF -> id_transfd FF
```

- Routed displayed identity folds through `id_transfd` rather than matching
  only ordinary `id` directly:

```text
tdapp1_int_fapp0_transfd FF FF (id_transfd FF)
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

- Probed the pointwise displayed-composition projection:

```text
Fibre_func (comp_catd_fapp0 E D C FF GG) x
  -> comp_cat_fapp0
       (Fibre_cat E x) (Fibre_cat D x) (Fibre_cat C x)
       (tapp0_fapp0 K Cat_cat D C x FF)
       (tapp0_fapp0 K Cat_cat E D x GG)
```

  No such rule is currently kept. The `D`/`C` outer-slot variant accepted as a
  rewrite command but failed a meaningful standalone assertion. The `E`/`C`
  semantic variant is correct and validated when appended late, including with
  the intended `Fibre_func` assertion, but timed out when inserted early near the
  other projection rules.

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

- Added terminal-source cascade probes showing:

```text
fapp0 (tapp0_fapp0 (Const_catd K Terminal_cat) E k s) Terminal_obj
  ≡ piapp0 s k

homd_ (Const_catd K Terminal_cat) E s x (piapp0 s x) y Terminal_obj
  ≡ homd_ E E (id_funcd E) x (piapp0 s x) y (piapp0 s y)
```

- Added an endpoint-object assertion that applying the terminal-source
  generalized endpoint to a base arrow exposes the same hom category used by
  `piapp1_fapp0`.
- Added an assertion that the terminal-source `tdapp1_int` identity
  specialization folds to `fdapp1_int_transfd` when the displayed identity is
  written with `id_transfd`.
- Added the internal terminal-source Pi-action witness:

```text
piapp1_int E s
  : type of fdapp1_int_transfd K (Const_catd K Terminal_cat) E s
```

- Added the stable fold:

```text
fdapp1_int_transfd K (Const_catd K Terminal_cat) E s
  -> piapp1_int E s
```

- Added assertions that both the direct `fdapp1_int_transfd` specialization and
  the `tdapp1_int` identity-specialized path compute to `piapp1_int E s`.
- Added projected terminal-source normal forms for the homd spine:

```text
homd_src_func (Const_catd K Terminal_cat) x
  -> Obj_func (homd_src_sec ... Terminal_obj)

homd_tgt_func (Const_catd K Terminal_cat) x Terminal_obj y
  -> Obj_func (Terminal_catd (Op_cat (Hom_cat K x y)))
```

- Added assertions that the terminal source of
  `homd_int (id_funcd (Const_catd K Terminal_cat))` reduces through these
  projected normal forms. These are intentionally not direct whole-family
  `homd_int` or endpoint `homd_` rewrite rules.
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

The latest pass settled two prerequisites for this fold:

- terminal-source endpoint normalization from `homd_ (Const_catd K Terminal_cat)
  E s ... Terminal_obj` to the identity-specialized `homd_ E E (id_funcd E)
  ...` succeeds by cascade;
- terminal-source identity specialization of `tdapp1_int` succeeds when the
  displayed identity is written as `id_transfd`.
- the terminal-source `piapp1_int` witness exists as a stable fold target, but
  the later `piapp1_int_*` projection aliases were removed as plan-divergent.

Do not add a general terminal-source component rule
`tapp0_fapp0 (Const_catd K Terminal_cat) E k s -> Obj_func ... (piapp0 s k)` in
the current architecture: with `piapp0` defined through the same projection, that
rule loops. The next fold should instead use the already-validated
Terminal_obj-applied projection, or introduce a nonrecursive purpose-built
projection only if an exact later LHS requires it.

The later `piapp1_int_*` projection aliases and capped target-section bridge
were removed. They were plan-divergent derived names, and the capped bridge
matched the kind of composite/cut subterm that this development is trying to
avoid. The next clean fold toward `piapp1_func` should be resumed from existing
stable heads: `piapp1_int`, `fdapp1_int_fibre_*`, `homd_int` projections, and
any future principled displayed-composition projection if one can pass both
typechecking and a meaningful assertion.

Implemented clarified design target: add a stable internal Pi-action witness
`piapp1_int` by specializing the existing internal displayed action:

```text
fdapp1_int_transfd K (Const_catd K Terminal_cat) E s
  : I K E s
```

where `s : Obj (Pi_cat E)` is the specialized `FF` argument. Prefer the fully
applied `I` version, because it matches the existing stable-head rewrite style:

```text
symbol piapp1_int [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E))) : I K E s;

rule @fdapp1_int_transfd
      $K
      (@Const_catd $K Terminal_cat)
      $E
      $s
  ↪ @piapp1_int $K $E $s;
```

This is an internal witness fold only. Projection rules from `piapp1_int` down
to `piapp1_func` remain intentionally deferred. They may need the planned
terminal/constant whole-family `homd_int` rules, or equivalent projection-level
cascades, before the LHS and RHS types expose the same `Pi_cat` target.

### 2. General Endpoint Promotion Is Complete

The old endpoint shape:

```text
homd_ E x u y v
```

has been replaced by the generalized endpoint:

```text
homd_ [D E] (FF : Functord D E) x u y v
```

Old one-family uses are now written as `homd_ E E (id_funcd E) x u y v`.
Remaining work in this area is not the endpoint arity itself, but using the
generalized endpoint in the later `piapp1` terminal-specialization fold.

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

### 8. Displayed Composition Fibre Projection Is Still Deferred

The desired projection shape is:

```text
Fibre_func (comp_catd_fapp0 FF GG) x
  -> comp_cat_fapp0 (Fibre_func FF x) (Fibre_func GG x)
```

The semantically aligned primitive/stable `tapp0_fapp0` shape would use the
full composite source and target, `E` and `C`, in the outer slots:

```text
rule @tapp0_fapp0 K Cat_cat E C x
      (comp_catd_fapp0 K E D C FF GG)
  -> comp_cat_fapp0
       (Fibre_cat E x) (Fibre_cat D x) (Fibre_cat C x)
       (tapp0_fapp0 K Cat_cat D C x FF)
       (tapp0_fapp0 K Cat_cat E D x GG)
```

This `E`/`C` version is the correct semantic shape. It timed out when inserted
early near the other projection rules, but when appended at the end of the file
it typechecked quickly, including with a focused assertion for the intended
`Fibre_func (comp_catd_fapp0 FF GG)` normal form. The proposed `D`/`C`
outer-slot version typechecked as a rule command, but a standalone assertion
showed it is not the intended general projection: `tapp0_fapp0 ... D C ...
(comp_catd_fapp0 E D C FF GG)` is not typable for arbitrary `E,D,C`, since the
composite component should live from `E[x]` to `C[x]`.

SOP correction: explicit outer slots can be useful when variables otherwise
occur only inside non-injective subterms, but those explicit slots must still be
the real source/target slots of the head being projected. Do not refactor
`Fibre_func` into a primitive head for this; the plan explicitly treats
`Fibre_func` as derived notation. Also, placement matters: installing this broad
projection before later assertions can increase conversion/critical-pair work
enough to time out, even though the same rule is accepted when appended after
the existing development.

## Assessment

The first implementation pass is successful as a typechecked core migration. It
implements the main architecture changes:

- `Terminal_catd` as a `Const_catd` alias.
- `piapp0` as defined notation.
- `fib_cov_tapp0_fapp0` as a defined projection.
- most-internal `fib_cov_int` projection package.
- endpoint `homd_` as a defined `hom_con` endpoint.
- generalized endpoint/projection path through `homd_ [D E] FF`.
- generalized `homd_int`.
- internal ordinary/displayed object and hom action heads.
- derived `tdapp0_func` / `tdapp0_fapp0` notation.
- derived `Fibre_func` / `Fibre_transf` / `Fibre_transf_app` notation.
- pointwise `Op_funcd` fibre projection and related `Fibre_func` assertions.
- `Fibre_func (homd_int FF)` source-projection assertions.
- derived `fdapp1_int_fibre_transf` / `fdapp1_int_fibre_app` projections.
- initial `piapp1_func` / `piapp1_fapp0` stable package plus
  `piapp1_src_obj`.

It does not complete the full plan. The next work should focus on the remaining
action questions, especially:

1. how to derive the terminal-specialization fold to `piapp1_func`,
2. when to install the correct displayed-composition fibre projection, likely
   late or near its first concrete use, without making `Fibre_func` primitive,
3. whether constant/terminal whole-family `homd_int` normal forms are now safe
   to add.

## Recommended Resume Order

1. Checkpoint the current typechecked state with:

```bash
timeout 30s lambdapi check -w emdash3_2.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

2. Completed: refactor the migration endpoint `homd_funcd_` into the generalized
   `homd_` arity:

```text
homd_ [Z] [D E : Catd Z] (FF : Functord D E) x u y v
```

The current `homd_funcd_` body was promoted to the generalized endpoint body.
All old one-family endpoint uses were rewritten as the identity-specialized case
`homd_ E E (id_funcd E) x u y v`, the projection folds and assertions were
updated, and the `homd_funcd_` symbol was removed.

3. Revalidate the constant and terminal endpoint cascades after the endpoint
   refactor. They should still compute indirectly through `hom_con`,
   `fib_cov_tapp0_func`, `Const_func`, and `hom_`. Do not add direct endpoint
   rewrite rules unless that cascade fails in a concrete typechecked probe.

4. Preserve the generalized `homd_int` projection chain as the stable internal
   computation spine:

```text
homd_int -> homd_src_funcd -> homd_src_secd -> homd_tgt_funcd -> homd_
```

The identity-specialized helper heads `homd_src_func`, `homd_src_sec`, and
`homd_tgt_func` remain compatibility normal forms only.

5. Deferred: do not keep the `D`/`C` displayed-composition projection rule. It
   can be accepted as a rewrite command, but it does not type as the intended
   general fibre assertion. The semantically correct `E`/`C` outer-slot version
   validates when appended late, including with the intended `E[x] -> C[x]`
   assertion, but times out when inserted early near the projection-rule block.
   Keep `Fibre_func` as derived notation and add the rule only when a concrete
   later use provides a safe insertion point.

6. Partially completed: after generalized `homd_`, validate the
   terminal-source cascade toward `piapp1_func`. The current file now has
   focused probes for Terminal_obj-applied `piapp0`, terminal-source `homd_`,
   and terminal-source `tdapp1_int` identity specialization through
   `id_transfd`.

7. Completed: declared the fully applied internal Pi-action witness:

```text
piapp1_int [K] (E : Catd K) (s : Obj (Pi_cat E))
  : type of fdapp1_int_transfd K (Const_catd K Terminal_cat) E s
```

The declaration uses a readable explicit Lambdapi type, with implicit arguments
omitted in applications according to local style. The stable fold is:

```text
fdapp1_int_transfd K (Const_catd K Terminal_cat) E s
  -> piapp1_int E s
```

Focused assertions now validate that the direct specialization and the
`tdapp1_int` identity-specialization path both compute to `piapp1_int E s`.

8. Defer the planned projection/fold from `piapp1_int E s` to the existing
   external package `piapp1_func E s x y` until the later phase that deals with
   the inter-related `homd_int` rules for `Const_catd` / `Terminal_catd`. That
   phase should decide whether a whole-family terminal/constant `homd_int`
   normal form is needed, or whether the existing projection cascade is enough
   to expose the same `Pi_cat` target.

9. Partially completed: after the internal `piapp1_int` witness fold became
   stable, add narrow projected terminal-source normal forms for the existing
   `homd_int` spine. The current file now reduces:

```text
homd_src_func (Const_catd K Terminal_cat) x
  -> Obj_func (homd_src_sec ... Terminal_obj)

homd_tgt_func (Const_catd K Terminal_cat) x Terminal_obj y
  -> Obj_func (Terminal_catd (Op_cat (Hom_cat K x y)))
```

These rules are enough to expose the terminal source and inner terminal
endpoint through projections, while avoiding a broad whole-family `homd_int`
rule.

10. Removed: do not keep the plan-divergent `piapp1_int_tgt_sec`,
    `piapp1_int_fibre_transf`, or `piapp1_int_fibre_app` aliases, and do not keep
    the capped terminal-source bridge that matched a displayed-composition
    subterm. The intended stable route is the existing plan-backed projections
    plus any future displayed-composition projection that passes a meaningful
    `E[x] -> C[x]` assertion.

11. Next: resume the `piapp1_int -> piapp1_func` work only from stable plan
    heads. First try exact assertions showing that the target of the specialized
    `piapp1_int` projection reaches the `Pi_cat` target used by `piapp1_func`
    via:

```text
fdapp1_int_transfd
  -> piapp1_int
  -> tapp0_fapp0/Fibre_func projections
  -> future principled comp_catd_fapp0 pointwise projection, if needed
  -> homd_int terminal/constant projected normal forms
```

    If that cascade still does not expose the target, evaluate whether a
    principled constant/terminal whole-family `homd_int` rule is required. Do
    not introduce new `piapp1_int_*` migration names unless a typechecked probe
    shows that a primitive stable head is genuinely needed.

12. Keep the deferred `Hom_cat (Pi_cat H) a b -> Transfd_cat ...` question
    separate. It may become necessary for a later section-level hom fold, but it
    should not be conflated with the already-corrected displayed-composition
    fibre projection.
