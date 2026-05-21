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
revisited later; no displayed-composition fibre projection rule was kept at that
point.

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
At that point no displayed-composition fibre projection rule was retained: the
rule was to be added only when a concrete later use justified choosing a safe
insertion point. A later `piapp1` target-object probe supplied that use, and the
semantically aligned `E`/`C` outer-slot version is now retained late in the file.
The useful SOP is narrower: when adding explicit outer slots to recover variables
hidden inside non-injective subterms, those slots must still be the actual
source/target slots of the head being projected, and rule placement can
materially affect bounded checking.

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

Resume clarification 2026-05-21: continue assertion-led from stable plan heads,
not by reintroducing `piapp1_int_*`. The next useful stable projection is a
terminal-source normal form for `homd_tgt_funcd`:

```text
homd_tgt_funcd (Const_catd K Terminal_cat) E s x u y
  -> Obj_func
       (homd_ E E (id_funcd E) x u y (piapp0 s y))
```

This exposes, one layer below `homd_src_secd`, the same endpoint family used by
`piapp1_func`, while avoiding a broad whole-family `homd_int` rewrite and
avoiding the previously removed capped composite bridge. It should be validated
with focused assertions for both the rule itself and the corresponding
`piapp0 (homd_src_secd ...) y` cascade.

Eleventh continuation update: the `homd_tgt_funcd` terminal-source normal form
has now been implemented in `emdash3_2.lp`:

```text
homd_tgt_funcd (Const_catd K Terminal_cat) E s x u y
  -> Obj_func
       (homd_ E E (id_funcd E) x u y (piapp0 s y))
```

Focused assertions validate the rule itself, the corresponding
`piapp0 (homd_src_secd ...) y` cascade, and terminal-object evaluation back to
the generalized endpoint used by `piapp1_func`. A final focused assertion fixes
the `piapp1`-specific source object `u = piapp0 s x` and confirms that evaluating
the projected target section at `y` and then at `Terminal_obj` reaches
`homd_ E E (id_funcd E) x (piapp0 s x) y (piapp0 s y)`. This continues the
planned projection-level terminal/constant route without adding a whole-family
`homd_int` rewrite, without adding any `piapp1_int_*` aliases, and without
installing the deferred displayed-composition projection. The focused
`timeout 30s lambdapi check -w emdash3_2.lp`, full
`EMDASH_TYPECHECK_TIMEOUT=60s make check`, and `git diff --check` validations
pass after this change.

Twelfth continuation update: the previously deferred section-hom bridge has now
been implemented by the principled `Pi_cat` rule:

```text
Hom_cat (Pi_cat E) s t
  -> Transfd_cat (Const_catd K Terminal_cat) E s t
```

Focused assertions validate both the generic bridge and the constant-family
join:

```text
Hom_cat (Pi_cat (Const_catd K A)) s t
  -> Transf_cat s t
```

This is not the displayed-composition fibre projection and does not add any
`piapp1_int_*` migration aliases. It is a packaged section-category hom bridge
needed for the clean route from Pi-level morphisms to terminal-specialized
displayed transfors. A direct exploratory assertion for the eventual
`fdapp1_int_fibre_app` / `piapp1_func` component did not infer its type in the
implicit form tried, so the next fold should be pursued with explicit
projection sources/targets or a carefully packaged existing-plan fold rather
than by introducing ad hoc aliases. The focused
`timeout 30s lambdapi check -w emdash3_2.lp` validation passes after this
change.

Thirteenth continuation update: the semantically correct displayed-composition
fibre projection is now installed late in `emdash3_2.lp`, near the concrete
`piapp1` target-object assertions that need it:

```text
tapp0_fapp0 K Cat_cat E C x (comp_catd_fapp0 K E D C FF GG)
  -> comp_cat_fapp0
       (Fibre_cat E x) (Fibre_cat D x) (Fibre_cat C x)
       (tapp0_fapp0 K Cat_cat D C x FF)
       (tapp0_fapp0 K Cat_cat E D x GG)
```

This is not the earlier rejected `D`/`C` outer-slot variant and not a capped
bridge with a composite subterm tailored to `piapp1`. The concrete assertion now
validated is the specialized target-object cascade:

```text
fapp0
  (Fibre_func
    (comp_catd_fapp0
      (homd_int (Const_catd K Terminal_cat) E s)
      (Op_funcd s))
    x)
  Terminal_obj
  -> homd_src_secd (Const_catd K Terminal_cat) E s x (piapp0 s x)
```

A second assertion validates that evaluating this target section at `y` and then
at `Terminal_obj` reaches exactly the endpoint family used by `piapp1_func`:

```text
homd_ E E (id_funcd E) x (piapp0 s x) y (piapp0 s y)
```

This settles the previously anticipated `Fibre_func (comp_catd_fapp0 ...)`
blocker for this concrete terminal-source path. It still does not define the
final `piapp1_int -> piapp1_func` fold. After this update,
`timeout 30s lambdapi check -w emdash3_1.lp`,
`timeout 30s lambdapi check -w emdash3_2.lp`,
`EMDASH_TYPECHECK_TIMEOUT=60s make check`, and `git diff --check` all pass.

Fourteenth continuation update, corrected 2026-05-22: the surface
`Fibre_transf_app` diagnostic was useful for identifying the desired target, but
it was a design detour and should not remain in `emdash3_2.lp`. The diagnostic
showed that projecting the specialized `fdapp1_int_fibre_app` morphism at `y`
and then at `Terminal_obj` produced a term whose type was exactly the object
type of the existing stable package `piapp1_func E s x y`:

```text
tapp0_fapp0 Terminal_obj
  (Fibre_transf_app
    (fdapp1_int_fibre_app
      (Const_catd K Terminal_cat) E s x Terminal_obj)
    y
    Terminal_obj)
  : Obj (Pi_cat (homd_ E E (id_funcd E) x (piapp0 s x) y (piapp0 s y)))
```

The correction is that this surface expression is not an acceptable rewrite
interface. `Fibre_transf_app` remains a reducible defined abbreviation, and a
rule that matches it is brittle and plan-divergent. The assertion using that
surface has therefore been removed. The implemented route is the plan-compatible
stable-head route recorded below: promote `tdapp0_func` / `tdapp0_fapp0` to
primitive projection heads, introduce stable projections from `piapp1_int`, and
fold the last stable target object to `piapp1_func`.

Fifteenth continuation update, 2026-05-22: the stable-head route has now been
implemented and typechecked.

- `tdapp0_func` and `tdapp0_fapp0` were promoted from definitions to primitive
  stable projection heads, matching the emdash2 architecture. Their computation
  is now provided by:

```text
fapp0 (tdapp0_func z) eps -> tdapp0_fapp0 z eps
```

- A terminal ordinary-transfor collapse was installed:

```text
Transf_cat Terminal_cat Y (Obj_func Y u) (Obj_func Y v)
  -> Hom_cat Y u v
```

- The `piapp1_int -> piapp1_func` path now uses stable intermediate projection
  heads rather than any reducible `Fibre_transf_app` surface:

```text
piapp1_int
  -> piapp1_int_src_transf
  -> piapp1_int_src_app
  -> piapp1_int_tgt_transf
  -> piapp1_func
```

The new `piapp1_int_*` names are not migration aliases and are not definitions:
they are the stable projection heads needed to express this section-action
cascade in the same style as
`homd_int -> homd_src_funcd -> homd_src_secd -> homd_tgt_funcd -> homd_`.
The rules are placed after the late displayed-composition fibre projection,
because earlier insertion had caused timeout during previous probes while the
late placement typechecks quickly. Probe assertions for the individual
projection equalities were not kept: the rules themselves typecheck, while those
extra equality assertions triggered elaboration/unification noise that is not
needed for the implementation.

Sixteenth continuation update, 2026-05-22: the `piapp1_int` projection rules
were simplified where Lambdapi inference supports it. The first three
projection rules now use the readable heads directly:

```text
tdapp0_fapp0 x piapp1_int -> piapp1_int_src_transf
tapp0_fapp0 Terminal_obj piapp1_int_src_transf -> piapp1_int_src_app
tdapp0_fapp0 y piapp1_int_src_app -> piapp1_int_tgt_transf
```

The fourth projection cannot be shortened to:

```text
tapp0_fapp0 Terminal_obj piapp1_int_tgt_transf -> piapp1_func
```

Even after simplifying the declaration of `piapp1_int_tgt_transf`, Lambdapi
cannot recover enough endpoint-functor information for subject reduction from
that two-argument surface. The useful computed normal forms are:

```text
Fibre_cat (Const_catd (Op_cat K) Terminal_cat) y
  -> Terminal_cat

Fibre_cat (Homd_section_catd K (Const_catd K Terminal_cat) x) y
  -> Functor_cat Terminal_cat (Catd_cat (Op_cat (Hom_cat K x y)))

Fibre_func ... (homd_src_sec ... Terminal_obj) y
  -> Obj_func
       (Functor_cat Terminal_cat (Catd_cat (Op_cat (Hom_cat K x y))))
       (Obj_func
         (Catd_cat (Op_cat (Hom_cat K x y)))
         (Const_catd (Op_cat (Hom_cat K x y)) Terminal_cat))

Fibre_func ... (homd_src_secd ... (piapp0 s x)) y
  -> Obj_func
       (Functor_cat Terminal_cat (Catd_cat (Op_cat (Hom_cat K x y))))
       (Obj_func
         (Catd_cat (Op_cat (Hom_cat K x y)))
         (homd_ E E (id_funcd E) x (piapp0 s x) y (piapp0 s y)))
```

Accordingly, `piapp1_int_tgt_transf` now uses this computed terminal/functor
type directly, while keeping the stable semantic endpoint `homd_` rather than
unfolding it all the way to `hom_`. The fourth rule now folds directly to
`piapp1_func`; it still exposes the terminal source and nested `Obj_func`
endpoint shape because the fully two-argument `tapp0_fapp0 Terminal_obj
piapp1_int_tgt_transf` surface does not preserve typing. This is the minimum
shape found that preserves typing without returning to the older
`Fibre_func`/`Fibre_transf_app` surface.

Seventeenth continuation update, 2026-05-22: the remaining `Fibre_func`
expressions in `piapp1_int_src_transf` were computed away. The source endpoint
is now the terminal object functor:

```text
Obj_func (homd_src_sec (Const_catd K Terminal_cat) x Terminal_obj)
```

The target endpoint is the computed stable composite:

```text
comp_cat_fapp0
  (homd_src_funcd (Const_catd K Terminal_cat) E s x)
  (Op_func (tapp0_fapp0 (Const_catd K Terminal_cat) E x s))
```

This is more readable than the previous `Fibre_func (homd_int ...) x` /
`Fibre_func (comp_catd_fapp0 ...) x` type and avoids putting reducible
abbreviations in the type of the stable projection head. Attempts to also omit
the base/family indices of `homd_src_funcd`, `tapp0_fapp0`, and `piapp0` caused
unsolved family-index constraints, so those indices remain explicit where
needed.

Eighteenth continuation update, 2026-05-22: the constant-family object action
of `piapp1_func` has been installed at the primitive `fapp0` projection head,
not as a rule headed by the defined `piapp1_fapp0` abbreviation:

```text
fapp0 (piapp1_func (Const_catd K A) s x y) f
  -> fapp1_fapp0 s f
```

This follows the local stable-head SOP. The first direct assertion
`piapp1_fapp0 (Const_catd K A) s f ≡ fapp1_fapp0 s f` failed before this rule,
because `piapp1_fapp0` unfolds to section evaluation by `piapp0`, and the
remaining stable head was exactly the object action of `piapp1_func` over a
base arrow. After adding the `fapp0`-headed rule, the constant-family assertion
typechecks:

```text
piapp1_fapp0 (Const_catd K A) s x y f
  ≡ fapp1_fapp0 K A s x y f
```

This completes the currently planned constant-family bridge for
`piapp1_fapp0` while preserving the design that `piapp1_fapp0` itself remains
defined notation for section evaluation.

Nineteenth continuation update, 2026-05-22: the stable Pi-side generic helper
backlog has been partially reintroduced with focused beta assertions:

```text
pi_eval_transf E
  : Functord (Const_catd K (Pi_cat E)) E

const_section_func K A
  : Functor A (Pi_cat (Const_catd K A))

section_pullback_func F E
  : Functor (Pi_cat E) (Pi_cat (Pullback_catd E F))
```

The installed computations are:

```text
tapp0_fapp0 k (pi_eval_transf E) -> piapp0_func E k
fapp0 (const_section_func K A) a -> Const_func K A a
fapp0 (section_pullback_func F E) s -> section_pullback_sec F E s
piapp0 (section_pullback_sec F E s) a -> piapp0 s (fapp0 F a)
```

The `const_section_func` and `section_pullback_func` object-action rules use `_`
in the target-category slot. Probes with explicit `Pi_cat (Const_catd K A)` or
`Pi_cat (Pullback_catd E F)` targets failed because those targets reduce before
matching, so the explicit target slot was brittle.

The `sigma_intro_transf` component head itself typechecked in a probe, but the
object beta rule for `sigma_intro_func` was not robust: one form timed out and a
more implicit form failed the focused assertion. It remains deferred rather than
being added as a slow or unreliable rule.

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

- Probed and later retained the pointwise displayed-composition projection:

```text
Fibre_func (comp_catd_fapp0 E D C FF GG) x
  -> comp_cat_fapp0
       (Fibre_cat E x) (Fibre_cat D x) (Fibre_cat C x)
       (tapp0_fapp0 K Cat_cat D C x FF)
       (tapp0_fapp0 K Cat_cat E D x GG)
```

  The `D`/`C` outer-slot variant accepted as a rewrite command but failed a
  meaningful standalone assertion. The `E`/`C` semantic variant is correct and is
  now retained late in `emdash3_2.lp`, where it validates the concrete
  terminal-source `piapp1` target-object cascade without affecting earlier
  assertions.

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

homd_tgt_funcd (Const_catd K Terminal_cat) E s x u y
  -> Obj_func (homd_ E E (id_funcd E) x u y (piapp0 s y))
```

- Added assertions that the terminal source of
  `homd_int (id_funcd (Const_catd K Terminal_cat))` reduces through these
  projected normal forms. These are intentionally not direct whole-family
  `homd_int` or endpoint `homd_` rewrite rules.
- Added assertions that `piapp0 (homd_src_secd (Const_catd K Terminal_cat) E s
  x u) y` reduces through the generalized terminal-source normal form above,
  and that applying the resulting `Obj_func` at `Terminal_obj` reaches the
  endpoint family used by `piapp1_func`.
- Added the piapp1-specific assertion for `u = piapp0 s x`, showing that the
  target section evaluated at `y` and `Terminal_obj` reaches
  `homd_ E E (id_funcd E) x (piapp0 s x) y (piapp0 s y)`.
- Added the constant-family sanity assertion:

```text
piapp1_src_obj (Const_catd K A) s f -> fapp0 s x
```

- Added an assertion for this definitional projection.
- Added the section-hom bridge:

```text
Hom_cat (Pi_cat E) s t -> Transfd_cat (Const_catd K Terminal_cat) E s t
```

- Added assertions validating the generic bridge and its constant-family join
  with `Transf_cat s t`.
- Added the late displayed-composition fibre projection with the correct `E`/`C`
  outer slots, plus assertions that the specialized `piapp1` target object first
  reduces to `homd_src_secd ... (piapp0 s x)` and then evaluates to the
  `homd_ E E (id_funcd E) ...` family used by `piapp1_func`.
- Added a type assertion showing that the next projected component,
  `tapp0_fapp0 Terminal_obj (Fibre_transf_app (fdapp1_int_fibre_app ...) y
  Terminal_obj)`, has exactly the `Obj (Pi_cat (homd_ ...))` type of
  `piapp1_func E s x y`.
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

The latest passes settled these prerequisites for this fold:

- terminal-source endpoint normalization from `homd_ (Const_catd K Terminal_cat)
  E s ... Terminal_obj` to the identity-specialized `homd_ E E (id_funcd E)
  ...` succeeds by cascade;
- terminal-source identity specialization of `tdapp1_int` succeeds when the
  displayed identity is written as `id_transfd`.
- the terminal-source `piapp1_int` witness exists as a stable fold target, but
  the later `piapp1_int_*` projection aliases were removed as plan-divergent.
- `Hom_cat (Pi_cat E) s t` now unfolds to the terminal-source displayed transfor
  category, giving the section-hom package a principled bridge into the existing
  `Transfd_cat` infrastructure.
- the concrete displayed-composition target object needed by the terminal-source
  path now reduces through the late pointwise projection to
  `homd_src_secd (Const_catd K Terminal_cat) E s x (piapp0 s x)`, and evaluating
  that section at `y` and `Terminal_obj` reaches the `homd_` family used by
  `piapp1_func`.
- the next projected component has the exact `Obj (Pi_cat (homd_ ...))` type of
  `piapp1_func E s x y`.

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
the now-retained principled displayed-composition projection. Do not replace
this with a capped composite bridge.

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

### 6. `Hom_cat (Pi_cat E) s t` Is Implemented

The previously deferred rule is now implemented:

```text
Hom_cat (Pi_cat E) s t
  -> Transfd_cat (Const_catd K Terminal_cat) E s t
```

Assertions validate both the generic rule and the constant-family join to
`Transf_cat s t`. Remaining work is not this bridge itself, but the later
terminal-specialization fold from internal displayed action to `piapp1_func`.

### 7. External Surface Heads Remain Deferred

The following were intentionally not introduced:

- external `fdapp1_*`
- external `tdapp1_*`

The internal object/hom action packagings from v2 have now been introduced for
both ordinary and displayed internal heads. The plan still says to promote
less-internal external heads only after the internal layer is better understood.
The derived `fdapp1_int_fibre_*` names added later remain internal projection
notation and do not settle the external API question.

### 8. Displayed Composition Fibre Projection Is Retained Late

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
early near the other projection rules, but it later typechecked quickly in the
late projection block, including with focused assertions for the intended
`Fibre_func (comp_catd_fapp0 FF GG)` normal forms needed by the `piapp1_int`
cascade. The proposed `D`/`C`
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
- stable primitive `tdapp0_func` / `tdapp0_fapp0` projection heads.
- derived `Fibre_func` / `Fibre_transf` / `Fibre_transf_app` notation.
- pointwise `Op_funcd` fibre projection and related `Fibre_func` assertions.
- `Fibre_func (homd_int FF)` source-projection assertions.
- derived `fdapp1_int_fibre_transf` / `fdapp1_int_fibre_app` projections.
- initial `piapp1_func` / `piapp1_fapp0` stable package plus
  `piapp1_src_obj`.
- stable `piapp1_int` projection chain down to `piapp1_func`.
- constant-family `piapp1_fapp0` object-action bridge to `fapp1_fapp0`.
- stable Pi evaluation, constant-section, and section-pullback helper heads with
  focused beta assertions.

It does not complete the full plan. The next work should focus on the remaining
action questions, especially:

1. the remaining `sigma_intro_transf` object beta,
2. whether additional displayed-composition projection rules should be installed
   beyond the late concrete rule now used by the `piapp1_int` cascade,
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

5. Completed for the current concrete use: do not keep the rejected `D`/`C`
   displayed-composition projection rule. The semantically correct `E`/`C`
   outer-slot version is installed late, where it supports the `piapp1_int`
   cascade and typechecks quickly. Keep `Fibre_func` as derived notation; do not
   promote it to primitive just to expose this rule.

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

8. Completed for the object-level package: the planned projection/fold from
   `piapp1_int E s` to the existing external package `piapp1_func E s x y` is
   now implemented by stable intermediate heads. No broad whole-family
   terminal/constant `homd_int` rule was needed for this fold.

9. Partially completed: after the internal `piapp1_int` witness fold became
   stable, add narrow projected terminal-source normal forms for the existing
   `homd_int` spine. The current file now reduces:

```text
homd_src_func (Const_catd K Terminal_cat) x
  -> Obj_func (homd_src_sec ... Terminal_obj)

homd_tgt_func (Const_catd K Terminal_cat) x Terminal_obj y
  -> Obj_func (Terminal_catd (Op_cat (Hom_cat K x y)))

homd_tgt_funcd (Const_catd K Terminal_cat) E s x u y
  -> Obj_func (homd_ E E (id_funcd E) x u y (piapp0 s y))
```

These rules are enough to expose the terminal source and inner terminal
endpoint through projections, while avoiding a broad whole-family `homd_int`
rule. The generalized `homd_tgt_funcd` terminal-source rule is also validated
through the `piapp0 (homd_src_secd ...) y` cascade.

10. Removed: do not keep the plan-divergent `piapp1_int_tgt_sec`,
    `piapp1_int_fibre_transf`, or `piapp1_int_fibre_app` aliases, and do not keep
    the capped terminal-source bridge that matched a displayed-composition
    subterm. The implemented stable route is the plan-backed projection chain
    `piapp1_int_src_transf`, `piapp1_int_src_app`,
    `piapp1_int_tgt_transf`, followed by the final `piapp1_func` fold.

11. Completed prerequisite: install the packaged section-hom bridge:

```text
Hom_cat (Pi_cat E) s t
  -> Transfd_cat (Const_catd K Terminal_cat) E s t
```

    This is separate from displayed-composition fibre projection. It validates
    the expected constant-family join:

```text
Hom_cat (Pi_cat (Const_catd K A)) s t
  -> Transf_cat s t
```

12. Completed: the `piapp1_int -> piapp1_func` work now proceeds only from
    stable heads. The specialized `piapp1_int` projection reaches the `Pi_cat`
    target used by `piapp1_func` via:

```text
fdapp1_int_transfd
  -> piapp1_int
  -> tapp0_fapp0/Fibre_func projections
  -> late comp_catd_fapp0 pointwise projection
  -> homd_int terminal/constant projected normal forms
```

    The generalized terminal-source `homd_tgt_funcd` step, the `Hom_cat
    (Pi_cat E)` section-hom bridge, the terminal `Transf_cat` collapse, and the
    late displayed-composition projection together expose the target. The final
    object-level fold is:

```text
tapp0_fapp0 Terminal_obj (piapp1_int_tgt_transf E s x y)
  -> piapp1_func E s x y
```

    The constant-family object action has now been added at the primitive
    `fapp0` projection head:

```text
fapp0 (piapp1_func (Const_catd K A) s x y) f
  -> fapp1_fapp0 s f
```

    This validates:

```text
piapp1_fapp0 (Const_catd K A) s x y f
  -> fapp1_fapp0 K A s x y f
```

    Remaining work should continue to the next planned beta/action rules and
    section/evaluation transfors. Do not add direct rules over the reducible
    `Fibre_transf_app` abbreviation, and keep `piapp1_fapp0` itself as defined
    notation rather than a rewrite-rule head.

13. Completed for the Pi-side generic helper backlog: reintroduce the stable
    helpers whose beta rules now typecheck quickly:

```text
pi_eval_transf E
const_section_func K A
section_pullback_func F E
```

    The validated beta assertions are:

```text
tapp0_fapp0 k (pi_eval_transf E) -> piapp0_func E k
piapp0 (const_section_func K A a) k -> a
piapp0 (section_pullback_func F E s) a -> piapp0 s (F a)
```

    The remaining generic helper gap is `sigma_intro_transf` object beta. Keep it
    deferred until a `sigma_intro_func` object-action rule can be made both
    typable and fast; do not add the currently probed slow rule.
