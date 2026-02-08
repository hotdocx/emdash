# REPORT_EMDASH_LOGIC_DEV_3.md

Date: 2026-02-08

## Implemented In This Phase

### 1) `Total_cat` now has always-Σ core behavior

Added generic rules:

- `rule τ (Obj (@Total_cat $B $E)) ↪ \`τΣ_ x : τ (Obj $B), Obj (Fibre_cat $E x);`
- `rule fapp0 (Total_proj1_func $E) (Struct_sigma $x $u) ↪ $x;`
- `rule Hom_cat (@Total_cat $Z $E) (Struct_sigma $x $u) (Struct_sigma $y $v)
    ↪ Op_cat (Total_cat (Fibration_cov_catd (Homd_func $E $x $u $y $v)));`

with the canonical head:

- `sequential symbol Homd_func ...;`

So `Total_cat` now normalizes through the internal `homd_cov_curry`/uncurry pipeline instead of relying on the old Groth-only hom shortcut.

### 2) Removed collapse-dependent shortcuts

Deferred/removed collapse rules and dependent short-hands that were causing non-joinable overlaps:

- `Total_cat (Terminal_catd A) ↪ A`
- `Total_cat (Lift_catd A) ↪ A`
- associated `Total_proj1_func` shortcuts
- `Unlift_func` and its β-shortcut
- terminal-target shortcut for `Total_intro_func`
- terminal-domain Groth section shortcut/assert around `Total_intro_func ... (Terminal_catd X) ...`

### 3) Removed legacy Groth-specific `Total_cat` hom/identity shortcuts

Deferred/removed rules that conflicted with the always-Σ path:

- old `Hom_cat (Total_cat (Fibration_cov_catd M)) ... ↪ ... comp_hom_con_fib_cov ...`
- old hom-level `fapp1_func` projection shortcut for `Total_proj1_func`
- old `id`/`comp_fapp0` shortcuts for `Total_cat (Fibration_cov_catd M)`
- old Groth-only sanity assertions tied to these shortcuts

`comp_hom_con_fib_cov` remains available as a standalone helper symbol/assert, but is no longer the definitional head for `Total_cat` homs.

## Result

- `EMDASH_TYPECHECK_TIMEOUT=60s make check` passes.
- The file is in a consistent “always-Σ `Total_cat`” migration state with legacy Groth shortcuts deferred.

## Next Cleanup Step

Once stable, remove the remaining `TotalΣ_*` naming indirection by folding `TotalΣ_hom_func` into `Homd_func`
and pruning duplicate parallel symbols/rules.

## Inventory: Rules Lost When Removing `Total_cat (Terminal_catd _)` / `Total_cat (Lift_catd _)` Collapses

Reference baseline: `emdash2.backup.lp`.

### A) Terminal-collapse family (`Total_cat (Terminal_catd A) ↪ A`)

Removed rules:

- `rule Total_cat (Terminal_catd $A) ↪ $A;`
- `rule Total_proj1_func (Terminal_catd $A) ↪ @id_func $A;`
- `rule Total_proj2_funcd (Terminal_catd $A) ↪ @id_funcd $A (Terminal_catd $A);`
- `rule @Total_intro_func $X $Y $A (Terminal_catd $Y) $xy (Terminal_funcd $A)
    ↪ comp_cat_fapp0 $xy (Total_proj1_func $A);`

Also removed (collapse-dependent usage form):

- `rule @fapp0 $X (Total_cat (@Fibration_cov_catd $B $M))
      (@Total_intro_func $X $B (Terminal_catd $X) (@Fibration_cov_catd $B $M) $xy $FF) $x
    ↪ Struct_sigma (fapp0 $xy $x) (...);`
- with the companion sanity assert `π₁ ∘ (∫FF) ≡ xy`.

Recoverability if collapses are reintroduced progressively:

- **Direct definitional recovery**:
  re-add the four terminal-collapse rules above exactly.
- **Equivalent non-collapse form (already possible now)**:
  keep always-`Σ` `Total_cat`, and use formulas over
  `Total_cat (Terminal_catd X)` objects as `Struct_sigma x Terminal_obj`
  (or equivalent normalized fibre terminal object), instead of collapsing to `x : Obj X`.
- **Progressive strategy**:
  first re-add only `Total_cat (Terminal_catd A) ↪ A` + `Total_proj1_func` collapse;
  then add `Total_proj2_funcd` and terminal `Total_intro_func` shortcut after checking joinability
  against the always-`Σ` rules and the `Homd_func` path.

### B) Lift-collapse family (`Total_cat (Lift_catd A) ↪ A`)

Removed rules/symbol path:

- `rule Total_cat (Lift_catd $A) ↪ $A;`
- `rule Total_proj1_func (Lift_catd $A) ↪ Terminal_func $A;`
- `symbol Unlift_func ... ≔ @Total_intro_func Terminal_cat Terminal_cat ...;`
- `rule @Total_intro_func Terminal_cat Terminal_cat (Lift_catd $A) (Lift_catd $B)
    (@id_func Terminal_cat) (@Lift_funcd $A $B $F) ↪ $F;`

Also removed collapse-era sanity assertion:

- `assert [A B : Cat] (F : τ (Functor A B)) ⊢ Unlift_func (Lift_funcd F) ≡ F;`

Recoverability if collapses are reintroduced progressively:

- **Direct definitional recovery**:
  re-add the two lift collapse rules and re-enable `Unlift_func` + its β-shortcut.
- **Equivalent semantic recovery without collapse**:
  keep `Lift_funcd` + `fdapp0` computation (already present) and work fibrewise;
  use equivalence lemmas/asserts instead of definitional collapse (`∫const ≃ A` behavior).
- **Progressive strategy**:
  reintroduce `Total_cat (Lift_catd A) ↪ A` first, postpone `Total_proj1_func (Lift_catd A)` and
  `Unlift_func` β-shortcut until overlaps with terminal and hom rules are validated.

### C) Practical recommendation for staged reintroduction

If we decide to restore collapses, safest order is:

1. Reintroduce terminal collapse only:
   `Total_cat (Terminal_catd A) ↪ A` and `Total_proj1_func (Terminal_catd A) ↪ id`.
2. Recheck all `Total_intro_func` rewrite rules and only then re-enable terminal-target shortcut.
3. Reintroduce lift collapse (`Total_cat (Lift_catd A) ↪ A`) next.
4. Re-enable `Unlift_func` and its β-rule last.

This order minimizes critical-pair pressure with the always-`Σ` `Total_cat` rules and with the new
`Homd_func`/`homd_cov_curry` normalization pipeline.

## Rewrite Cleanup Pass (from REPORT_EMDASH_LOGIC_DEV_2.md "Key rewrite principles")

Date: 2026-02-08 (follow-up)

We revisited the extra engineering rules that were introduced during the earlier `Total_uncurry_eval2` /
`homd_cov_int_altproj` stabilization phase, and tested removal incrementally with
`EMDASH_TYPECHECK_TIMEOUT=60s make check`.

### Removed as non-essential (typecheck still passes)

- `rule @comp_cat_fapp0 $A $B $D (@comp_cat_fapp0 $B $C $D $F $G) $H
    ↪ @comp_cat_fapp0 $A $C $D $F (@comp_cat_fapp0 $A $B $C $G $H);`
  - Removed (associativity normalization at functor-composition head).
- `rule @comp_cat_fapp0 (Op_cat $C) (Op_cat $B) (Op_cat Cat_cat)
      (@Op_func $B Cat_cat (@hom_cov $A $W $B $F)) $H
    ↪ @Op_func $C Cat_cat
        (@hom_cov $A $W $C (comp_cat_fapp0 $F (@Op_func (Op_cat $C) (Op_cat $B) $H)));`
  - Removed (special contravariant accumulation form).
- `rule @comp_cat_fapp0 (Op_cat $C) (Op_cat $B) Cat_cat
      (@hom_con $A $W $B $F) (@Op_func $C $B $G)
    ↪ @hom_con $A $W $C (@comp_cat_fapp0 $C $B $A $F $G);`
  - Removed (derived from existing `hom_con` definition + remaining rules).
- `rule @Pullback_catd $A $B
      (@Op_catd (Op_cat $B) (@Fibration_cov_catd (Op_cat $B) $H)) $F
    ↪ @Op_catd (Op_cat $A)
        (@Fibration_cov_catd (Op_cat $A) (comp_cat_fapp0 $H (@Op_func $A $B $F)));`
  - Removed (no longer required by current `homd_cov_curry`/uncurry normalization chain).

### Kept as genuinely useful / currently required

- `rule @comp_cat_fapp0 $B $B $C $F (@id_func $B) ↪ $F;`
- `rule @comp_cat_fapp0 $A $B $B (@id_func $B) $F ↪ $F;`
  - Kept as mild identity simplifications on the stable composition head.
- `rule @comp_cat_fapp0 $C $B Cat_cat (@hom_cov $A $W $B $F) $G
    ↪ hom_cov $W (comp_cat_fapp0 $F $G);`
  - Kept: removing it causes an immediate assertion failure in the current file (`hom_cov` precomposition
    definitional behavior is relied upon).

### Outcome

- The ad hoc rule set was reduced while preserving successful typecheck.
- We now keep only the rules that are either broadly canonical simplifications or demonstrably required
  by existing assertions/computations.

## homd_cov_curry Consolidation Pass (Naming/Glue Cleanup)

Date: 2026-02-08 (same session)

Goal:
- reduce one-off `homd_cov_curry*` wrappers,
- keep only semantic/reused heads,
- preserve computation and current `Homd_func` behavior.

### Removed one-off glue symbols

The following intermediate wrappers were removed:

- `Functor_catd_fixR_func`
- `Edge_catd_fam_op`
- `Edge_catd_at`
- `swap_homd_cov_curry_section2`
- `Total_uncurry_eval2`

All were single-purpose plumbing around the swap/uncurry primitives (now named
`logic_swap_funcd` and `logic_uncurry_total`) and are now inlined.

### Kept semantic/reused symbols

Retained heads in the `homd_cov_curry` path:

- `CatCat_catd`
- `Edge_catd_fam`
- `homd_cov_curry_base_fam`
- `homd_cov_curry_base`
- `homd_cov_curry`
- `homd_cov_curry_fapp0`
- `logic_swap_funcd` (primitive)
- `logic_uncurry_total` (primitive)

### Renames

- `homd_cov_curry_target_catd`-style wrapper → (inlined)
- `homd_cov_int_altproj` → `homd_cov_curry_fapp0_uncurry`

This removes migration suffixes (`*2`, `*proj`) and makes the role explicit.

### Structural change

`homd_cov_curry_fapp0_uncurry` is now defined directly as:
- swap the section using `logic_swap_funcd` via `comp_catd_fapp0`,
- uncurry to the total using `logic_uncurry_total`.

No auxiliary wrapper symbol is needed between these two steps.

### Homd_func integration update

The generic `Homd_func` rule now uses:
- `Pullback_catd (Functor_catd (fapp0 Edge_catd_fam x) (CatCat_catd Z)) (Total_proj1_func E)`
- `homd_cov_curry_fapp0_uncurry E x u`

Groth shortcut behavior is unchanged.

### Validation

- `EMDASH_TYPECHECK_TIMEOUT=60s make check` passes after consolidation.

## Naming Harmonization Pass (fapp0/eval)

Date: 2026-02-08 (follow-up)

Implemented:

- Renamed `eval0_func` to `fapp0_func` in `emdash2.lp`.
- Updated the associated β-rule and sanity assertion:
  - `fapp0 (fapp0_func x) F ↪ fapp0 F x`.
- Updated internal call sites (notably in the `homd_cov_curry_base_fam` definition).

Comment harmonization:

- Kept the current canonical terminology in code comments:
  - `homd_cov_curry*` for the internal dependent-hom curry pipeline,
  - `Homd_func` for the total-hom classifier head,
  - `logic_uncurry_total` / `logic_swap_funcd` for logic primitives.

Validation:

- `EMDASH_TYPECHECK_TIMEOUT=60s make check` passes.

## Groth Bridge for `homd_cov_curry` (Direct Curry-Path Computation)

Date: 2026-02-08 (follow-up)

Implemented a direct Groth bridge on the fully applied curry-path expression, in addition to
keeping the convenient `Homd_func` Groth shortcut.

Added rewrite rule (engineering-critical):

```lp
rule @fdapp0
      (Total_cat (@Fibration_cov_catd $B $M))
      (Terminal_catd (Total_cat (@Fibration_cov_catd $B $M)))
      (Pullback_catd
        (Functor_catd (@fapp0 (Op_cat $B) (Catd_cat $B) (Edge_catd_fam) $x) (CatCat_catd $B))
        (Total_proj1_func (@Fibration_cov_catd $B $M)))
      (homd_cov_curry_fapp0_uncurry (@Fibration_cov_catd $B $M) $x $u)
      (Struct_sigma $y $v)
      Terminal_obj
  ↪ @comp_hom_con_fib_cov $B $M $x $y $u $v;
```

Rationale:

- This gives direct computation for the generic `homd_cov_curry_fapp0_uncurry` route in the Groth case,
  so the curry path is no longer only “spec-level”; it now computes to the transported hom functor.
- We still keep `Homd_func` as `sequential` with the explicit Groth shortcut first, because it remains
  a useful fast head and preserves current normalization behavior.
- We intentionally did **not** introduce additional partial-application stable heads for this bridge;
  the single fully applied rule is enough for now and keeps the rule surface minimal.

Note on validation shape:

- We intentionally keep this bridge as a rewrite rule (without an additional explicit `assert`),
  because explicit fully-applied `fdapp0` sanity terms at `Terminal_catd (Total_cat ...)` currently
  trigger brittle implicit reconstruction for the fibre object argument.
- End-to-end behavior remains covered by `make check` through the `Hom_cat`/`Homd_func` normalization path.
