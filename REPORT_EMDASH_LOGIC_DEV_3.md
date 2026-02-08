# REPORT_EMDASH_LOGIC_DEV_3.md

Date: 2026-02-08

## Implemented In This Phase

### 1) `Total_cat` now has always-Σ core behavior

Added generic rules:

- `rule τ (Obj (@Total_cat $B $E)) ↪ \`τΣ_ x : τ (Obj $B), Obj (Fibre_cat $E x);`
- `rule fapp0 (Total_proj1_func $E) (Struct_sigma $x $u) ↪ $x;`
- `rule Hom_cat (@Total_cat $Z $E) (Struct_sigma $x $u) (Struct_sigma $y $v)
    ↪ Op_cat (Total_cat (Fibration_cov_catd (Total_hom_func $E $x $u $y $v)));`

with the canonical head:

- `symbol Total_hom_func ... ≔ TotalΣ_hom_func ...;`

So `Total_cat` now normalizes through the internal alt4/uncurry pipeline instead of relying on the old Groth-only hom shortcut.

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

Once stable, remove the remaining `TotalΣ_*` naming indirection by folding `TotalΣ_hom_func` into `Total_hom_func`
and pruning duplicate parallel symbols/rules.
