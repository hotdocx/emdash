# Plan: Clean v3 Foundations, Internalize Constructor Functoriality, and Rework Sigma Hom

## Summary

Refactor `emdash3.lp` toward the cleaner v3 architecture: make displayed functors the general evaluator layer, make `Pi_cat` its terminal-context instance, internalize pullback/composition/Catdd constructors as functor objects, and remove the temporary `homd_eval_func` / `Homd_func` endpoint bridge.

`Pi` hom should be characterized first, because it gives the section/transfor/evaluation infrastructure needed for the later Sigma/dependent-hom story. Sigma hom should then use a `Catd` classifier over the base hom category, not a Cat-valued endpoint functor.

## Key Changes

- Consolidate documentation into `reports/REPORT_EMDASH_V3_CONSOLIDATED.md`.
  - Summarize the PRD, the current emdash2 lessons that still matter, the accepted v3 architecture, and the next implementation sequence.
  - Include a “superseded reports” index for all existing `reports/*` files so old reports can be retired without losing context.
  - Do not read or reference `.scratchpad/`.

- Rebase `Pi_cat` on displayed functor evaluation.
  - Restore `Functord_cat [Z] E D` as the primitive slice hom category and `Functord E D := Obj (Functord_cat E D)`.
  - Make `Catd_cat Z` use `Hom_cat (Catd_cat Z) E D ↪ Functord_cat E D`.
  - Define `Pi_cat E` as the terminal displayed-functor instance: `Functord_cat (Terminal_catd Z) E`.
  - Make `piapp0 s z` compute through `fdapp0 s z Terminal_obj`.
  - Define generic `Transf_catd` / `Transfd_cat` for homs in `Functord_cat`, then add the terminal-source collapse so `Hom_cat (Pi_cat E) s t` reduces to `Pi_cat (PiHom_catd E s t)`.

- Internalize constructor functoriality.
  - Add `Pullback_catd_func F : Functor (Catd_cat B) (Catd_cat A)` with object action `E ↦ Pullback_catd E F`; fold its hom action to `Pullback_funcd`.
  - Add `comp_cat_func [X Y Z] : Functor (Functor_cat Y Z) (Functor_cat (Functor_cat X Y) (Functor_cat X Z))`; keep `comp_cat_cov_func G` as its object action.
  - Update `op_val_func` and similar pipelines to use the functorial composition package.
  - Add `Pullback_catdd_func F` and `Functor_catdd_func B` as functor-object versions of the current `Pullback_catdd` and `Functor_catdd`; keep the existing names as object-action aliases.
  - Clarify `Const_catdd [I Z] E` as weakening both `Z` and `E` into the extra `I` context.

- Make `Totald_catd` semantically functorial in `H`.
  - Add `Total_intro_func`, the induced functor on totals from a displayed functor.
  - Add `Totald_func Z : Functor (Catd_cat Z) Cat_cat`, with object action `H ↦ Total_cat H` and hom action `FF ↦ Total_intro_func (id_func Z) FF`.
  - Define `Totald_catd Z` via `Fibration_cov_catd (Totald_func Z)` instead of a bare fibre-only rule.
  - Keep `Total_proj1_functord Z`, with fibre functor reducing to `Total_proj1_func H`.

- Rework dependent hom endpoints and Sigma hom.
  - Remove `homd_eval_func`, `Homd_func`, and their assertions.
  - Keep `homd_curry` / `homd_int` as the internal primitive.
  - Introduce `SigmaHom_catd E x u y v : Catd (Op_cat (Hom_cat Z x y))` as the Sigma-hom classifier.
  - Define:
    `Hom_cat (Sigma_cat E) (Struct_sigma x u) (Struct_sigma y v) ↪ Op_cat (Total_cat (SigmaHom_catd E x u y v))`.
  - Add the Groth sanity rule for `E = Fibration_cov_catd M`:
    the fibre at `f : x → y` reduces to `Hom_cat (M y) (fib_cov_tapp0_fapp0 M f u) v`.
  - Do not reintroduce a Cat-valued `Homd_func` unless later extraction from `homd_curry` proves it is the right normal form.

## Test Plan

- Run after each slice:
  - `lambdapi check -w emdash3.lp`
- Final validation:
  - `EMDASH_TYPECHECK_TIMEOUT=60s make check`

- Required assertions:
  - `piapp0 s z ≡ fdapp0 s z Terminal_obj`.
  - `Hom_cat (Pi_cat E) s t ≡ Pi_cat (PiHom_catd E s t)`.
  - `fapp0 (Pullback_catd_func F) E ≡ Pullback_catd E F`.
  - `fapp1_fapp0 (Pullback_catd_func F) FF ≡ Pullback_funcd F FF`.
  - `fapp0 (fapp0 comp_cat_func G) F ≡ comp_cat_fapp0 G F`.
  - `Fibre_cat (Totald_catd Z) H ≡ Total_cat H`.
  - `fapp1_fapp0 (Totald_func Z) FF ≡ Total_intro_func (id_func Z) FF`.
  - `Fibre_cat (SigmaHom_catd (Fibration_cov_catd M) x u y v) f ≡ Hom_cat (M y) (fib_cov_tapp0_fapp0 M f u) v`.
  - Existing `hom2_int`, `hom_`, `hom_con`, `Functor_catd`, `Catdd`, and `PredPi_catd` sanity checks still pass.

## Assumptions

- `emdash3.lp` is allowed to break compatibility with temporary v3 names from earlier iterations.
- `emdash2.lp` remains read-only reference material.
- `Functord_cat` becomes primitive again because it makes section evaluation and Pi hom a terminal-context instance of the general displayed-functor story.
- Sigma hom is tested before attempting a fully derived generic endpoint extraction from `homd_curry`.
- Old reports will not be moved by this implementation; the consolidated report will make them safe for the user to retire afterward.
