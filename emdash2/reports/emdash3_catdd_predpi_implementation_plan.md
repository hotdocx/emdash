# Plan: Rebuild `emdash3.lp` Homd Around `PredPi_catd` and `Catdd`

## Summary

Update `emdash3.lp` so the dependent-hom core is no longer built from object-only intermediates like `Edge_catd`, `homd_curry_base_fam`, or `homd_curry_base`.

The new architecture will introduce a reusable second displayed layer:

```text
Catdd_cat B := Pi_cat (Catd_catd B)
Catdd B     := Obj (Catdd_cat B)
```

Then define the predicate-indexed Π construction as a **derived displayed category**:

```text
PredPi_catd E : Catd (Catd_cat Z)
```

with intended fibre:

```text
PredPi_catd(E)[H]
=
Pi_cat
  (Functor_catd
    (Pullback_catd E (Total_proj1_func H))
    (CatCat_catd (Total_cat H)))
```

No `PredPi_func` object-only rewrite will be introduced. The old “functor-valued” `PredPi_func` idea will be treated as a slogan; the implemented canonical object is `PredPi_catd`.

## Key Changes

- Add general internal constructor infrastructure:
  - `Fibre_func` for extracting fibre functors from displayed functors.
  - `Pullback_funcd` for reindexing displayed functors.
  - `Functor_cat_func`, `Functor_catd_func`, `Pi_func`, `op`, `comp_cat_cov_func`, `op_val_func`, `hom_int`, and `Fibration_cov_func` as reusable constructor/functor-object forms.
  - These are general infrastructure, not homd-specific rules.

- Add the `Catdd` layer:
  - `Catdd_cat [I] (B : Catd I) : Cat ≔ Pi_cat (Catd_catd B)`.
  - `Catdd [I] (B : Catd I) : Grpd ≔ Obj (Catdd_cat B)`.
  - Use `piapp0` as the canonical evaluator for `Catdd` objects; do not introduce a competing generic evaluator.
  - Add general constructors:
    - `Const_catdd [I Z] (E : Catd Z) : Catdd (Const_catd I Z)`.
    - `CatCat_catdd [I] (B : Catd I) : Catdd B`.
    - `Pullback_catdd [I] [A B : Catd I] (F : Functord A B) : Catdd B -> Catdd A`.
    - `Functor_catdd [I] [B : Catd I] : Catdd B -> Catdd B -> Catdd B`.
    - `Pi_catdd [I] [B : Catd I] : Catdd B -> Catd I`.

- Add the total/projection family over `Catd_cat Z`:
  - `Totald_catd Z : Catd (Catd_cat Z)`, fibre at `H` is `Total_cat H`.
  - `ConstZ_catd Z : Catd (Catd_cat Z) ≔ Const_catd (Catd_cat Z) Z`.
  - `Total_proj1_functord Z : Functord (Totald_catd Z) (ConstZ_catd Z)`.
  - Its fibre functor computes to `Total_proj1_func H`.

- Define `PredPi_catd` as a pure abbreviation:
  ```text
  PredPi_catd E
  ≔ Pi_catdd
      (Functor_catdd
        (Pullback_catdd (Total_proj1_functord Z) (Const_catdd E))
        (CatCat_catdd (Totald_catd Z)))
  ```
  The exact Lambdapi arguments will be fully explicit. The important invariant is: `PredPi_catd` gets no custom rewrite rules.

- Replace the current homd base stack:
  - Add `Edge_catd_fam : Functor (Op_cat Z) (Catd_cat Z)` as a δ-definition:
    ```text
    Edge_catd_fam
    ≔ Fibration_cov_func Z ∘ op_val_func Z ∘ hom_int(id_Z)
    ```
  - Redefine `Edge_catd x` as `fapp0 Edge_catd_fam x`, not as a symbol with a fibre rule.
  - Remove/replace `homd_curry_base_fam` and `homd_curry_base`.
  - Add:
    ```text
    homd_curry_target_catd E
    ≔ Pullback_catd (PredPi_catd E) Edge_catd_fam
    ```
  - Add primary primitive:
    ```text
    homd_curry E :
      Functord (Op_catd E) (homd_curry_target_catd E)
    ```
  - Keep `homd_int` only as a compatibility alias to `homd_curry`, with the new type.

- Preserve endpoint compatibility:
  - Keep `homd_eval_func` / `Homd_func` as endpoint projection/debugging heads.
  - Keep the current Grothendieck computation rule for `homd_eval_func`.
  - Keep the `Sigma_cat` hom rule routed through `homd_eval_func`.
  - Do not try in this slice to derive generic endpoint evaluation from `homd_curry`.

## Test Plan

- Run after each implementation slice:
  - `lambdapi check -w emdash3.lp`
  - final repo SOP check: `EMDASH_TYPECHECK_TIMEOUT=60s make check`

- Add assertions for the new infrastructure:
  - `Fibre_func FF z` applies like `fdapp0 FF z`.
  - `Pullback_funcd` acts by `fdapp0 GG (F x)`.
  - `Fibre_cat (Totald_catd Z) H ≡ Total_cat H`.
  - `Fibre_func (Total_proj1_functord Z) H ≡ Total_proj1_func H`.
  - `piapp0 (Const_catdd E) i ≡ E`.
  - `piapp0 (CatCat_catdd B) i ≡ CatCat_catd (Fibre_cat B i)`.
  - `piapp0 (Pullback_catdd F D) i ≡ Pullback_catd (piapp0 D i) (Fibre_func F i)`.
  - `piapp0 (Functor_catdd K L) i ≡ Functor_catd (piapp0 K i) (piapp0 L i)`.
  - `Fibre_cat (Pi_catdd K) i ≡ Pi_cat (piapp0 K i)`.

- Add semantic assertions for the new homd target:
  - `Fibre_cat (PredPi_catd E) H` reduces to:
    ```text
    Pi_cat
      (Functor_catd
        (Pullback_catd E (Total_proj1_func H))
        (CatCat_catd (Total_cat H)))
    ```
  - `Fibre_cat (Edge_catd x) y ≡ Op_cat (Hom_cat Z x y)`.
  - `Fibre_cat (homd_curry_target_catd E) x` reduces through `PredPi_catd` applied to `Edge_catd_fam x`.

- Keep existing regression assertions:
  - `hom2_int`, `hom_`, `hom_con`.
  - `Sigma_cat` object/projection behavior.
  - `Functor_catd`, `Functord_cat`, `fdapp0`.
  - Groth endpoint computation for `homd_eval_func` and `Homd_func`.

## Assumptions

- Work only in `emdash3.lp` plus one report file documenting this plan.
- `emdash2.lp` remains reference material and is not edited.
- `PredPi_func` will not be implemented as a primitive `Functor`; the implemented canonical construction is `PredPi_catd`.
- Generic `Catdd` constructors may have pointwise `piapp0`/`Fibre_cat` computation rules, because they are reusable logical infrastructure. `PredPi_catd` itself must remain a δ-definition with no bespoke rewrite rules.
- Full generic derivation of `homd_eval_func` from `homd_curry` is deferred; the current endpoint/Groth bridge remains in place for validation and compatibility.
