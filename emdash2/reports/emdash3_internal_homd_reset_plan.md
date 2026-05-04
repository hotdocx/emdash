# emdash3 Architecture Reset: Internal Dependent Hom

## Summary

Keep the typechecking v3 core as a useful first slice, but redesign the displayed/`homd` layer before building more on it. The current `Homd_func E x u y v` is acceptable only as an endpoint projection; it should not be the primary dependent-hom construction. The next iteration should introduce weakening/constant displayed categories first, then define the dependent hom internally as a section-valued displayed functor that can be iterated.

## Key Changes

- Add first-class weakening:
  - `Const_catd Z A : Catd Z`, with `Fibre_cat (Const_catd Z A) z ↪ A`.
  - `Lift_catd A ≔ Const_catd Terminal_cat A` for the terminal-context special case.
  - `CatCat_catd Z ≔ Const_catd Z Cat_cat`.
  - Keep `Catd_catd E : Catd Z` for the varying universe with fibre `Catd_cat (E[z])`.
- Add minimal reindexing/duality infrastructure:
  - `Pullback_catd E F : Catd A`, with fibre `E[F x]`.
  - `Op_catd E : Catd (Op_cat Z)`, with fibre `Op_cat (E[z])`.
  - `Const_catd`, `Pullback_catd`, and `Op_catd` get only object/fibre computation initially.
- Replace foundational `Homd_func` with internal families:
  - `Edge_catd x : Catd Z`, with fibre at `y` equal to `Op_cat (Hom_cat Z x y)`.
  - `homd_curry_base_fam E x : Catd Z`, fibre at `y` equal to `Functor_cat (Edge_catd x[y]) (Functor_cat (Fibre_cat E y) Cat_cat)`.
  - `homd_curry_base E : Functor (Op_cat Z) Cat_cat`, where `x` maps to `Pi_cat (homd_curry_base_fam E x)`.
  - `homd_int E : Functord (Op_catd E) (Fibration_cov_catd (homd_curry_base E))`.
- Demote `Homd_func` to a derived projection:
  - Keep a stable head such as `homd_eval_func E x u y v : Functor (Op_cat (Hom_cat Z x y)) Cat_cat`.
  - Its intended source is `homd_int E` evaluated at `x,u`, then at `y`, then at `v`.
  - The old `Homd_func` name can alias this projection only after `homd_int` exists.
- Keep `Sigma_cat` homs endpoint-level, but route them through the derived projection:
  - `Hom_cat (Sigma_cat E) (x,u) (y,v)` reduces to the total over `homd_eval_func E x u y v`.
  - The Grothendieck computation rule moves to `homd_eval_func`, not to the internal primitive.

## Implementation Plan

1. Preserve the checked v3 core through `Functor_cat`, `Cat_cat`, `hom2_int`, `Pi_cat`, `Sigma_cat`, and `Functor_catd`.
2. Insert `Const_catd`, `Lift_catd`, `Pullback_catd`, and `Op_catd` before `Functor_catd` starts depending on higher displayed constructions.
3. Replace the current Section 6 `Homd_func` block with the internal `Edge_catd` / `homd_curry_base_fam` / `homd_curry_base` / `homd_int` stack.
4. Reintroduce endpoint projection heads only after the internal stack:
   - `homd_eval_func`
   - optional compatibility alias `Homd_func`
   - `Sigma_cat` hom rule using that projection
5. Update the report plan to mark the first `Homd_func` design as superseded and document the new architecture.

## Test Plan

- Run `lambdapi check -w emdash3.lp` after each layer.
- Add assertions for:
  - `Fibre_cat (Const_catd Z A) z ≡ A`.
  - `Fibre_cat (Pullback_catd E F) x ≡ Fibre_cat E (fapp0 F x)`.
  - `Fibre_cat (Op_catd E) z ≡ Op_cat (Fibre_cat E z)`.
  - `Fibre_cat (CatCat_catd Z) z ≡ Cat_cat`.
  - `Fibre_cat (Edge_catd x) y ≡ Op_cat (Hom_cat Z x y)`.
  - `Fibre_cat (homd_curry_base_fam E x) y ≡ Functor_cat (Op_cat (Hom_cat Z x y)) (Functor_cat (Fibre_cat E y) Cat_cat)`.
  - Groth projection: `fapp0 (homd_eval_func (Fibration_cov_catd M) x u y v) f ≡ Hom_cat (M[y]) (f_! u) v`.
  - `Sigma_cat` homs still reduce through the endpoint projection.

## Assumptions

- The current v3 file is not discarded wholesale; only the dependent-hom architecture is reset.
- `Homd_func` remains useful as a projection/debugging head, but it is no longer the design center.
- The immediate target is still a small typechecking kernel, not a full port of v2's `homd_curry` machinery.
