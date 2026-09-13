/* The ordinary profile makes native square fillers propositions. */
require open emdash.emdash3_2_one_cat_native_square_paths;

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [x0 x1 y0 y1 : τ (Obj C)]
  (u : τ (Hom C x0 y0)) (v : τ (Hom C x1 y1))
  (a : τ (Hom C x0 x1)) (b : τ (Hom C y0 y1))
  (alpha beta : τ (Obj (@homdc_square_fibre C x0 x1 y0 y1 u v a b))) ⊢
  @one_cat_native_square_path C C1 x0 x1 y0 y1 u v a a b b alpha beta (eq_refl a) (eq_refl b)
  : τ (@= (Hom (@LaxArrow_cat C) (@lax_edge C x0 y0 u) (@lax_edge C x1 y1 v))
    (@lax_square C x0 x1 y0 y1 u v a b alpha)
    (@lax_square C x0 x1 y0 y1 u v a b beta));

// No unrestricted erasure of arbitrary directed fillers is introduced.
assertnot [C : Cat] [x0 x1 y0 y1 : τ (Obj C)]
  (u : τ (Hom C x0 y0)) (v : τ (Hom C x1 y1))
  (a : τ (Hom C x0 x1)) (b : τ (Hom C y0 y1))
  (alpha beta : τ (Obj (@homdc_square_fibre C x0 x1 y0 y1 u v a b))) ⊢
  @eq_refl (Obj (@homdc_square_fibre C x0 x1 y0 y1 u v a b)) alpha
  : τ (@= (Obj (@homdc_square_fibre C x0 x1 y0 y1 u v a b)) alpha beta);
