/* NON-LIBRARY whole source-2-cell computation and direction control. */
require open emdash.native_index_source_two_cell_observation;

symbol native_index_source_two_cell_expected [Z : Cat] (D : τ (Catd Z))
  (x x' : τ (Obj Z)) (r s : τ (Hom Z x x'))
  (alpha : τ (Hom (Hom_cat Z x x') r s))
  (d : τ (Obj (@Sigma_cat Z D)))
  (a : τ (Hom Z x' (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d)))
  : τ (Hom (@native_index_cat Z D x)
      (@fapp0 (@native_index_cat Z D x') (@native_index_cat Z D x)
        (@native_index_source_func Z D x x' s) (@native_index_point Z D x' d a))
      (@fapp0 (@native_index_cat Z D x') (@native_index_cat Z D x)
        (@native_index_source_func Z D x x' r) (@native_index_point Z D x' d a)))
≔ Struct_sigma (@id (@Sigma_cat Z D) d)
    (@comp_prod_fapp1_fapp0 Z x x' (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d)
      (Struct_sigma r a) (Struct_sigma s a)
      (Struct_sigma alpha (@id (Hom_cat Z x' (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d)) a)));

symbol native_index_source_two_cell_beta [Z : Cat] (D : τ (Catd Z))
  (x x' : τ (Obj Z)) (r s : τ (Hom Z x x'))
  (alpha : τ (Hom (Hom_cat Z x x') r s))
  (d : τ (Obj (@Sigma_cat Z D)))
  (a : τ (Hom Z x' (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d)))
  : τ (@= (Hom (@native_index_cat Z D x)
      (@fapp0 (@native_index_cat Z D x') (@native_index_cat Z D x)
        (@native_index_source_func Z D x x' s) (@native_index_point Z D x' d a))
      (@fapp0 (@native_index_cat Z D x') (@native_index_cat Z D x)
        (@native_index_source_func Z D x x' r) (@native_index_point Z D x' d a)))
      (@native_index_source_two_cell_observation Z D x x' r s alpha d a)
      (@native_index_source_two_cell_expected Z D x x' r s alpha d a))
≔ @eq_refl (Hom (@native_index_cat Z D x)
      (@fapp0 (@native_index_cat Z D x') (@native_index_cat Z D x)
        (@native_index_source_func Z D x x' s) (@native_index_point Z D x' d a))
      (@fapp0 (@native_index_cat Z D x') (@native_index_cat Z D x)
        (@native_index_source_func Z D x x' r) (@native_index_point Z D x' d a))) (@native_index_source_two_cell_expected Z D x x' r s alpha d a);

// A genuine directed source 2-cell is not silently inverted.
assertnot [Z : Cat] (D : τ (Catd Z))
  (x x' : τ (Obj Z)) (r s : τ (Hom Z x x'))
  (alpha : τ (Hom (Hom_cat Z x x') r s))
  (d : τ (Obj (@Sigma_cat Z D)))
  (a : τ (Hom Z x' (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d))) ⊢
  @native_index_source_two_cell_expected Z D x x' r s alpha d a
  : τ (Hom (@native_index_cat Z D x)
      (@fapp0 (@native_index_cat Z D x') (@native_index_cat Z D x)
        (@native_index_source_func Z D x x' r) (@native_index_point Z D x' d a))
      (@fapp0 (@native_index_cat Z D x') (@native_index_cat Z D x)
        (@native_index_source_func Z D x x' s) (@native_index_point Z D x' d a)));
