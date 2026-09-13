/* NON-LIBRARY source-2-cell observation in the structural Sigma experiment. */
require open emdash.native_index_family_prototype;

symbol native_index_source_two_cell_observation [Z : Cat] (D : τ (Catd Z))
  (x x' : τ (Obj Z)) (r s : τ (Hom Z x x'))
  (alpha : τ (Hom (Hom_cat Z x x') r s))
  (d : τ (Obj (@Sigma_cat Z D)))
  (a : τ (Hom Z x' (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d)))
  : τ (Hom (@native_index_cat Z D x)
      (@fapp0 (@native_index_cat Z D x') (@native_index_cat Z D x)
        (@native_index_source_func Z D x x' s) (@native_index_point Z D x' d a))
      (@fapp0 (@native_index_cat Z D x') (@native_index_cat Z D x)
        (@native_index_source_func Z D x x' r) (@native_index_point Z D x' d a)))
≔ @tapp0_fapp0 (@native_index_cat Z D x') (@native_index_cat Z D x)
    (@native_index_source_func Z D x x' s) (@native_index_source_func Z D x x' r)
    (@native_index_point Z D x' d a)
    (@native_index_source_transf Z D x x' r s alpha);

compute @native_index_source_two_cell_observation;
