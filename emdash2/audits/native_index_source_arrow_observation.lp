require open emdash.native_index_family_prototype;

symbol native_index_source_arrow_observation [Z : Cat] (D : τ (Catd Z)) (x0 x : τ (Obj Z)) (r : τ (Hom Z x0 x))
  (d e : τ (Obj (@Sigma_cat Z D)))
  (a : τ (Hom Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d)))
  (b : τ (Hom Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e)))
  (m : τ (Hom (@Sigma_cat Z D) d e))
  (theta : τ (Hom (Hom_cat Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e)) b
    (@comp_fapp0 Z x
      (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d)
      (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e)
      (@fapp1_fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d e m) a)))
  : τ (Hom (@native_index_cat Z D x0)
      (@fapp0 (@native_index_cat Z D x) (@native_index_cat Z D x0)
        (@native_index_source_func Z D x0 x r) (@native_index_point Z D x d a))
      (@fapp0 (@native_index_cat Z D x) (@native_index_cat Z D x0)
        (@native_index_source_func Z D x0 x r) (@native_index_point Z D x e b)))
≔ @fapp1_fapp0 (@native_index_cat Z D x) (@native_index_cat Z D x0)
    (@native_index_source_func Z D x0 x r)
    (@native_index_point Z D x d a) (@native_index_point Z D x e b)
    (@native_index_arrow Z D x d e a b m theta);

compute @native_index_source_arrow_observation;
