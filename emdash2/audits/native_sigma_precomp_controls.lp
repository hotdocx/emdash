/* NON-LIBRARY structural Sigma source-action controls on the staged prefix.
   The generic laxity and full Homd/profile qualifications remain separate. */
require open emdash.native_index_family_prototype;

// The consumed-point bridge compares the same retained r,m,a in both orders.
symbol native_prepost_interchange [A B : Cat] (F : τ (Functor B A))
  (u v : τ (Obj A)) (x y : τ (Obj B))
  (r : τ (Hom A v u)) (m : τ (Hom B x y)) (a : τ (Hom A u (@fapp0 B A F x)))
  : τ (@= (Hom A v (@fapp0 B A F y))
      (@hom_precomp_along_fapp0 A A (@id_func A) (@fapp0 B A F y) v u r
        (@hom_postcomp_fapp0 A B F u x y m a))
      (@hom_postcomp_fapp0 A B F v x y m
        (@hom_precomp_along_fapp0 A A (@id_func A) (@fapp0 B A F x) v u r a)))
≔ @eq_refl (Hom A v (@fapp0 B A F y))
    (@hom_postcomp_fapp0 A B F v x y m
      (@hom_precomp_along_fapp0 A A (@id_func A) (@fapp0 B A F x) v u r a));

assertnot [A B : Cat] (F : τ (Functor B A))
  (u v : τ (Obj A)) (x y : τ (Obj B))
  (r r' : τ (Hom A v u)) (m : τ (Hom B x y)) (a : τ (Hom A u (@fapp0 B A F x))) ⊢
  @eq_refl (Hom A v (@fapp0 B A F y))
    (@hom_postcomp_fapp0 A B F v x y m
      (@hom_precomp_along_fapp0 A A (@id_func A) (@fapp0 B A F x) v u r' a))
  : τ (@= (Hom A v (@fapp0 B A F y))
      (@hom_precomp_along_fapp0 A A (@id_func A) (@fapp0 B A F y) v u r
        (@hom_postcomp_fapp0 A B F u x y m a))
      (@hom_postcomp_fapp0 A B F v x y m
        (@hom_precomp_along_fapp0 A A (@id_func A) (@fapp0 B A F x) v u r' a)));

assertnot [A B : Cat] (F : τ (Functor B A))
  (u v : τ (Obj A)) (x y : τ (Obj B))
  (r : τ (Hom A v u)) (m m' : τ (Hom B x y)) (a : τ (Hom A u (@fapp0 B A F x))) ⊢
  @eq_refl (Hom A v (@fapp0 B A F y))
    (@hom_postcomp_fapp0 A B F v x y m'
      (@hom_precomp_along_fapp0 A A (@id_func A) (@fapp0 B A F x) v u r a))
  : τ (@= (Hom A v (@fapp0 B A F y))
      (@hom_precomp_along_fapp0 A A (@id_func A) (@fapp0 B A F y) v u r
        (@hom_postcomp_fapp0 A B F u x y m a))
      (@hom_postcomp_fapp0 A B F v x y m'
        (@hom_precomp_along_fapp0 A A (@id_func A) (@fapp0 B A F x) v u r a)));

// Theta is mapped by the existing whole precomposition functor. Its target
// endpoint uses the proven rigid pre/postcomposition comparison.
symbol native_index_whiskered_triangle [Z : Cat] (D : τ (Catd Z))
  (x0 x : τ (Obj Z)) (r : τ (Hom Z x0 x))
  (d e : τ (Obj (@Sigma_cat Z D)))
  (a : τ (Hom Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d)))
  (b : τ (Hom Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e)))
  (m : τ (Hom (@Sigma_cat Z D) d e))
  (theta : τ (Hom (Hom_cat Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e)) b
      (@hom_postcomp_fapp0 Z (@Sigma_cat Z D) (@Sigma_proj1_func Z D) x d e m a)))
  : τ (Hom (Hom_cat Z x0 (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e))
      (@hom_precomp_along_fapp0 Z Z (@id_func Z)
        (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e) x0 x r b)
      (@hom_postcomp_fapp0 Z (@Sigma_cat Z D) (@Sigma_proj1_func Z D) x0 d e m
        (@hom_precomp_along_fapp0 Z Z (@id_func Z)
          (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d) x0 x r a)))
≔ @fapp1_fapp0 (Hom_cat Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e))
    (Hom_cat Z x0 (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e))
    (@hom_precomp_along_func Z Z (@id_func Z)
      (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e) x0 x r)
    b (@hom_postcomp_fapp0 Z (@Sigma_cat Z D) (@Sigma_proj1_func Z D) x d e m a) theta;

// Complete source-arrow computation at the original index and triangle.
symbol native_index_source_arrow_beta [Z : Cat] (D : τ (Catd Z))
  (x0 x : τ (Obj Z)) (r : τ (Hom Z x0 x))
  (d e : τ (Obj (@Sigma_cat Z D)))
  (a : τ (Hom Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d)))
  (b : τ (Hom Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e)))
  (m : τ (Hom (@Sigma_cat Z D) d e))
  (theta : τ (Hom (Hom_cat Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e)) b
      (@hom_postcomp_fapp0 Z (@Sigma_cat Z D) (@Sigma_proj1_func Z D) x d e m a)))
  : τ (@= (Hom (@native_index_cat Z D x0)
      (@native_index_point Z D x0 d (@hom_precomp_along_fapp0 Z Z (@id_func Z)
        (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d) x0 x r a))
      (@native_index_point Z D x0 e (@hom_precomp_along_fapp0 Z Z (@id_func Z)
        (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e) x0 x r b)))
      (@fapp1_fapp0 (@native_index_cat Z D x) (@native_index_cat Z D x0)
        (@native_index_source_func Z D x0 x r)
        (@native_index_point Z D x d a) (@native_index_point Z D x e b)
        (@native_index_arrow Z D x d e a b m theta))
      (@native_index_arrow Z D x0 d e (@hom_precomp_along_fapp0 Z Z (@id_func Z)
        (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d) x0 x r a) (@hom_precomp_along_fapp0 Z Z (@id_func Z)
        (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e) x0 x r b) m
        (@native_index_whiskered_triangle Z D x0 x r d e a b m theta)))
≔ @eq_refl (Hom (@native_index_cat Z D x0)
      (@native_index_point Z D x0 d (@hom_precomp_along_fapp0 Z Z (@id_func Z)
        (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d) x0 x r a))
      (@native_index_point Z D x0 e (@hom_precomp_along_fapp0 Z Z (@id_func Z)
        (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e) x0 x r b))) (@native_index_arrow Z D x0 d e (@hom_precomp_along_fapp0 Z Z (@id_func Z)
        (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d) x0 x r a) (@hom_precomp_along_fapp0 Z Z (@id_func Z)
        (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e) x0 x r b) m
        (@native_index_whiskered_triangle Z D x0 x r d e a b m theta));

// Raw Sigma arrow presentation remains supported by the same action.
symbol native_index_raw_arrow [Z : Cat] (D : τ (Catd Z))
  (x : τ (Obj Z))
  (d e : τ (Obj (@Sigma_cat Z D)))
  (a : τ (Hom Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d)))
  (b : τ (Hom Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e)))
  (m : τ (Hom (@Sigma_cat Z D) d e))
  (theta : τ (Hom (Hom_cat Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e)) b
      (@hom_postcomp_fapp0 Z (@Sigma_cat Z D) (@Sigma_proj1_func Z D) x d e m a)))
  : τ (Hom (@native_index_cat Z D x)
      (@native_index_point Z D x d a) (@native_index_point Z D x e b))
≔ Struct_sigma m theta;

symbol native_index_raw_source_arrow_beta [Z : Cat] (D : τ (Catd Z))
  (x0 x : τ (Obj Z)) (r : τ (Hom Z x0 x))
  (d e : τ (Obj (@Sigma_cat Z D)))
  (a : τ (Hom Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d)))
  (b : τ (Hom Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e)))
  (m : τ (Hom (@Sigma_cat Z D) d e))
  (theta : τ (Hom (Hom_cat Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e)) b
      (@hom_postcomp_fapp0 Z (@Sigma_cat Z D) (@Sigma_proj1_func Z D) x d e m a)))
  : τ (@= (Hom (@native_index_cat Z D x0)
      (@native_index_point Z D x0 d (@hom_precomp_along_fapp0 Z Z (@id_func Z)
        (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d) x0 x r a))
      (@native_index_point Z D x0 e (@hom_precomp_along_fapp0 Z Z (@id_func Z)
        (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e) x0 x r b)))
      (@fapp1_fapp0 (@native_index_cat Z D x) (@native_index_cat Z D x0)
        (@native_index_source_func Z D x0 x r)
        (@native_index_point Z D x d a) (@native_index_point Z D x e b)
        (@native_index_raw_arrow Z D x d e a b m theta))
      (@native_index_arrow Z D x0 d e (@hom_precomp_along_fapp0 Z Z (@id_func Z)
        (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d) x0 x r a) (@hom_precomp_along_fapp0 Z Z (@id_func Z)
        (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e) x0 x r b) m
        (@native_index_whiskered_triangle Z D x0 x r d e a b m theta)))
≔ @eq_refl (Hom (@native_index_cat Z D x0)
      (@native_index_point Z D x0 d (@hom_precomp_along_fapp0 Z Z (@id_func Z)
        (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d) x0 x r a))
      (@native_index_point Z D x0 e (@hom_precomp_along_fapp0 Z Z (@id_func Z)
        (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e) x0 x r b))) (@native_index_arrow Z D x0 d e (@hom_precomp_along_fapp0 Z Z (@id_func Z)
        (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d) x0 x r a) (@hom_precomp_along_fapp0 Z Z (@id_func Z)
        (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e) x0 x r b) m
        (@native_index_whiskered_triangle Z D x0 x r d e a b m theta));

// The side condition must not invent a factorization of an arbitrary g.
assertnot [A B : Cat] (F : τ (Functor B A))
  (u v : τ (Obj A)) (x y : τ (Obj B))
  (r : τ (Hom A v u)) (m : τ (Hom B x y))
  (a : τ (Hom A u (@fapp0 B A F x))) (g : τ (Hom A u (@fapp0 B A F y))) ⊢
  @eq_refl (Hom A v (@fapp0 B A F y))
    (@hom_postcomp_fapp0 A B F v x y m
      (@hom_precomp_along_fapp0 A A (@id_func A) (@fapp0 B A F x) v u r a))
  : τ (@= (Hom A v (@fapp0 B A F y))
      (@hom_precomp_along_fapp0 A A (@id_func A) (@fapp0 B A F y) v u r g)
      (@hom_postcomp_fapp0 A B F v x y m
        (@hom_precomp_along_fapp0 A A (@id_func A) (@fapp0 B A F x) v u r a)));
