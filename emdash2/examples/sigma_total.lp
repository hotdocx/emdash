/*
  Reviewer milestone: directed Sigma totals.

  Sigma totals are dependent sums of directed Cat-valued families. These checks
  expose the total-category constructor, arbitrary-object and arrow
  projections, constant-family product specialization, Sigma-map object
  action, and the next hom action on displayed transformations.
*/

require open emdash.emdash3_2;

assert [K : Cat] (E : τ (Catd K)) ⊢
  @fapp0 (Catd_cat K) Cat_cat (Sigma_func K) E ≡ Sigma_cat E;

assert [K : Cat] (E : τ (Catd K)) (k : τ (Obj K)) (u : τ (Obj (Fibre_cat E k))) ⊢
  fapp0 (Sigma_proj1_func E) (Struct_sigma k u) ≡ k;

// The first projection also computes for an arbitrary total object.
assert [K : Cat]
  (E : τ (Catd K))
  (q : τ (Obj (@Sigma_cat K E))) ⊢
  @fapp0 (@Sigma_cat K E) K (@Sigma_proj1_func K E) q
  ≡ @sigma_obj_base K E q;

// Arbitrary-endpoint total arrows retain both generic projections.
assert [K : Cat]
  (E : τ (Catd K))
  (q r : τ (Obj (@Sigma_cat K E)))
  (p : τ (Hom K
    (@sigma_obj_base K E q)
    (@sigma_obj_base K E r)))
  (alpha : τ (Hom
    (@Fibre_cat K E (@sigma_obj_base K E r))
    (@fapp0
      (@Fibre_cat K E (@sigma_obj_base K E q))
      (@Fibre_cat K E (@sigma_obj_base K E r))
      (@catd_transport_func K E
        (@sigma_obj_base K E q)
        (@sigma_obj_base K E r)
        p)
      (@sigma_obj_fibre K E q))
    (@sigma_obj_fibre K E r))) ⊢
  @fapp1_fapp0
    (@Sigma_cat K E) K (@Sigma_proj1_func K E)
    q r (@sigma_arrow_intro K E q r p alpha)
  ≡ p;

assert [K : Cat]
  (E : τ (Catd K))
  (q r : τ (Obj (@Sigma_cat K E)))
  (p : τ (Hom K
    (@sigma_obj_base K E q)
    (@sigma_obj_base K E r)))
  (alpha : τ (Hom
    (@Fibre_cat K E (@sigma_obj_base K E r))
    (@fapp0
      (@Fibre_cat K E (@sigma_obj_base K E q))
      (@Fibre_cat K E (@sigma_obj_base K E r))
      (@catd_transport_func K E
        (@sigma_obj_base K E q)
        (@sigma_obj_base K E r)
        p)
      (@sigma_obj_fibre K E q))
    (@sigma_obj_fibre K E r))) ⊢
  @sigma_arrow_fibre K E q r
    (@sigma_arrow_intro K E q r p alpha)
  ≡ alpha;

// The same fibre observer retains the established raw-arrow computation.
assert [K : Cat]
  (E : τ (Catd K))
  (x y : τ (Obj K))
  (u : τ (Obj (@Fibre_cat K E x)))
  (v : τ (Obj (@Fibre_cat K E y)))
  (p : τ (Hom K x y))
  (alpha : τ (Hom
    (@Fibre_cat K E y)
    (@fapp0
      (@Fibre_cat K E x)
      (@Fibre_cat K E y)
      (@catd_transport_func K E x y p)
      u)
    v)) ⊢
  @sigma_arrow_fibre
    K E
    (Struct_sigma x u)
    (Struct_sigma y v)
    (@sigma_arrow K E x y u v p alpha)
  ≡ alpha;

// Generic constructor composition stays internal at arbitrary endpoints.
assert [K : Cat]
  (E : τ (Catd K))
  (a r s : τ (Obj (@Sigma_cat K E)))
  (p : τ (Hom K
    (@sigma_obj_base K E a)
    (@sigma_obj_base K E r)))
  (q : τ (Hom K
    (@sigma_obj_base K E r)
    (@sigma_obj_base K E s)))
  (alpha : τ (Hom
    (@Fibre_cat K E (@sigma_obj_base K E r))
    (@fapp0
      (@Fibre_cat K E (@sigma_obj_base K E a))
      (@Fibre_cat K E (@sigma_obj_base K E r))
      (@catd_transport_func K E
        (@sigma_obj_base K E a)
        (@sigma_obj_base K E r)
        p)
      (@sigma_obj_fibre K E a))
    (@sigma_obj_fibre K E r)))
  (beta : τ (Hom
    (@Fibre_cat K E (@sigma_obj_base K E s))
    (@fapp0
      (@Fibre_cat K E (@sigma_obj_base K E r))
      (@Fibre_cat K E (@sigma_obj_base K E s))
      (@catd_transport_func K E
        (@sigma_obj_base K E r)
        (@sigma_obj_base K E s)
        q)
      (@sigma_obj_fibre K E r))
    (@sigma_obj_fibre K E s))) ⊢
  @comp_fapp0
    (@Sigma_cat K E) a r s
    (@sigma_arrow_intro K E r s q beta)
    (@sigma_arrow_intro K E a r p alpha)
  ≡ @sigma_arrow_intro
      K E a s
      (@comp_fapp0 K
        (@sigma_obj_base K E a)
        (@sigma_obj_base K E r)
        (@sigma_obj_base K E s)
        q p)
      (@comp_fapp0
        (@Fibre_cat K E (@sigma_obj_base K E s))
        _ _ _
        beta
        (@fapp1_fapp0
          (@Fibre_cat K E (@sigma_obj_base K E r))
          (@Fibre_cat K E (@sigma_obj_base K E s))
          (@catd_transport_func K E
            (@sigma_obj_base K E r)
            (@sigma_obj_base K E s)
            q)
          _ _ alpha));

// If a constant-family total has already become a product, the same
// constructor law remains available in that canonical post-projection form.
assert [K A : Cat]
  (a r s : τ (Obj (@Sigma_cat K (@Const_catd K A))))
  (p : τ (Hom K
    (@sigma_obj_base K (@Const_catd K A) a)
    (@sigma_obj_base K (@Const_catd K A) r)))
  (q : τ (Hom K
    (@sigma_obj_base K (@Const_catd K A) r)
    (@sigma_obj_base K (@Const_catd K A) s)))
  (alpha : τ (Hom A
    (@sigma_obj_fibre K (@Const_catd K A) a)
    (@sigma_obj_fibre K (@Const_catd K A) r)))
  (beta : τ (Hom A
    (@sigma_obj_fibre K (@Const_catd K A) r)
    (@sigma_obj_fibre K (@Const_catd K A) s))) ⊢
  @comp_fapp0
    (Product_cat K A) a r s
    (@sigma_arrow_intro K (@Const_catd K A) r s q beta)
    (@sigma_arrow_intro K (@Const_catd K A) a r p alpha)
  ≡ @sigma_arrow_intro
      K (@Const_catd K A) a s
      (@comp_fapp0 K
        (@sigma_obj_base K (@Const_catd K A) a)
        (@sigma_obj_base K (@Const_catd K A) r)
        (@sigma_obj_base K (@Const_catd K A) s)
        q p)
      (@comp_fapp0 A
        (@sigma_obj_fibre K (@Const_catd K A) a)
        (@sigma_obj_fibre K (@Const_catd K A) r)
        (@sigma_obj_fibre K (@Const_catd K A) s)
        beta alpha);

assert [K A : Cat] ⊢
  @Sigma_cat K (@Const_catd K A) ≡ Product_cat K A;

assert [K : Cat] (E D : τ (Catd K)) (η : τ (Functord E D))
  (k : τ (Obj K)) (u : τ (Obj (Fibre_cat E k))) ⊢
  @fapp0 (@Sigma_cat K E) (@Sigma_cat K D)
    (@sigma_map_func K E D η)
    (Struct_sigma k u)
    ≡ @Struct_sigma
        (Obj K)
        (λ kk : τ (Obj K), Obj (Fibre_cat D kk))
        k
        (@fapp0 (Fibre_cat E k) (Fibre_cat D k)
          (@tapp0_fapp0 K Cat_cat E D k η)
          u);

// The stable arbitrary-object action agrees with whole Sigma action only at
// proof time; its two projections compute without object eta.
assert [K : Cat]
  (E D : τ (Catd K))
  (η : τ (Functord E D))
  (q : τ (Obj (@Sigma_cat K E))) ⊢
  @eq_refl
    (Obj (@Sigma_cat K D))
    (@fapp0
      (@Sigma_cat K E)
      (@Sigma_cat K D)
      (@sigma_map_func K E D η)
      q)
  : τ (@=
      (Obj (@Sigma_cat K D))
      (@fapp0
        (@Sigma_cat K E)
        (@Sigma_cat K D)
        (@sigma_map_func K E D η)
        q)
      (@sigma_map_obj K E D η q));

assertnot [K : Cat]
  (E D : τ (Catd K))
  (η : τ (Functord E D))
  (q : τ (Obj (@Sigma_cat K E))) ⊢
  @fapp0
    (@Sigma_cat K E)
    (@Sigma_cat K D)
    (@sigma_map_func K E D η)
    q
  ≡ @sigma_map_obj K E D η q;

assert [K : Cat]
  (E D : τ (Catd K))
  (η : τ (Functord E D))
  (q : τ (Obj (@Sigma_cat K E))) ⊢
  @sigma_Fst
    (Obj K)
    (λ k : τ (Obj K), Obj (@Fibre_cat K D k))
    (@sigma_map_obj K E D η q)
  ≡ @sigma_obj_base K E q;

assert [K : Cat]
  (E D : τ (Catd K))
  (η : τ (Functord E D))
  (q : τ (Obj (@Sigma_cat K E))) ⊢
  @sigma_Snd
    (Obj K)
    (λ k : τ (Obj K), Obj (@Fibre_cat K D k))
    (@sigma_map_obj K E D η q)
  ≡ @fapp0
      (@Fibre_cat K E (@sigma_obj_base K E q))
      (@Fibre_cat K D (@sigma_obj_base K E q))
      (@tapp0_fapp0
        K Cat_cat E D (@sigma_obj_base K E q) η)
      (@sigma_obj_fibre K E q);

assert [K : Cat]
  [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)]
  (eta : τ (Transfd FF GG)) ⊢
  @fapp1_fapp0
    (@Functord_cat K E D)
    (Functor_cat (@Sigma_cat K E) (@Sigma_cat K D))
    (@fapp1_func (@Catd_cat K) Cat_cat (@Sigma_func K) E D)
    FF GG eta
  ≡ @sigma_map_transf K E D FF GG eta;
