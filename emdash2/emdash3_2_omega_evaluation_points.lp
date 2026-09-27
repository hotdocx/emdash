/* Evaluate retained whole inverse data at its original category index. */
require open emdash.emdash3_2;

symbol omega_equiv_at [K D : Cat]
  [F G : τ (Functor K D)] [epsilon : τ (@Transf K D F G)]
  (u : τ (@OmegaEquivAlong (Functor_cat K D) F G epsilon))
  (x : τ (Obj K))
  : τ (@OmegaEquivAlong D (@fapp0 K D F x) (@fapp0 K D G x)
      (@tapp0_fapp0 K D F G x epsilon))
≔ @omega_equiv_along_intro D (@fapp0 K D F x) (@fapp0 K D G x)
    (@tapp0_fapp0 K D F G x epsilon)
    (@tapp0_fapp0 K D G F x
      (@omega_equiv_along_left_inv (Functor_cat K D) F G epsilon u))
    (@tapp0_fapp0 K D G F x
      (@omega_equiv_along_right_inv (Functor_cat K D) F G epsilon u))
    (@eq_ap (Hom (Functor_cat K D) F F)
      (Hom D (@fapp0 K D F x) (@fapp0 K D F x))
      (λ theta : τ (Hom (Functor_cat K D) F F), @tapp0_fapp0 K D F F x theta)
      (@comp_fapp0 (Functor_cat K D) F G F
        (@omega_equiv_along_left_inv (Functor_cat K D) F G epsilon u) epsilon)
      (@id (Functor_cat K D) F)
      (@omega_equiv_along_left_law (Functor_cat K D) F G epsilon u))
    (@eq_ap (Hom (Functor_cat K D) G G)
      (Hom D (@fapp0 K D G x) (@fapp0 K D G x))
      (λ theta : τ (Hom (Functor_cat K D) G G), @tapp0_fapp0 K D G G x theta)
      (@comp_fapp0 (Functor_cat K D) G F G epsilon
        (@omega_equiv_along_right_inv (Functor_cat K D) F G epsilon u))
      (@id (Functor_cat K D) G)
      (@omega_equiv_along_right_law (Functor_cat K D) F G epsilon u));

symbol omega_equiv_catd_at [K : Cat]
  [F G : τ (Catd K)] [epsilon : τ (@Functord K F G)]
  (u : τ (@OmegaEquivAlong (Catd_cat K) F G epsilon))
  (x : τ (Obj K))
  : τ (@OmegaEquivAlong Cat_cat (@fapp0 K Cat_cat F x) (@fapp0 K Cat_cat G x)
      (@tapp0_fapp0 K Cat_cat F G x epsilon))
≔ @omega_equiv_along_intro Cat_cat (@fapp0 K Cat_cat F x) (@fapp0 K Cat_cat G x)
    (@tapp0_fapp0 K Cat_cat F G x epsilon)
    (@tapp0_fapp0 K Cat_cat G F x
      (@omega_equiv_along_left_inv (Catd_cat K) F G epsilon u))
    (@tapp0_fapp0 K Cat_cat G F x
      (@omega_equiv_along_right_inv (Catd_cat K) F G epsilon u))
    (@eq_ap (Hom (Catd_cat K) F F)
      (Hom Cat_cat (@fapp0 K Cat_cat F x) (@fapp0 K Cat_cat F x))
      (λ theta : τ (Hom (Catd_cat K) F F), @tapp0_fapp0 K Cat_cat F F x theta)
      (@comp_fapp0 (Catd_cat K) F G F
        (@omega_equiv_along_left_inv (Catd_cat K) F G epsilon u) epsilon)
      (@id (Catd_cat K) F)
      (@omega_equiv_along_left_law (Catd_cat K) F G epsilon u))
    (@eq_ap (Hom (Catd_cat K) G G)
      (Hom Cat_cat (@fapp0 K Cat_cat G x) (@fapp0 K Cat_cat G x))
      (λ theta : τ (Hom (Catd_cat K) G G), @tapp0_fapp0 K Cat_cat G G x theta)
      (@comp_fapp0 (Catd_cat K) G F G epsilon
        (@omega_equiv_along_right_inv (Catd_cat K) F G epsilon u))
      (@id (Catd_cat K) G)
      (@omega_equiv_along_right_law (Catd_cat K) F G epsilon u));
