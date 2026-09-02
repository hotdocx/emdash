/*
  Constructive balancedness from computational normality.

  For an explicitly monic and epic arrow, epicity makes its selected cokernel
  projection zero. The codomain identity is therefore a normal-monomorphism
  test. Its selected lift is an inverse on the right, and monic cancellation
  derives the left inverse law. The result uses the existing IsoEvidence
  owner and adds no runtime rule.
*/

require open emdash.emdash3_2_abelian_images;

symbol computational_abelian_bimorphism_inverse_test
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Abl : τ (@ComputationalAbelianCategory C Prod t))
  [X Y : τ (Obj C)]
  (h : τ (Hom C X Y))
  (epic : τ (@IsEpic C X Y h))
  : τ (@NormalMonoTest C
      (@preabelian_preadditive C Prod t
        (@computational_abelian_preabelian C Prod t Abl))
      X Y h
      (@preabelian_cokernel C Prod t
        (@computational_abelian_preabelian C Prod t Abl) X Y h)
      Y)
≔ @Struct_sigma
    (Hom C Y Y)
    (λ u : τ (Hom C Y Y),
      @= (Hom C Y
          (@computational_cokernel_object C
            (@preabelian_preadditive C Prod t
              (@computational_abelian_preabelian C Prod t Abl))
            X Y h
            (@preabelian_cokernel C Prod t
              (@computational_abelian_preabelian C Prod t Abl) X Y h)))
        (@comp_fapp0 C Y Y
          (@computational_cokernel_object C
            (@preabelian_preadditive C Prod t
              (@computational_abelian_preabelian C Prod t Abl))
            X Y h
            (@preabelian_cokernel C Prod t
              (@computational_abelian_preabelian C Prod t Abl) X Y h))
          (@computational_cokernel_morphism C
            (@preabelian_preadditive C Prod t
              (@computational_abelian_preabelian C Prod t Abl))
            X Y h
            (@preabelian_cokernel C Prod t
              (@computational_abelian_preabelian C Prod t Abl) X Y h)) u)
        (@preadditive_hom_zero C
          (@preabelian_preadditive C Prod t
            (@computational_abelian_preabelian C Prod t Abl))
          Y
          (@computational_cokernel_object C
            (@preabelian_preadditive C Prod t
              (@computational_abelian_preabelian C Prod t Abl))
            X Y h
            (@preabelian_cokernel C Prod t
              (@computational_abelian_preabelian C Prod t Abl) X Y h))))
    (@id C Y)
    (@epic_cokernel_morphism_zero_path C
      (@preabelian_preadditive C Prod t
        (@computational_abelian_preabelian C Prod t Abl))
      X Y h
      (@preabelian_cokernel C Prod t
        (@computational_abelian_preabelian C Prod t Abl) X Y h)
      epic);

symbol computational_abelian_bimorphism_inverse
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Abl : τ (@ComputationalAbelianCategory C Prod t))
  [X Y : τ (Obj C)]
  (h : τ (Hom C X Y))
  (monic : τ (@IsMonic C X Y h))
  (epic : τ (@IsEpic C X Y h))
  : τ (Hom C Y X)
≔ @lift_along_monomorphism C
    (@preabelian_preadditive C Prod t
      (@computational_abelian_preabelian C Prod t Abl))
    (@preabelian_cokernels C Prod t
      (@computational_abelian_preabelian C Prod t Abl))
    (@computational_abelian_mono_lifts C Prod t Abl)
    X Y h monic Y
    (@computational_abelian_bimorphism_inverse_test C Prod t Abl X Y h epic);

symbol computational_abelian_bimorphism_right_path
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Abl : τ (@ComputationalAbelianCategory C Prod t))
  [X Y : τ (Obj C)]
  (h : τ (Hom C X Y))
  (monic : τ (@IsMonic C X Y h))
  (epic : τ (@IsEpic C X Y h))
  : τ (@= (Hom C Y Y)
      (@comp_fapp0 C Y X Y h
        (@computational_abelian_bimorphism_inverse C Prod t
          Abl X Y h monic epic))
      (@id C Y))
≔ @lift_along_monomorphism_path C
    (@preabelian_preadditive C Prod t
      (@computational_abelian_preabelian C Prod t Abl))
    (@preabelian_cokernels C Prod t
      (@computational_abelian_preabelian C Prod t Abl))
    (@computational_abelian_mono_lifts C Prod t Abl)
    X Y h monic Y
    (@computational_abelian_bimorphism_inverse_test C Prod t Abl X Y h epic);

symbol computational_abelian_bimorphism_left_comparison_path
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Abl : τ (@ComputationalAbelianCategory C Prod t))
  [X Y : τ (Obj C)]
  (h : τ (Hom C X Y))
  (monic : τ (@IsMonic C X Y h))
  (epic : τ (@IsEpic C X Y h))
  : τ (@= (Hom C X Y)
      (@comp_fapp0 C X X Y h
        (@comp_fapp0 C X Y X
          (@computational_abelian_bimorphism_inverse C Prod t
            Abl X Y h monic epic) h))
      (@comp_fapp0 C X X Y h (@id C X)))
≔ @eq_trans
    (Hom C X Y)
    (@comp_fapp0 C X X Y h
      (@comp_fapp0 C X Y X
        (@computational_abelian_bimorphism_inverse C Prod t
          Abl X Y h monic epic) h))
    (@comp_fapp0 C X Y Y
      (@comp_fapp0 C Y X Y h
        (@computational_abelian_bimorphism_inverse C Prod t
          Abl X Y h monic epic)) h)
    (@comp_fapp0 C X X Y h (@id C X))
    (@comp_assoc C X Y X Y h
      (@computational_abelian_bimorphism_inverse C Prod t
        Abl X Y h monic epic) h)
    (@eq_ap
      (Hom C Y Y) (Hom C X Y)
      (λ z : τ (Hom C Y Y), @comp_fapp0 C X Y Y z h)
      (@comp_fapp0 C Y X Y h
        (@computational_abelian_bimorphism_inverse C Prod t
          Abl X Y h monic epic))
      (@id C Y)
      (@computational_abelian_bimorphism_right_path C Prod t
        Abl X Y h monic epic));

symbol computational_abelian_bimorphism_left_path
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Abl : τ (@ComputationalAbelianCategory C Prod t))
  [X Y : τ (Obj C)]
  (h : τ (Hom C X Y))
  (monic : τ (@IsMonic C X Y h))
  (epic : τ (@IsEpic C X Y h))
  : τ (@= (Hom C X X)
      (@comp_fapp0 C X Y X
        (@computational_abelian_bimorphism_inverse C Prod t
          Abl X Y h monic epic) h)
      (@id C X))
≔ monic X
    (@comp_fapp0 C X Y X
      (@computational_abelian_bimorphism_inverse C Prod t
        Abl X Y h monic epic) h)
    (@id C X)
    (@computational_abelian_bimorphism_left_comparison_path C Prod t
      Abl X Y h monic epic);

symbol computational_abelian_bimorphism_iso
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Abl : τ (@ComputationalAbelianCategory C Prod t))
  [X Y : τ (Obj C)]
  (h : τ (Hom C X Y))
  (monic : τ (@IsMonic C X Y h))
  (epic : τ (@IsEpic C X Y h))
  : τ (@IsoEvidence C X Y)
≔ @Struct_sigma
    (Hom C X Y)
    (λ to : τ (Hom C X Y),
      `Σ_ from : τ (Hom C Y X),
      `Σ_ lawL : τ (@= (Hom C X X)
        (@comp_fapp0 C X Y X from to) (@id C X)),
      @= (Hom C Y Y) (@comp_fapp0 C Y X Y to from) (@id C Y))
    h
    (@Struct_sigma
      (Hom C Y X)
      (λ from : τ (Hom C Y X),
        `Σ_ lawL : τ (@= (Hom C X X)
          (@comp_fapp0 C X Y X from h) (@id C X)),
        @= (Hom C Y Y) (@comp_fapp0 C Y X Y h from) (@id C Y))
      (@computational_abelian_bimorphism_inverse C Prod t
        Abl X Y h monic epic)
      (@Struct_sigma
        (@= (Hom C X X)
          (@comp_fapp0 C X Y X
            (@computational_abelian_bimorphism_inverse C Prod t
              Abl X Y h monic epic) h)
          (@id C X))
        (λ _ : τ _,
          @= (Hom C Y Y)
            (@comp_fapp0 C Y X Y h
              (@computational_abelian_bimorphism_inverse C Prod t
                Abl X Y h monic epic))
            (@id C Y))
        (@computational_abelian_bimorphism_left_path C Prod t
          Abl X Y h monic epic)
        (@computational_abelian_bimorphism_right_path C Prod t
          Abl X Y h monic epic)));

// Apply constructive balancedness to the canonical coimage-image comparison.
symbol computational_abelian_coimage_image_iso
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Abl : τ (@ComputationalAbelianCategory C Prod t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  (monic : τ (@IsMonic C
    (@computational_coimage_object C Prod t
      (@computational_abelian_preabelian C Prod t Abl) A B f)
    (@computational_image_object C Prod t
      (@computational_abelian_preabelian C Prod t Abl) A B f)
    (@coimage_image_comparison C Prod t
      (@computational_abelian_preabelian C Prod t Abl) A B f)))
  (epic : τ (@IsEpic C
    (@computational_coimage_object C Prod t
      (@computational_abelian_preabelian C Prod t Abl) A B f)
    (@computational_image_object C Prod t
      (@computational_abelian_preabelian C Prod t Abl) A B f)
    (@coimage_image_comparison C Prod t
      (@computational_abelian_preabelian C Prod t Abl) A B f)))
  : τ (@IsoEvidence C
      (@computational_coimage_object C Prod t
        (@computational_abelian_preabelian C Prod t Abl) A B f)
      (@computational_image_object C Prod t
        (@computational_abelian_preabelian C Prod t Abl) A B f))
≔ @computational_abelian_bimorphism_iso C Prod t Abl
    (@computational_coimage_object C Prod t
      (@computational_abelian_preabelian C Prod t Abl) A B f)
    (@computational_image_object C Prod t
      (@computational_abelian_preabelian C Prod t Abl) A B f)
    (@coimage_image_comparison C Prod t
      (@computational_abelian_preabelian C Prod t Abl) A B f)
    monic epic;
