/* Reviewer-facing constructive balancedness consumers. */

require open emdash.emdash3_2_abelian_bimorphisms;

assert
  (C : Cat)
  (Prod : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Abl : τ (@ComputationalAbelianCategory C Prod t))
  (X Y : τ (Obj C))
  (h : τ (Hom C X Y))
  (monic : τ (@IsMonic C X Y h))
  (epic : τ (@IsEpic C X Y h))
  ⊢ @computational_abelian_bimorphism_inverse C Prod t
      Abl X Y h monic epic
  : τ (Hom C Y X);

assert
  (C : Cat)
  (Prod : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Abl : τ (@ComputationalAbelianCategory C Prod t))
  (X Y : τ (Obj C))
  (h : τ (Hom C X Y))
  (monic : τ (@IsMonic C X Y h))
  (epic : τ (@IsEpic C X Y h))
  ⊢ @computational_abelian_bimorphism_left_path C Prod t
      Abl X Y h monic epic
  : τ (@= (Hom C X X)
      (@comp_fapp0 C X Y X
        (@computational_abelian_bimorphism_inverse C Prod t
          Abl X Y h monic epic) h)
      (@id C X));

assert
  (C : Cat)
  (Prod : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Abl : τ (@ComputationalAbelianCategory C Prod t))
  (X Y : τ (Obj C))
  (h : τ (Hom C X Y))
  (monic : τ (@IsMonic C X Y h))
  (epic : τ (@IsEpic C X Y h))
  ⊢ @computational_abelian_bimorphism_right_path C Prod t
      Abl X Y h monic epic
  : τ (@= (Hom C Y Y)
      (@comp_fapp0 C Y X Y h
        (@computational_abelian_bimorphism_inverse C Prod t
          Abl X Y h monic epic))
      (@id C Y));

assert
  (C : Cat)
  (Prod : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Abl : τ (@ComputationalAbelianCategory C Prod t))
  (X Y : τ (Obj C))
  (h : τ (Hom C X Y))
  (monic : τ (@IsMonic C X Y h))
  (epic : τ (@IsEpic C X Y h))
  ⊢ @computational_abelian_bimorphism_iso C Prod t
      Abl X Y h monic epic
  : τ (@IsoEvidence C X Y);

assert
  (C : Cat)
  (Prod : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Abl : τ (@ComputationalAbelianCategory C Prod t))
  (A B : τ (Obj C))
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
  ⊢ @computational_abelian_coimage_image_iso C Prod t
      Abl A B f monic epic
  : τ (@IsoEvidence C
      (@computational_coimage_object C Prod t
        (@computational_abelian_preabelian C Prod t Abl) A B f)
      (@computational_image_object C Prod t
        (@computational_abelian_preabelian C Prod t Abl) A B f));
