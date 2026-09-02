/* Reviewer-facing canonical coimage-to-image bimorphism consumers. */

require open emdash.emdash3_2_abelian_image_bimorphisms;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B : τ (Obj C))
  (f : τ (Hom C A B))
  ⊢ @abelian_coimage_image_comparison_is_monic C P t Ab A B f
  : τ (@IsMonic C
      (@computational_coimage_object C P t
        (@abelian_stability_preabelian C P t Ab) A B f)
      (@computational_image_object C P t
        (@abelian_stability_preabelian C P t Ab) A B f)
      (@coimage_image_comparison C P t
        (@abelian_stability_preabelian C P t Ab) A B f));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B : τ (Obj C))
  (f : τ (Hom C A B))
  ⊢ @abelian_coimage_image_comparison_is_epic C P t Ab A B f
  : τ (@IsEpic C
      (@computational_coimage_object C P t
        (@abelian_stability_preabelian C P t Ab) A B f)
      (@computational_image_object C P t
        (@abelian_stability_preabelian C P t Ab) A B f)
      (@coimage_image_comparison C P t
        (@abelian_stability_preabelian C P t Ab) A B f));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B : τ (Obj C))
  (f : τ (Hom C A B))
  ⊢ @abelian_coimage_image_comparison_bimorphism C P t Ab A B f
  : τ (@AbelianCoimageImageComparisonBimorphism C P t Ab A B f);
