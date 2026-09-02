/*
  Abelian stability for the selected genuine fiber products and pushouts.

  The first layer proves the two difference-arrow cancellation facts used by
  the constructive stability argument. The completed layer derives epicity of
  the selected fiber-product projection and monicity of the selected pushout
  injection from Abelian normality. No property flag or runtime rule is used.
*/

require open emdash.emdash3_2_computational_pushouts;
require open emdash.emdash3_2_abelian_categories;

// Negation is injective in every abelian group.
symbol abelian_group_neg_cancel_path
  [A : Grpd]
  (S : τ (@AbelianGroupStructure A))
  (a b : τ A)
  (p : τ (@= A
    (@abelian_group_ops_neg A (@abelian_group_structure_ops A S) a)
    (@abelian_group_ops_neg A (@abelian_group_structure_ops A S) b)))
  : τ (@= A a b)
≔ @eq_trans A a
    (@abelian_group_ops_neg A (@abelian_group_structure_ops A S)
      (@abelian_group_ops_neg A (@abelian_group_structure_ops A S) a))
    b
    (@eq_sym A _ a (@abelian_group_neg_involutive_path A S a))
    (@eq_trans A _
      (@abelian_group_ops_neg A (@abelian_group_structure_ops A S)
        (@abelian_group_ops_neg A (@abelian_group_structure_ops A S) b))
      b
      (@eq_ap A A
        (λ x : τ A,
          @abelian_group_ops_neg A (@abelian_group_structure_ops A S) x)
        _ _ p)
      (@abelian_group_neg_involutive_path A S b));

symbol abelian_group_neg_zero_path
  [A : Grpd]
  (S : τ (@AbelianGroupStructure A))
  : τ (@= A
      (@abelian_group_ops_neg A (@abelian_group_structure_ops A S)
        (@abelian_group_ops_zero A (@abelian_group_structure_ops A S)))
      (@abelian_group_ops_zero A (@abelian_group_structure_ops A S)))
≔ @eq_sym A _ _
    (@abelian_group_add_inverse_unique_path A S
      (@abelian_group_ops_zero A (@abelian_group_structure_ops A S))
      (@abelian_group_ops_zero A (@abelian_group_structure_ops A S))
      (@abelian_group_add_zero_law A S
        (@abelian_group_ops_zero A (@abelian_group_structure_ops A S))));

// Equal composites make the precomposed difference zero.
symbol preadditive_comp_difference_zero_path
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [X Y Z : τ (Obj C)]
  (u v : τ (Hom C Y Z))
  (f : τ (Hom C X Y))
  (p : τ (@= (Hom C X Z)
    (@comp_fapp0 C X Y Z u f)
    (@comp_fapp0 C X Y Z v f)))
  : τ (@= (Hom C X Z)
      (@comp_fapp0 C X Y Z
        (@preadditive_hom_add C S Y Z u
          (@preadditive_hom_neg C S Y Z v)) f)
      (@preadditive_hom_zero C S X Z))
≔ @eq_trans (Hom C X Z) _ _ _
    ((@preadditive_comp_add_left_law C S) X Y Z
      u (@preadditive_hom_neg C S Y Z v) f)
    (@eq_trans (Hom C X Z) _ _ _
      (@eq_trans (Hom C X Z) _ _ _
        (@eq_ap (Hom C X Z) (Hom C X Z)
          (λ q : τ (Hom C X Z),
            @preadditive_hom_add C S X Z q
              (@comp_fapp0 C X Y Z
                (@preadditive_hom_neg C S Y Z v) f))
          _ _ p)
        (@eq_ap (Hom C X Z) (Hom C X Z)
          (λ q : τ (Hom C X Z),
            @preadditive_hom_add C S X Z
              (@comp_fapp0 C X Y Z v f) q)
          _ _
          (@preadditive_comp_neg_left_path C S X Y Z v f)))
      ((@abelian_group_add_inv_law
        (Hom C X Z) (@preadditive_hom_structure C S X Z))
        (@comp_fapp0 C X Y Z v f)));

// Equal postcomposites also make the postcomposed difference zero.
symbol preadditive_difference_postcomp_zero_path
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [X Y Z : τ (Obj C)]
  (g : τ (Hom C Y Z))
  (u v : τ (Hom C X Y))
  (p : τ (@= (Hom C X Z)
    (@comp_fapp0 C X Y Z g u)
    (@comp_fapp0 C X Y Z g v)))
  : τ (@= (Hom C X Z)
      (@comp_fapp0 C X Y Z g
        (@preadditive_hom_add C S X Y u
          (@preadditive_hom_neg C S X Y v)))
      (@preadditive_hom_zero C S X Z))
≔ @eq_trans (Hom C X Z) _ _ _
    ((@preadditive_comp_add_right_law C S) X Y Z g
      u (@preadditive_hom_neg C S X Y v))
    (@eq_trans (Hom C X Z) _ _ _
      (@eq_trans (Hom C X Z) _ _ _
        (@eq_ap (Hom C X Z) (Hom C X Z)
          (λ q : τ (Hom C X Z),
            @preadditive_hom_add C S X Z q
              (@comp_fapp0 C X Y Z g
                (@preadditive_hom_neg C S X Y v)))
          _ _ p)
        (@eq_ap (Hom C X Z) (Hom C X Z)
          (λ q : τ (Hom C X Z),
            @preadditive_hom_add C S X Z
              (@comp_fapp0 C X Y Z g v) q)
          _ _
          (@preadditive_comp_neg_right_path C S X Y Z g v)))
      ((@abelian_group_add_inv_law
        (Hom C X Z) (@preadditive_hom_structure C S X Z))
        (@comp_fapp0 C X Y Z g v)));

// Reading the second summand after a copair and postcomposition.
symbol additive_postcomp_copair_inj2_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C P t))
  [X Y Z T : τ (Obj C)]
  (f : τ (Hom C X Z))
  (g : τ (Hom C Y Z))
  (h : τ (Hom C Z T))
  : τ (@= (Hom C Y T)
      (@comp_fapp0 C Y
        (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) T
        (@comp_fapp0 C
          (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) Z T
          h (@additive_copair_fapp0 C P t A X Y Z f g))
        (@additive_inj2_fapp0 C P t A X Y))
      (@comp_fapp0 C Y Z T h g))
≔ @eq_trans (Hom C Y T) _ _ _
    (@eq_sym _ _ _
      (@comp_assoc C Y
        (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) Z T
        h (@additive_copair_fapp0 C P t A X Y Z f g)
        (@additive_inj2_fapp0 C P t A X Y)))
    (@eq_ap (Hom C Y Z) (Hom C Y T)
      (λ q : τ (Hom C Y Z), @comp_fapp0 C Y Z T h q)
      _ g
      (@additive_copair_inj2_path C P t A X Y Z f g));

// If e is epic, then [a,-e] is epic.
symbol additive_copair_second_epic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C P t))
  [X Y Z : τ (Obj C)]
  (a : τ (Hom C X Z))
  (e : τ (Hom C Y Z))
  (epic : τ (@IsEpic C Y Z e))
  : τ (@IsEpic C
      (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) Z
      (@additive_copair_fapp0 C P t A X Y Z a
        (@preadditive_hom_neg C
          (@additive_preadditive C P t A) Y Z e)))
≔ λ T : τ (Obj C), λ u : τ (Hom C Z T), λ v : τ (Hom C Z T),
    λ p : τ (@= (Hom C
      (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) T)
      (@comp_fapp0 C
        (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) Z T
        u
        (@additive_copair_fapp0 C P t A X Y Z a
          (@preadditive_hom_neg C
            (@additive_preadditive C P t A) Y Z e)))
      (@comp_fapp0 C
        (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) Z T
        v
        (@additive_copair_fapp0 C P t A X Y Z a
          (@preadditive_hom_neg C
            (@additive_preadditive C P t A) Y Z e)))),
      epic T u v
        (@abelian_group_neg_cancel_path
          (Hom C Y T)
          (@preadditive_hom_structure C
            (@additive_preadditive C P t A) Y T)
          (@comp_fapp0 C Y Z T u e)
          (@comp_fapp0 C Y Z T v e)
          (@eq_trans (Hom C Y T)
            (@preadditive_hom_neg C
              (@additive_preadditive C P t A) Y T
              (@comp_fapp0 C Y Z T u e))
            (@comp_fapp0 C Y Z T u
              (@preadditive_hom_neg C
                (@additive_preadditive C P t A) Y Z e))
            (@preadditive_hom_neg C
              (@additive_preadditive C P t A) Y T
              (@comp_fapp0 C Y Z T v e))
            (@eq_sym _ _ _
              (@preadditive_comp_neg_right_path C
                (@additive_preadditive C P t A) Y Z T u e))
            (@eq_trans (Hom C Y T) _
              (@comp_fapp0 C Y Z T v
                (@preadditive_hom_neg C
                  (@additive_preadditive C P t A) Y Z e))
              _
              (@eq_trans (Hom C Y T) _ _ _
                (@eq_sym _ _ _
                  (@additive_postcomp_copair_inj2_path C P t A
                    X Y Z T a
                    (@preadditive_hom_neg C
                      (@additive_preadditive C P t A) Y Z e) u))
                (@eq_trans (Hom C Y T) _ _ _
                  (@eq_ap
                    (Hom C
                      (@fapp0 (Product_cat C C) C P
                        (@Product_pair C C X Y)) T)
                    (Hom C Y T)
                    (λ q : τ (Hom C
                      (@fapp0 (Product_cat C C) C P
                        (@Product_pair C C X Y)) T),
                      @comp_fapp0 C Y
                        (@fapp0 (Product_cat C C) C P
                          (@Product_pair C C X Y)) T q
                        (@additive_inj2_fapp0 C P t A X Y))
                    _ _ p)
                  (@additive_postcomp_copair_inj2_path C P t A
                    X Y Z T a
                    (@preadditive_hom_neg C
                      (@additive_preadditive C P t A) Y Z e) v)))
              (@preadditive_comp_neg_right_path C
                (@additive_preadditive C P t A) Y Z T v e))));

// Reading the first component after a pair and precomposition.
symbol additive_proj1_pair_precomp_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C P t))
  [T X Y Z : τ (Obj C)]
  (h : τ (Hom C T X))
  (f : τ (Hom C X Y))
  (g : τ (Hom C X Z))
  : τ (@= (Hom C T Y)
      (@comp_fapp0 C T
        (@fapp0 (Product_cat C C) C P (@Product_pair C C Y Z)) Y
        (@binary_products_proj1_fapp0 C P
          (@additive_binary_products C P t A) Y Z)
        (@comp_fapp0 C T X
          (@fapp0 (Product_cat C C) C P (@Product_pair C C Y Z))
          (@binary_products_pair_fapp0 C P
            (@additive_binary_products C P t A) X Y Z f g) h))
      (@comp_fapp0 C T X Y f h))
≔ @eq_trans (Hom C T Y) _ _ _
    (@comp_assoc C T X
      (@fapp0 (Product_cat C C) C P (@Product_pair C C Y Z)) Y
      (@binary_products_proj1_fapp0 C P
        (@additive_binary_products C P t A) Y Z)
      (@binary_products_pair_fapp0 C P
        (@additive_binary_products C P t A) X Y Z f g) h)
    (@eq_refl (Hom C T Y) (@comp_fapp0 C T X Y f h));

// If m is monic, then <m,-b> is monic.
symbol additive_pair_first_monic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C P t))
  [X Y Z : τ (Obj C)]
  (m : τ (Hom C X Y))
  (b : τ (Hom C X Z))
  (monic : τ (@IsMonic C X Y m))
  : τ (@IsMonic C X
      (@fapp0 (Product_cat C C) C P (@Product_pair C C Y Z))
      (@binary_products_pair_fapp0 C P
        (@additive_binary_products C P t A) X Y Z m
        (@preadditive_hom_neg C
          (@additive_preadditive C P t A) X Z b)))
≔ λ T : τ (Obj C), λ u : τ (Hom C T X), λ v : τ (Hom C T X),
    λ p : τ (@= (Hom C T
      (@fapp0 (Product_cat C C) C P (@Product_pair C C Y Z)))
      (@comp_fapp0 C T X
        (@fapp0 (Product_cat C C) C P (@Product_pair C C Y Z))
        (@binary_products_pair_fapp0 C P
          (@additive_binary_products C P t A) X Y Z m
          (@preadditive_hom_neg C
            (@additive_preadditive C P t A) X Z b)) u)
      (@comp_fapp0 C T X
        (@fapp0 (Product_cat C C) C P (@Product_pair C C Y Z))
        (@binary_products_pair_fapp0 C P
          (@additive_binary_products C P t A) X Y Z m
          (@preadditive_hom_neg C
            (@additive_preadditive C P t A) X Z b)) v)),
      monic T u v
        (@eq_trans (Hom C T Y)
          (@comp_fapp0 C T X Y m u)
          (@comp_fapp0 C T
            (@fapp0 (Product_cat C C) C P (@Product_pair C C Y Z)) Y
            (@binary_products_proj1_fapp0 C P
              (@additive_binary_products C P t A) Y Z)
            (@comp_fapp0 C T X
              (@fapp0 (Product_cat C C) C P (@Product_pair C C Y Z))
              (@binary_products_pair_fapp0 C P
                (@additive_binary_products C P t A) X Y Z m
                (@preadditive_hom_neg C
                  (@additive_preadditive C P t A) X Z b)) u))
          (@comp_fapp0 C T X Y m v)
          (@eq_sym _ _ _
            (@additive_proj1_pair_precomp_path C P t A T X Y Z u m
              (@preadditive_hom_neg C
                (@additive_preadditive C P t A) X Z b)))
          (@eq_trans (Hom C T Y) _ _ _
            (@eq_ap
              (Hom C T
                (@fapp0 (Product_cat C C) C P (@Product_pair C C Y Z)))
              (Hom C T Y)
              (λ q : τ (Hom C T
                (@fapp0 (Product_cat C C) C P (@Product_pair C C Y Z))),
                @comp_fapp0 C T
                  (@fapp0 (Product_cat C C) C P (@Product_pair C C Y Z)) Y
                  (@binary_products_proj1_fapp0 C P
                    (@additive_binary_products C P t A) Y Z) q)
              _ _ p)
            (@additive_proj1_pair_precomp_path C P t A T X Y Z v m
              (@preadditive_hom_neg C
                (@additive_preadditive C P t A) X Z b))));

// --------------------------------------------------------------------------
// Canonical selected structures used by stability
// --------------------------------------------------------------------------

symbol abelian_stability_preabelian
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  : τ (@PreAbelianCategory C P t)
≔ @computational_abelian_preabelian C P t A;

symbol abelian_stability_additive
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  : τ (@AdditiveCategory C P t)
≔ @preabelian_additive C P t (@abelian_stability_preabelian C P t A);

symbol abelian_stability_preadditive
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  : τ (@PreadditiveCategory C)
≔ @additive_preadditive C P t (@abelian_stability_additive C P t A);

symbol abelian_stability_kernels
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  : τ (@HasComputationalKernels C (@abelian_stability_preadditive C P t A))
≔ @preabelian_kernels C P t (@abelian_stability_preabelian C P t A);

symbol abelian_stability_cokernels
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  : τ (@HasComputationalCokernels C (@abelian_stability_preadditive C P t A))
≔ @preabelian_cokernels C P t (@abelian_stability_preabelian C P t A);

symbol abelian_stability_epi_colifts
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  : τ (@HasColiftsAlongEpimorphisms C
      (@abelian_stability_preadditive C P t A)
      (@abelian_stability_kernels C P t A))
≔ @computational_abelian_epi_colifts C P t A;

symbol abelian_stability_mono_lifts
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  : τ (@HasLiftsAlongMonomorphisms C
      (@abelian_stability_preadditive C P t A)
      (@abelian_stability_cokernels C P t A))
≔ @computational_abelian_mono_lifts C P t A;

symbol abelian_selected_fiber_product
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [I X E : τ (Obj C)]
  (iota : τ (Hom C I X))
  (epsilon : τ (Hom C E X))
  : τ (@ComputationalFiberProduct C P t
      (@abelian_stability_additive C P t A) I X E iota epsilon)
≔ @computational_fiber_product_of_kernels C P t
    (@abelian_stability_additive C P t A)
    (@abelian_stability_kernels C P t A)
    I X E iota epsilon;

symbol abelian_selected_pushout
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [K X Q : τ (Obj C)]
  (mu : τ (Hom C K X))
  (pi : τ (Hom C K Q))
  : τ (@ComputationalPushout C P t
      (@abelian_stability_additive C P t A) X K Q mu pi)
≔ @computational_pushout_of_cokernels C P t
    (@abelian_stability_additive C P t A)
    (@abelian_stability_cokernels C P t A)
    X K Q mu pi;

// The defining fiber-product difference is epic when epsilon is epic.
symbol abelian_fiber_product_difference_epic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [I X E : τ (Obj C)]
  (iota : τ (Hom C I X))
  (epsilon : τ (Hom C E X))
  (epic : τ (@IsEpic C E X epsilon))
  : τ (@IsEpic C
      (@weak_pullback_product_object C P t
        (@abelian_stability_additive C P t A) I E) X
      (@weak_pullback_difference_fapp0 C P t
        (@abelian_stability_additive C P t A)
        I X E iota epsilon))
≔ @additive_copair_second_epic C P t
    (@abelian_stability_additive C P t A)
    I E X iota epsilon epic;

// Difference of two candidate maps out of the first pullback factor.
symbol abelian_fiber_projection_difference_arrow
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [I T : τ (Obj C)]
  (u v : τ (Hom C I T))
  : τ (Hom C I T)
≔ @preadditive_hom_add C (@abelian_stability_preadditive C P t A) I T
    u (@preadditive_hom_neg C
      (@abelian_stability_preadditive C P t A) I T v);

// Extend that difference by the first biproduct projection.
symbol abelian_fiber_projection_extension_arrow
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [I E T : τ (Obj C)]
  (u v : τ (Hom C I T))
  : τ (Hom C
      (@weak_pullback_product_object C P t
        (@abelian_stability_additive C P t A) I E) T)
≔ @comp_fapp0 C
    (@weak_pullback_product_object C P t
      (@abelian_stability_additive C P t A) I E)
    I T
    (@abelian_fiber_projection_difference_arrow C P t A I T u v)
    (@binary_products_proj1_fapp0 C P
      (@additive_binary_products C P t
        (@abelian_stability_additive C P t A)) I E);

// Equality after p1 makes the extended difference annihilate Ker([iota,-epsilon]).
symbol abelian_fiber_projection_extension_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [I X E T : τ (Obj C)]
  (iota : τ (Hom C I X))
  (epsilon : τ (Hom C E X))
  (u v : τ (Hom C I T))
  (p : τ (@= (Hom C
    (@computational_fiber_product_object C P t
      (@abelian_stability_additive C P t A) I X E iota epsilon
      (@abelian_selected_fiber_product C P t A I X E iota epsilon)) T)
    (@comp_fapp0 C
      (@computational_fiber_product_object C P t
        (@abelian_stability_additive C P t A) I X E iota epsilon
        (@abelian_selected_fiber_product C P t A I X E iota epsilon))
      I T u
      (@computational_fiber_product_proj1 C P t
        (@abelian_stability_additive C P t A) I X E iota epsilon
        (@abelian_selected_fiber_product C P t A I X E iota epsilon)))
    (@comp_fapp0 C
      (@computational_fiber_product_object C P t
        (@abelian_stability_additive C P t A) I X E iota epsilon
        (@abelian_selected_fiber_product C P t A I X E iota epsilon))
      I T v
      (@computational_fiber_product_proj1 C P t
        (@abelian_stability_additive C P t A) I X E iota epsilon
        (@abelian_selected_fiber_product C P t A I X E iota epsilon)))))
  : τ (@= (Hom C
      (@computational_fiber_product_object C P t
        (@abelian_stability_additive C P t A) I X E iota epsilon
        (@abelian_selected_fiber_product C P t A I X E iota epsilon)) T)
      (@comp_fapp0 C
        (@computational_fiber_product_object C P t
          (@abelian_stability_additive C P t A) I X E iota epsilon
          (@abelian_selected_fiber_product C P t A I X E iota epsilon))
        (@weak_pullback_product_object C P t
          (@abelian_stability_additive C P t A) I E) T
        (@abelian_fiber_projection_extension_arrow C P t A I E T u v)
        (@computational_fiber_product_morphism C P t
          (@abelian_stability_additive C P t A) I X E iota epsilon
          (@abelian_selected_fiber_product C P t A I X E iota epsilon)))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t A)
        (@computational_fiber_product_object C P t
          (@abelian_stability_additive C P t A) I X E iota epsilon
          (@abelian_selected_fiber_product C P t A I X E iota epsilon)) T))
≔ @eq_trans _ _ _ _
    (@eq_sym _ _ _
      (@comp_assoc C
        (@computational_fiber_product_object C P t
          (@abelian_stability_additive C P t A) I X E iota epsilon
          (@abelian_selected_fiber_product C P t A I X E iota epsilon))
        (@weak_pullback_product_object C P t
          (@abelian_stability_additive C P t A) I E)
        I T
        (@abelian_fiber_projection_difference_arrow C P t A I T u v)
        (@binary_products_proj1_fapp0 C P
          (@additive_binary_products C P t
            (@abelian_stability_additive C P t A)) I E)
        (@computational_fiber_product_morphism C P t
          (@abelian_stability_additive C P t A) I X E iota epsilon
          (@abelian_selected_fiber_product C P t A I X E iota epsilon))))
    (@preadditive_comp_difference_zero_path C
      (@abelian_stability_preadditive C P t A)
      (@computational_fiber_product_object C P t
        (@abelian_stability_additive C P t A) I X E iota epsilon
        (@abelian_selected_fiber_product C P t A I X E iota epsilon))
      I T u v
      (@computational_fiber_product_proj1 C P t
        (@abelian_stability_additive C P t A) I X E iota epsilon
        (@abelian_selected_fiber_product C P t A I X E iota epsilon)) p);

symbol abelian_fiber_projection_normal_epi_test
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [I X E T : τ (Obj C)]
  (iota : τ (Hom C I X))
  (epsilon : τ (Hom C E X))
  (u v : τ (Hom C I T))
  (p : τ (@= (Hom C
    (@computational_fiber_product_object C P t
      (@abelian_stability_additive C P t A) I X E iota epsilon
      (@abelian_selected_fiber_product C P t A I X E iota epsilon)) T)
    (@comp_fapp0 C
      (@computational_fiber_product_object C P t
        (@abelian_stability_additive C P t A) I X E iota epsilon
        (@abelian_selected_fiber_product C P t A I X E iota epsilon)) I T u
      (@computational_fiber_product_proj1 C P t
        (@abelian_stability_additive C P t A) I X E iota epsilon
        (@abelian_selected_fiber_product C P t A I X E iota epsilon)))
    (@comp_fapp0 C
      (@computational_fiber_product_object C P t
        (@abelian_stability_additive C P t A) I X E iota epsilon
        (@abelian_selected_fiber_product C P t A I X E iota epsilon)) I T v
      (@computational_fiber_product_proj1 C P t
        (@abelian_stability_additive C P t A) I X E iota epsilon
        (@abelian_selected_fiber_product C P t A I X E iota epsilon)))))
  : τ (@NormalEpiTest C
      (@abelian_stability_preadditive C P t A)
      (@weak_pullback_product_object C P t
        (@abelian_stability_additive C P t A) I E) X
      (@weak_pullback_difference_fapp0 C P t
        (@abelian_stability_additive C P t A) I X E iota epsilon)
      ((@abelian_stability_kernels C P t A)
        (@weak_pullback_product_object C P t
          (@abelian_stability_additive C P t A) I E) X
        (@weak_pullback_difference_fapp0 C P t
          (@abelian_stability_additive C P t A) I X E iota epsilon))
      T)
≔ @Struct_sigma
    (Hom C
      (@weak_pullback_product_object C P t
        (@abelian_stability_additive C P t A) I E) T)
    (λ h : τ (Hom C
      (@weak_pullback_product_object C P t
        (@abelian_stability_additive C P t A) I E) T),
      @= (Hom C
        (@computational_fiber_product_object C P t
          (@abelian_stability_additive C P t A) I X E iota epsilon
          (@abelian_selected_fiber_product C P t A I X E iota epsilon)) T)
        (@comp_fapp0 C
          (@computational_fiber_product_object C P t
            (@abelian_stability_additive C P t A) I X E iota epsilon
            (@abelian_selected_fiber_product C P t A I X E iota epsilon))
          (@weak_pullback_product_object C P t
            (@abelian_stability_additive C P t A) I E) T h
          (@computational_fiber_product_morphism C P t
            (@abelian_stability_additive C P t A) I X E iota epsilon
            (@abelian_selected_fiber_product C P t A I X E iota epsilon)))
        (@preadditive_hom_zero C
          (@abelian_stability_preadditive C P t A)
          (@computational_fiber_product_object C P t
            (@abelian_stability_additive C P t A) I X E iota epsilon
            (@abelian_selected_fiber_product C P t A I X E iota epsilon)) T))
    (@abelian_fiber_projection_extension_arrow C P t A I E T u v)
    (@abelian_fiber_projection_extension_zero_path C P t A
      I X E T iota epsilon u v p);

// Normality of the epic difference extends the annihilated arrow to X.
symbol abelian_fiber_projection_colift
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [I X E T : τ (Obj C)]
  (iota : τ (Hom C I X))
  (epsilon : τ (Hom C E X))
  (epsilon_epic : τ (@IsEpic C E X epsilon))
  (u v : τ (Hom C I T))
  (p : τ (@= (Hom C
    (@computational_fiber_product_object C P t
      (@abelian_stability_additive C P t A) I X E iota epsilon
      (@abelian_selected_fiber_product C P t A I X E iota epsilon)) T)
    (@comp_fapp0 C
      (@computational_fiber_product_object C P t
        (@abelian_stability_additive C P t A) I X E iota epsilon
        (@abelian_selected_fiber_product C P t A I X E iota epsilon)) I T u
      (@computational_fiber_product_proj1 C P t
        (@abelian_stability_additive C P t A) I X E iota epsilon
        (@abelian_selected_fiber_product C P t A I X E iota epsilon)))
    (@comp_fapp0 C
      (@computational_fiber_product_object C P t
        (@abelian_stability_additive C P t A) I X E iota epsilon
        (@abelian_selected_fiber_product C P t A I X E iota epsilon)) I T v
      (@computational_fiber_product_proj1 C P t
        (@abelian_stability_additive C P t A) I X E iota epsilon
        (@abelian_selected_fiber_product C P t A I X E iota epsilon)))))
  : τ (Hom C X T)
≔ @colift_along_epimorphism C
    (@abelian_stability_preadditive C P t A)
    (@abelian_stability_kernels C P t A)
    (@abelian_stability_epi_colifts C P t A)
    (@weak_pullback_product_object C P t
      (@abelian_stability_additive C P t A) I E) X
    (@weak_pullback_difference_fapp0 C P t
      (@abelian_stability_additive C P t A) I X E iota epsilon)
    (@abelian_fiber_product_difference_epic C P t A
      I X E iota epsilon epsilon_epic)
    T
    (@abelian_fiber_projection_normal_epi_test C P t A
      I X E T iota epsilon u v p);

symbol abelian_fiber_projection_colift_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [I X E T : τ (Obj C)]
  (iota : τ (Hom C I X))
  (epsilon : τ (Hom C E X))
  (epsilon_epic : τ (@IsEpic C E X epsilon))
  (u v : τ (Hom C I T))
  (p : τ (@= (Hom C
    (@computational_fiber_product_object C P t
      (@abelian_stability_additive C P t A) I X E iota epsilon
      (@abelian_selected_fiber_product C P t A I X E iota epsilon)) T)
    (@comp_fapp0 C
      (@computational_fiber_product_object C P t
        (@abelian_stability_additive C P t A) I X E iota epsilon
        (@abelian_selected_fiber_product C P t A I X E iota epsilon)) I T u
      (@computational_fiber_product_proj1 C P t
        (@abelian_stability_additive C P t A) I X E iota epsilon
        (@abelian_selected_fiber_product C P t A I X E iota epsilon)))
    (@comp_fapp0 C
      (@computational_fiber_product_object C P t
        (@abelian_stability_additive C P t A) I X E iota epsilon
        (@abelian_selected_fiber_product C P t A I X E iota epsilon)) I T v
      (@computational_fiber_product_proj1 C P t
        (@abelian_stability_additive C P t A) I X E iota epsilon
        (@abelian_selected_fiber_product C P t A I X E iota epsilon)))))
  : τ (@= (Hom C
      (@weak_pullback_product_object C P t
        (@abelian_stability_additive C P t A) I E) T)
      (@comp_fapp0 C
        (@weak_pullback_product_object C P t
          (@abelian_stability_additive C P t A) I E) X T
        (@abelian_fiber_projection_colift C P t A
          I X E T iota epsilon epsilon_epic u v p)
        (@weak_pullback_difference_fapp0 C P t
          (@abelian_stability_additive C P t A) I X E iota epsilon))
      (@abelian_fiber_projection_extension_arrow C P t A I E T u v))
≔ @colift_along_epimorphism_path C
    (@abelian_stability_preadditive C P t A)
    (@abelian_stability_kernels C P t A)
    (@abelian_stability_epi_colifts C P t A)
    (@weak_pullback_product_object C P t
      (@abelian_stability_additive C P t A) I E) X
    (@weak_pullback_difference_fapp0 C P t
      (@abelian_stability_additive C P t A) I X E iota epsilon)
    (@abelian_fiber_product_difference_epic C P t A
      I X E iota epsilon epsilon_epic)
    T
    (@abelian_fiber_projection_normal_epi_test C P t A
      I X E T iota epsilon u v p);

// The extended arrow vanishes on the second biproduct injection.
symbol abelian_fiber_projection_extension_inj2_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [I E T : τ (Obj C)]
  (u v : τ (Hom C I T))
  : τ (@= (Hom C E T)
      (@comp_fapp0 C E
        (@weak_pullback_product_object C P t
          (@abelian_stability_additive C P t A) I E) T
        (@abelian_fiber_projection_extension_arrow C P t A I E T u v)
        (@additive_inj2_fapp0 C P t
          (@abelian_stability_additive C P t A) I E))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t A) E T))
≔ @eq_trans (Hom C E T) _ _ _
    (@eq_sym _ _ _
      (@comp_assoc C E
        (@weak_pullback_product_object C P t
          (@abelian_stability_additive C P t A) I E) I T
        (@abelian_fiber_projection_difference_arrow C P t A I T u v)
        (@binary_products_proj1_fapp0 C P
          (@additive_binary_products C P t
            (@abelian_stability_additive C P t A)) I E)
        (@additive_inj2_fapp0 C P t
          (@abelian_stability_additive C P t A) I E)))
    (@preadditive_comp_zero_right_path C
      (@abelian_stability_preadditive C P t A) E I T
      (@abelian_fiber_projection_difference_arrow C P t A I T u v));

symbol AbelianFiberProjectionEquality
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [I X E T : τ (Obj C)]
  (iota : τ (Hom C I X))
  (epsilon : τ (Hom C E X))
  (u v : τ (Hom C I T))
  : Grpd
≔ @= (Hom C
    (@computational_fiber_product_object C P t
      (@abelian_stability_additive C P t A) I X E iota epsilon
      (@abelian_selected_fiber_product C P t A I X E iota epsilon)) T)
    (@comp_fapp0 C
      (@computational_fiber_product_object C P t
        (@abelian_stability_additive C P t A) I X E iota epsilon
        (@abelian_selected_fiber_product C P t A I X E iota epsilon)) I T u
      (@computational_fiber_product_proj1 C P t
        (@abelian_stability_additive C P t A) I X E iota epsilon
        (@abelian_selected_fiber_product C P t A I X E iota epsilon)))
    (@comp_fapp0 C
      (@computational_fiber_product_object C P t
        (@abelian_stability_additive C P t A) I X E iota epsilon
        (@abelian_selected_fiber_product C P t A I X E iota epsilon)) I T v
      (@computational_fiber_product_proj1 C P t
        (@abelian_stability_additive C P t A) I X E iota epsilon
        (@abelian_selected_fiber_product C P t A I X E iota epsilon)));

// The normal colift vanishes after the original epic epsilon.
symbol abelian_fiber_projection_colift_neg_epsilon_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [I X E T : τ (Obj C)]
  (iota : τ (Hom C I X))
  (epsilon : τ (Hom C E X))
  (epsilon_epic : τ (@IsEpic C E X epsilon))
  (u v : τ (Hom C I T))
  (p : τ (@AbelianFiberProjectionEquality C P t A
    I X E T iota epsilon u v))
  : τ (@= (Hom C E T)
      (@comp_fapp0 C E X T
        (@abelian_fiber_projection_colift C P t A
          I X E T iota epsilon epsilon_epic u v p)
        (@preadditive_hom_neg C
          (@abelian_stability_preadditive C P t A) E X epsilon))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t A) E T))
≔ @eq_trans (Hom C E T) _ _ _
    (@eq_sym _ _ _
      (@additive_postcomp_copair_inj2_path C P t
        (@abelian_stability_additive C P t A)
        I E X T iota
        (@preadditive_hom_neg C
          (@abelian_stability_preadditive C P t A) E X epsilon)
        (@abelian_fiber_projection_colift C P t A
          I X E T iota epsilon epsilon_epic u v p)))
    (@eq_trans (Hom C E T) _ _ _
      (@eq_ap
        (Hom C
          (@weak_pullback_product_object C P t
            (@abelian_stability_additive C P t A) I E) T)
        (Hom C E T)
        (λ h : τ (Hom C
          (@weak_pullback_product_object C P t
            (@abelian_stability_additive C P t A) I E) T),
          @comp_fapp0 C E
            (@weak_pullback_product_object C P t
              (@abelian_stability_additive C P t A) I E) T h
            (@additive_inj2_fapp0 C P t
              (@abelian_stability_additive C P t A) I E))
        _ _
        (@abelian_fiber_projection_colift_path C P t A
          I X E T iota epsilon epsilon_epic u v p))
      (@abelian_fiber_projection_extension_inj2_zero_path C P t A
        I E T u v));

symbol abelian_fiber_projection_colift_epsilon_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [I X E T : τ (Obj C)]
  (iota : τ (Hom C I X))
  (epsilon : τ (Hom C E X))
  (epsilon_epic : τ (@IsEpic C E X epsilon))
  (u v : τ (Hom C I T))
  (p : τ (@AbelianFiberProjectionEquality C P t A
    I X E T iota epsilon u v))
  : τ (@= (Hom C E T)
      (@comp_fapp0 C E X T
        (@abelian_fiber_projection_colift C P t A
          I X E T iota epsilon epsilon_epic u v p) epsilon)
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t A) E T))
≔ @abelian_group_neg_cancel_path
    (Hom C E T)
    (@preadditive_hom_structure C
      (@abelian_stability_preadditive C P t A) E T)
    (@comp_fapp0 C E X T
      (@abelian_fiber_projection_colift C P t A
        I X E T iota epsilon epsilon_epic u v p) epsilon)
    (@preadditive_hom_zero C
      (@abelian_stability_preadditive C P t A) E T)
    (@eq_trans (Hom C E T) _ _ _
      (@eq_sym _ _ _
        (@preadditive_comp_neg_right_path C
          (@abelian_stability_preadditive C P t A) E X T
          (@abelian_fiber_projection_colift C P t A
            I X E T iota epsilon epsilon_epic u v p) epsilon))
      (@eq_trans (Hom C E T) _ _ _
        (@abelian_fiber_projection_colift_neg_epsilon_zero_path C P t A
          I X E T iota epsilon epsilon_epic u v p)
        (@eq_sym _ _ _
          (@abelian_group_neg_zero_path
            (Hom C E T)
            (@preadditive_hom_structure C
              (@abelian_stability_preadditive C P t A) E T)))));

symbol abelian_fiber_projection_colift_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [I X E T : τ (Obj C)]
  (iota : τ (Hom C I X))
  (epsilon : τ (Hom C E X))
  (epsilon_epic : τ (@IsEpic C E X epsilon))
  (u v : τ (Hom C I T))
  (p : τ (@AbelianFiberProjectionEquality C P t A
    I X E T iota epsilon u v))
  : τ (@= (Hom C X T)
      (@abelian_fiber_projection_colift C P t A
        I X E T iota epsilon epsilon_epic u v p)
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t A) X T))
≔ epsilon_epic T
    (@abelian_fiber_projection_colift C P t A
      I X E T iota epsilon epsilon_epic u v p)
    (@preadditive_hom_zero C
      (@abelian_stability_preadditive C P t A) X T)
    (@eq_trans (Hom C E T) _ _ _
      (@abelian_fiber_projection_colift_epsilon_zero_path C P t A
        I X E T iota epsilon epsilon_epic u v p)
      (@eq_sym _ _ _
        (@preadditive_comp_zero_left_path C
          (@abelian_stability_preadditive C P t A) E X T epsilon)));

symbol abelian_fiber_projection_extension_zero_arrow_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [I X E T : τ (Obj C)]
  (iota : τ (Hom C I X))
  (epsilon : τ (Hom C E X))
  (epsilon_epic : τ (@IsEpic C E X epsilon))
  (u v : τ (Hom C I T))
  (p : τ (@AbelianFiberProjectionEquality C P t A
    I X E T iota epsilon u v))
  : τ (@= (Hom C
      (@weak_pullback_product_object C P t
        (@abelian_stability_additive C P t A) I E) T)
      (@abelian_fiber_projection_extension_arrow C P t A I E T u v)
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t A)
        (@weak_pullback_product_object C P t
          (@abelian_stability_additive C P t A) I E) T))
≔ @eq_trans _ _ _ _
    (@eq_sym _ _ _
      (@abelian_fiber_projection_colift_path C P t A
        I X E T iota epsilon epsilon_epic u v p))
    (@eq_trans _ _ _ _
      (@eq_ap (Hom C X T)
        (Hom C
          (@weak_pullback_product_object C P t
            (@abelian_stability_additive C P t A) I E) T)
        (λ h : τ (Hom C X T),
          @comp_fapp0 C
            (@weak_pullback_product_object C P t
              (@abelian_stability_additive C P t A) I E) X T h
            (@weak_pullback_difference_fapp0 C P t
              (@abelian_stability_additive C P t A)
              I X E iota epsilon))
        _ _
        (@abelian_fiber_projection_colift_zero_path C P t A
          I X E T iota epsilon epsilon_epic u v p))
      (@preadditive_comp_zero_left_path C
        (@abelian_stability_preadditive C P t A)
        (@weak_pullback_product_object C P t
          (@abelian_stability_additive C P t A) I E) X T
        (@weak_pullback_difference_fapp0 C P t
          (@abelian_stability_additive C P t A)
          I X E iota epsilon)));

// The extended difference reads back as the original difference on iota_1.
symbol abelian_fiber_projection_extension_inj1_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [I E T : τ (Obj C)]
  (u v : τ (Hom C I T))
  : τ (@= (Hom C I T)
      (@comp_fapp0 C I
        (@weak_pullback_product_object C P t
          (@abelian_stability_additive C P t A) I E) T
        (@abelian_fiber_projection_extension_arrow C P t A I E T u v)
        (@additive_inj1_fapp0 C P t
          (@abelian_stability_additive C P t A) I E))
      (@abelian_fiber_projection_difference_arrow C P t A I T u v))
≔ @eq_trans (Hom C I T) _ _ _
    (@eq_sym _ _ _
      (@comp_assoc C I
        (@weak_pullback_product_object C P t
          (@abelian_stability_additive C P t A) I E) I T
        (@abelian_fiber_projection_difference_arrow C P t A I T u v)
        (@binary_products_proj1_fapp0 C P
          (@additive_binary_products C P t
            (@abelian_stability_additive C P t A)) I E)
        (@additive_inj1_fapp0 C P t
          (@abelian_stability_additive C P t A) I E)))
    (@eq_refl (Hom C I T)
      (@abelian_fiber_projection_difference_arrow C P t A I T u v));

symbol abelian_fiber_projection_difference_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [I X E T : τ (Obj C)]
  (iota : τ (Hom C I X))
  (epsilon : τ (Hom C E X))
  (epsilon_epic : τ (@IsEpic C E X epsilon))
  (u v : τ (Hom C I T))
  (p : τ (@AbelianFiberProjectionEquality C P t A
    I X E T iota epsilon u v))
  : τ (@= (Hom C I T)
      (@abelian_fiber_projection_difference_arrow C P t A I T u v)
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t A) I T))
≔ @eq_trans (Hom C I T) _ _ _
    (@eq_sym _ _ _
      (@abelian_fiber_projection_extension_inj1_path C P t A I E T u v))
    (@eq_trans (Hom C I T) _ _ _
      (@eq_ap
        (Hom C
          (@weak_pullback_product_object C P t
            (@abelian_stability_additive C P t A) I E) T)
        (Hom C I T)
        (λ h : τ (Hom C
          (@weak_pullback_product_object C P t
            (@abelian_stability_additive C P t A) I E) T),
          @comp_fapp0 C I
            (@weak_pullback_product_object C P t
              (@abelian_stability_additive C P t A) I E) T h
            (@additive_inj1_fapp0 C P t
              (@abelian_stability_additive C P t A) I E))
        _ _
        (@abelian_fiber_projection_extension_zero_arrow_path C P t A
          I X E T iota epsilon epsilon_epic u v p))
      (@preadditive_comp_zero_left_path C
        (@abelian_stability_preadditive C P t A)
        I
        (@weak_pullback_product_object C P t
          (@abelian_stability_additive C P t A) I E) T
        (@additive_inj1_fapp0 C P t
          (@abelian_stability_additive C P t A) I E)));

// Pullback stability: the selected projection opposite an epic arrow is epic.
symbol abelian_fiber_product_epic_projection
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [I X E : τ (Obj C)]
  (iota : τ (Hom C I X))
  (epsilon : τ (Hom C E X))
  (epsilon_epic : τ (@IsEpic C E X epsilon))
  : τ (@IsEpic C
      (@computational_fiber_product_object C P t
        (@abelian_stability_additive C P t A) I X E iota epsilon
        (@abelian_selected_fiber_product C P t A I X E iota epsilon)) I
      (@computational_fiber_product_proj1 C P t
        (@abelian_stability_additive C P t A) I X E iota epsilon
        (@abelian_selected_fiber_product C P t A I X E iota epsilon)))
≔ λ T : τ (Obj C), λ u : τ (Hom C I T), λ v : τ (Hom C I T),
    λ p : τ (@AbelianFiberProjectionEquality C P t A
      I X E T iota epsilon u v),
      @abelian_group_sub_zero_to_eq_path
        (Hom C I T)
        (@preadditive_hom_structure C
          (@abelian_stability_preadditive C P t A) I T)
        u v
        (@abelian_fiber_projection_difference_zero_path C P t A
          I X E T iota epsilon epsilon_epic u v p);

// First projection of the pushout difference is its monic first leg.
symbol abelian_pushout_difference_proj1_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [K X Q : τ (Obj C)]
  (mu : τ (Hom C K X))
  (pi : τ (Hom C K Q))
  : τ (@= (Hom C K X)
      (@comp_fapp0 C K
        (@pushout_product_object C P t
          (@abelian_stability_additive C P t A) X Q) X
        (@binary_products_proj1_fapp0 C P
          (@additive_binary_products C P t
            (@abelian_stability_additive C P t A)) X Q)
        (@pushout_difference_fapp0 C P t
          (@abelian_stability_additive C P t A) X K Q mu pi))
      mu)
≔ @eq_trans (Hom C K X) _ _ _
    ((@preadditive_comp_add_right_law C
      (@abelian_stability_preadditive C P t A))
      K
      (@pushout_product_object C P t
        (@abelian_stability_additive C P t A) X Q) X
      (@binary_products_proj1_fapp0 C P
        (@additive_binary_products C P t
          (@abelian_stability_additive C P t A)) X Q)
      (@comp_fapp0 C K X
        (@pushout_product_object C P t
          (@abelian_stability_additive C P t A) X Q)
        (@additive_inj1_fapp0 C P t
          (@abelian_stability_additive C P t A) X Q) mu)
      (@comp_fapp0 C K Q
        (@pushout_product_object C P t
          (@abelian_stability_additive C P t A) X Q)
        (@additive_inj2_fapp0 C P t
          (@abelian_stability_additive C P t A) X Q)
        (@preadditive_hom_neg C
          (@abelian_stability_preadditive C P t A) K Q pi)))
    (@eq_trans (Hom C K X) _ _ _
      (@additive_add_congr_path C P t
        (@abelian_stability_additive C P t A) K X _ _ _ _
        (@eq_trans (Hom C K X) _ _ _
          (@comp_assoc C K X
            (@pushout_product_object C P t
              (@abelian_stability_additive C P t A) X Q) X
            (@binary_products_proj1_fapp0 C P
              (@additive_binary_products C P t
                (@abelian_stability_additive C P t A)) X Q)
            (@additive_inj1_fapp0 C P t
              (@abelian_stability_additive C P t A) X Q) mu)
          (@eq_refl (Hom C K X) mu))
        (@eq_trans (Hom C K X) _ _ _
          (@comp_assoc C K Q
            (@pushout_product_object C P t
              (@abelian_stability_additive C P t A) X Q) X
            (@binary_products_proj1_fapp0 C P
              (@additive_binary_products C P t
                (@abelian_stability_additive C P t A)) X Q)
            (@additive_inj2_fapp0 C P t
              (@abelian_stability_additive C P t A) X Q)
            (@preadditive_hom_neg C
              (@abelian_stability_preadditive C P t A) K Q pi))
          (@preadditive_comp_zero_left_path C
            (@abelian_stability_preadditive C P t A) K Q X
            (@preadditive_hom_neg C
              (@abelian_stability_preadditive C P t A) K Q pi))))
      ((@abelian_group_add_zero_law (Hom C K X)
        (@preadditive_hom_structure C
          (@abelian_stability_preadditive C P t A) K X)) mu));

symbol abelian_pushout_difference_precomp_proj1_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [T K X Q : τ (Obj C)]
  (h : τ (Hom C T K))
  (mu : τ (Hom C K X))
  (pi : τ (Hom C K Q))
  : τ (@= (Hom C T X)
      (@comp_fapp0 C T
        (@pushout_product_object C P t
          (@abelian_stability_additive C P t A) X Q) X
        (@binary_products_proj1_fapp0 C P
          (@additive_binary_products C P t
            (@abelian_stability_additive C P t A)) X Q)
        (@comp_fapp0 C T K
          (@pushout_product_object C P t
            (@abelian_stability_additive C P t A) X Q)
          (@pushout_difference_fapp0 C P t
            (@abelian_stability_additive C P t A) X K Q mu pi) h))
      (@comp_fapp0 C T K X mu h))
≔ @eq_trans (Hom C T X) _ _ _
    (@comp_assoc C T K
      (@pushout_product_object C P t
        (@abelian_stability_additive C P t A) X Q) X
      (@binary_products_proj1_fapp0 C P
        (@additive_binary_products C P t
          (@abelian_stability_additive C P t A)) X Q)
      (@pushout_difference_fapp0 C P t
        (@abelian_stability_additive C P t A) X K Q mu pi) h)
    (@eq_ap (Hom C K X) (Hom C T X)
      (λ q : τ (Hom C K X), @comp_fapp0 C T K X q h)
      _ mu
      (@abelian_pushout_difference_proj1_path C P t A K X Q mu pi));

// The defining pushout difference is monic when mu is monic.
symbol abelian_pushout_difference_monic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [K X Q : τ (Obj C)]
  (mu : τ (Hom C K X))
  (pi : τ (Hom C K Q))
  (monic : τ (@IsMonic C K X mu))
  : τ (@IsMonic C K
      (@pushout_product_object C P t
        (@abelian_stability_additive C P t A) X Q)
      (@pushout_difference_fapp0 C P t
        (@abelian_stability_additive C P t A) X K Q mu pi))
≔ λ T : τ (Obj C), λ u : τ (Hom C T K), λ v : τ (Hom C T K),
    λ p : τ (@= (Hom C T
      (@pushout_product_object C P t
        (@abelian_stability_additive C P t A) X Q))
      (@comp_fapp0 C T K
        (@pushout_product_object C P t
          (@abelian_stability_additive C P t A) X Q)
        (@pushout_difference_fapp0 C P t
          (@abelian_stability_additive C P t A) X K Q mu pi) u)
      (@comp_fapp0 C T K
        (@pushout_product_object C P t
          (@abelian_stability_additive C P t A) X Q)
        (@pushout_difference_fapp0 C P t
          (@abelian_stability_additive C P t A) X K Q mu pi) v)),
      monic T u v
        (@eq_trans (Hom C T X)
          (@comp_fapp0 C T K X mu u)
          (@comp_fapp0 C T
            (@pushout_product_object C P t
              (@abelian_stability_additive C P t A) X Q) X
            (@binary_products_proj1_fapp0 C P
              (@additive_binary_products C P t
                (@abelian_stability_additive C P t A)) X Q)
            (@comp_fapp0 C T K
              (@pushout_product_object C P t
                (@abelian_stability_additive C P t A) X Q)
              (@pushout_difference_fapp0 C P t
                (@abelian_stability_additive C P t A) X K Q mu pi) u))
          (@comp_fapp0 C T K X mu v)
          (@eq_sym _ _ _
            (@abelian_pushout_difference_precomp_proj1_path C P t A
              T K X Q u mu pi))
          (@eq_trans (Hom C T X) _ _ _
            (@eq_ap
              (Hom C T
                (@pushout_product_object C P t
                  (@abelian_stability_additive C P t A) X Q))
              (Hom C T X)
              (λ q : τ (Hom C T
                (@pushout_product_object C P t
                  (@abelian_stability_additive C P t A) X Q)),
                @comp_fapp0 C T
                  (@pushout_product_object C P t
                    (@abelian_stability_additive C P t A) X Q) X
                  (@binary_products_proj1_fapp0 C P
                    (@additive_binary_products C P t
                      (@abelian_stability_additive C P t A)) X Q) q)
              _ _ p)
            (@abelian_pushout_difference_precomp_proj1_path C P t A
              T K X Q v mu pi)));

symbol AbelianPushoutInjectionEquality
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [K X Q T : τ (Obj C)]
  (mu : τ (Hom C K X))
  (pi : τ (Hom C K Q))
  (u v : τ (Hom C T Q))
  : Grpd
≔ @= (Hom C T
    (@computational_pushout_object C P t
      (@abelian_stability_additive C P t A) X K Q mu pi
      (@abelian_selected_pushout C P t A K X Q mu pi)))
    (@comp_fapp0 C T Q
      (@computational_pushout_object C P t
        (@abelian_stability_additive C P t A) X K Q mu pi
        (@abelian_selected_pushout C P t A K X Q mu pi))
      (@computational_pushout_inj2 C P t
        (@abelian_stability_additive C P t A) X K Q mu pi
        (@abelian_selected_pushout C P t A K X Q mu pi)) u)
    (@comp_fapp0 C T Q
      (@computational_pushout_object C P t
        (@abelian_stability_additive C P t A) X K Q mu pi
        (@abelian_selected_pushout C P t A K X Q mu pi))
      (@computational_pushout_inj2 C P t
        (@abelian_stability_additive C P t A) X K Q mu pi
        (@abelian_selected_pushout C P t A K X Q mu pi)) v);

symbol abelian_pushout_injection_difference_arrow
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [T Q : τ (Obj C)]
  (u v : τ (Hom C T Q))
  : τ (Hom C T Q)
≔ @preadditive_hom_add C (@abelian_stability_preadditive C P t A) T Q
    u (@preadditive_hom_neg C
      (@abelian_stability_preadditive C P t A) T Q v);

// Extend the difference into the second biproduct injection.
symbol abelian_pushout_injection_extension_arrow
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [T X Q : τ (Obj C)]
  (u v : τ (Hom C T Q))
  : τ (Hom C T
      (@pushout_product_object C P t
        (@abelian_stability_additive C P t A) X Q))
≔ @comp_fapp0 C T Q
    (@pushout_product_object C P t
      (@abelian_stability_additive C P t A) X Q)
    (@additive_inj2_fapp0 C P t
      (@abelian_stability_additive C P t A) X Q)
    (@abelian_pushout_injection_difference_arrow C P t A T Q u v);

// Equality after j2 makes that extension vanish after the selected cokernel.
symbol abelian_pushout_injection_extension_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [K X Q T : τ (Obj C)]
  (mu : τ (Hom C K X))
  (pi : τ (Hom C K Q))
  (u v : τ (Hom C T Q))
  (p : τ (@AbelianPushoutInjectionEquality C P t A
    K X Q T mu pi u v))
  : τ (@= (Hom C T
      (@computational_pushout_object C P t
        (@abelian_stability_additive C P t A) X K Q mu pi
        (@abelian_selected_pushout C P t A K X Q mu pi)))
      (@comp_fapp0 C T
        (@pushout_product_object C P t
          (@abelian_stability_additive C P t A) X Q)
        (@computational_pushout_object C P t
          (@abelian_stability_additive C P t A) X K Q mu pi
          (@abelian_selected_pushout C P t A K X Q mu pi))
        (@computational_pushout_morphism C P t
          (@abelian_stability_additive C P t A) X K Q mu pi
          (@abelian_selected_pushout C P t A K X Q mu pi))
        (@abelian_pushout_injection_extension_arrow C P t A T X Q u v))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t A) T
        (@computational_pushout_object C P t
          (@abelian_stability_additive C P t A) X K Q mu pi
          (@abelian_selected_pushout C P t A K X Q mu pi))))
≔ @eq_trans _ _ _ _
    (@comp_assoc C T Q
      (@pushout_product_object C P t
        (@abelian_stability_additive C P t A) X Q)
      (@computational_pushout_object C P t
        (@abelian_stability_additive C P t A) X K Q mu pi
        (@abelian_selected_pushout C P t A K X Q mu pi))
      (@computational_pushout_morphism C P t
        (@abelian_stability_additive C P t A) X K Q mu pi
        (@abelian_selected_pushout C P t A K X Q mu pi))
      (@additive_inj2_fapp0 C P t
        (@abelian_stability_additive C P t A) X Q)
      (@abelian_pushout_injection_difference_arrow C P t A T Q u v))
    (@preadditive_difference_postcomp_zero_path C
      (@abelian_stability_preadditive C P t A)
      T Q
      (@computational_pushout_object C P t
        (@abelian_stability_additive C P t A) X K Q mu pi
        (@abelian_selected_pushout C P t A K X Q mu pi))
      (@computational_pushout_inj2 C P t
        (@abelian_stability_additive C P t A) X K Q mu pi
        (@abelian_selected_pushout C P t A K X Q mu pi))
      u v p);

symbol abelian_pushout_injection_normal_mono_test
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [K X Q T : τ (Obj C)]
  (mu : τ (Hom C K X))
  (pi : τ (Hom C K Q))
  (u v : τ (Hom C T Q))
  (p : τ (@AbelianPushoutInjectionEquality C P t A
    K X Q T mu pi u v))
  : τ (@NormalMonoTest C
      (@abelian_stability_preadditive C P t A)
      K
      (@pushout_product_object C P t
        (@abelian_stability_additive C P t A) X Q)
      (@pushout_difference_fapp0 C P t
        (@abelian_stability_additive C P t A) X K Q mu pi)
      ((@abelian_stability_cokernels C P t A) K
        (@pushout_product_object C P t
          (@abelian_stability_additive C P t A) X Q)
        (@pushout_difference_fapp0 C P t
          (@abelian_stability_additive C P t A) X K Q mu pi))
      T)
≔ @Struct_sigma
    (Hom C T
      (@pushout_product_object C P t
        (@abelian_stability_additive C P t A) X Q))
    (λ h : τ (Hom C T
      (@pushout_product_object C P t
        (@abelian_stability_additive C P t A) X Q)),
      @= (Hom C T
        (@computational_pushout_object C P t
          (@abelian_stability_additive C P t A) X K Q mu pi
          (@abelian_selected_pushout C P t A K X Q mu pi)))
        (@comp_fapp0 C T
          (@pushout_product_object C P t
            (@abelian_stability_additive C P t A) X Q)
          (@computational_pushout_object C P t
            (@abelian_stability_additive C P t A) X K Q mu pi
            (@abelian_selected_pushout C P t A K X Q mu pi))
          (@computational_pushout_morphism C P t
            (@abelian_stability_additive C P t A) X K Q mu pi
            (@abelian_selected_pushout C P t A K X Q mu pi)) h)
        (@preadditive_hom_zero C
          (@abelian_stability_preadditive C P t A) T
          (@computational_pushout_object C P t
            (@abelian_stability_additive C P t A) X K Q mu pi
            (@abelian_selected_pushout C P t A K X Q mu pi))))
    (@abelian_pushout_injection_extension_arrow C P t A T X Q u v)
    (@abelian_pushout_injection_extension_zero_path C P t A
      K X Q T mu pi u v p);

// Normality of the monic difference lifts the extension back to K.
symbol abelian_pushout_injection_lift
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [K X Q T : τ (Obj C)]
  (mu : τ (Hom C K X))
  (pi : τ (Hom C K Q))
  (mu_monic : τ (@IsMonic C K X mu))
  (u v : τ (Hom C T Q))
  (p : τ (@AbelianPushoutInjectionEquality C P t A
    K X Q T mu pi u v))
  : τ (Hom C T K)
≔ @lift_along_monomorphism C
    (@abelian_stability_preadditive C P t A)
    (@abelian_stability_cokernels C P t A)
    (@abelian_stability_mono_lifts C P t A)
    K
    (@pushout_product_object C P t
      (@abelian_stability_additive C P t A) X Q)
    (@pushout_difference_fapp0 C P t
      (@abelian_stability_additive C P t A) X K Q mu pi)
    (@abelian_pushout_difference_monic C P t A K X Q mu pi mu_monic)
    T
    (@abelian_pushout_injection_normal_mono_test C P t A
      K X Q T mu pi u v p);

symbol abelian_pushout_injection_lift_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [K X Q T : τ (Obj C)]
  (mu : τ (Hom C K X))
  (pi : τ (Hom C K Q))
  (mu_monic : τ (@IsMonic C K X mu))
  (u v : τ (Hom C T Q))
  (p : τ (@AbelianPushoutInjectionEquality C P t A
    K X Q T mu pi u v))
  : τ (@= (Hom C T
      (@pushout_product_object C P t
        (@abelian_stability_additive C P t A) X Q))
      (@comp_fapp0 C T K
        (@pushout_product_object C P t
          (@abelian_stability_additive C P t A) X Q)
        (@pushout_difference_fapp0 C P t
          (@abelian_stability_additive C P t A) X K Q mu pi)
        (@abelian_pushout_injection_lift C P t A
          K X Q T mu pi mu_monic u v p))
      (@abelian_pushout_injection_extension_arrow C P t A T X Q u v))
≔ @lift_along_monomorphism_path C
    (@abelian_stability_preadditive C P t A)
    (@abelian_stability_cokernels C P t A)
    (@abelian_stability_mono_lifts C P t A)
    K
    (@pushout_product_object C P t
      (@abelian_stability_additive C P t A) X Q)
    (@pushout_difference_fapp0 C P t
      (@abelian_stability_additive C P t A) X K Q mu pi)
    (@abelian_pushout_difference_monic C P t A K X Q mu pi mu_monic)
    T
    (@abelian_pushout_injection_normal_mono_test C P t A
      K X Q T mu pi u v p);

symbol abelian_pushout_injection_extension_proj1_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [T X Q : τ (Obj C)]
  (u v : τ (Hom C T Q))
  : τ (@= (Hom C T X)
      (@comp_fapp0 C T
        (@pushout_product_object C P t
          (@abelian_stability_additive C P t A) X Q) X
        (@binary_products_proj1_fapp0 C P
          (@additive_binary_products C P t
            (@abelian_stability_additive C P t A)) X Q)
        (@abelian_pushout_injection_extension_arrow C P t A T X Q u v))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t A) T X))
≔ @eq_trans (Hom C T X) _ _ _
    (@comp_assoc C T Q
      (@pushout_product_object C P t
        (@abelian_stability_additive C P t A) X Q) X
      (@binary_products_proj1_fapp0 C P
        (@additive_binary_products C P t
          (@abelian_stability_additive C P t A)) X Q)
      (@additive_inj2_fapp0 C P t
        (@abelian_stability_additive C P t A) X Q)
      (@abelian_pushout_injection_difference_arrow C P t A T Q u v))
    (@preadditive_comp_zero_left_path C
      (@abelian_stability_preadditive C P t A) T Q X
      (@abelian_pushout_injection_difference_arrow C P t A T Q u v));

symbol abelian_pushout_injection_lift_mu_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [K X Q T : τ (Obj C)]
  (mu : τ (Hom C K X))
  (pi : τ (Hom C K Q))
  (mu_monic : τ (@IsMonic C K X mu))
  (u v : τ (Hom C T Q))
  (p : τ (@AbelianPushoutInjectionEquality C P t A
    K X Q T mu pi u v))
  : τ (@= (Hom C T X)
      (@comp_fapp0 C T K X mu
        (@abelian_pushout_injection_lift C P t A
          K X Q T mu pi mu_monic u v p))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t A) T X))
≔ @eq_trans (Hom C T X) _ _ _
    (@eq_sym _ _ _
      (@abelian_pushout_difference_precomp_proj1_path C P t A
        T K X Q
        (@abelian_pushout_injection_lift C P t A
          K X Q T mu pi mu_monic u v p) mu pi))
    (@eq_trans (Hom C T X) _ _ _
      (@eq_ap
        (Hom C T
          (@pushout_product_object C P t
            (@abelian_stability_additive C P t A) X Q))
        (Hom C T X)
        (λ h : τ (Hom C T
          (@pushout_product_object C P t
            (@abelian_stability_additive C P t A) X Q)),
          @comp_fapp0 C T
            (@pushout_product_object C P t
              (@abelian_stability_additive C P t A) X Q) X
            (@binary_products_proj1_fapp0 C P
              (@additive_binary_products C P t
                (@abelian_stability_additive C P t A)) X Q) h)
        _ _
        (@abelian_pushout_injection_lift_path C P t A
          K X Q T mu pi mu_monic u v p))
      (@abelian_pushout_injection_extension_proj1_zero_path C P t A
        T X Q u v));

symbol abelian_pushout_injection_lift_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [K X Q T : τ (Obj C)]
  (mu : τ (Hom C K X))
  (pi : τ (Hom C K Q))
  (mu_monic : τ (@IsMonic C K X mu))
  (u v : τ (Hom C T Q))
  (p : τ (@AbelianPushoutInjectionEquality C P t A
    K X Q T mu pi u v))
  : τ (@= (Hom C T K)
      (@abelian_pushout_injection_lift C P t A
        K X Q T mu pi mu_monic u v p)
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t A) T K))
≔ mu_monic T
    (@abelian_pushout_injection_lift C P t A
      K X Q T mu pi mu_monic u v p)
    (@preadditive_hom_zero C
      (@abelian_stability_preadditive C P t A) T K)
    (@eq_trans (Hom C T X) _ _ _
      (@abelian_pushout_injection_lift_mu_zero_path C P t A
        K X Q T mu pi mu_monic u v p)
      (@eq_sym _ _ _
        (@preadditive_comp_zero_right_path C
          (@abelian_stability_preadditive C P t A) T K X mu)));

symbol abelian_pushout_injection_extension_zero_arrow_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [K X Q T : τ (Obj C)]
  (mu : τ (Hom C K X))
  (pi : τ (Hom C K Q))
  (mu_monic : τ (@IsMonic C K X mu))
  (u v : τ (Hom C T Q))
  (p : τ (@AbelianPushoutInjectionEquality C P t A
    K X Q T mu pi u v))
  : τ (@= (Hom C T
      (@pushout_product_object C P t
        (@abelian_stability_additive C P t A) X Q))
      (@abelian_pushout_injection_extension_arrow C P t A T X Q u v)
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t A) T
        (@pushout_product_object C P t
          (@abelian_stability_additive C P t A) X Q)))
≔ @eq_trans _ _ _ _
    (@eq_sym _ _ _
      (@abelian_pushout_injection_lift_path C P t A
        K X Q T mu pi mu_monic u v p))
    (@eq_trans _ _ _ _
      (@eq_ap (Hom C T K)
        (Hom C T
          (@pushout_product_object C P t
            (@abelian_stability_additive C P t A) X Q))
        (λ h : τ (Hom C T K),
          @comp_fapp0 C T K
            (@pushout_product_object C P t
              (@abelian_stability_additive C P t A) X Q)
            (@pushout_difference_fapp0 C P t
              (@abelian_stability_additive C P t A) X K Q mu pi) h)
        _ _
        (@abelian_pushout_injection_lift_zero_path C P t A
          K X Q T mu pi mu_monic u v p))
      (@preadditive_comp_zero_right_path C
        (@abelian_stability_preadditive C P t A) T K
        (@pushout_product_object C P t
          (@abelian_stability_additive C P t A) X Q)
        (@pushout_difference_fapp0 C P t
          (@abelian_stability_additive C P t A) X K Q mu pi)));

// The second projection of the extension is the original difference.
symbol abelian_pushout_injection_extension_proj2_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [T X Q : τ (Obj C)]
  (u v : τ (Hom C T Q))
  : τ (@= (Hom C T Q)
      (@comp_fapp0 C T
        (@pushout_product_object C P t
          (@abelian_stability_additive C P t A) X Q) Q
        (@binary_products_proj2_fapp0 C P
          (@additive_binary_products C P t
            (@abelian_stability_additive C P t A)) X Q)
        (@abelian_pushout_injection_extension_arrow C P t A T X Q u v))
      (@abelian_pushout_injection_difference_arrow C P t A T Q u v))
≔ @eq_trans (Hom C T Q) _ _ _
    (@comp_assoc C T Q
      (@pushout_product_object C P t
        (@abelian_stability_additive C P t A) X Q) Q
      (@binary_products_proj2_fapp0 C P
        (@additive_binary_products C P t
          (@abelian_stability_additive C P t A)) X Q)
      (@additive_inj2_fapp0 C P t
        (@abelian_stability_additive C P t A) X Q)
      (@abelian_pushout_injection_difference_arrow C P t A T Q u v))
    (@eq_refl (Hom C T Q)
      (@abelian_pushout_injection_difference_arrow C P t A T Q u v));

symbol abelian_pushout_injection_difference_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [K X Q T : τ (Obj C)]
  (mu : τ (Hom C K X))
  (pi : τ (Hom C K Q))
  (mu_monic : τ (@IsMonic C K X mu))
  (u v : τ (Hom C T Q))
  (p : τ (@AbelianPushoutInjectionEquality C P t A
    K X Q T mu pi u v))
  : τ (@= (Hom C T Q)
      (@abelian_pushout_injection_difference_arrow C P t A T Q u v)
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t A) T Q))
≔ @eq_trans (Hom C T Q) _ _ _
    (@eq_sym _ _ _
      (@abelian_pushout_injection_extension_proj2_path C P t A T X Q u v))
    (@eq_trans (Hom C T Q) _ _ _
      (@eq_ap
        (Hom C T
          (@pushout_product_object C P t
            (@abelian_stability_additive C P t A) X Q))
        (Hom C T Q)
        (λ h : τ (Hom C T
          (@pushout_product_object C P t
            (@abelian_stability_additive C P t A) X Q)),
          @comp_fapp0 C T
            (@pushout_product_object C P t
              (@abelian_stability_additive C P t A) X Q) Q
            (@binary_products_proj2_fapp0 C P
              (@additive_binary_products C P t
                (@abelian_stability_additive C P t A)) X Q) h)
        _ _
        (@abelian_pushout_injection_extension_zero_arrow_path C P t A
          K X Q T mu pi mu_monic u v p))
      (@preadditive_comp_zero_right_path C
        (@abelian_stability_preadditive C P t A) T
        (@pushout_product_object C P t
          (@abelian_stability_additive C P t A) X Q) Q
        (@binary_products_proj2_fapp0 C P
          (@additive_binary_products C P t
            (@abelian_stability_additive C P t A)) X Q)));

// Pushout stability: the selected injection opposite a monic arrow is monic.
symbol abelian_pushout_monic_injection
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  [K X Q : τ (Obj C)]
  (mu : τ (Hom C K X))
  (pi : τ (Hom C K Q))
  (mu_monic : τ (@IsMonic C K X mu))
  : τ (@IsMonic C Q
      (@computational_pushout_object C P t
        (@abelian_stability_additive C P t A) X K Q mu pi
        (@abelian_selected_pushout C P t A K X Q mu pi))
      (@computational_pushout_inj2 C P t
        (@abelian_stability_additive C P t A) X K Q mu pi
        (@abelian_selected_pushout C P t A K X Q mu pi)))
≔ λ T : τ (Obj C), λ u : τ (Hom C T Q), λ v : τ (Hom C T Q),
    λ p : τ (@AbelianPushoutInjectionEquality C P t A
      K X Q T mu pi u v),
      @abelian_group_sub_zero_to_eq_path
        (Hom C T Q)
        (@preadditive_hom_structure C
          (@abelian_stability_preadditive C P t A) T Q)
        u v
        (@abelian_pushout_injection_difference_zero_path C P t A
          K X Q T mu pi mu_monic u v p);
