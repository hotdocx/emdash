/* Reusable simplification of a postcomposed difference. */

require open emdash.emdash3_2_abelian_fiber_pushout_stability;

symbol preadditive_postcompose_difference_right_zero_path
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [X Y Z : τ (Obj C)]
  (g : τ (Hom C Y Z))
  (u v : τ (Hom C X Y))
  (h : τ (Hom C X Z))
  (p : τ (@= (Hom C X Z) (@comp_fapp0 C _ _ _ g u) h))
  (q : τ (@= (Hom C X Z)
    (@comp_fapp0 C _ _ _ g v)
    (@preadditive_hom_zero C S X Z)))
  : τ (@= (Hom C X Z)
      (@comp_fapp0 C _ _ _ g
        (@preadditive_hom_add C S X Y u
          (@preadditive_hom_neg C S X Y v)))
      h)
≔ @eq_trans _ _ _ _
    ((@preadditive_comp_add_right_law C S) X Y Z g u
      (@preadditive_hom_neg C S X Y v))
    (@eq_trans _ _ _ _
      (@eq_ap
        (Hom C X Z) (Hom C X Z)
        (λ x : τ (Hom C X Z),
          @preadditive_hom_add C S X Z x
            (@comp_fapp0 C _ _ _ g
              (@preadditive_hom_neg C S X Y v)))
        _ _ p)
      (@eq_trans _ _ _ _
        (@eq_ap
          (Hom C X Z) (Hom C X Z)
          (λ y : τ (Hom C X Z),
            @preadditive_hom_add C S X Z h y)
          _ _
          (@preadditive_comp_neg_right_path C S X Y Z g v))
        (@eq_trans _ _ _ _
          (@eq_ap
            (Hom C X Z) (Hom C X Z)
            (λ y : τ (Hom C X Z),
              @preadditive_hom_add C S X Z h
                (@preadditive_hom_neg C S X Z y))
            _ _ q)
          (@eq_trans _ _ _ _
            (@eq_ap
              (Hom C X Z) (Hom C X Z)
              (λ y : τ (Hom C X Z),
                @preadditive_hom_add C S X Z h y)
              _ _
              (@abelian_group_neg_zero_path
                (Hom C X Z) (@preadditive_hom_structure C S X Z)))
            ((@abelian_group_add_zero_law
              (Hom C X Z) (@preadditive_hom_structure C S X Z)) h)))));

/* If u f = h and v f = 0, then (u - v) f = h. */

symbol preadditive_precompose_difference_right_zero_path
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [X Y Z : τ (Obj C)]
  (u v : τ (Hom C Y Z))
  (f : τ (Hom C X Y))
  (h : τ (Hom C X Z))
  (p : τ (@= (Hom C X Z) (@comp_fapp0 C _ _ _ u f) h))
  (q : τ (@= (Hom C X Z)
    (@comp_fapp0 C _ _ _ v f)
    (@preadditive_hom_zero C S X Z)))
  : τ (@= (Hom C X Z)
      (@comp_fapp0 C _ _ _
        (@preadditive_hom_add C S Y Z u
          (@preadditive_hom_neg C S Y Z v)) f)
      h)
≔ @eq_trans _ _ _ _
    ((@preadditive_comp_add_left_law C S) X Y Z u
      (@preadditive_hom_neg C S Y Z v) f)
    (@eq_trans _ _ _ _
      (@eq_ap
        (Hom C X Z) (Hom C X Z)
        (λ x : τ (Hom C X Z),
          @preadditive_hom_add C S X Z x
            (@comp_fapp0 C _ _ _
              (@preadditive_hom_neg C S Y Z v) f))
        _ _ p)
      (@eq_trans _ _ _ _
        (@eq_ap
          (Hom C X Z) (Hom C X Z)
          (λ y : τ (Hom C X Z),
            @preadditive_hom_add C S X Z h y)
          _ _
          (@preadditive_comp_neg_left_path C S X Y Z v f))
        (@eq_trans _ _ _ _
          (@eq_ap
            (Hom C X Z) (Hom C X Z)
            (λ y : τ (Hom C X Z),
              @preadditive_hom_add C S X Z h
                (@preadditive_hom_neg C S X Z y))
            _ _ q)
          (@eq_trans _ _ _ _
            (@eq_ap
              (Hom C X Z) (Hom C X Z)
              (λ y : τ (Hom C X Z),
                @preadditive_hom_add C S X Z h y)
              _ _
              (@abelian_group_neg_zero_path
                (Hom C X Z) (@preadditive_hom_structure C S X Z)))
            ((@abelian_group_add_zero_law
              (Hom C X Z) (@preadditive_hom_structure C S X Z)) h)))));
