/* Epic-cover descent through existing whole Hom factors. */
require open emdash.emdash3_2_hom_factor_views;
require open emdash.emdash3_2_hom_factor_comparison_pasting;
require open emdash.emdash3_2_preabelian_bimorphism_lemmas;

// A zero after the preceding map also kills any arrow factoring after an epic.
symbol annihilation_from_epic_factor
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D X Y : τ (Obj C)]
  (m : τ (Hom C A B)) (z : τ (Hom C B D))
  (h : τ (Hom C X B)) (e : τ (Hom C Y X))
  (epic : τ (@IsEpic C Y X e))
  (F : τ (@HomPostcompFactor C A B Y m (@comp_fapp0 C Y X B h e)))
  (zero : τ (@= (Hom C A D) (@comp_fapp0 C A B D z m)
    (@preadditive_hom_zero C S A D)))
  : τ (@= (Hom C X D) (@comp_fapp0 C X B D z h)
    (@preadditive_hom_zero C S X D))
≔ @epic_precomposition_zero_to_zero_path C S Y X D e epic
    (@comp_fapp0 C X B D z h)
    (@eq_trans _ _ _ _
      (@eq_sym _ _ _ (@comp_assoc C Y X B D z h e))
      (@kernel_lift_postannihilation_path C S Y A B D m
        (@hom_postcomp_factor_arrow C A B Y m (@comp_fapp0 C Y X B h e) F)
        (@comp_fapp0 C Y X B h e) z
        (@hom_postcomp_factor_path C A B Y m (@comp_fapp0 C Y X B h e) F) zero));

// For e g = out k, a boundary through e lifts through g after p.
symbol covered_comparison_factor
  [C : Cat] [U V B K L D : τ (Obj C)]
  (p : τ (Hom C U V)) (d : τ (Hom C U B))
  (out : τ (Hom C B D)) (k : τ (Hom C K B))
  (e : τ (Hom C L D)) (g : τ (Hom C K L))
  (comparison : τ (@= (Hom C K D) (@comp_fapp0 C K L D e g)
    (@comp_fapp0 C K B D out k)))
  (upper : τ (@HomPrecompFactor C U V D p (@comp_fapp0 C U B D out d)))
  (boundary : τ (@HomPostcompFactor C L D V e
    (@hom_precomp_factor_arrow C U V D p (@comp_fapp0 C U B D out d) upper)))
  (lift : τ (@HomPostcompFactor C K B U k d))
  (monic : τ (@IsMonic C L D e))
  : τ (@HomPostcompFactor C K L U g
      (@comp_fapp0 C U V L
        (@hom_postcomp_factor_arrow C L D V e
          (@hom_precomp_factor_arrow C U V D p (@comp_fapp0 C U B D out d) upper) boundary) p))
≔ @monic_comparison_factor C K L D U
    (@comp_fapp0 C K B D out k) e g comparison
    (@comp_fapp0 C U B D out d)
    (@hom_postcomp_factor_trans C V L D U
      (@hom_precomp_factor_arrow C U V D p (@comp_fapp0 C U B D out d) upper)
      e (@comp_fapp0 C U B D out d)
      (@hom_precomp_factor_postcomp_view C U V D p (@comp_fapp0 C U B D out d) upper)
      boundary)
    (@hom_postcomp_factor_whisker C K B D U k d out lift)
    monic;
