/* Covered factors retain the actual lift; zero descends only with epicity. */
require open emdash.emdash3_2_hom_factor_epic_descent;

assert
  (C : Cat) (S : τ (@PreadditiveCategory C))
  (A B D X Y : τ (Obj C))
  (m : τ (Hom C A B)) (z : τ (Hom C B D))
  (h : τ (Hom C X B)) (e : τ (Hom C Y X))
  (epic : τ (@IsEpic C Y X e))
  (F : τ (@HomPostcompFactor C A B Y m (@comp_fapp0 C Y X B h e)))
  (zero : τ (@= (Hom C A D) (@comp_fapp0 C A B D z m)
    (@preadditive_hom_zero C S A D)))
  ⊢ @annihilation_from_epic_factor C S A B D X Y m z h e epic F zero : τ (@= (Hom C X D) (@comp_fapp0 C X B D z h)
    (@preadditive_hom_zero C S X D));

assertnot
  (C : Cat) (S : τ (@PreadditiveCategory C))
  (A B D X Y : τ (Obj C))
  (m : τ (Hom C A B)) (z : τ (Hom C B D))
  (h : τ (Hom C X B)) (e : τ (Hom C Y X))
  (epic : τ (@IsEpic C Y X e))
  (F : τ (@HomPostcompFactor C A B Y m (@comp_fapp0 C Y X B h e)))
  (zero : τ (@= (Hom C A D) (@comp_fapp0 C A B D z m)
    (@preadditive_hom_zero C S A D)))
  ⊢ @eq_refl (Hom C X D) (@comp_fapp0 C X B D z h) : τ (@= (Hom C X D) (@comp_fapp0 C X B D z h)
    (@preadditive_hom_zero C S X D));

assert
  (C : Cat) (U V B K L D : τ (Obj C))
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
  ⊢ @covered_comparison_factor C U V B K L D p d out k e g comparison upper boundary lift monic : τ (@HomPostcompFactor C K L U g
      (@comp_fapp0 C U V L
        (@hom_postcomp_factor_arrow C L D V e
          (@hom_precomp_factor_arrow C U V D p (@comp_fapp0 C U B D out d) upper) boundary) p));

assert
  (C : Cat) (U V B K L D : τ (Obj C))
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
  ⊢ @hom_postcomp_factor_arrow C K L U g (@comp_fapp0 C U V L (@hom_postcomp_factor_arrow C L D V e (@hom_precomp_factor_arrow C U V D p (@comp_fapp0 C U B D out d) upper) boundary) p)
      (@covered_comparison_factor C U V B K L D p d out k e g comparison upper boundary lift monic)
    ≡ @hom_postcomp_factor_arrow C K B U k d lift;
