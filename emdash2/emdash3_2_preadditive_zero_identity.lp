/* Zero identities pass backwards through monics and forwards through epics. */
require open emdash.emdash3_2_preabelian_bimorphism_lemmas;

symbol monic_source_identity_zero
  [C : Cat] (S : τ (@PreadditiveCategory C)) [A B : τ (Obj C)]
  (m : τ (Hom C A B)) (monic : τ (@IsMonic C A B m))
  (zero_B : τ (@= (Hom C B B) (@id C B) (@preadditive_hom_zero C S B B)))
  : τ (@= (Hom C A A) (@id C A) (@preadditive_hom_zero C S A A))
≔ @monic_postcomposition_zero_to_zero_path C S A A B m monic (@id C A)
    (@preadditive_precompose_zero_path C S A B B (@id C B) m zero_B);

symbol epic_target_identity_zero
  [C : Cat] (S : τ (@PreadditiveCategory C)) [A B : τ (Obj C)]
  (e : τ (Hom C A B)) (epic : τ (@IsEpic C A B e))
  (zero_A : τ (@= (Hom C A A) (@id C A) (@preadditive_hom_zero C S A A)))
  : τ (@= (Hom C B B) (@id C B) (@preadditive_hom_zero C S B B))
≔ @epic_precomposition_zero_to_zero_path C S A B B e epic (@id C B)
    (@preadditive_postcompose_zero_path C S A A B e (@id C A) zero_A);
