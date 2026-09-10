/* Cancellation transports zero identity with the required mono/epi evidence. */
require open emdash.emdash3_2_preadditive_zero_identity;
assert [C : Cat] (S : τ (@PreadditiveCategory C)) [A B : τ (Obj C)]
  (m : τ (Hom C A B)) (mono : τ (@IsMonic C A B m))
  (z : τ (@= (Hom C B B) (@id C B) (@preadditive_hom_zero C S B B))) ⊢
  @monic_source_identity_zero C S A B m mono z
    : τ (@= (Hom C A A) (@id C A) (@preadditive_hom_zero C S A A));
assert [C : Cat] (S : τ (@PreadditiveCategory C)) [A B : τ (Obj C)]
  (e : τ (Hom C A B)) (epi : τ (@IsEpic C A B e))
  (z : τ (@= (Hom C A A) (@id C A) (@preadditive_hom_zero C S A A))) ⊢
  @epic_target_identity_zero C S A B e epi z
    : τ (@= (Hom C B B) (@id C B) (@preadditive_hom_zero C S B B));
