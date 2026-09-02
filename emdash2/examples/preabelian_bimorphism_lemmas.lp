/* Reviewer-facing pre-Abelian cancellation converses. */

require open emdash.emdash3_2_preabelian_bimorphism_lemmas;

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A B : τ (Obj C))
  (m : τ (Hom C A B))
  (K : τ (@ComputationalKernel C S A B m))
  (zero : τ (@= (Hom C
    (@computational_kernel_object C S A B m K) A)
    (@computational_kernel_morphism C S A B m K)
    (@preadditive_hom_zero C S
      (@computational_kernel_object C S A B m K) A)))
  ⊢ @computational_kernel_zero_to_monic C S A B m K zero
  : τ (@IsMonic C A B m);

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A B : τ (Obj C))
  (e : τ (Hom C A B))
  (Q : τ (@ComputationalCokernel C S A B e))
  (zero : τ (@= (Hom C B
    (@computational_cokernel_object C S A B e Q))
    (@computational_cokernel_morphism C S A B e Q)
    (@preadditive_hom_zero C S B
      (@computational_cokernel_object C S A B e Q))))
  ⊢ @computational_cokernel_zero_to_epic C S A B e Q zero
  : τ (@IsEpic C A B e);

assert
  (C : Cat)
  (A B D : τ (Obj C))
  (f : τ (Hom C A B))
  (g : τ (Hom C B D))
  (fm : τ (@IsMonic C A B f))
  (gm : τ (@IsMonic C B D g))
  ⊢ @is_monic_comp C A B D f g fm gm
  : τ (@IsMonic C A D (@comp_fapp0 C A B D g f));

assert
  (C : Cat)
  (A B D : τ (Obj C))
  (f : τ (Hom C A B))
  (g : τ (Hom C B D))
  (fe : τ (@IsEpic C A B f))
  (ge : τ (@IsEpic C B D g))
  ⊢ @is_epic_comp C A B D f g fe ge
  : τ (@IsEpic C A D (@comp_fapp0 C A B D g f));
