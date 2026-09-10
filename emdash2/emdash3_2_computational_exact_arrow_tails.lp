/*
  Exactness annotations on a finite result tail.

  The indexed record requires g ∘ f = 0 and the existing selected exactness
  witness for that same pair. It introduces no exactness or homology choice.
  Rigid f/g indices prevent repeated inversion of the expanded all-test
  predicate. The corresponding Sigma model remains in the research audit.
  The original pair/zero/proof enter through a transparent usability view.
*/
require open emdash.emdash3_2_short_exact_sequences;
require open emdash.emdash3_2_finite_arrow_tails;

constant symbol ComputationalExactArrowStep
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (A B D : τ (Obj C)) (f : τ (Hom C A B)) (g : τ (Hom C B D)) : Grpd;

constant symbol computational_exact_arrow_step_intro
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B D : τ (Obj C)] [f : τ (Hom C A B)] [g : τ (Hom C B D)]
  (z : τ (@= (Hom C A D) (@comp_fapp0 C A B D g f)
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t PA) A D)))
  (exact : τ (@computational_exact_at_selected C P t PA A B D
    (@computational_chain_pair_intro C (@computational_homology_preadditive C P t PA) A B D f g z)))
  : τ (@ComputationalExactArrowStep C P t PA A B D f g);

symbol computational_exact_arrow_step_zero
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B D : τ (Obj C)] [f : τ (Hom C A B)] [g : τ (Hom C B D)]
  (step : τ (@ComputationalExactArrowStep C P t PA A B D f g))
  : τ (@= (Hom C A D) (@comp_fapp0 C A B D g f)
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t PA) A D));
rule @computational_exact_arrow_step_zero _ _ _ _ _ _ _ _ _
  (@computational_exact_arrow_step_intro _ _ _ _ _ _ _ _ _ $z _) ↪ $z;

symbol computational_exact_arrow_step_of_pair
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A B D))
  (exact : τ (@computational_exact_at_selected C P t PA A B D pair))
  : τ (@ComputationalExactArrowStep C P t PA A B D
      (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t PA) A B D pair)
      (@computational_chain_pair_d C (@computational_homology_preadditive C P t PA) A B D pair))
≔ @computational_exact_arrow_step_intro C P t PA A B D
    (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t PA) A B D pair)
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t PA) A B D pair)
    (@computational_chain_pair_path C (@computational_homology_preadditive C P t PA) A B D pair)
    exact;

symbol computational_exact_arrow_step_pair
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B D : τ (Obj C)] [f : τ (Hom C A B)] [g : τ (Hom C B D)]
  (step : τ (@ComputationalExactArrowStep C P t PA A B D f g))
  : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A B D)
≔ @computational_chain_pair_intro C (@computational_homology_preadditive C P t PA) A B D f g
  (@computational_exact_arrow_step_zero C P t PA A B D f g step);

symbol computational_exact_arrow_step_exact
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B D : τ (Obj C)] [f : τ (Hom C A B)] [g : τ (Hom C B D)]
  (step : τ (@ComputationalExactArrowStep C P t PA A B D f g))
  : τ (@computational_exact_at_selected C P t PA A B D
    (@computational_exact_arrow_step_pair C P t PA A B D f g step));
rule @computational_exact_arrow_step_exact _ _ _ _ _ _ _ _ _
  (@computational_exact_arrow_step_intro _ _ _ _ _ _ _ _ _ _ $e) ↪ $e;

symbol ComputationalExactArrowTail
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (n : τ Nat_grpd) (A B : τ (Obj C)) (f : τ (Hom C A B)) : Grpd
≔ @FiniteArrowTail C (@ComputationalExactArrowStep C P t PA) n A B f;

symbol computational_exact_arrow_tail_nil
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B : τ (Obj C)] [f : τ (Hom C A B)]
  : τ (@ComputationalExactArrowTail C P t PA zero A B f)
≔ @finite_arrow_tail_nil C (@ComputationalExactArrowStep C P t PA) A B f;

// Reuse the original pair and its exactness, sharing its outgoing arrow with rest.
symbol computational_exact_arrow_tail_cons_pair
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) [n : τ Nat_grpd] [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A B D))
  (exact : τ (@computational_exact_at_selected C P t PA A B D pair))
  (rest : τ (@ComputationalExactArrowTail C P t PA n B D
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t PA) A B D pair)))
  : τ (@ComputationalExactArrowTail C P t PA (succ n) A B
    (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t PA) A B D pair))
≔ @finite_arrow_tail_cons C (@ComputationalExactArrowStep C P t PA) n A B
    (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t PA) A B D pair)
    D (@computational_chain_pair_d C (@computational_homology_preadditive C P t PA) A B D pair)
    (@computational_exact_arrow_step_of_pair C P t PA A B D pair exact) rest;
