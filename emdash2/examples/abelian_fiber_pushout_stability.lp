/* Reviewer-facing Abelian stability of genuine fiber products and pushouts. */

require open emdash.emdash3_2_abelian_fiber_pushout_stability;

// Pullback of an epic arrow: the opposite selected projection is epic.
assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (A : τ (@ComputationalAbelianCategory C P t))
  (I X E : τ (Obj C))
  (iota : τ (Hom C I X))
  (epsilon : τ (Hom C E X))
  (epic : τ (@IsEpic C E X epsilon))
  ⊢ @abelian_fiber_product_epic_projection C P t A
      I X E iota epsilon epic
  : τ (@IsEpic C
      (@computational_fiber_product_object C P t
        (@abelian_stability_additive C P t A) I X E iota epsilon
        (@abelian_selected_fiber_product C P t A I X E iota epsilon)) I
      (@computational_fiber_product_proj1 C P t
        (@abelian_stability_additive C P t A) I X E iota epsilon
        (@abelian_selected_fiber_product C P t A I X E iota epsilon)));

// Its difference arrow is itself epic, enabling the normal colift proof.
assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (A : τ (@ComputationalAbelianCategory C P t))
  (I X E : τ (Obj C))
  (iota : τ (Hom C I X))
  (epsilon : τ (Hom C E X))
  (epic : τ (@IsEpic C E X epsilon))
  ⊢ @abelian_fiber_product_difference_epic C P t A
      I X E iota epsilon epic
  : τ (@IsEpic C
      (@weak_pullback_product_object C P t
        (@abelian_stability_additive C P t A) I E) X
      (@weak_pullback_difference_fapp0 C P t
        (@abelian_stability_additive C P t A)
        I X E iota epsilon));

// Pushout of a monic arrow: the opposite selected injection is monic.
assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (A : τ (@ComputationalAbelianCategory C P t))
  (K X Q : τ (Obj C))
  (mu : τ (Hom C K X))
  (pi : τ (Hom C K Q))
  (monic : τ (@IsMonic C K X mu))
  ⊢ @abelian_pushout_monic_injection C P t A
      K X Q mu pi monic
  : τ (@IsMonic C Q
      (@computational_pushout_object C P t
        (@abelian_stability_additive C P t A) X K Q mu pi
        (@abelian_selected_pushout C P t A K X Q mu pi))
      (@computational_pushout_inj2 C P t
        (@abelian_stability_additive C P t A) X K Q mu pi
        (@abelian_selected_pushout C P t A K X Q mu pi)));

// Its difference arrow is itself monic, enabling the normal lift proof.
assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (A : τ (@ComputationalAbelianCategory C P t))
  (K X Q : τ (Obj C))
  (mu : τ (Hom C K X))
  (pi : τ (Hom C K Q))
  (monic : τ (@IsMonic C K X mu))
  ⊢ @abelian_pushout_difference_monic C P t A
      K X Q mu pi monic
  : τ (@IsMonic C K
      (@pushout_product_object C P t
        (@abelian_stability_additive C P t A) X Q)
      (@pushout_difference_fapp0 C P t
        (@abelian_stability_additive C P t A) X K Q mu pi));
