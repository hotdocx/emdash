/* Generic result packaging with supplied proofs; real window proofs are separate. */
require open emdash.emdash3_2_computational_exact_arrow_tails;
constant symbol C : Cat;
constant symbol P : τ (Functor (Product_cat C C) C);
constant symbol t : τ (Obj C);
constant symbol PA : τ (@PreAbelianCategory C P t);
symbol S ≔ @computational_homology_preadditive C P t PA;
constant symbol A : τ (Obj C);
constant symbol B : τ (Obj C);
constant symbol D : τ (Obj C);
constant symbol E : τ (Obj C);
constant symbol f : τ (Hom C A B);
constant symbol g : τ (Hom C B D);
constant symbol h : τ (Hom C D E);
constant symbol z : τ (@= (Hom C A D) (@comp_fapp0 C A B D g f) (@preadditive_hom_zero C S A D));
constant symbol w : τ (@= (Hom C B E) (@comp_fapp0 C B D E h g) (@preadditive_hom_zero C S B E));
symbol pair1 ≔ @computational_chain_pair_intro C S A B D f g z;
symbol pair2 ≔ @computational_chain_pair_intro C S B D E g h w;
constant symbol exact1 : τ (@computational_exact_at_selected C P t PA A B D pair1);
constant symbol exact2 : τ (@computational_exact_at_selected C P t PA B D E pair2);
symbol step1 ≔ @computational_exact_arrow_step_of_pair C P t PA A B D pair1 exact1;
symbol Q ≔ @ComputationalExactArrowStep C P t PA;
symbol tail ≔ @computational_exact_arrow_tail_cons_pair C P t PA (succ zero) A B D pair1 exact1
  (@computational_exact_arrow_tail_cons_pair C P t PA zero B D E pair2 exact2
    (@computational_exact_arrow_tail_nil C P t PA D E h));

assert ⊢ @computational_exact_arrow_step_pair C P t PA A B D f g step1 ≡ pair1;
assert ⊢ @computational_exact_arrow_step_exact C P t PA A B D f g step1 ≡ exact1;
assert ⊢ @finite_arrow_tail_arrow C Q (succ zero) A B f tail ≡ g;
// No zero/exact annotation can be manufactured from the unit inhabitant.
assertnot ⊢ tt : τ (@ComputationalExactArrowStep C P t PA A B D f g);
// Zero alone does not provide the missing exactness field.
assertnot ⊢ @computational_exact_arrow_step_intro C P t PA A B D f g z
  : τ (@ComputationalExactArrowStep C P t PA A B D f g);
