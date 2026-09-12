/* NON-LIBRARY SOUNDNESS DIAGNOSTIC — Homd target section polarity.
   The old positive section over the opposite target base produces a reverse
   Hom action. Acceptance reproduces a defect of the current coupled package;
   independence from the existing op/Sigma defects is NOT established here.
   No primitive witness, rewrite, unifier or extra axiom is introduced.
   Do not import this file into the library or its positive check registry.
   See docs/TYPESCRIPT_EMDASH_HOMD_TARGET_POLARITY_DIAGNOSTIC.md. */
require open emdash.emdash3_2;

symbol homd_target_polarity_section [Z C : Cat] (F : τ (Functor Z C))
  (x : τ (Obj Z)) (u : τ (Obj C))
  : τ (Obj (@Pi_cat (Op_cat Z)
      (@Homd_target_section_catd Z (@Const_catd Z Terminal_cat) x)))
≔ @homd_src_sec Z (@Const_catd Z Terminal_cat) (@Const_catd Z C) F x u;

symbol homd_target_polarity_reverse_functor [Z C : Cat] (F : τ (Functor Z C))
  (x y : τ (Obj Z)) (u : τ (Obj C)) (p : τ (Hom Z x y))
  : τ (Functor (Hom_cat C u (@fapp0 Z C F y))
      (Hom_cat C u (@fapp0 Z C F x)))
≔ @fapp1_fapp0 _ _ (@fapp0_func _ _ (@id Z x)) _ _
    (@fapp1_fapp0 _ _ (@fapp0_func _ _ Terminal_obj) _ _
      (@piapp1_fapp0 (Op_cat Z)
        (@Homd_target_section_catd Z (@Const_catd Z Terminal_cat) x)
        (@homd_target_polarity_section Z C F x u) y x p));

symbol homd_target_polarity_reverse [C : Cat]
  (x y : τ (Obj C)) (p : τ (Hom C x y))
  : τ (Hom C y x)
≔ @fapp0 _ _
    (@homd_target_polarity_reverse_functor C C (@id_func C) x y y p)
    (@id C y);

symbol homd_target_empty_witness : τ Empty_grpd
≔ (@homd_target_polarity_reverse Grpd_cat Empty_grpd Unit_grpd
    (λ _ : τ Empty_grpd, tt)) tt;

assert ⊢ homd_target_empty_witness : τ Empty_grpd;
