/* Actual whole six-term result: four original comparisons and witnesses,
   with both selected inverse maps at every interior. Each definition's
   stated type is checked against its actual transparent projection body.
   Direct comparison to standalone theorem presentations is a separate
   retained diagnostic, not asserted by this reviewer. */
require open emdash.emdash3_2_one_cat_native_exact_tail_observations;

require open emdash.emdash3_2_one_cat_native_snake_six_term_result;
symbol K : Cat;
symbol C : Cat;
symbol C1 : τ (IsNCat (cat_succ cat_zero) C);
symbol Prod : τ (Functor (Product_cat C C) C);
symbol t : τ (Obj C);
symbol Add : τ (@AdditiveCategory C Prod t);
symbol T0 : τ (@TerminalObject (Op_cat C) t);
symbol P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add));
symbol Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0);
symbol N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q);
symbol A : τ (Functor K C);
symbol B : τ (Functor K C);
symbol X : τ (Functor K C);
symbol D : τ (Functor K C);
symbol b : τ (@Transf K C B X);
symbol c : τ (@Transf K C X D);
symbol h : τ (@NativeSnakeInput K C t (@additive_terminal_object C Prod t Add) A B X D b c);

symbol V0 : τ (Functor K C) ≔ (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h));

symbol V1 : τ (Functor K C) ≔ (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b));

symbol f0 : τ (@Transf K C V0 V1) ≔ (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h);

symbol result : τ (@OneCatNativeSnakeSixTermResult K C C1 Prod t Add T0 P Q N A B X D b c h) ≔
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h);

symbol data0 : τ (OmegaArrowData (Functor_cat K C)) ≔ (@one_cat_native_exact_tail_data K C (@additive_preadditive C Prod
  t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N (succ (succ (succ zero))) V0 V1 f0 result);

symbol arrow0 : τ (Obj (@LaxArrow_cat (Functor_cat K C))) ≔ (@omega_arrow_observation (Functor_cat K C) data0);

symbol evidence0 : τ (@ArrowOmegaEvidence (Functor_cat K C) arrow0) ≔ (@omega_arrow_observation_evidence
  (Functor_cat K C) data0);

symbol inverse_left0 : τ (Hom (Functor_cat K C) (sigma_Fst (sigma_Snd arrow0)) (sigma_Fst arrow0)) ≔
  (@omega_equiv_along_left_inv (Functor_cat K C) (sigma_Fst arrow0) (sigma_Fst (sigma_Snd arrow0)) (sigma_Snd
  (sigma_Snd arrow0)) evidence0);

symbol inverse_right0 : τ (Hom (Functor_cat K C) (sigma_Fst (sigma_Snd arrow0)) (sigma_Fst arrow0)) ≔
  (@omega_equiv_along_right_inv (Functor_cat K C) (sigma_Fst arrow0) (sigma_Fst (sigma_Snd arrow0)) (sigma_Snd
  (sigma_Snd arrow0)) evidence0);

symbol next0 ≔ (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ
  zero))) V0 V1 f0 result);

symbol following0 ≔ (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ
  zero))) V0 V1 f0 result);

symbol rest0 ≔ (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ
  zero))) V0 V1 f0 result);

symbol data1 : τ (OmegaArrowData (Functor_cat K C)) ≔ (@one_cat_native_exact_tail_data K C (@additive_preadditive C Prod
  t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N (succ (succ zero)) V1 next0 following0 rest0);

symbol arrow1 : τ (Obj (@LaxArrow_cat (Functor_cat K C))) ≔ (@omega_arrow_observation (Functor_cat K C) data1);

symbol evidence1 : τ (@ArrowOmegaEvidence (Functor_cat K C) arrow1) ≔ (@omega_arrow_observation_evidence
  (Functor_cat K C) data1);

symbol inverse_left1 : τ (Hom (Functor_cat K C) (sigma_Fst (sigma_Snd arrow1)) (sigma_Fst arrow1)) ≔
  (@omega_equiv_along_left_inv (Functor_cat K C) (sigma_Fst arrow1) (sigma_Fst (sigma_Snd arrow1)) (sigma_Snd
  (sigma_Snd arrow1)) evidence1);

symbol inverse_right1 : τ (Hom (Functor_cat K C) (sigma_Fst (sigma_Snd arrow1)) (sigma_Fst arrow1)) ≔
  (@omega_equiv_along_right_inv (Functor_cat K C) (sigma_Fst arrow1) (sigma_Fst (sigma_Snd arrow1)) (sigma_Snd
  (sigma_Snd arrow1)) evidence1);

symbol next1 ≔ (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) V1 next0 following0 rest0);

symbol following1 ≔ (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) V1 next0 following0 rest0);

symbol rest1 ≔ (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) V1 next0 following0 rest0);

symbol data2 : τ (OmegaArrowData (Functor_cat K C)) ≔ (@one_cat_native_exact_tail_data K C (@additive_preadditive C Prod
  t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N (succ zero) next0 next1 following1 rest1);

symbol arrow2 : τ (Obj (@LaxArrow_cat (Functor_cat K C))) ≔ (@omega_arrow_observation (Functor_cat K C) data2);

symbol evidence2 : τ (@ArrowOmegaEvidence (Functor_cat K C) arrow2) ≔ (@omega_arrow_observation_evidence
  (Functor_cat K C) data2);

symbol inverse_left2 : τ (Hom (Functor_cat K C) (sigma_Fst (sigma_Snd arrow2)) (sigma_Fst arrow2)) ≔
  (@omega_equiv_along_left_inv (Functor_cat K C) (sigma_Fst arrow2) (sigma_Fst (sigma_Snd arrow2)) (sigma_Snd
  (sigma_Snd arrow2)) evidence2);

symbol inverse_right2 : τ (Hom (Functor_cat K C) (sigma_Fst (sigma_Snd arrow2)) (sigma_Fst arrow2)) ≔
  (@omega_equiv_along_right_inv (Functor_cat K C) (sigma_Fst arrow2) (sigma_Fst (sigma_Snd arrow2)) (sigma_Snd
  (sigma_Snd arrow2)) evidence2);

symbol next2 ≔ (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero) next0
  next1 following1 rest1);

symbol following2 ≔ (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero) next0
  next1 following1 rest1);

symbol rest2 ≔ (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero) next0
  next1 following1 rest1);

symbol data3 : τ (OmegaArrowData (Functor_cat K C)) ≔ (@one_cat_native_exact_tail_data K C (@additive_preadditive C Prod
  t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N zero next1 next2 following2 rest2);

symbol arrow3 : τ (Obj (@LaxArrow_cat (Functor_cat K C))) ≔ (@omega_arrow_observation (Functor_cat K C) data3);

symbol evidence3 : τ (@ArrowOmegaEvidence (Functor_cat K C) arrow3) ≔ (@omega_arrow_observation_evidence
  (Functor_cat K C) data3);

symbol inverse_left3 : τ (Hom (Functor_cat K C) (sigma_Fst (sigma_Snd arrow3)) (sigma_Fst arrow3)) ≔
  (@omega_equiv_along_left_inv (Functor_cat K C) (sigma_Fst arrow3) (sigma_Fst (sigma_Snd arrow3)) (sigma_Snd
  (sigma_Snd arrow3)) evidence3);

symbol inverse_right3 : τ (Hom (Functor_cat K C) (sigma_Fst (sigma_Snd arrow3)) (sigma_Fst arrow3)) ≔
  (@omega_equiv_along_right_inv (Functor_cat K C) (sigma_Fst arrow3) (sigma_Fst (sigma_Snd arrow3)) (sigma_Snd
  (sigma_Snd arrow3)) evidence3);
