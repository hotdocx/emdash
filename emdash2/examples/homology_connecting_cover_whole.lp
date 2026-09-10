/* The cover reaches the actual whole cycle object, not an endpoint conversion. */
require open emdash.emdash3_2_homology_connecting_cover;
require open emdash.emdash3_2_chain_pair_homology_records;

assert [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (QP : τ (@CokernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T0 (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab))))
  [A B X Y Z : τ (Obj C)]
  (row : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A B Y))
  (right_pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z)) ⊢
  @homology_connecting_cover_projection C P t Ab A B X Y Z row right_pair (@chain_pair_homology_record C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP X Y Z right_pair)
  : τ (Hom C (@homology_connecting_cover_object C P t Ab A B X Y Z row right_pair (@chain_pair_homology_record C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP X Y Z right_pair)) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP) (@chain_pair_outgoing_diagram C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z right_pair)));

assert [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (QP : τ (@CokernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T0 (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab))))
  [A B X Y Z : τ (Obj C)]
  (row : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A B Y))
  (right_pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z)) ⊢
  @homology_connecting_cover_epic C P t Ab A B X Y Z row right_pair (@chain_pair_homology_record C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP X Y Z right_pair)
  : τ (@IsEpic C (@homology_connecting_cover_object C P t Ab A B X Y Z row right_pair (@chain_pair_homology_record C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP X Y Z right_pair)) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP) (@chain_pair_outgoing_diagram C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z right_pair))
      (@homology_connecting_cover_projection C P t Ab A B X Y Z row right_pair (@chain_pair_homology_record C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP X Y Z right_pair)));
