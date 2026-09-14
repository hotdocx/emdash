require open emdash.emdash3_2_one_cat_constant_chain_zeros;
// The native zero is compared as one whole transformation.
assert [K C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (x y : τ (Obj C)) ⊢ @one_cat_constant_family_zero_path K C S C1 t T T0 x y
  : τ (@= (@Transf K C (@Const_func K C x) (@Const_func K C y))
    (@Const_transf K C x y (@preadditive_hom_zero C S x y))
    (@zero_arrow_family_zero_transf K C t T T0 (@Const_func K C x) (@Const_func K C y)));
// Existing scalar chain data suffice; no whole zero or coherence proof is supplied.
assert [K C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  [x y z : τ (Obj C)] (f : τ (Hom C x y)) (g : τ (Hom C y z))
  (p : τ (@= (Hom C x z) (@comp_fapp0 C x y z g f) (@preadditive_hom_zero C S x z))) ⊢
  @one_cat_constant_chain_zero_path K C S C1 t T T0 x y z f g p
  : τ (@= (@Transf K C (@Const_func K C x) (@Const_func K C z))
    (@comp_fapp0 (Functor_cat K C) (@Const_func K C x) (@Const_func K C y) (@Const_func K C z)
      (@Const_transf K C y z g) (@Const_transf K C x y f))
    (@zero_arrow_family_zero_transf K C t T T0 (@Const_func K C x) (@Const_func K C z)));
