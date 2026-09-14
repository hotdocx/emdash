/* Whole additive inverses and the original universal negative identity. */
require open emdash.emdash3_2_one_cat_additive_family_cancellation;

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (V
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X : τ (Functor B C)) ⊢
  @one_cat_shear_negative_identity_add_path B C C1 Prod t V T0 X : τ (@= (@Transf B C X X)
  (@one_cat_additive_family_add B C C1 Prod t V T0 X X (@id (Functor_cat B C) X)
  (@one_cat_shear_negative_identity_family B C C1 Prod t V T0 X)) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t V) T0 X X));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (V
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X : τ (Functor B C)) ⊢
  @one_cat_negative_family_add_path B C C1 Prod t V T0 X : τ (@= (@Transf B C X X) (@one_cat_additive_family_add B C
  C1 Prod t V T0 X X (@id (Functor_cat B C) X) (@one_cat_negative_family_transf B C C1 Prod t V T0 X))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t V) T0 X X));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (V
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X : τ (Functor B C)) ⊢
  @one_cat_negative_family_shear_path B C C1 Prod t V T0 X : τ (@= (@Transf B C X X)
  (@one_cat_shear_negative_identity_family B C C1 Prod t V T0 X) (@one_cat_negative_family_transf B C C1 Prod t V T0
  X));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (V
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C)) (f : τ (@Transf B
  C X Y)) ⊢ @one_cat_additive_family_inverse_path B C C1 Prod t V T0 X Y f : τ (@= (@Transf B C X Y)
  (@one_cat_additive_family_add B C C1 Prod t V T0 X Y f (@one_cat_negative_family B C C1 Prod t V T0 X Y f))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t V) T0 X Y));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (V
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C)) (f : τ (@Transf B
  C X Y)) ⊢ @one_cat_difference_family_self_path B C C1 Prod t V T0 X Y f : τ (@= (@Transf B C X Y)
  (@one_cat_difference_family B C C1 Prod t V T0 X Y f f) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t V) T0 X Y));
assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) (Prod : τ (Functor (Product_cat C C) C)) (t : τ (Obj C)) (V :
  τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (x : τ (Obj C)) ⊢ @tapp0_fapp0 C C (@id_func
  C) (@id_func C) x (@omega_equiv_along_left_inv (Functor_cat C C) (@id_func C) (@id_func C)
  (@one_cat_negative_identity_transf C C1 Prod t V T0) (@one_cat_negative_identity_omega C C1 Prod t V T0)) ≡
  @preadditive_hom_neg C (@additive_preadditive C Prod t V) x x (@id C x);
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (V
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X : τ (Functor B C)) ⊢
  @omega_equiv_along_left_law (Functor_cat B C) X X (@one_cat_negative_family_transf B C C1 Prod t V T0 X)
  (@one_cat_negative_family_omega B C C1 Prod t V T0 X) : τ (@= (@Transf B C X X) (@comp_fapp0 (Functor_cat B C) X X X
  (@omega_equiv_along_left_inv (Functor_cat B C) X X (@one_cat_negative_family_transf B C C1 Prod t V T0 X)
  (@one_cat_negative_family_omega B C C1 Prod t V T0 X)) (@one_cat_negative_family_transf B C C1 Prod t V T0 X)) (@id
  (Functor_cat B C) X));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (V
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X : τ (Functor B C)) ⊢
  @omega_equiv_left_as_right_law (Functor_cat B C) X X (@one_cat_negative_family_transf B C C1 Prod t V T0 X)
  (@one_cat_negative_family_omega B C C1 Prod t V T0 X) : τ (@= (@Transf B C X X) (@comp_fapp0 (Functor_cat B C) X X X
  (@one_cat_negative_family_transf B C C1 Prod t V T0 X) (@omega_equiv_along_left_inv (Functor_cat B C) X X
  (@one_cat_negative_family_transf B C C1 Prod t V T0 X) (@one_cat_negative_family_omega B C C1 Prod t V T0 X))) (@id
  (Functor_cat B C) X));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (V
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C)) (f : τ (@Transf B
  C X Y)) (i j : τ (Obj B)) ⊢ @eq_ap (@Transf B C X Y) (Functor (Hom_cat B i j) (Hom_cat C (@fapp0 B C X i) (@fapp0 B
  C Y j))) (λ h : τ (@Transf B C X Y), @tapp1_func B C X Y i j h) (@one_cat_additive_family_add B C C1 Prod t V T0 X Y
  f (@one_cat_negative_family B C C1 Prod t V T0 X Y f)) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t V) T0 X Y) (@one_cat_additive_family_inverse_path B C C1 Prod t V T0 X Y f) : τ
  (@= (Functor (Hom_cat B i j) (Hom_cat C (@fapp0 B C X i) (@fapp0 B C Y j))) (@tapp1_func B C X Y i j
  (@one_cat_additive_family_add B C C1 Prod t V T0 X Y f (@one_cat_negative_family B C C1 Prod t V T0 X Y f)))
  (@tapp1_func B C X Y i j (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t V) T0 X Y)));
assertnot [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (V : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C)) (f g : τ
  (@Transf B C X Y)) ⊢ @eq_refl (@Transf B C X Y) (@one_cat_negative_family B C C1 Prod t V T0 X Y f) : τ (@= (@Transf
  B C X Y) (@one_cat_negative_family B C C1 Prod t V T0 X Y f) g);
