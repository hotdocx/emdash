require open emdash.emdash3_2_one_cat_zero_cone_fibre_inclusion;
symbol C : Cat;
symbol C1 : τ (IsNCat (cat_succ cat_zero) C);
symbol t : τ (Obj C);
symbol T : τ (@TerminalObject C t);
symbol a : τ (Obj C);
symbol d : τ (Functor WalkingArrow_cat C);
symbol h : τ (@Transf WalkingArrow_cat C
  (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a) d);
symbol k : τ (@Transf WalkingArrow_cat C
  (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a) d);
symbol alpha : τ (Hom (@Transf_cat WalkingArrow_cat C
  (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a) d) h k);
symbol inclusion ≔ @zero_arrow_cone_fibre_inclusion_func C C1 t T a d;
symbol mapped ≔ @fapp1_fapp0 _ _ inclusion h k alpha;

// Both bases remain fixed and the existing fibre cell is retained.
assert ⊢ sigma_Fst mapped ≡ @id C a;
assert ⊢ sigma_Fst (sigma_Snd mapped) ≡ @id (Functor_cat WalkingArrow_cat C) d;
assert ⊢ sigma_Snd (sigma_Snd mapped) ≡ alpha;

// The full Hom functor remains available for the next cell.
assert ⊢ @fapp1_func _ _ inclusion h k : τ (Functor
  (Hom_cat (@Transf_cat WalkingArrow_cat C
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a) d) h k)
  (Hom_cat (@ZeroArrowCone_cat C t T)
    (@zero_arrow_cone_obj C t T a d h) (@zero_arrow_cone_obj C t T a d k)));

// Point inclusion retains the original transformation.
assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (a : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a) d)) ⊢
  @fapp0 _ _ (@zero_arrow_cone_fibre_inclusion_func C C1 t T a d) h
  ≡ @zero_arrow_cone_obj C t T a d h;
