/* Whole reconstruction at the actual supplied walking-arrow family D.
   The two existing maps are unchanged. They inherit the declared ordinary
   reconstruction at Functor_cat(B,C) and exchange its parameter axis.
   No terminal-family normalization or kernel/cokernel choices are inputs. */
require open emdash.emdash3_2_one_cat_diagram_family_reflection;
require open emdash.emdash3_2_one_cat_diagram_reconstruction;

// Apply the existing forward reconstruction to Sym(D), then exchange back.
symbol one_cat_diagram_family_reconstruction_to [B C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
    (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) D)
≔ @sym_func_func_transf WalkingArrow_cat B C (@walking_arrow_func (Functor_cat B C) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
  (@sym_func B WalkingArrow_cat C D)
    (@one_cat_diagram_reconstruction_to (Functor_cat B C) (@one_cat_functor_category B C C1) (@sym_func B
      WalkingArrow_cat C D));

// Reconstruct Sym(D) in Functor_cat(B,C), then exchange back, retaining D.
symbol one_cat_diagram_family_reconstruction_from [B C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  : τ (@Transf B (Functor_cat WalkingArrow_cat C) D
      (@transf_arrow_diagram_func B C
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
        (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)))
≔ @sym_func_func_transf WalkingArrow_cat B C
    (@sym_func B WalkingArrow_cat C D)
    (@walking_arrow_func (Functor_cat B C)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
    (@one_cat_diagram_reconstruction_from (Functor_cat B C) (@one_cat_functor_category B C C1)
      (@sym_func B WalkingArrow_cat C D));


// Existing reconstruction maps are inverse as whole diagram transformations.
symbol one_cat_diagram_family_reconstruction_left_law [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  : τ (@= (@Transf B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))) (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) D (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@one_cat_diagram_family_reconstruction_from B C C1 D) (@one_cat_diagram_family_reconstruction_to B C C1 D)) (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))))
≔ @one_cat_diagram_family_map_path B C C1 (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) D (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@one_cat_diagram_family_reconstruction_from B C C1 D) (@one_cat_diagram_family_reconstruction_to B C C1 D)) (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)))
    (@eq_trans (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) D (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@one_cat_diagram_family_reconstruction_from B C C1 D) (@one_cat_diagram_family_reconstruction_to B C C1 D)) walking_arrow_src) (@id (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))) walking_arrow_src)
      (@one_cat_diagram_family_evaluation_comp_path B WalkingArrow_cat C C1 walking_arrow_src (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) D (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@one_cat_diagram_family_reconstruction_from B C C1 D) (@one_cat_diagram_family_reconstruction_to B C C1 D))
      (@eq_sym (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))) walking_arrow_src) (@id (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@fapp1_id_path (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src) (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)))))
    (@eq_trans (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) D (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@one_cat_diagram_family_reconstruction_from B C C1 D) (@one_cat_diagram_family_reconstruction_to B C C1 D)) walking_arrow_tgt) (@id (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))) walking_arrow_tgt)
      (@one_cat_diagram_family_evaluation_comp_path B WalkingArrow_cat C C1 walking_arrow_tgt (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) D (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@one_cat_diagram_family_reconstruction_from B C C1 D) (@one_cat_diagram_family_reconstruction_to B C C1 D))
      (@eq_sym (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))) walking_arrow_tgt) (@id (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@fapp1_id_path (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_tgt) (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)))));

// Existing reconstruction maps are inverse as whole diagram transformations.
symbol one_cat_diagram_family_reconstruction_right_law [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  : τ (@= (@Transf B (Functor_cat WalkingArrow_cat C) D D) (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) D (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) D (@one_cat_diagram_family_reconstruction_to B C C1 D) (@one_cat_diagram_family_reconstruction_from B C C1 D)) (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) D))
≔ @one_cat_diagram_family_map_path B C C1 D D (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) D (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) D (@one_cat_diagram_family_reconstruction_to B C C1 D) (@one_cat_diagram_family_reconstruction_from B C C1 D)) (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) D)
    (@eq_trans (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@sym_transf_tapp0_transf B WalkingArrow_cat C D D (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) D (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) D (@one_cat_diagram_family_reconstruction_to B C C1 D) (@one_cat_diagram_family_reconstruction_from B C C1 D)) walking_arrow_src) (@id (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@sym_transf_tapp0_transf B WalkingArrow_cat C D D (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) D) walking_arrow_src)
      (@one_cat_diagram_family_evaluation_comp_path B WalkingArrow_cat C C1 walking_arrow_src D (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) D (@one_cat_diagram_family_reconstruction_to B C C1 D) (@one_cat_diagram_family_reconstruction_from B C C1 D))
      (@eq_sym (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@sym_transf_tapp0_transf B WalkingArrow_cat C D D (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) D) walking_arrow_src) (@id (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@fapp1_id_path (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src) D)))
    (@eq_trans (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@sym_transf_tapp0_transf B WalkingArrow_cat C D D (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) D (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) D (@one_cat_diagram_family_reconstruction_to B C C1 D) (@one_cat_diagram_family_reconstruction_from B C C1 D)) walking_arrow_tgt) (@id (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@sym_transf_tapp0_transf B WalkingArrow_cat C D D (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) D) walking_arrow_tgt)
      (@one_cat_diagram_family_evaluation_comp_path B WalkingArrow_cat C C1 walking_arrow_tgt D (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) D (@one_cat_diagram_family_reconstruction_to B C C1 D) (@one_cat_diagram_family_reconstruction_from B C C1 D))
      (@eq_sym (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@sym_transf_tapp0_transf B WalkingArrow_cat C D D (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) D) walking_arrow_tgt) (@id (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@fapp1_id_path (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_tgt) D)));

// Retain both original maps; equality fields certify laws, not operational casts.
symbol one_cat_diagram_family_reconstruction_evidence [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  : τ (IsoEvidence (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) D)
≔ Struct_sigma (@one_cat_diagram_family_reconstruction_to B C C1 D) (Struct_sigma (@one_cat_diagram_family_reconstruction_from B C C1 D)
    (Struct_sigma (@one_cat_diagram_family_reconstruction_left_law B C C1 D)
      (@one_cat_diagram_family_reconstruction_right_law B C C1 D)));
