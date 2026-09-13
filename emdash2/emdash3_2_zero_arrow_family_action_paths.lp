/* Whole source/target observations of the existing zero-arrow embeddings.
   The only new comparison is sufficient congruence of whole evaluation.
   Runtime computation belongs to the introduced-arrow owner. */
require open emdash.emdash3_2;
require open emdash.emdash3_2_arrow_diagram_families;
require open emdash.emdash3_2_zero_arrow_diagrams;

// Proof-time sufficient congruence of the same whole evaluation projection.
// Compare every index, family and transformation; no data is erased.
unif_rule @sym_transf_tapp0_transf $B $I $C $F $G $h $i
  ≡ @sym_transf_tapp0_transf $B0 $I0 $C0 $F0 $G0 $h0 $i0
  ↪ [ $B ≡ $B0; $I ≡ $I0; $C ≡ $C0; $F ≡ $F0;
      $G ≡ $G0; $h ≡ $h0; $i ≡ $i0 ];

// Generic Hom action of a composite, used only by the two embedding observations.
protected symbol zero_arrow_family_comp_hom_path [A B C : Cat] (F : τ (Functor B C)) (G : τ (Functor A B))
  (x y : τ (Obj A))
  : τ (@= (Functor (Hom_cat A x y)
      (Hom_cat C (@fapp0 A C (@comp_cat_fapp0 A B C F G) x) (@fapp0 A C (@comp_cat_fapp0 A B C F G) y)))
      (@fapp1_func A C (@comp_cat_fapp0 A B C F G) x y)
      (@comp_cat_fapp0 (Hom_cat A x y)
        (Hom_cat B (@fapp0 A B G x) (@fapp0 A B G y))
        (Hom_cat C (@fapp0 B C F (@fapp0 A B G x)) (@fapp0 B C F (@fapp0 A B G y)))
        (@fapp1_func B C F (@fapp0 A B G x) (@fapp0 A B G y)) (@fapp1_func A B G x y)))
≔ eq_refl (@fapp1_func A C (@comp_cat_fapp0 A B C F G) x y);

// E₀(J∗k)=k as a whole transformation; the parent family retains its raw view.
symbol terminal_arrow_family_action_source_path [B C : Cat]
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (A D : τ (Functor B C)) (k : τ (@Transf B C A D))
  : τ (@= (@Transf B C A D) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
    WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) D) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
    WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
    T)) A D k) walking_arrow_src) k)
≔ @eq_sym (@Transf B C A D) k (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) D) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat
  C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A D k)
  walking_arrow_src)
    (@eq_ap (Functor (@Transf_cat B C A D) (@Transf_cat B C A D)) (@Transf B C A D)
      (λ H : τ (Functor (@Transf_cat B C A D) (@Transf_cat B C A D)), @fapp0 (@Transf_cat B C A D) (@Transf_cat B C A
        D) H k)
      (@fapp1_func (Functor_cat B C) (Functor_cat B C) (@comp_cat_fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
        WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B WalkingArrow_cat C
        walking_arrow_src) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
        T))) A D) (@comp_cat_fapp0 (@Transf_cat B C A D) (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C))
        (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C
        (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A) (@fapp0 (Functor_cat B C)
        (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T)) D)) (@Transf_cat B C A D) (@fapp1_func (Functor_cat B (Functor_cat
        WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B WalkingArrow_cat C
        walking_arrow_src) (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C))
        (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A) (@fapp0
        (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
        WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) D)) (@fapp1_func (Functor_cat B C) (Functor_cat B
        (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T)) A D))
      (@zero_arrow_family_comp_hom_path (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C))
        (Functor_cat B C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src) (@comp_cat_cov_func
        B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A D));

// E₁(I∗k)=k, the dual whole observation of the same introduced-arrow computation.
symbol initial_arrow_family_action_target_path [B C : Cat]
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (A D : τ (Functor B C)) (k : τ (@Transf B C A D))
  : τ (@= (@Transf B C A D) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
    WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) A) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@initial_arrow_diagram_func C t T) D) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
    WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T))
    A D k) walking_arrow_tgt) k)
≔ @eq_sym (@Transf B C A D) k (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) A) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T) D) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat
  C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T)) A D k)
  walking_arrow_tgt)
    (@eq_ap (Functor (@Transf_cat B C A D) (@Transf_cat B C A D)) (@Transf B C A D)
      (λ H : τ (Functor (@Transf_cat B C A D) (@Transf_cat B C A D)), @fapp0 (@Transf_cat B C A D) (@Transf_cat B C A
        D) H k)
      (@fapp1_func (Functor_cat B C) (Functor_cat B C) (@comp_cat_fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
        WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B WalkingArrow_cat C
        walking_arrow_tgt) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t
        T))) A D) (@comp_cat_fapp0 (@Transf_cat B C A D) (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C))
        (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C
        (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T)) A) (@fapp0 (Functor_cat B C)
        (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
        (@initial_arrow_diagram_func C t T)) D)) (@Transf_cat B C A D) (@fapp1_func (Functor_cat B (Functor_cat
        WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B WalkingArrow_cat C
        walking_arrow_tgt) (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C))
        (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T)) A) (@fapp0
        (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
        WalkingArrow_cat C) (@initial_arrow_diagram_func C t T)) D)) (@fapp1_func (Functor_cat B C) (Functor_cat B
        (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
        (@initial_arrow_diagram_func C t T)) A D))
      (@zero_arrow_family_comp_hom_path (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C))
        (Functor_cat B C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_tgt) (@comp_cat_cov_func
        B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T)) A D));
