/*
  Whole structural transformations and their homology-map factors.
  Whisker the actual kernel inclusion and cokernel projection along the
  diagram and boundary families. Their naturality supplies the existing
  Hom factors, with the actual record fields as endpoints. Higher action
  remains that of genuine whole transformations. The equality paths use
  the current globally strict profile, not arbitrary laxity erasure.
*/
require open emdash.emdash3_2_homology_family_records;

// Whisker the existing whole kernel inclusion along the diagram family.
symbol kernel_family_inclusion_transf
  [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  : τ (@Transf B C (@kernel_family_func B C S t T W P D) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) D))
≔ @fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@kernel_presentation_func C S t T W P)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src))
    (@kernel_presentation_inclusion C S t T W P);

// Whisker the existing whole cokernel projection along the boundary family.
symbol homology_family_projection_transf
  [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  : τ (@Transf B C (@kernel_family_func B C S t T W P D) (@homology_family_func B C S t T T0 W V P Q A D h))
≔ @fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@kernel_family_boundary_diagram_func B C S t T W P A D
  h) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@cokernel_presentation_func C S t T0 V Q))
    (@cokernel_presentation_projection C S t T0 V Q);

// These equations are ordinary strict-profile naturality, not new runtime laws.
symbol kernel_family_inclusion_naturality
  [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  [x y : τ (Obj B)] (p : τ (Hom B x y))
  : τ (@= (Hom C (@fapp0 B C (@kernel_family_func B C S t T W P D) x) (@fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat
    C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) D) y))
      (@comp_fapp0 C _ _ _
        (@fapp1_fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
          walking_arrow_src) D) x y p) (@tapp0_fapp0 B C (@kernel_family_func B C S t T W P D) (@comp_cat_fapp0 B (Functor_cat
          WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) D) x
          (@kernel_family_inclusion_transf B C S t T W P D)))
      (@comp_fapp0 C _ _ _
        (@tapp0_fapp0 B C (@kernel_family_func B C S t T W P D) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
          (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) D) y (@kernel_family_inclusion_transf B C S t T W P D))
          (@fapp1_fapp0 B C (@kernel_family_func B C S t T W P D) x y p)))
≔ @strict_component_naturality_path B C (@kernel_family_func B C S t T W P D) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) D) (@kernel_family_inclusion_transf B C S t T W P D) x y p;

symbol homology_family_projection_naturality
  [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  [x y : τ (Obj B)] (p : τ (Hom B x y))
  : τ (@= (Hom C (@fapp0 B C (@kernel_family_func B C S t T W P D) x) (@fapp0 B C (@homology_family_func B C S t T T0 W V P Q A D h)
    y))
      (@comp_fapp0 C _ _ _
        (@fapp1_fapp0 B C (@homology_family_func B C S t T T0 W V P Q A D h) x y p) (@tapp0_fapp0 B C (@kernel_family_func B C S t T
          W P D) (@homology_family_func B C S t T T0 W V P Q A D h) x (@homology_family_projection_transf B C S t T T0 W V P Q A D
          h)))
      (@comp_fapp0 C _ _ _
        (@tapp0_fapp0 B C (@kernel_family_func B C S t T W P D) (@homology_family_func B C S t T T0 W V P Q A D h) y
          (@homology_family_projection_transf B C S t T T0 W V P Q A D h)) (@fapp1_fapp0 B C (@kernel_family_func B C S t T W P D) x
          y p)))
≔ @strict_component_naturality_path B C (@kernel_family_func B C S t T W P D) (@homology_family_func B C S t T T0 W V P Q A D h)
  (@homology_family_projection_transf B C S t T T0 W V P Q A D h) x y p;

// Whole H action reconstructs after the original quotient, without choosing a raw map.
symbol homology_family_record_map_factor
  [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  [x y : τ (Obj B)] (p : τ (Hom B x y))
  : τ (@HomPrecompFactor C (@homology_record_cycle_object C S (@fapp0 B C A x) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat
    WalkingArrow_cat C) D x) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D x)
    walking_arrow_tgt) (@homology_family_pair B C S t T A D h x) (@homology_family_record B C S t T T0 W V P Q A D h x))
    (@homology_record_object C S (@fapp0 B C A x) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D x)
    walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D x) walking_arrow_tgt)
    (@homology_family_pair B C S t T A D h x) (@homology_family_record B C S t T T0 W V P Q A D h x)) (@homology_record_object C S
    (@fapp0 B C A y) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D y) walking_arrow_src) (@fapp0
    WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D y) walking_arrow_tgt) (@homology_family_pair B C S t T A D h y)
    (@homology_family_record B C S t T T0 W V P Q A D h y))
      (@homology_record_projection C S (@fapp0 B C A x) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D x)
        walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D x) walking_arrow_tgt)
        (@homology_family_pair B C S t T A D h x) (@homology_family_record B C S t T T0 W V P Q A D h x)) (@comp_fapp0 C
        (@homology_record_cycle_object C S (@fapp0 B C A x) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D
        x) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D x) walking_arrow_tgt)
        (@homology_family_pair B C S t T A D h x) (@homology_family_record B C S t T T0 W V P Q A D h x))
        (@homology_record_cycle_object C S (@fapp0 B C A y) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D
        y) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D y) walking_arrow_tgt)
        (@homology_family_pair B C S t T A D h y) (@homology_family_record B C S t T T0 W V P Q A D h y)) (@homology_record_object C
        S (@fapp0 B C A y) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D y) walking_arrow_src) (@fapp0
        WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D y) walking_arrow_tgt) (@homology_family_pair B C S t T A D h
        y) (@homology_family_record B C S t T T0 W V P Q A D h y)) (@homology_record_projection C S (@fapp0 B C A y) (@fapp0
        WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D y) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B
        (Functor_cat WalkingArrow_cat C) D y) walking_arrow_tgt) (@homology_family_pair B C S t T A D h y) (@homology_family_record
        B C S t T T0 W V P Q A D h y)) (@fapp1_fapp0 B C (@kernel_family_func B C S t T W P D) x y p)))
≔ @hom_precomp_factor_intro C (@homology_record_cycle_object C S (@fapp0 B C A x) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat
  WalkingArrow_cat C) D x) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_tgt) (@homology_family_pair B C S t T A D h x) (@homology_family_record B C S t T T0 W V P Q A D h x))
  (@homology_record_object C S (@fapp0 B C A x) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D x) walking_arrow_tgt)
  (@homology_family_pair B C S t T A D h x) (@homology_family_record B C S t T T0 W V P Q A D h x)) (@homology_record_object C S
  (@fapp0 B C A y) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D y) walking_arrow_src) (@fapp0
  WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D y) walking_arrow_tgt) (@homology_family_pair B C S t T A D h y)
  (@homology_family_record B C S t T T0 W V P Q A D h y))
    (@homology_record_projection C S (@fapp0 B C A x) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D x)
      walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D x) walking_arrow_tgt)
      (@homology_family_pair B C S t T A D h x) (@homology_family_record B C S t T T0 W V P Q A D h x)) (@comp_fapp0 C
      (@homology_record_cycle_object C S (@fapp0 B C A x) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D x)
      walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D x) walking_arrow_tgt)
      (@homology_family_pair B C S t T A D h x) (@homology_family_record B C S t T T0 W V P Q A D h x))
      (@homology_record_cycle_object C S (@fapp0 B C A y) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D y)
      walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D y) walking_arrow_tgt)
      (@homology_family_pair B C S t T A D h y) (@homology_family_record B C S t T T0 W V P Q A D h y)) (@homology_record_object C S
      (@fapp0 B C A y) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D y) walking_arrow_src) (@fapp0
      WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D y) walking_arrow_tgt) (@homology_family_pair B C S t T A D h
      y) (@homology_family_record B C S t T T0 W V P Q A D h y)) (@homology_record_projection C S (@fapp0 B C A y) (@fapp0
      WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D y) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B
      (Functor_cat WalkingArrow_cat C) D y) walking_arrow_tgt) (@homology_family_pair B C S t T A D h y) (@homology_family_record B
      C S t T T0 W V P Q A D h y)) (@fapp1_fapp0 B C (@kernel_family_func B C S t T W P D) x y p))
    (@fapp1_fapp0 B C (@homology_family_func B C S t T T0 W V P Q A D h) x y p) (@homology_family_projection_naturality B C S t T T0
      W V P Q A D h x y p);

symbol homology_family_record_cycle_factor
  [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  [x y : τ (Obj B)] (p : τ (Hom B x y))
  : τ (@HomPostcompFactor C (@homology_record_cycle_object C S (@fapp0 B C A y) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat
    WalkingArrow_cat C) D y) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D y)
    walking_arrow_tgt) (@homology_family_pair B C S t T A D h y) (@homology_family_record B C S t T T0 W V P Q A D h y)) (@fapp0 B C
    (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) D) y)
    (@homology_record_cycle_object C S (@fapp0 B C A x) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D x)
    walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D x) walking_arrow_tgt)
    (@homology_family_pair B C S t T A D h x) (@homology_family_record B C S t T T0 W V P Q A D h x))
      (@homology_record_cycle_embedding C S (@fapp0 B C A y) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D
        y) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D y) walking_arrow_tgt)
        (@homology_family_pair B C S t T A D h y) (@homology_family_record B C S t T T0 W V P Q A D h y)) (@comp_fapp0 C
        (@homology_record_cycle_object C S (@fapp0 B C A x) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D
        x) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D x) walking_arrow_tgt)
        (@homology_family_pair B C S t T A D h x) (@homology_family_record B C S t T T0 W V P Q A D h x)) (@fapp0 B C
        (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) D)
        x) (@fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
        walking_arrow_src) D) y) (@fapp1_fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
        (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) D) x y p) (@homology_record_cycle_embedding C S (@fapp0 B
        C A x) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D x) walking_arrow_src) (@fapp0
        WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D x) walking_arrow_tgt) (@homology_family_pair B C S t T A D h
        x) (@homology_family_record B C S t T T0 W V P Q A D h x))))
≔ @hom_postcomp_factor_intro C (@homology_record_cycle_object C S (@fapp0 B C A y) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat
  WalkingArrow_cat C) D y) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D y)
  walking_arrow_tgt) (@homology_family_pair B C S t T A D h y) (@homology_family_record B C S t T T0 W V P Q A D h y)) (@fapp0 B C
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) D) y)
  (@homology_record_cycle_object C S (@fapp0 B C A x) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D x) walking_arrow_tgt)
  (@homology_family_pair B C S t T A D h x) (@homology_family_record B C S t T T0 W V P Q A D h x))
    (@homology_record_cycle_embedding C S (@fapp0 B C A y) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D
      y) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D y) walking_arrow_tgt)
      (@homology_family_pair B C S t T A D h y) (@homology_family_record B C S t T T0 W V P Q A D h y)) (@comp_fapp0 C
      (@homology_record_cycle_object C S (@fapp0 B C A x) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D x)
      walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D x) walking_arrow_tgt)
      (@homology_family_pair B C S t T A D h x) (@homology_family_record B C S t T T0 W V P Q A D h x)) (@fapp0 B C (@comp_cat_fapp0
      B (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) D) x) (@fapp0 B C
      (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) D) y)
      (@fapp1_fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
      walking_arrow_src) D) x y p) (@homology_record_cycle_embedding C S (@fapp0 B C A x) (@fapp0 WalkingArrow_cat C (@fapp0 B
      (Functor_cat WalkingArrow_cat C) D x) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C)
      D x) walking_arrow_tgt) (@homology_family_pair B C S t T A D h x) (@homology_family_record B C S t T T0 W V P Q A D h x)))
    (@fapp1_fapp0 B C (@kernel_family_func B C S t T W P D) x y p) (@eq_sym _ _ _ (@kernel_family_inclusion_naturality B C S t T W P
      D x y p));
