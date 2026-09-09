/* Existing native represented-comma/zero-arrow-cone construction.
   Objects and directed Homs are unchanged; the qualified whole observation
   is introduced separately, only for an explicitly one-categorical target. */
require open emdash.emdash3_2_cubical_internalization;
require open emdash.emdash3_2_zero_arrow_diagrams;

// Hom_B(F[-],-), with the first coordinate contravariant as required by homdc.
symbol represented_comma_prof [A B : Cat] (F : τ (Functor A B))
  : τ (Functor (Op_cat A) (@Catd_cat B))
≔ @comp_cat_fapp0 (Op_cat A) (Op_cat B) (@Catd_cat B)
    (@hom_int B B (@id_func B)) (@Op_func A B F);

symbol RepresentedComma_cat [A B : Cat] (F : τ (Functor A B)) : Cat
≔ @homdc_total_cat A B (@represented_comma_prof A B F);

symbol represented_comma_obj [A B : Cat] [F : τ (Functor A B)]
  (a : τ (Obj A)) (b : τ (Obj B)) (h : τ (Hom B (@fapp0 A B F a) b))
  : τ (Obj (@RepresentedComma_cat A B F))
≔ @homdc_total_obj A B (@represented_comma_prof A B F) a b h;

symbol represented_comma_source_func [A B : Cat] (F : τ (Functor A B))
  : τ (Functor (@RepresentedComma_cat A B F) A)
≔ @homdc_total_source_func A B (@represented_comma_prof A B F);

symbol represented_comma_target_func [A B : Cat] (F : τ (Functor A B))
  : τ (Functor (@RepresentedComma_cat A B F) B)
≔ @homdc_total_target_func A B (@represented_comma_prof A B F);

// The zero-cone's datum is an actual transformation J(A)⇒d of arrow diagrams.
symbol ZeroArrowCone_cat [C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t)) : Cat
≔ @RepresentedComma_cat C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T);

symbol zero_arrow_cone_obj [C : Cat] [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  (A : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) d))
  : τ (Obj (@ZeroArrowCone_cat C t T))
≔ @represented_comma_obj C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A d h;

symbol zero_arrow_cone_first_func [C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  : τ (Functor (@ZeroArrowCone_cat C t T) C)
≔ @represented_comma_source_func C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T);

symbol zero_arrow_cone_diagram_func [C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  : τ (Functor (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C))
≔ @represented_comma_target_func C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T);

// Both other vertices are whole evaluations of the retained diagram.
symbol zero_arrow_cone_vertex_func [C : Cat] [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (i : τ (Obj WalkingArrow_cat))
  : τ (Functor (@ZeroArrowCone_cat C t T) C)
≔ @diagram_family_at_func (@ZeroArrowCone_cat C t T) WalkingArrow_cat C
    (@zero_arrow_cone_diagram_func C t T) i;

// The outgoing differential is a whole transformation over the comma category.
symbol zero_arrow_cone_differential_transf [C : Cat] [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  : τ (@Transf (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_vertex_func C t T walking_arrow_src)
    (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt))
≔ @diagram_family_transf (@ZeroArrowCone_cat C t T) WalkingArrow_cat C
    (@zero_arrow_cone_diagram_func C t T) walking_arrow_src walking_arrow_tgt walking_arrow_generator;
