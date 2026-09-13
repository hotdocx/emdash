/* Whole native observation of walking-arrow diagrams.
   The existing evaluation transformation has an existing native arrow graph.
   This defined functor retains its complete action; no diagram inverse or
   faithfulness law is asserted here. The ordinary realization functor is
   separately owned by one_cat_arrow_diagrams. */
require open emdash.emdash3_2_gray_transformation_graph;
require open emdash.emdash3_2_diagram_evaluation;

// The actual evaluation transformation, observed as a native arrow graph.
symbol diagram_native_arrow_func [C : Cat]
  : τ (Functor (Functor_cat WalkingArrow_cat C) (@LaxArrow_cat C))
≔ @gray_transf_graph_func (Functor_cat WalkingArrow_cat C) C
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
    (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator);
