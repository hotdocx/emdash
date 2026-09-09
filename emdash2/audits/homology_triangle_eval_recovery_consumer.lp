/* NON-LIBRARY recovered triangle consumer. This records the actual
   pre-op prototype and its constructor-visible nonidentity edge action.
   It is not a completed zero-complex category, whole H, or a claim of
   global consistency of the imported kernel. */
require open emdash.audits.homology_triangle_eval_rules_prototype;
require open emdash.emdash3_2_walking_arrow_introduction;
require open emdash.emdash3_2_dependent_simplex_native_dimensions;
require open emdash.emdash3_2_cubical_internalization;

/* Whole evaluation in a varying category, using existing displayed product
   and evaluation owners. No new naturality or evaluation law is assumed. */

symbol diagram_fibre_catd
  [K : Cat] (I : Cat) (E : τ (Catd K))
  : τ (Catd K)
≔ @Functor_catd K (@Const_catd (Op_cat K) I) E;

// Displayed constant argument: each diagram is paired with the fixed i.
symbol diagram_fibre_fixed_argument_funcd
  [K : Cat] (I : Cat) (E : τ (Catd K)) (i : τ (Obj I))
  : τ (Functord (@diagram_fibre_catd K I E) (@Const_catd K I))
≔ @section_weaken_funcd K
    (@diagram_fibre_catd K I E) (@Const_catd K I)
    (@Const_func K I i);

// ev_i : (k ↦ Functor(I,E[k])) ⇒ E, as an actual displayed functor.
symbol diagram_fibre_evaluation_funcd
  [K : Cat] (I : Cat) (E : τ (Catd K)) (i : τ (Obj I))
  : τ (Functord (@diagram_fibre_catd K I E) E)
≔ @comp_fapp0 (Catd_cat K)
    (@diagram_fibre_catd K I E)
    (@comp_cat_fapp0 K (Product_cat Cat_cat Cat_cat) Cat_cat
      (@uncurry_func Cat_cat Cat_cat Cat_cat Product_cat_func)
      (Struct_sigma (@diagram_fibre_catd K I E) (@Const_catd K I)))
    E
    (@Eval_funcd K I E)
    (@Product_pair_funcd K
      (@diagram_fibre_catd K I E)
      (@diagram_fibre_catd K I E) (@Const_catd K I)
      (@id_funcd K (@diagram_fibre_catd K I E))
      (@diagram_fibre_fixed_argument_funcd K I E i));

assert [K I : Cat] (E : τ (Catd K))
  (k : τ (Obj K)) (i : τ (Obj I))
  (D : τ (Functor I (Fibre_cat E k))) ⊢
  @fapp0 _ _
    (@tapp0_fapp0 K Cat_cat (@diagram_fibre_catd K I E) E k
      (@diagram_fibre_evaluation_funcd K I E i)) D
  ≡ @fapp0 I (Fibre_cat E k) D i;

/* Hybrid global triangle prototype: native outgoing paths, arrow diagrams,
   and the same opposite/Sigma variance used by the derived cubical total. */

// A ↦ Functor([1],PathOut_C(A)), contravariant in A.
symbol TriangleDiagram_catd (C : Cat) : τ (Catd (Op_cat C))
≔ @diagram_fibre_catd (Op_cat C) WalkingArrow_cat (@PathOut_cat_func C);

// Reverse fibre and base variance together, so initial vertices vary forward.
symbol TriangleDiagram_cat (C : Cat) : Cat
≔ Op_cat (@Sigma_cat (Op_cat C)
    (@Op_catd (Op_cat C) (@TriangleDiagram_catd C)));

// A constructor-visible object retains one source and one whole arrow diagram.
symbol triangle_diagram_obj
  [C : Cat] (A : τ (Obj C))
  (diagram : τ (Functor WalkingArrow_cat (@PathOut_cat C A)))
  : τ (Obj (@TriangleDiagram_cat C))
≔ Struct_sigma A diagram;

// Introduce the original native triangle through the existing arrow recursor.
symbol triangle_diagram_from_native
  [C : Cat] [A : τ (Obj C)]
  (edge : τ (Obj (@PathOut_cat C A)))
  (triangle : τ (Obj (@DependentSimplex2_cat C A edge)))
  : τ (Obj (@TriangleDiagram_cat C))
≔ @triangle_diagram_obj C A
    (@walking_arrow_func (@PathOut_cat C A)
      edge
      (@sigma_obj_base (@PathOut_cat C A)
        (@Rep_catd (@PathOut_cat C A) edge) triangle)
      (@sigma_obj_fibre (@PathOut_cat C A)
        (@Rep_catd (@PathOut_cat C A) edge) triangle));

// Whole initial-vertex observation, inherited from ordinary Sigma projection.
symbol triangle_diagram_initial_vertex_func
  (C : Cat)
  : τ (Functor (@TriangleDiagram_cat C) C)
≔ @Op_func
    (@Sigma_cat (Op_cat C)
      (@Op_catd (Op_cat C) (@TriangleDiagram_catd C)))
    (Op_cat C)
    (@Sigma_proj1_func (Op_cat C)
      (@Op_catd (Op_cat C) (@TriangleDiagram_catd C)));

// Retain the actual Functor_catd action owner in the reindexed diagram.
symbol triangle_diagram_reindex
  [C : Cat] [A0 A1 : τ (Obj C)] (a : τ (Hom C A0 A1))
  (T1 : τ (Functor WalkingArrow_cat (@PathOut_cat C A1)))
  : τ (Functor WalkingArrow_cat (@PathOut_cat C A0))
≔ @fapp0
    (Functor_cat WalkingArrow_cat (@PathOut_cat C A1))
    (Functor_cat WalkingArrow_cat (@PathOut_cat C A0))
    (@catd_transport_func (Op_cat C) (@TriangleDiagram_catd C) A1 A0 a)
    T1;

// An actual natural transformation after source reindexing is a total arrow.
// No extra componentwise square or prism equality is an input.
symbol triangle_diagram_arrow
  [C : Cat] [A0 A1 : τ (Obj C)]
  (T0 : τ (Functor WalkingArrow_cat (@PathOut_cat C A0)))
  (T1 : τ (Functor WalkingArrow_cat (@PathOut_cat C A1)))
  (a : τ (Hom C A0 A1))
  (eta : τ (@Transf WalkingArrow_cat (@PathOut_cat C A0) T0
    (@triangle_diagram_reindex C A0 A1 a T1)))
  : τ (Hom (@TriangleDiagram_cat C)
      (@triangle_diagram_obj C A0 T0) (@triangle_diagram_obj C A1 T1))
≔ @sigma_arrow (Op_cat C)
    (@Op_catd (Op_cat C) (@TriangleDiagram_catd C))
    A1 A0 T1 T0 a eta;

// Whole evaluation at either end of the internal arrow, including its source.
symbol triangle_diagram_edge_func
  (C : Cat) (i : τ (Obj WalkingArrow_cat))
  : τ (Functor (@TriangleDiagram_cat C) (@LaxArrow_cat C))
≔ @Op_func
    (@Sigma_cat (Op_cat C)
      (@Op_catd (Op_cat C) (@TriangleDiagram_catd C)))
    (@Sigma_cat (Op_cat C)
      (@Op_catd (Op_cat C) (@PathOut_cat_func C)))
    (@sigma_map_func (Op_cat C)
      (@Op_catd (Op_cat C) (@TriangleDiagram_catd C))
      (@Op_catd (Op_cat C) (@PathOut_cat_func C))
      (@Op_funcd (Op_cat C)
        (@TriangleDiagram_catd C) (@PathOut_cat_func C)
        (@diagram_fibre_evaluation_funcd (Op_cat C)
          WalkingArrow_cat (@PathOut_cat_func C) i)));

// The two other whole vertex observations are ordinary edge codomains.
symbol triangle_diagram_vertex_func
  (C : Cat) (i : τ (Obj WalkingArrow_cat))
  : τ (Functor (@TriangleDiagram_cat C) C)
≔ @comp_cat_fapp0 (@TriangleDiagram_cat C) (@LaxArrow_cat C) C
    (@homdc_total_target_func C C (@hom_int C C (@id_func C)))
    (@triangle_diagram_edge_func C i);

/* Nonidentity action of the whole varying triangle edge observation. */

// Native-typed observation avoids comparing inferred Hom(Σ) and Hom(Op Σ)
// before their endpoint reversal; it introduces no computation rule.
symbol triangle_diagram_expected_edge_arrow
  [C : Cat] [A0 A1 : τ (Obj C)]
  (T0 : τ (Functor WalkingArrow_cat (@PathOut_cat C A0)))
  (T1 : τ (Functor WalkingArrow_cat (@PathOut_cat C A1)))
  (a : τ (Hom C A0 A1))
  (eta : τ (@Transf WalkingArrow_cat (@PathOut_cat C A0) T0
    (@triangle_diagram_reindex C A0 A1 a T1)))
  (i : τ (Obj WalkingArrow_cat))
  : τ (Hom (@LaxArrow_cat C)
      (@fapp0 _ _ (@triangle_diagram_edge_func C i) (@triangle_diagram_obj C A0 T0))
      (@fapp0 _ _ (@triangle_diagram_edge_func C i) (@triangle_diagram_obj C A1 T1)))
≔ @sigma_arrow (Op_cat C)
    (@Op_catd (Op_cat C) (@PathOut_cat_func C)) A1 A0
    (@fapp0 WalkingArrow_cat (@PathOut_cat C A1) T1 i)
    (@fapp0 WalkingArrow_cat (@PathOut_cat C A0) T0 i)
    a
    (@tapp0_fapp0 WalkingArrow_cat (@PathOut_cat C A0) T0
      (@triangle_diagram_reindex C A0 A1 a T1)
      i eta);

assert
  [C : Cat] [A0 A1 : τ (Obj C)]
  (T0 : τ (Functor WalkingArrow_cat (@PathOut_cat C A0)))
  (T1 : τ (Functor WalkingArrow_cat (@PathOut_cat C A1)))
  (a : τ (Hom C A0 A1))
  (eta : τ (@Transf WalkingArrow_cat (@PathOut_cat C A0) T0
    (@triangle_diagram_reindex C A0 A1 a T1)))
  (i : τ (Obj WalkingArrow_cat)) ⊢
  @fapp1_fapp0 (@TriangleDiagram_cat C) (@LaxArrow_cat C)
    (@triangle_diagram_edge_func C i)
    (@triangle_diagram_obj C A0 T0) (@triangle_diagram_obj C A1 T1)
    (@triangle_diagram_arrow C A0 A1 T0 T1 a eta)
  ≡ @triangle_diagram_expected_edge_arrow C A0 A1 T0 T1 a eta i;

// Raw composition remains a usable proof-time view of this same reindexing.
assert [C : Cat] [A0 A1 : τ (Obj C)]
  (a : τ (Hom C A0 A1))
  (T1 : τ (Functor WalkingArrow_cat (@PathOut_cat C A1))) ⊢
  @eq_refl (Functor WalkingArrow_cat (@PathOut_cat C A0))
    (@triangle_diagram_reindex C A0 A1 a T1)
  : τ (@= (Functor WalkingArrow_cat (@PathOut_cat C A0))
      (@triangle_diagram_reindex C A0 A1 a T1)
      (@comp_cat_fapp0 WalkingArrow_cat
        (@PathOut_cat C A1) (@PathOut_cat C A0)
        (@PathOut_transport_func C A0 A1 a) T1));
