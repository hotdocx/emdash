/*
  Constructive ordinal dependent simplex in dimension four.

  The identity join Delta[4] = Delta[3] * 1 supplies one generic shaped
  outgoing-path comparison.  Iterating pathout_transf_lift at the canonical
  source edge and triangle makes its component at the canonical source
  tetrahedron into the fourth-level cell.  Pairing that component with its
  endpoints gives one native DependentSimplex4 object; the existing map and
  intrinsic FaceCode actions give the observation in every target category
  and all five tetrahedral faces.

  No opaque filler, endpoint normalization, broad Sigma eta, runtime rule, or
  proof-time unifier is introduced here.  Native projections and code-selected
  cofaces remain parallel whole presentations until a later mapping-category
  comparison is justified.
*/

require open emdash.emdash3_2_ordinal_join_pathout_successor;
require open emdash.emdash3_2_dependent_simplex_ordinal_dimension3;
require open emdash.emdash3_2_dependent_simplex_dimension4;

symbol ordinal_simplex4_source_cat : Cat
≔ ordinal_simplex3_target_cat;

symbol ordinal_simplex4_target_cat : Cat
≔ @ordinal_join_target_cat ordinal_simplex4_source_cat;

symbol ordinal_simplex4_source_x0 : τ (Obj ordinal_simplex4_source_cat)
≔ ordinal_simplex3_y0;

symbol ordinal_simplex4_source_e01
  : τ (Obj (@PathOut_cat ordinal_simplex4_source_cat ordinal_simplex4_source_x0))
≔ ordinal_simplex3_e01;

symbol ordinal_simplex4_source_t012
  : τ (Obj (@PathOut_cat
      (@PathOut_cat ordinal_simplex4_source_cat ordinal_simplex4_source_x0)
      ordinal_simplex4_source_e01))
≔ ordinal_simplex3_face012_obj;

symbol ordinal_simplex4_source_s0123
  : τ (Obj (@PathOut_cat
      (@PathOut_cat
        (@PathOut_cat ordinal_simplex4_source_cat ordinal_simplex4_source_x0)
        ordinal_simplex4_source_e01)
      ordinal_simplex4_source_t012))
≔ ordinal_dependent_simplex3_source;

// First shaped comparison: edges of Delta[3] map to edges of Delta[4].
symbol ordinal_simplex4_source_level1 : Cat
≔ @PathOut_cat ordinal_simplex4_source_cat ordinal_simplex4_source_x0;

symbol ordinal_simplex4_target_y0 : τ (Obj ordinal_simplex4_target_cat)
≔ @ordinal_join_target_base ordinal_simplex4_source_cat ordinal_simplex4_source_x0;

symbol ordinal_simplex4_target_level1 : Cat
≔ @PathOut_cat ordinal_simplex4_target_cat ordinal_simplex4_target_y0;

symbol ordinal_simplex4_left1
  : τ (Functor ordinal_simplex4_source_level1 ordinal_simplex4_target_level1)
≔ @ordinal_join_observed_pathout
    ordinal_simplex4_source_cat ordinal_simplex4_source_x0;

symbol ordinal_simplex4_right1
  : τ (Functor ordinal_simplex4_source_level1 ordinal_simplex4_target_level1)
≔ @ordinal_join_primitive_pathout
    ordinal_simplex4_source_cat ordinal_simplex4_source_x0;

symbol ordinal_simplex4_epsilon1
  : τ (Transf ordinal_simplex4_left1 ordinal_simplex4_right1)
≔ @ordinal_join_pathout_transf
    ordinal_simplex4_source_cat ordinal_simplex4_source_x0;

// Lift at the canonical source edge.
symbol ordinal_simplex4_source_level2 : Cat
≔ @PathOut_cat ordinal_simplex4_source_level1 ordinal_simplex4_source_e01;

symbol ordinal_simplex4_target_e01 : τ (Obj ordinal_simplex4_target_level1)
≔ @fapp0
    ordinal_simplex4_source_level1 ordinal_simplex4_target_level1
    ordinal_simplex4_left1 ordinal_simplex4_source_e01;

symbol ordinal_simplex4_target_level2 : Cat
≔ @PathOut_cat ordinal_simplex4_target_level1 ordinal_simplex4_target_e01;

symbol ordinal_simplex4_left2
  : τ (Functor ordinal_simplex4_source_level2 ordinal_simplex4_target_level2)
≔ @pathout_map_func
    ordinal_simplex4_source_level1 ordinal_simplex4_target_level1
    ordinal_simplex4_left1 ordinal_simplex4_source_e01;

symbol ordinal_simplex4_right2
  : τ (Functor ordinal_simplex4_source_level2 ordinal_simplex4_target_level2)
≔ @pathout_transf_target_func
    ordinal_simplex4_source_level1 ordinal_simplex4_target_level1
    ordinal_simplex4_left1 ordinal_simplex4_right1 ordinal_simplex4_epsilon1
    ordinal_simplex4_source_e01;

symbol ordinal_simplex4_epsilon2
  : τ (Transf ordinal_simplex4_left2 ordinal_simplex4_right2)
≔ @pathout_transf_lift
    ordinal_simplex4_source_level1 ordinal_simplex4_target_level1
    ordinal_simplex4_left1 ordinal_simplex4_right1 ordinal_simplex4_epsilon1
    ordinal_simplex4_source_e01;

// Lift again at the canonical source triangle.
symbol ordinal_simplex4_source_level3 : Cat
≔ @PathOut_cat ordinal_simplex4_source_level2 ordinal_simplex4_source_t012;

symbol ordinal_simplex4_target_t012 : τ (Obj ordinal_simplex4_target_level2)
≔ @fapp0
    ordinal_simplex4_source_level2 ordinal_simplex4_target_level2
    ordinal_simplex4_left2 ordinal_simplex4_source_t012;

symbol ordinal_simplex4_target_level3 : Cat
≔ @PathOut_cat ordinal_simplex4_target_level2 ordinal_simplex4_target_t012;

symbol ordinal_simplex4_left3
  : τ (Functor ordinal_simplex4_source_level3 ordinal_simplex4_target_level3)
≔ @pathout_map_func
    ordinal_simplex4_source_level2 ordinal_simplex4_target_level2
    ordinal_simplex4_left2 ordinal_simplex4_source_t012;

symbol ordinal_simplex4_right3
  : τ (Functor ordinal_simplex4_source_level3 ordinal_simplex4_target_level3)
≔ @pathout_transf_target_func
    ordinal_simplex4_source_level2 ordinal_simplex4_target_level2
    ordinal_simplex4_left2 ordinal_simplex4_right2 ordinal_simplex4_epsilon2
    ordinal_simplex4_source_t012;

symbol ordinal_simplex4_epsilon3
  : τ (Transf ordinal_simplex4_left3 ordinal_simplex4_right3)
≔ @pathout_transf_lift
    ordinal_simplex4_source_level2 ordinal_simplex4_target_level2
    ordinal_simplex4_left2 ordinal_simplex4_right2 ordinal_simplex4_epsilon2
    ordinal_simplex4_source_t012;

// The component at the canonical source tetrahedron is the fourth-level cell.
symbol ordinal_simplex4_target_s0123 : τ (Obj ordinal_simplex4_target_level3)
≔ @fapp0
    ordinal_simplex4_source_level3 ordinal_simplex4_target_level3
    ordinal_simplex4_left3 ordinal_simplex4_source_s0123;

symbol ordinal_simplex4_target_s0124 : τ (Obj ordinal_simplex4_target_level3)
≔ @fapp0
    ordinal_simplex4_source_level3 ordinal_simplex4_target_level3
    ordinal_simplex4_right3 ordinal_simplex4_source_s0123;

symbol ordinal_simplex4_omega
  : τ (Hom ordinal_simplex4_target_level3
      ordinal_simplex4_target_s0123 ordinal_simplex4_target_s0124)
≔ @tapp0_fapp0
    ordinal_simplex4_source_level3 ordinal_simplex4_target_level3
    ordinal_simplex4_left3 ordinal_simplex4_right3
    ordinal_simplex4_source_s0123 ordinal_simplex4_epsilon3;

symbol ordinal_dependent_simplex4_source
  : τ (Obj (@PathOut_cat
      ordinal_simplex4_target_level3 ordinal_simplex4_target_s0123))
≔ @pathout_obj
    ordinal_simplex4_target_level3 ordinal_simplex4_target_s0123
    ordinal_simplex4_target_s0124 ordinal_simplex4_omega;

// One further hom action remains available after the fourth-level component.
symbol ordinal_simplex4_top_next_action
  (u v : τ (Obj ordinal_simplex4_source_level3))
  : τ (Functor
      (Hom_cat ordinal_simplex4_source_level3 u v)
      (Hom_cat ordinal_simplex4_target_level3
        (@fapp0
          ordinal_simplex4_source_level3 ordinal_simplex4_target_level3
          ordinal_simplex4_left3 u)
        (@fapp0
          ordinal_simplex4_source_level3 ordinal_simplex4_target_level3
          ordinal_simplex4_right3 v)))
≔ @tapp1_func
    ordinal_simplex4_source_level3 ordinal_simplex4_target_level3
    ordinal_simplex4_left3 ordinal_simplex4_right3 u v
    ordinal_simplex4_epsilon3;

// Map the one source under an arbitrary H : Delta[4] -> C.
symbol ordinal_dependent_simplex4_x0
  [C : Cat]
  (H : τ (Functor ordinal_simplex4_target_cat C))
  : τ (Obj C)
≔ @fapp0 ordinal_simplex4_target_cat C H ordinal_simplex4_target_y0;

symbol ordinal_dependent_simplex4_e01
  [C : Cat]
  (H : τ (Functor ordinal_simplex4_target_cat C))
  : τ (Obj (@DependentSimplex1_cat C (@ordinal_dependent_simplex4_x0 C H)))
≔ @fapp0
    (@DependentSimplex1_cat ordinal_simplex4_target_cat ordinal_simplex4_target_y0)
    (@DependentSimplex1_cat C (@ordinal_dependent_simplex4_x0 C H))
    (@dependent_simplex1_map
      ordinal_simplex4_target_cat C H ordinal_simplex4_target_y0)
    ordinal_simplex4_target_e01;

symbol ordinal_dependent_simplex4_t012
  [C : Cat]
  (H : τ (Functor ordinal_simplex4_target_cat C))
  : τ (Obj (@DependentSimplex2_cat
      C (@ordinal_dependent_simplex4_x0 C H) (@ordinal_dependent_simplex4_e01 C H)))
≔ @fapp0
    (@DependentSimplex2_cat
      ordinal_simplex4_target_cat ordinal_simplex4_target_y0 ordinal_simplex4_target_e01)
    (@DependentSimplex2_cat
      C (@ordinal_dependent_simplex4_x0 C H) (@ordinal_dependent_simplex4_e01 C H))
    (@dependent_simplex2_map
      ordinal_simplex4_target_cat C H
      ordinal_simplex4_target_y0 ordinal_simplex4_target_e01)
    ordinal_simplex4_target_t012;

symbol ordinal_dependent_simplex4_s0123
  [C : Cat]
  (H : τ (Functor ordinal_simplex4_target_cat C))
  : τ (Obj (@DependentSimplex3_cat
      C (@ordinal_dependent_simplex4_x0 C H) (@ordinal_dependent_simplex4_e01 C H)
      (@ordinal_dependent_simplex4_t012 C H)))
≔ @fapp0
    (@DependentSimplex3_cat
      ordinal_simplex4_target_cat ordinal_simplex4_target_y0
      ordinal_simplex4_target_e01 ordinal_simplex4_target_t012)
    (@DependentSimplex3_cat
      C (@ordinal_dependent_simplex4_x0 C H) (@ordinal_dependent_simplex4_e01 C H)
      (@ordinal_dependent_simplex4_t012 C H))
    (@dependent_simplex3_map
      ordinal_simplex4_target_cat C H
      ordinal_simplex4_target_y0 ordinal_simplex4_target_e01 ordinal_simplex4_target_t012)
    ordinal_simplex4_target_s0123;

symbol ordinal_dependent_simplex4_map
  [C : Cat]
  (H : τ (Functor ordinal_simplex4_target_cat C))
  : τ (Functor
      (@DependentSimplex4_cat
        ordinal_simplex4_target_cat ordinal_simplex4_target_y0
        ordinal_simplex4_target_e01 ordinal_simplex4_target_t012 ordinal_simplex4_target_s0123)
      (@DependentSimplex4_cat
        C (@ordinal_dependent_simplex4_x0 C H) (@ordinal_dependent_simplex4_e01 C H)
        (@ordinal_dependent_simplex4_t012 C H) (@ordinal_dependent_simplex4_s0123 C H)))
≔ @dependent_simplex4_map
    ordinal_simplex4_target_cat C H
    ordinal_simplex4_target_y0 ordinal_simplex4_target_e01
    ordinal_simplex4_target_t012 ordinal_simplex4_target_s0123;

symbol ordinal_dependent_simplex4_observation
  [C : Cat]
  (H : τ (Functor ordinal_simplex4_target_cat C))
  : τ (Obj (@DependentSimplex4_cat
      C (@ordinal_dependent_simplex4_x0 C H) (@ordinal_dependent_simplex4_e01 C H)
      (@ordinal_dependent_simplex4_t012 C H) (@ordinal_dependent_simplex4_s0123 C H)))
≔ @fapp0
    (@DependentSimplex4_cat
      ordinal_simplex4_target_cat ordinal_simplex4_target_y0
      ordinal_simplex4_target_e01 ordinal_simplex4_target_t012 ordinal_simplex4_target_s0123)
    (@DependentSimplex4_cat
      C (@ordinal_dependent_simplex4_x0 C H) (@ordinal_dependent_simplex4_e01 C H)
      (@ordinal_dependent_simplex4_t012 C H) (@ordinal_dependent_simplex4_s0123 C H))
    (@ordinal_dependent_simplex4_map C H) ordinal_dependent_simplex4_source;

symbol ordinal_dependent_simplex4_s0124
  [C : Cat]
  (H : τ (Functor ordinal_simplex4_target_cat C))
  : τ (Obj (@DependentSimplex3_cat
      C (@ordinal_dependent_simplex4_x0 C H) (@ordinal_dependent_simplex4_e01 C H)
      (@ordinal_dependent_simplex4_t012 C H)))
≔ sigma_Fst (@ordinal_dependent_simplex4_observation C H);

symbol ordinal_dependent_simplex4_omega
  [C : Cat]
  (H : τ (Functor ordinal_simplex4_target_cat C))
  : τ (Hom
      (@DependentSimplex3_cat
        C (@ordinal_dependent_simplex4_x0 C H) (@ordinal_dependent_simplex4_e01 C H)
        (@ordinal_dependent_simplex4_t012 C H))
      (@ordinal_dependent_simplex4_s0123 C H)
      (@ordinal_dependent_simplex4_s0124 C H))
≔ sigma_Snd (@ordinal_dependent_simplex4_observation C H);

symbol ordinal_dependent_simplex4_t013
  [C : Cat]
  (H : τ (Functor ordinal_simplex4_target_cat C))
  : τ (Obj (@DependentSimplex2_cat
      C (@ordinal_dependent_simplex4_x0 C H) (@ordinal_dependent_simplex4_e01 C H)))
≔ sigma_Fst (@ordinal_dependent_simplex4_s0123 C H);

symbol ordinal_dependent_simplex4_t014
  [C : Cat]
  (H : τ (Functor ordinal_simplex4_target_cat C))
  : τ (Obj (@DependentSimplex2_cat
      C (@ordinal_dependent_simplex4_x0 C H) (@ordinal_dependent_simplex4_e01 C H)))
≔ sigma_Fst (@ordinal_dependent_simplex4_s0124 C H);

symbol ordinal_dependent_simplex4_theta0123
  [C : Cat]
  (H : τ (Functor ordinal_simplex4_target_cat C))
  : τ (Hom
      (@DependentSimplex2_cat
        C (@ordinal_dependent_simplex4_x0 C H) (@ordinal_dependent_simplex4_e01 C H))
      (@ordinal_dependent_simplex4_t012 C H) (@ordinal_dependent_simplex4_t013 C H))
≔ sigma_Snd (@ordinal_dependent_simplex4_s0123 C H);

symbol ordinal_dependent_simplex4_theta0124
  [C : Cat]
  (H : τ (Functor ordinal_simplex4_target_cat C))
  : τ (Hom
      (@DependentSimplex2_cat
        C (@ordinal_dependent_simplex4_x0 C H) (@ordinal_dependent_simplex4_e01 C H))
      (@ordinal_dependent_simplex4_t012 C H) (@ordinal_dependent_simplex4_t014 C H))
≔ sigma_Snd (@ordinal_dependent_simplex4_s0124 C H);

symbol ordinal_dependent_simplex4_theta_base_index
  [C : Cat]
  (H : τ (Functor ordinal_simplex4_target_cat C))
  : Grpd
≔ Obj (Op_cat (Hom_cat
    (@DependentSimplex2_cat
      C (@ordinal_dependent_simplex4_x0 C H) (@ordinal_dependent_simplex4_e01 C H))
    (@ordinal_dependent_simplex4_t013 C H) (@ordinal_dependent_simplex4_t014 C H)));

symbol ordinal_dependent_simplex4_theta_fibre
  [C : Cat]
  (H : τ (Functor ordinal_simplex4_target_cat C))
  (s0134 : τ (@ordinal_dependent_simplex4_theta_base_index C H))
  : Grpd
≔ Obj (@Fibre_cat
    (Op_cat (Hom_cat
      (@DependentSimplex2_cat
        C (@ordinal_dependent_simplex4_x0 C H) (@ordinal_dependent_simplex4_e01 C H))
      (@ordinal_dependent_simplex4_t013 C H) (@ordinal_dependent_simplex4_t014 C H)))
    (@homd_
      (@DependentSimplex2_cat
        C (@ordinal_dependent_simplex4_x0 C H) (@ordinal_dependent_simplex4_e01 C H))
      (@Rep_catd
        (@DependentSimplex2_cat
          C (@ordinal_dependent_simplex4_x0 C H) (@ordinal_dependent_simplex4_e01 C H))
        (@ordinal_dependent_simplex4_t012 C H))
      (@Rep_catd
        (@DependentSimplex2_cat
          C (@ordinal_dependent_simplex4_x0 C H) (@ordinal_dependent_simplex4_e01 C H))
        (@ordinal_dependent_simplex4_t012 C H))
      (@id_funcd
        (@DependentSimplex2_cat
          C (@ordinal_dependent_simplex4_x0 C H) (@ordinal_dependent_simplex4_e01 C H))
        (@Rep_catd
          (@DependentSimplex2_cat
            C (@ordinal_dependent_simplex4_x0 C H) (@ordinal_dependent_simplex4_e01 C H))
          (@ordinal_dependent_simplex4_t012 C H)))
      (@ordinal_dependent_simplex4_t013 C H) (@ordinal_dependent_simplex4_theta0123 C H)
      (@ordinal_dependent_simplex4_t014 C H) (@ordinal_dependent_simplex4_theta0124 C H))
    s0134);

symbol ordinal_dependent_simplex4_theta0134
  [C : Cat]
  (H : τ (Functor ordinal_simplex4_target_cat C))
  : τ (Hom
      (@DependentSimplex2_cat
        C (@ordinal_dependent_simplex4_x0 C H) (@ordinal_dependent_simplex4_e01 C H))
      (@ordinal_dependent_simplex4_t013 C H) (@ordinal_dependent_simplex4_t014 C H))
≔ @sigma_Fst
    (@ordinal_dependent_simplex4_theta_base_index C H)
    (λ s0134 : τ (@ordinal_dependent_simplex4_theta_base_index C H),
      @ordinal_dependent_simplex4_theta_fibre C H s0134)
    (@ordinal_dependent_simplex4_omega C H);

symbol ordinal_dependent_simplex4_alpha01234
  [C : Cat]
  (H : τ (Functor ordinal_simplex4_target_cat C))
  : τ (Obj (Fibre_cat
      (@DependentTriangle_catd
        (@DependentSimplex2_cat
          C (@ordinal_dependent_simplex4_x0 C H) (@ordinal_dependent_simplex4_e01 C H))
        (@Rep_catd
          (@DependentSimplex2_cat
            C (@ordinal_dependent_simplex4_x0 C H) (@ordinal_dependent_simplex4_e01 C H))
          (@ordinal_dependent_simplex4_t012 C H))
        (@ordinal_dependent_simplex4_t013 C H) (@ordinal_dependent_simplex4_theta0123 C H)
        (@ordinal_dependent_simplex4_t014 C H) (@ordinal_dependent_simplex4_theta0124 C H))
      (@ordinal_dependent_simplex4_theta0134 C H)))
≔ @sigma_Snd
    (@ordinal_dependent_simplex4_theta_base_index C H)
    (λ s0134 : τ (@ordinal_dependent_simplex4_theta_base_index C H),
      @ordinal_dependent_simplex4_theta_fibre C H s0134)
    (@ordinal_dependent_simplex4_omega C H);

symbol ordinal_dependent_simplex4_readable_cell
  [C : Cat]
  (H : τ (Functor ordinal_simplex4_target_cat C))
  : τ (Obj (Hom_cat
      (Hom_cat
        (@DependentSimplex2_cat
          C (@ordinal_dependent_simplex4_x0 C H) (@ordinal_dependent_simplex4_e01 C H))
        (@ordinal_dependent_simplex4_t012 C H) (@ordinal_dependent_simplex4_t014 C H))
      (@comp_fapp0
        (@DependentSimplex2_cat
          C (@ordinal_dependent_simplex4_x0 C H) (@ordinal_dependent_simplex4_e01 C H))
        (@ordinal_dependent_simplex4_t012 C H)
        (@ordinal_dependent_simplex4_t013 C H)
        (@ordinal_dependent_simplex4_t014 C H)
        (@ordinal_dependent_simplex4_theta0134 C H)
        (@ordinal_dependent_simplex4_theta0123 C H))
      (@ordinal_dependent_simplex4_theta0124 C H)))
≔ @dependent_simplex4_readable_cell
    C (@ordinal_dependent_simplex4_x0 C H) (@ordinal_dependent_simplex4_e01 C H)
    (@ordinal_dependent_simplex4_t012 C H)
    (@ordinal_dependent_simplex4_t013 C H)
    (@ordinal_dependent_simplex4_t014 C H)
    (@ordinal_dependent_simplex4_theta0123 C H)
    (@ordinal_dependent_simplex4_theta0124 C H)
    (@ordinal_dependent_simplex4_theta0134 C H)
    (@ordinal_dependent_simplex4_alpha01234 C H);

// Intrinsic code view of the same source and its arbitrary-target image.
symbol ordinal_dependent_simplex4_source_code
  : τ (@DependentSimplexCode
      ordinal_simplex4_target_cat (succ (succ (succ (succ zero)))))
≔ @dependent_simplex_code4
    ordinal_simplex4_target_cat ordinal_simplex4_target_y0 ordinal_simplex4_target_e01
    ordinal_simplex4_target_t012 ordinal_simplex4_target_s0123;

symbol ordinal_dependent_simplex4_code
  [C : Cat]
  (H : τ (Functor ordinal_simplex4_target_cat C))
  : τ (@DependentSimplexCode C (succ (succ (succ (succ zero)))))
≔ @dependent_simplex_code_map_target
    ordinal_simplex4_target_cat C H
    (succ (succ (succ (succ zero)))) ordinal_dependent_simplex4_source_code;

// The five cofaces [3] -> [4], named by their retained vertices.
symbol ordinal_simplex4_face0123_code
  : τ (@DependentSimplexFaceRef
      (succ (succ (succ zero)))
      (succ (succ (succ (succ zero)))))
≔ @face_skip
    (succ (succ (succ (succ zero))))
    (succ (succ (succ (succ zero))))
    (@face_identity (succ (succ (succ (succ zero)))));

symbol ordinal_simplex4_face0124_code
  : τ (@DependentSimplexFaceRef
      (succ (succ (succ zero)))
      (succ (succ (succ (succ zero)))))
≔ @face_keep
    (succ (succ (succ zero)))
    (succ (succ (succ (succ zero))))
    (@face_skip
      (succ (succ (succ zero)))
      (succ (succ (succ zero)))
      (@face_identity (succ (succ (succ zero)))));

symbol ordinal_simplex4_face0134_code
  : τ (@DependentSimplexFaceRef
      (succ (succ (succ zero)))
      (succ (succ (succ (succ zero)))))
≔ @face_keep
    (succ (succ (succ zero)))
    (succ (succ (succ (succ zero))))
    (@face_keep
      (succ (succ zero))
      (succ (succ (succ zero)))
      (@face_skip
        (succ (succ zero))
        (succ (succ zero))
        (@face_identity (succ (succ zero)))));

symbol ordinal_simplex4_face0234_code
  : τ (@DependentSimplexFaceRef
      (succ (succ (succ zero)))
      (succ (succ (succ (succ zero)))))
≔ @face_keep
    (succ (succ (succ zero)))
    (succ (succ (succ (succ zero))))
    (@face_keep
      (succ (succ zero))
      (succ (succ (succ zero)))
      (@face_keep
        (succ zero)
        (succ (succ zero))
        (@face_skip
          (succ zero) (succ zero)
          (@face_identity (succ zero)))));

symbol ordinal_simplex4_face1234_code
  : τ (@DependentSimplexFaceRef
      (succ (succ (succ zero)))
      (succ (succ (succ (succ zero)))))
≔ @face_keep
    (succ (succ (succ zero)))
    (succ (succ (succ (succ zero))))
    (@face_keep
      (succ (succ zero))
      (succ (succ (succ zero)))
      (@face_keep
        (succ zero)
        (succ (succ zero))
        (@face_keep
          zero (succ zero)
          (@face_skip zero zero face_nil))));

// Generic whole face observation; the five readable names below are aliases.
symbol ordinal_dependent_simplex4_face
  [C : Cat]
  (H : τ (Functor ordinal_simplex4_target_cat C))
  (alpha : τ (@DependentSimplexFaceRef
      (succ (succ (succ zero)))
      (succ (succ (succ (succ zero))))))
  : τ (Obj (@dependent_simplex_code_decode_cat
      C (succ (succ (succ zero)))
      (@dependent_simplex_face_target
        C (succ (succ (succ zero)))
        (succ (succ (succ (succ zero))))
        (@ordinal_dependent_simplex4_code C H) alpha)))
≔ @fapp0
    (@dependent_simplex_code_decode_cat
      C (succ (succ (succ (succ zero))))
      (@ordinal_dependent_simplex4_code C H))
    (@dependent_simplex_code_decode_cat
      C (succ (succ (succ zero)))
      (@dependent_simplex_face_target
        C (succ (succ (succ zero)))
        (succ (succ (succ (succ zero))))
        (@ordinal_dependent_simplex4_code C H) alpha))
    (@dependent_simplex_face_func
      C (succ (succ (succ zero)))
      (succ (succ (succ (succ zero))))
      (@ordinal_dependent_simplex4_code C H) alpha)
    (@ordinal_dependent_simplex4_observation C H);

symbol ordinal_dependent_simplex4_face0123
  [C : Cat]
  (H : τ (Functor ordinal_simplex4_target_cat C))
  : τ (Obj (@dependent_simplex_code_decode_cat
      C (succ (succ (succ zero)))
      (@dependent_simplex_face_target
        C (succ (succ (succ zero)))
        (succ (succ (succ (succ zero))))
        (@ordinal_dependent_simplex4_code C H)
        ordinal_simplex4_face0123_code)))
≔ @ordinal_dependent_simplex4_face
    C H ordinal_simplex4_face0123_code;

symbol ordinal_dependent_simplex4_face0124
  [C : Cat]
  (H : τ (Functor ordinal_simplex4_target_cat C))
  : τ (Obj (@dependent_simplex_code_decode_cat
      C (succ (succ (succ zero)))
      (@dependent_simplex_face_target
        C (succ (succ (succ zero)))
        (succ (succ (succ (succ zero))))
        (@ordinal_dependent_simplex4_code C H)
        ordinal_simplex4_face0124_code)))
≔ @ordinal_dependent_simplex4_face
    C H ordinal_simplex4_face0124_code;

symbol ordinal_dependent_simplex4_face0134
  [C : Cat]
  (H : τ (Functor ordinal_simplex4_target_cat C))
  : τ (Obj (@dependent_simplex_code_decode_cat
      C (succ (succ (succ zero)))
      (@dependent_simplex_face_target
        C (succ (succ (succ zero)))
        (succ (succ (succ (succ zero))))
        (@ordinal_dependent_simplex4_code C H)
        ordinal_simplex4_face0134_code)))
≔ @ordinal_dependent_simplex4_face
    C H ordinal_simplex4_face0134_code;

symbol ordinal_dependent_simplex4_face0234
  [C : Cat]
  (H : τ (Functor ordinal_simplex4_target_cat C))
  : τ (Obj (@dependent_simplex_code_decode_cat
      C (succ (succ (succ zero)))
      (@dependent_simplex_face_target
        C (succ (succ (succ zero)))
        (succ (succ (succ (succ zero))))
        (@ordinal_dependent_simplex4_code C H)
        ordinal_simplex4_face0234_code)))
≔ @ordinal_dependent_simplex4_face
    C H ordinal_simplex4_face0234_code;

symbol ordinal_dependent_simplex4_face1234
  [C : Cat]
  (H : τ (Functor ordinal_simplex4_target_cat C))
  : τ (Obj (@dependent_simplex_code_decode_cat
      C (succ (succ (succ zero)))
      (@dependent_simplex_face_target
        C (succ (succ (succ zero)))
        (succ (succ (succ (succ zero))))
        (@ordinal_dependent_simplex4_code C H)
        ordinal_simplex4_face1234_code)))
≔ @ordinal_dependent_simplex4_face
    C H ordinal_simplex4_face1234_code;

// The top component remains the native recursive homd_ filler.
symbol ordinal_dependent_simplex4_top_component
  [C : Cat]
  (H : τ (Functor ordinal_simplex4_target_cat C))
  : τ (Obj (Fibre_cat
      (@DependentTriangle_catd
        (@DependentSimplex2_cat
          C (@ordinal_dependent_simplex4_x0 C H)
          (@ordinal_dependent_simplex4_e01 C H))
        (@Rep_catd
          (@DependentSimplex2_cat
            C (@ordinal_dependent_simplex4_x0 C H)
            (@ordinal_dependent_simplex4_e01 C H))
          (@ordinal_dependent_simplex4_t012 C H))
        (@ordinal_dependent_simplex4_t013 C H)
        (@ordinal_dependent_simplex4_theta0123 C H)
        (@ordinal_dependent_simplex4_t014 C H)
        (@ordinal_dependent_simplex4_theta0124 C H))
      (@ordinal_dependent_simplex4_theta0134 C H)))
≔ @ordinal_dependent_simplex4_alpha01234 C H;
