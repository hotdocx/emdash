/*
  Emdash v3.2: whole semicubical nerve of groupoidal path cubes.

  This module specializes the already-computing Cat-valued semicubical nerve,
  face interpreter, immediate-face family, representable decoder, and Yoneda
  object operations to Path_cat(A). All definitions are transparent aliases
  over the generic cubical owners. No path-specific face equation, nerve rule,
  eta law, mapping-object equivalence, boundary, box, or Kan operation is
  introduced.
*/

require open emdash.emdash3_2_cubical_yoneda;
require open emdash.emdash3_2_path_cubical_square_readback;

// Whole Cat-valued semicubical nerve of the path category.
symbol path_semicubical_nerve_func
  (A : Grpd)
  : τ (Functor (Op_cat SemiCubePlus_cat) Cat_cat)
≔ @semicubical_nerve_func (Path_cat A);

// Whole restriction selected by any public semicubical face code.
symbol path_cube_face_action_func
  [A : Grpd]
  [p n : τ Nat_grpd]
  (f : τ (@CubeFaceCode p n))
  : τ (Functor
      (@PathCubicalLevel_cat A n)
      (@PathCubicalLevel_cat A p))
≔ @cube_face_action_func (Path_cat A) p n f;

// All 2(n+1) immediate faces of a successor path cube.
symbol path_cube_immediate_face_actions
  (A : Grpd)
  (n : τ Nat_grpd)
  : τ (@FiniteFamily
      (Functor
        (@PathCubicalLevel_cat A (succ n))
        (@PathCubicalLevel_cat A n))
      (@CubeImmediateFaceCount (succ n)))
≔ @cube_immediate_face_actions (Path_cat A) n;

// Whole representable face decoder specialized to path cubes.
symbol path_standard_semicube_native_decode_func
  [A : Grpd]
  (p n : τ (Obj SemiCubePlus_cat))
  : τ (Functor
      (@standard_semicube_level n p)
      (Functor_cat
        (@PathCubicalLevel_cat A n)
        (@PathCubicalLevel_cat A p)))
≔ @standard_semicube_native_decode_func (Path_cat A) p n;

// One native path cube supplies a whole map from the representable semicube.
symbol path_cubical_yoneda_section
  [A : Grpd]
  [n : τ (Obj SemiCubePlus_cat)]
  (X : τ (@PathCube_grpd A n))
  : τ (Hom
      (@Psh_cat SemiCubePlus_cat)
      (@StandardSemicube n)
      (@path_semicubical_nerve_func A))
≔ @cubical_yoneda_section (Path_cat A) n X;

// Evaluation at the public identity face.
symbol path_cubical_yoneda_eval
  [A : Grpd]
  [n : τ (Obj SemiCubePlus_cat)]
  (eta : τ (Hom
    (@Psh_cat SemiCubePlus_cat)
    (@StandardSemicube n)
    (@path_semicubical_nerve_func A)))
  : τ (@PathCube_grpd A n)
≔ @cubical_yoneda_eval (Path_cat A) n eta;

// Existing Yoneda beta specialized to path cubes.
symbol path_cubical_yoneda_beta
  [A : Grpd]
  [n : τ (Obj SemiCubePlus_cat)]
  (X : τ (@PathCube_grpd A n))
  : τ (@=
      (@PathCube_grpd A n)
      (@path_cubical_yoneda_eval
        A n (@path_cubical_yoneda_section A n X))
      X)
≔ @cubical_yoneda_beta (Path_cat A) n X;
