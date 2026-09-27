/*
  Emdash v3.2: realize explicit open squares as compatible sieve maps.

  An explicit box is filled to a native path square, sent to its existing
  representable Yoneda section, and restricted along the corresponding
  ordinary open-box inclusion. This direction uses only the active Yoneda
  beta infrastructure and is whole at the mapping-object boundary.

  No inverse from an arbitrary sieve map to the explicit three-edge carrier is
  claimed: assembling that comparison uniformly would require the absent
  Yoneda eta/native mapping-object equivalence.
*/

require open emdash.emdash3_2_path_cubical_open_square_actions;
require open emdash.emdash3_2_path_cubical_open_square_sieves;

// Common mapping-object classifier for one selected open-box kind.
symbol PathCube2OpenBoxMap_cat
  (A : Grpd)
  (kind : τ Cube2OpenBoxKind)
  : Cat
≔ @Hom_cat
    (@Psh_cat SemiCubePlus_cat)
    (@cube2_open_extension_psh kind)
    (@path_semicubical_nerve_func A);

symbol path_open_square_sieve_map_missing_u
  [A : Grpd]
  (box : τ (@PathOpenSquareMissingU_grpd A))
  : τ (Obj (@PathCube2OpenBoxMap_cat A cube2_missing_u_kind))
≔ @fapp0
    (Hom_cat
      (@Psh_cat SemiCubePlus_cat)
      (@StandardSemicube (succ (succ zero)))
      (@path_semicubical_nerve_func A))
    (@PathCube2OpenBoxMap_cat A cube2_missing_u_kind)
    (@path_cube2_open_restrict_func A cube2_missing_u_kind)
    (@path_cubical_yoneda_section
      A (succ (succ zero))
      (@path_open_square_fill_missing_u A box));

symbol path_open_square_sieve_map_missing_v
  [A : Grpd]
  (box : τ (@PathOpenSquareMissingV_grpd A))
  : τ (Obj (@PathCube2OpenBoxMap_cat A cube2_missing_v_kind))
≔ @fapp0
    (Hom_cat
      (@Psh_cat SemiCubePlus_cat)
      (@StandardSemicube (succ (succ zero)))
      (@path_semicubical_nerve_func A))
    (@PathCube2OpenBoxMap_cat A cube2_missing_v_kind)
    (@path_cube2_open_restrict_func A cube2_missing_v_kind)
    (@path_cubical_yoneda_section
      A (succ (succ zero))
      (@path_open_square_fill_missing_v A box));

symbol path_open_square_sieve_map_missing_a
  [A : Grpd]
  (box : τ (@PathOpenSquareMissingA_grpd A))
  : τ (Obj (@PathCube2OpenBoxMap_cat A cube2_missing_a_kind))
≔ @fapp0
    (Hom_cat
      (@Psh_cat SemiCubePlus_cat)
      (@StandardSemicube (succ (succ zero)))
      (@path_semicubical_nerve_func A))
    (@PathCube2OpenBoxMap_cat A cube2_missing_a_kind)
    (@path_cube2_open_restrict_func A cube2_missing_a_kind)
    (@path_cubical_yoneda_section
      A (succ (succ zero))
      (@path_open_square_fill_missing_a A box));

symbol path_open_square_sieve_map_missing_b
  [A : Grpd]
  (box : τ (@PathOpenSquareMissingB_grpd A))
  : τ (Obj (@PathCube2OpenBoxMap_cat A cube2_missing_b_kind))
≔ @fapp0
    (Hom_cat
      (@Psh_cat SemiCubePlus_cat)
      (@StandardSemicube (succ (succ zero)))
      (@path_semicubical_nerve_func A))
    (@PathCube2OpenBoxMap_cat A cube2_missing_b_kind)
    (@path_cube2_open_restrict_func A cube2_missing_b_kind)
    (@path_cubical_yoneda_section
      A (succ (succ zero))
      (@path_open_square_fill_missing_b A box));

// Whole equality action of a representative explicit-to-sieve realization.
symbol path_open_square_sieve_map_missing_b_func
  (A : Grpd)
  : τ (Functor
      (Path_cat (@PathOpenSquareMissingB_grpd A))
      (Path_cat (Obj (@PathCube2OpenBoxMap_cat A cube2_missing_b_kind))))
≔ @path_map_func
    (@PathOpenSquareMissingB_grpd A)
    (Obj (@PathCube2OpenBoxMap_cat A cube2_missing_b_kind))
    (λ box : τ (@PathOpenSquareMissingB_grpd A),
      @path_open_square_sieve_map_missing_b A box);
