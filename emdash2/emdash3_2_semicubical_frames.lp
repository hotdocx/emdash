/*
  Recursive two-per-dimension boundary frames from semicubical codes.

  `CubeImmediateFaceCount` adds two faces at each successor. The family of
  immediate coface codes begins with the new coordinate's L/R pair and then
  maps every older face by star. Mapping that finite family through the native
  code action exposes all immediate whole face functors in variable dimension.

  Public truncation constructors do not fuse at arbitrary inputs. Restricted
  induction therefore derives raw-decoder comparisons for L/R/star; ordinary
  path action turns them into whole action-constructor comparisons. New L/R
  faces then agree with native source/target using the all-star identity law,
  while inherited faces agree with profiled `CubicalArrow_func`. Object-level
  projections expose the same recursion on visible successor cells.

  This module adds no `Fin`/list syntax, dimension-specific boundary record,
  runtime rewrite, face equation, Gray comparison, degeneracy, connection, or
  proof-time unifier.
*/

require open emdash.emdash3_2_semicubical_nerve;
require open emdash.emdash3_2_finite_families;

// Public decoding commutes propositionally with L for every public code.
symbol cube_face_code_raw_left_path
  [p n : τ Nat_grpd]
  (f : τ (@CubeFaceCode p n))
  : τ (@=
      (@RawCubeFaceCode p (succ n))
      (@cube_face_code_raw p (succ n) (@cube_face_left p n f))
      (@raw_cube_left p n (@cube_face_code_raw p n f)))
≔ @trunc_ind_ambient
    trunc_zero
    (@RawCubeFaceCode p n)
    (λ f0 : τ (@CubeFaceCode p n),
      @=
        (@RawCubeFaceCode p (succ n))
        (@cube_face_code_raw p (succ n) (@cube_face_left p n f0))
        (@raw_cube_left p n (@cube_face_code_raw p n f0)))
    (λ f0 : τ (@CubeFaceCode p n),
      @is_trunc_path_same_level
        trunc_zero
        (@RawCubeFaceCode p (succ n))
        (@raw_cube_face_code_is_set p (succ n))
        (@cube_face_code_raw p (succ n) (@cube_face_left p n f0))
        (@raw_cube_left p n (@cube_face_code_raw p n f0)))
    (λ raw : τ (@RawCubeFaceCode p n),
      @eq_refl
        (@RawCubeFaceCode p (succ n))
        (@raw_cube_left p n raw))
    f;

// Public decoding commutes propositionally with R for every public code.
symbol cube_face_code_raw_right_path
  [p n : τ Nat_grpd]
  (f : τ (@CubeFaceCode p n))
  : τ (@=
      (@RawCubeFaceCode p (succ n))
      (@cube_face_code_raw p (succ n) (@cube_face_right p n f))
      (@raw_cube_right p n (@cube_face_code_raw p n f)))
≔ @trunc_ind_ambient
    trunc_zero
    (@RawCubeFaceCode p n)
    (λ f0 : τ (@CubeFaceCode p n),
      @=
        (@RawCubeFaceCode p (succ n))
        (@cube_face_code_raw p (succ n) (@cube_face_right p n f0))
        (@raw_cube_right p n (@cube_face_code_raw p n f0)))
    (λ f0 : τ (@CubeFaceCode p n),
      @is_trunc_path_same_level
        trunc_zero
        (@RawCubeFaceCode p (succ n))
        (@raw_cube_face_code_is_set p (succ n))
        (@cube_face_code_raw p (succ n) (@cube_face_right p n f0))
        (@raw_cube_right p n (@cube_face_code_raw p n f0)))
    (λ raw : τ (@RawCubeFaceCode p n),
      @eq_refl
        (@RawCubeFaceCode p (succ n))
        (@raw_cube_right p n raw))
    f;

// Public decoding commutes propositionally with star for every public code.
symbol cube_face_code_raw_keep_path
  [p n : τ Nat_grpd]
  (f : τ (@CubeFaceCode p n))
  : τ (@=
      (@RawCubeFaceCode (succ p) (succ n))
      (@cube_face_code_raw
        (succ p) (succ n) (@cube_face_keep p n f))
      (@raw_cube_keep p n (@cube_face_code_raw p n f)))
≔ @trunc_ind_ambient
    trunc_zero
    (@RawCubeFaceCode p n)
    (λ f0 : τ (@CubeFaceCode p n),
      @=
        (@RawCubeFaceCode (succ p) (succ n))
        (@cube_face_code_raw
          (succ p) (succ n) (@cube_face_keep p n f0))
        (@raw_cube_keep p n (@cube_face_code_raw p n f0)))
    (λ f0 : τ (@CubeFaceCode p n),
      @is_trunc_path_same_level
        trunc_zero
        (@RawCubeFaceCode (succ p) (succ n))
        (@raw_cube_face_code_is_set (succ p) (succ n))
        (@cube_face_code_raw
          (succ p) (succ n) (@cube_face_keep p n f0))
        (@raw_cube_keep p n (@cube_face_code_raw p n f0)))
    (λ raw : τ (@RawCubeFaceCode p n),
      @eq_refl
        (@RawCubeFaceCode (succ p) (succ n))
        (@raw_cube_keep p n raw))
    f;

// Whole public L action for an arbitrary public predecessor.
symbol cube_face_action_left_path
  [C : Cat]
  [p n : τ Nat_grpd]
  (f : τ (@CubeFaceCode p n))
  : τ (@=
      (Hom Cat_cat
        (@CubicalLevel_cat C (succ n))
        (@CubicalLevel_cat C p))
      (@cube_face_action_func C p (succ n) (@cube_face_left p n f))
      (@comp_cat_fapp0
        (@CubicalLevel_cat C (succ n))
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C p)
        (@cube_face_action_func C p n f)
        (@cubical_src_func (@CubicalLevel_cat C n))))
≔ @eq_ap
    (@RawCubeFaceCode p (succ n))
    (Hom Cat_cat
      (@CubicalLevel_cat C (succ n))
      (@CubicalLevel_cat C p))
    (λ raw : τ (@RawCubeFaceCode p (succ n)),
      sigma_Fst (@raw_cube_face_action C p (succ n) raw))
    (@cube_face_code_raw p (succ n) (@cube_face_left p n f))
    (@raw_cube_left p n (@cube_face_code_raw p n f))
    (@cube_face_code_raw_left_path p n f);

// Whole public R action for an arbitrary public predecessor.
symbol cube_face_action_right_path
  [C : Cat]
  [p n : τ Nat_grpd]
  (f : τ (@CubeFaceCode p n))
  : τ (@=
      (Hom Cat_cat
        (@CubicalLevel_cat C (succ n))
        (@CubicalLevel_cat C p))
      (@cube_face_action_func C p (succ n) (@cube_face_right p n f))
      (@comp_cat_fapp0
        (@CubicalLevel_cat C (succ n))
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C p)
        (@cube_face_action_func C p n f)
        (@cubical_tgt_func (@CubicalLevel_cat C n))))
≔ @eq_ap
    (@RawCubeFaceCode p (succ n))
    (Hom Cat_cat
      (@CubicalLevel_cat C (succ n))
      (@CubicalLevel_cat C p))
    (λ raw : τ (@RawCubeFaceCode p (succ n)),
      sigma_Fst (@raw_cube_face_action C p (succ n) raw))
    (@cube_face_code_raw p (succ n) (@cube_face_right p n f))
    (@raw_cube_right p n (@cube_face_code_raw p n f))
    (@cube_face_code_raw_right_path p n f);

// Whole public star action for an arbitrary public predecessor.
symbol cube_face_action_keep_path
  [C : Cat]
  [p n : τ Nat_grpd]
  (f : τ (@CubeFaceCode p n))
  : τ (@=
      (Hom Cat_cat
        (@CubicalLevel_cat C (succ n))
        (@CubicalLevel_cat C (succ p)))
      (@cube_face_action_func
        C (succ p) (succ n) (@cube_face_keep p n f))
      (@CubicalArrow_func
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C p)
        (@cube_face_action_func C p n f)
        (@cube_face_action_is_pseudo C p n f)))
≔ @eq_ap
    (@RawCubeFaceCode (succ p) (succ n))
    (Hom Cat_cat
      (@CubicalLevel_cat C (succ n))
      (@CubicalLevel_cat C (succ p)))
    (λ raw : τ (@RawCubeFaceCode (succ p) (succ n)),
      sigma_Fst (@raw_cube_face_action C (succ p) (succ n) raw))
    (@cube_face_code_raw
      (succ p) (succ n) (@cube_face_keep p n f))
    (@raw_cube_keep p n (@cube_face_code_raw p n f))
    (@cube_face_code_raw_keep_path p n f);

// Two new immediate faces are added at every successor dimension.
symbol CubeImmediateFaceCount
  (n : τ Nat_grpd)
  : τ Nat_grpd
≔ @nat_elim
    (λ _ : τ Nat_grpd, Nat_grpd)
    zero
    (λ _ : τ Nat_grpd,
      λ previous : τ Nat_grpd,
        succ (succ previous))
    n;

// New-coordinate L and R codes.
symbol cube_new_left_face_code
  (n : τ Nat_grpd)
  : τ (@CubeFaceCode n (succ n))
≔ @cube_face_left n n (@cube_face_identity n);

symbol cube_new_right_face_code
  (n : τ Nat_grpd)
  : τ (@CubeFaceCode n (succ n))
≔ @cube_face_right n n (@cube_face_identity n);

// The immediate cofaces of an (n+1)-cube: new L/R, then star-lifted older
// cofaces. This is a family of 2(n+1) codes n -> n+1.
symbol cube_immediate_face_codes
  (n : τ Nat_grpd)
  : τ (@FiniteFamily
      (@CubeFaceCode n (succ n))
      (@CubeImmediateFaceCount (succ n)))
≔ @nat_elim
    (λ n0 : τ Nat_grpd,
      @FiniteFamily
        (@CubeFaceCode n0 (succ n0))
        (@CubeImmediateFaceCount (succ n0)))
    (@finite_family_pair
      (@CubeFaceCode zero (succ zero))
      (@cube_face_left zero zero cube_face_nil)
      (@cube_face_right zero zero cube_face_nil))
    (λ n0 : τ Nat_grpd,
      λ previous : τ (@FiniteFamily
        (@CubeFaceCode n0 (succ n0))
        (@CubeImmediateFaceCount (succ n0))),
        @finite_family_cons
          (@CubeFaceCode (succ n0) (succ (succ n0)))
          (succ (@CubeImmediateFaceCount (succ n0)))
          (@cube_face_left
            (succ n0) (succ n0)
            (@cube_face_identity (succ n0)))
          (@finite_family_cons
            (@CubeFaceCode (succ n0) (succ (succ n0)))
            (@CubeImmediateFaceCount (succ n0))
            (@cube_face_right
              (succ n0) (succ n0)
              (@cube_face_identity (succ n0)))
            (@finite_family_map
              (@CubeFaceCode n0 (succ n0))
              (@CubeFaceCode (succ n0) (succ (succ n0)))
              (λ f : τ (@CubeFaceCode n0 (succ n0)),
                @cube_face_keep n0 (succ n0) f)
              (@CubeImmediateFaceCount (succ n0))
              previous)))
    n;

// The first two entries are the new coordinate's L and R cofaces.
symbol cube_immediate_new_left_observation
  (n : τ Nat_grpd)
  : τ (@CubeFaceCode n (succ n))
≔ @finite_family_head
    (@CubeFaceCode n (succ n))
    (succ (@CubeImmediateFaceCount n))
    (@cube_immediate_face_codes n);

symbol cube_immediate_new_right_observation
  (n : τ Nat_grpd)
  : τ (@CubeFaceCode n (succ n))
≔ @finite_family_head
    (@CubeFaceCode n (succ n))
    (@CubeImmediateFaceCount n)
    (@finite_family_tail
      (@CubeFaceCode n (succ n))
      (succ (@CubeImmediateFaceCount n))
      (@cube_immediate_face_codes n));

// Variable-dimension observations require Nat induction; they compute
// definitionally once the dimension constructor is visible.
symbol cube_immediate_new_left_observation_path
  (n : τ Nat_grpd)
  : τ (@=
      (@CubeFaceCode n (succ n))
      (@cube_immediate_new_left_observation n)
      (@cube_new_left_face_code n))
≔ @nat_elim
    (λ n0 : τ Nat_grpd,
      @=
        (@CubeFaceCode n0 (succ n0))
        (@cube_immediate_new_left_observation n0)
        (@cube_new_left_face_code n0))
    (@eq_refl
      (@CubeFaceCode zero (succ zero))
      (@cube_new_left_face_code zero))
    (λ n0 : τ Nat_grpd,
      λ _ : τ (@=
        (@CubeFaceCode n0 (succ n0))
        (@cube_immediate_new_left_observation n0)
        (@cube_new_left_face_code n0)),
      @eq_refl
        (@CubeFaceCode (succ n0) (succ (succ n0)))
        (@cube_new_left_face_code (succ n0)))
    n;

symbol cube_immediate_new_right_observation_path
  (n : τ Nat_grpd)
  : τ (@=
      (@CubeFaceCode n (succ n))
      (@cube_immediate_new_right_observation n)
      (@cube_new_right_face_code n))
≔ @nat_elim
    (λ n0 : τ Nat_grpd,
      @=
        (@CubeFaceCode n0 (succ n0))
        (@cube_immediate_new_right_observation n0)
        (@cube_new_right_face_code n0))
    (@eq_refl
      (@CubeFaceCode zero (succ zero))
      (@cube_new_right_face_code zero))
    (λ n0 : τ Nat_grpd,
      λ _ : τ (@=
        (@CubeFaceCode n0 (succ n0))
        (@cube_immediate_new_right_observation n0)
        (@cube_new_right_face_code n0)),
      @eq_refl
        (@CubeFaceCode (succ n0) (succ (succ n0)))
        (@cube_new_right_face_code (succ n0)))
    n;

// Removing the new pair at the next dimension leaves exactly the star-map of
// the older immediate-face family.
symbol cube_immediate_inherited_face_codes
  (n : τ Nat_grpd)
  : τ (@FiniteFamily
      (@CubeFaceCode (succ n) (succ (succ n)))
      (@CubeImmediateFaceCount (succ n)))
≔ @finite_family_tail
    (@CubeFaceCode (succ n) (succ (succ n)))
    (@CubeImmediateFaceCount (succ n))
    (@finite_family_tail
      (@CubeFaceCode (succ n) (succ (succ n)))
      (succ (@CubeImmediateFaceCount (succ n)))
      (@cube_immediate_face_codes (succ n)));

symbol cube_immediate_inherited_face_codes_path
  (n : τ Nat_grpd)
  : τ (@=
      (@FiniteFamily
        (@CubeFaceCode (succ n) (succ (succ n)))
        (@CubeImmediateFaceCount (succ n)))
      (@cube_immediate_inherited_face_codes n)
      (@finite_family_map
        (@CubeFaceCode n (succ n))
        (@CubeFaceCode (succ n) (succ (succ n)))
        (λ f : τ (@CubeFaceCode n (succ n)),
          @cube_face_keep n (succ n) f)
        (@CubeImmediateFaceCount (succ n))
        (@cube_immediate_face_codes n)))
≔ @eq_refl
    (@FiniteFamily
      (@CubeFaceCode (succ n) (succ (succ n)))
      (@CubeImmediateFaceCount (succ n)))
    (@cube_immediate_inherited_face_codes n);

// The corresponding whole restriction functors expose all immediate faces.
symbol cube_immediate_face_actions
  (C : Cat)
  (n : τ Nat_grpd)
  : τ (@FiniteFamily
      (Functor
        (@CubicalLevel_cat C (succ n))
        (@CubicalLevel_cat C n))
      (@CubeImmediateFaceCount (succ n)))
≔ @finite_family_map
    (@CubeFaceCode n (succ n))
    (Functor
      (@CubicalLevel_cat C (succ n))
      (@CubicalLevel_cat C n))
    (λ f : τ (@CubeFaceCode n (succ n)),
      @cube_face_action_func C n (succ n) f)
    (@CubeImmediateFaceCount (succ n))
    (@cube_immediate_face_codes n);

// New L agrees propositionally with the native source face. The only
// comparison is action(id_n)=id, postcomposed after source.
symbol cube_new_left_face_action_path
  [C : Cat]
  (n : τ Nat_grpd)
  : τ (@=
      (Hom Cat_cat
        (@CubicalLevel_cat C (succ n))
        (@CubicalLevel_cat C n))
      (@cube_face_action_func
        C n (succ n) (@cube_new_left_face_code n))
      (@cubical_src_func (@CubicalLevel_cat C n)))
≔ @eq_trans
    (Hom Cat_cat
      (@CubicalLevel_cat C (succ n))
      (@CubicalLevel_cat C n))
    (@cube_face_action_func
      C n (succ n) (@cube_new_left_face_code n))
    (@comp_cat_fapp0
      (@CubicalLevel_cat C (succ n))
      (@CubicalLevel_cat C n)
      (@CubicalLevel_cat C n)
      (@cube_face_action_func C n n (@cube_face_identity n))
      (@cubical_src_func (@CubicalLevel_cat C n)))
    (@cubical_src_func (@CubicalLevel_cat C n))
    (@cube_face_action_left_path C n n (@cube_face_identity n))
    (@eq_ap
      (Hom Cat_cat
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C n))
      (Hom Cat_cat
        (@CubicalLevel_cat C (succ n))
        (@CubicalLevel_cat C n))
      (λ F : τ (Functor
          (@CubicalLevel_cat C n)
          (@CubicalLevel_cat C n)),
        @comp_cat_fapp0
          (@CubicalLevel_cat C (succ n))
          (@CubicalLevel_cat C n)
          (@CubicalLevel_cat C n)
          F
          (@cubical_src_func (@CubicalLevel_cat C n)))
      (@cube_face_action_func C n n (@cube_face_identity n))
      (@id_func (@CubicalLevel_cat C n))
      (@cube_face_action_identity_path C n));

// New R agrees propositionally with the native target face.
symbol cube_new_right_face_action_path
  [C : Cat]
  (n : τ Nat_grpd)
  : τ (@=
      (Hom Cat_cat
        (@CubicalLevel_cat C (succ n))
        (@CubicalLevel_cat C n))
      (@cube_face_action_func
        C n (succ n) (@cube_new_right_face_code n))
      (@cubical_tgt_func (@CubicalLevel_cat C n)))
≔ @eq_trans
    (Hom Cat_cat
      (@CubicalLevel_cat C (succ n))
      (@CubicalLevel_cat C n))
    (@cube_face_action_func
      C n (succ n) (@cube_new_right_face_code n))
    (@comp_cat_fapp0
      (@CubicalLevel_cat C (succ n))
      (@CubicalLevel_cat C n)
      (@CubicalLevel_cat C n)
      (@cube_face_action_func C n n (@cube_face_identity n))
      (@cubical_tgt_func (@CubicalLevel_cat C n)))
    (@cubical_tgt_func (@CubicalLevel_cat C n))
    (@cube_face_action_right_path C n n (@cube_face_identity n))
    (@eq_ap
      (Hom Cat_cat
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C n))
      (Hom Cat_cat
        (@CubicalLevel_cat C (succ n))
        (@CubicalLevel_cat C n))
      (λ F : τ (Functor
          (@CubicalLevel_cat C n)
          (@CubicalLevel_cat C n)),
        @comp_cat_fapp0
          (@CubicalLevel_cat C (succ n))
          (@CubicalLevel_cat C n)
          (@CubicalLevel_cat C n)
          F
          (@cubical_tgt_func (@CubicalLevel_cat C n)))
      (@cube_face_action_func C n n (@cube_face_identity n))
      (@id_func (@CubicalLevel_cat C n))
      (@cube_face_action_identity_path C n));

// Star-lifted older faces are propositionally the native CubicalArrow lift at
// arbitrary public codes; visible truncation points still compute.
symbol cube_keep_face_action_path
  [C : Cat]
  [p n : τ Nat_grpd]
  (f : τ (@CubeFaceCode p n))
  : τ (@=
      (Hom Cat_cat
        (@CubicalLevel_cat C (succ n))
        (@CubicalLevel_cat C (succ p)))
      (@cube_face_action_func
        C (succ p) (succ n) (@cube_face_keep p n f))
      (@CubicalArrow_func
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C p)
        (@cube_face_action_func C p n f)
        (@cube_face_action_is_pseudo C p n f)))
≔ @cube_face_action_keep_path C p n f;

// Evaluating the new L comparison recovers the ordinary source endpoint of
// every constructor-visible successor cell.
symbol cube_new_left_face_at_path
  [C : Cat]
  (n : τ Nat_grpd)
  (X : τ (Obj (@CubicalLevel_cat C (succ n))))
  : τ (@=
      (Obj (@CubicalLevel_cat C n))
      (@fapp0
        (@CubicalLevel_cat C (succ n))
        (@CubicalLevel_cat C n)
        (@cube_face_action_func
          C n (succ n) (@cube_new_left_face_code n))
        X)
      (@fapp0
        (@CubicalLevel_cat C (succ n))
        (@CubicalLevel_cat C n)
        (@cubical_src_func (@CubicalLevel_cat C n))
        X))
≔ @eq_ap
    (Hom Cat_cat
      (@CubicalLevel_cat C (succ n))
      (@CubicalLevel_cat C n))
    (Obj (@CubicalLevel_cat C n))
    (λ F : τ (Functor
        (@CubicalLevel_cat C (succ n))
        (@CubicalLevel_cat C n)),
      @fapp0
        (@CubicalLevel_cat C (succ n))
        (@CubicalLevel_cat C n)
        F X)
    (@cube_face_action_func
      C n (succ n) (@cube_new_left_face_code n))
    (@cubical_src_func (@CubicalLevel_cat C n))
    (@cube_new_left_face_action_path C n);

// Evaluating the new R comparison recovers the ordinary target endpoint.
symbol cube_new_right_face_at_path
  [C : Cat]
  (n : τ Nat_grpd)
  (X : τ (Obj (@CubicalLevel_cat C (succ n))))
  : τ (@=
      (Obj (@CubicalLevel_cat C n))
      (@fapp0
        (@CubicalLevel_cat C (succ n))
        (@CubicalLevel_cat C n)
        (@cube_face_action_func
          C n (succ n) (@cube_new_right_face_code n))
        X)
      (@fapp0
        (@CubicalLevel_cat C (succ n))
        (@CubicalLevel_cat C n)
        (@cubical_tgt_func (@CubicalLevel_cat C n))
        X))
≔ @eq_ap
    (Hom Cat_cat
      (@CubicalLevel_cat C (succ n))
      (@CubicalLevel_cat C n))
    (Obj (@CubicalLevel_cat C n))
    (λ F : τ (Functor
        (@CubicalLevel_cat C (succ n))
        (@CubicalLevel_cat C n)),
      @fapp0
        (@CubicalLevel_cat C (succ n))
        (@CubicalLevel_cat C n)
        F X)
    (@cube_face_action_func
      C n (succ n) (@cube_new_right_face_code n))
    (@cubical_tgt_func (@CubicalLevel_cat C n))
    (@cube_new_right_face_action_path C n);

// A star-lifted older face maps a visible successor cell by the older whole
// functor and its retained hom action.
symbol cube_keep_face_at_path
  [C : Cat]
  [p n : τ Nat_grpd]
  (f : τ (@CubeFaceCode p n))
  [X Y : τ (Obj (@CubicalLevel_cat C n))]
  (theta : τ (Hom (@CubicalLevel_cat C n) X Y))
  : τ (@=
      (Obj (@CubicalLevel_cat C (succ p)))
      (@fapp0
        (@CubicalLevel_cat C (succ n))
        (@CubicalLevel_cat C (succ p))
        (@cube_face_action_func
          C (succ p) (succ n) (@cube_face_keep p n f))
        (@cubical_edge (@CubicalLevel_cat C n) X Y theta))
      (@cubical_edge
        (@CubicalLevel_cat C p)
        (@fapp0
          (@CubicalLevel_cat C n)
          (@CubicalLevel_cat C p)
          (@cube_face_action_func C p n f)
          X)
        (@fapp0
          (@CubicalLevel_cat C n)
          (@CubicalLevel_cat C p)
          (@cube_face_action_func C p n f)
          Y)
        (@fapp1_fapp0
          (@CubicalLevel_cat C n)
          (@CubicalLevel_cat C p)
          (@cube_face_action_func C p n f)
          X Y theta)))
≔ @eq_ap
    (Hom Cat_cat
      (@CubicalLevel_cat C (succ n))
      (@CubicalLevel_cat C (succ p)))
    (Obj (@CubicalLevel_cat C (succ p)))
    (λ F : τ (Functor
        (@CubicalLevel_cat C (succ n))
        (@CubicalLevel_cat C (succ p))),
      @fapp0
        (@CubicalLevel_cat C (succ n))
        (@CubicalLevel_cat C (succ p))
        F
        (@cubical_edge (@CubicalLevel_cat C n) X Y theta))
    (@cube_face_action_func
      C (succ p) (succ n) (@cube_face_keep p n f))
    (@CubicalArrow_func
      (@CubicalLevel_cat C n)
      (@CubicalLevel_cat C p)
      (@cube_face_action_func C p n f)
      (@cube_face_action_is_pseudo C p n f))
    (@cube_keep_face_action_path C p n f);

assert ⊢ @CubeImmediateFaceCount zero ≡ zero;
assert ⊢ @CubeImmediateFaceCount (succ zero) ≡ succ (succ zero);
assert ⊢ @CubeImmediateFaceCount (succ (succ zero))
  ≡ succ (succ (succ (succ zero)));

assert [C : Cat] (n : τ Nat_grpd) ⊢
  @cube_new_left_face_action_path C n
  : τ (@=
      (Hom Cat_cat
        (@CubicalLevel_cat C (succ n))
        (@CubicalLevel_cat C n))
      (@cube_face_action_func
        C n (succ n) (@cube_new_left_face_code n))
      (@cubical_src_func (@CubicalLevel_cat C n)));

assert [C : Cat]
  (p n : τ Nat_grpd)
  (f : τ (@CubeFaceCode p n)) ⊢
  @cube_keep_face_action_path C p n f
  : τ (@=
      (Hom Cat_cat
        (@CubicalLevel_cat C (succ n))
        (@CubicalLevel_cat C (succ p)))
      (@cube_face_action_func
        C (succ p) (succ n) (@cube_face_keep p n f))
      (@CubicalArrow_func
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C p)
        (@cube_face_action_func C p n f)
        (@cube_face_action_is_pseudo C p n f)));
