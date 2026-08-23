/*
  Whole native semicubical nerve and derived action laws.

  `semicubical_nerve_func(C) : SemiCubePlus^op -> Cat_cat` computes on
  objects to `CubicalLevel_cat(C,n)`. Its arrow observation is propositional:
  the whole nerve retains generic functoriality, while the standalone
  `cube_face_action_func` retains recursively selected profile histories.
  A runtime arrow beta would compete with the kernel's strict generic
  identity/composition cuts, so one typed path relates the two owners.

  Nested restricted truncation induction proves that the named public code
  substitution agrees with arbitrary category composition. The nerve's
  generic `fapp1_id_path` and `fapp1_comp_path`, transported across the whole
  arrow observation, then derive all-star identity and contravariant public
  composition. The whole `fapp1_func` remains available for higher action.

  This module adds only the nerve object beta. It adds no runtime arrow beta,
  face-specific equation, broad category fold, Gray comparison, degeneracy,
  connection, or proof-time unifier.
*/

require open emdash.emdash3_2_semicubical_index;
require open emdash.emdash3_2_semicubical_face_action;

injective symbol semicubical_nerve_func
  (C : Cat)
  : τ (Functor (Op_cat SemiCubePlus_cat) Cat_cat);

rule @fapp0
      (Op_cat SemiCubePlus_cat) Cat_cat
      (@semicubical_nerve_func $C) $n
  ↪ @CubicalLevel_cat $C $n;

// The whole nerve retains its own generic arrow action.
symbol semicubical_nerve_action_func
  [C : Cat]
  [n p : τ Nat_grpd]
  (f : τ (@CubeFaceCode p n))
  : τ (Functor
      (@CubicalLevel_cat C n)
      (@CubicalLevel_cat C p))
≔ @fapp1_fapp0
    (Op_cat SemiCubePlus_cat) Cat_cat
    (@semicubical_nerve_func C) n p f;

// Its selected arrow observation is propositional because the standalone
// action retains profile histories that generic strict cuts must not erase.
constant symbol semicubical_nerve_action_path
  [C : Cat]
  [n p : τ Nat_grpd]
  (f : τ (@CubeFaceCode p n))
  : τ (@=
      (Hom Cat_cat
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C p))
      (@semicubical_nerve_action_func C n p f)
      (@cube_face_action_func C p n f));

symbol cube_face_action_identity_path
  [C : Cat]
  (n : τ Nat_grpd)
  : τ (@=
      (Hom Cat_cat
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C n))
      (@cube_face_action_func C n n (@cube_face_identity n))
      (@id_func (@CubicalLevel_cat C n)))
≔ @eq_trans
    (Hom Cat_cat
      (@CubicalLevel_cat C n)
      (@CubicalLevel_cat C n))
    (@cube_face_action_func C n n (@cube_face_identity n))
    (@semicubical_nerve_action_func C n n (@cube_face_identity n))
    (@id_func (@CubicalLevel_cat C n))
    (@eq_sym
      (Hom Cat_cat
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C n))
      (@semicubical_nerve_action_func C n n (@cube_face_identity n))
      (@cube_face_action_func C n n (@cube_face_identity n))
      (@semicubical_nerve_action_path
        C n n (@cube_face_identity n)))
    (@fapp1_id_path
      (Op_cat SemiCubePlus_cat)
      Cat_cat
      (@semicubical_nerve_func C)
      n);

// For a constructor-visible outer code, public and categorical composition
// agree for every public inner code by restricted truncation induction.
symbol semi_cube_plus_comp_from_raw_path
  [p q n : τ Nat_grpd]
  (g : τ (@RawCubeFaceCode q n))
  (f : τ (@CubeFaceCode p q))
  : τ (@=
      (@CubeFaceCode p n)
      (@cube_face_comp
        p q n
        (@trunc_intro trunc_zero (@RawCubeFaceCode q n) g)
        f)
      (@comp_fapp0
        SemiCubePlus_cat p q n
        (@trunc_intro trunc_zero (@RawCubeFaceCode q n) g)
        f))
≔ @trunc_ind_ambient
    trunc_zero
    (@RawCubeFaceCode p q)
    (λ f0 : τ (@CubeFaceCode p q),
      @=
        (@CubeFaceCode p n)
        (@cube_face_comp
          p q n
          (@trunc_intro trunc_zero (@RawCubeFaceCode q n) g)
          f0)
        (@comp_fapp0
          SemiCubePlus_cat p q n
          (@trunc_intro trunc_zero (@RawCubeFaceCode q n) g)
          f0))
    (λ f0 : τ (@CubeFaceCode p q),
      @is_trunc_path_same_level
        trunc_zero
        (@CubeFaceCode p n)
        (@cube_face_code_is_set p n)
        (@cube_face_comp
          p q n
          (@trunc_intro trunc_zero (@RawCubeFaceCode q n) g)
          f0)
        (@comp_fapp0
          SemiCubePlus_cat p q n
          (@trunc_intro trunc_zero (@RawCubeFaceCode q n) g)
          f0))
    (λ raw : τ (@RawCubeFaceCode p q),
      @eq_refl
        (@CubeFaceCode p n)
        (@cube_face_comp
          p q n
          (@trunc_intro trunc_zero (@RawCubeFaceCode q n) g)
          (@trunc_intro trunc_zero (@RawCubeFaceCode p q) raw)))
    f;

// The named public substitution agrees propositionally with arbitrary
// categorical composition; no broad runtime fold is installed.
symbol semi_cube_plus_comp_public_path
  [p q n : τ Nat_grpd]
  (g : τ (@CubeFaceCode q n))
  (f : τ (@CubeFaceCode p q))
  : τ (@=
      (@CubeFaceCode p n)
      (@cube_face_comp p q n g f)
      (@comp_fapp0 SemiCubePlus_cat p q n g f))
≔ (@trunc_ind_ambient
      trunc_zero
      (@RawCubeFaceCode q n)
      (λ g0 : τ (@CubeFaceCode q n),
        @Pi_grpd
          (@CubeFaceCode p q)
          (λ f0 : τ (@CubeFaceCode p q),
            @=
              (@CubeFaceCode p n)
              (@cube_face_comp p q n g0 f0)
              (@comp_fapp0 SemiCubePlus_cat p q n g0 f0)))
      (λ g0 : τ (@CubeFaceCode q n),
        @is_trunc_pi
          trunc_zero
          (@CubeFaceCode p q)
          (λ f0 : τ (@CubeFaceCode p q),
            @=
              (@CubeFaceCode p n)
              (@cube_face_comp p q n g0 f0)
              (@comp_fapp0 SemiCubePlus_cat p q n g0 f0))
          (λ f0 : τ (@CubeFaceCode p q),
            @is_trunc_path_same_level
              trunc_zero
              (@CubeFaceCode p n)
              (@cube_face_code_is_set p n)
              (@cube_face_comp p q n g0 f0)
              (@comp_fapp0 SemiCubePlus_cat p q n g0 f0)))
      (λ raw : τ (@RawCubeFaceCode q n),
        λ f0 : τ (@CubeFaceCode p q),
          @semi_cube_plus_comp_from_raw_path p q n raw f0)
      g) f;

// Replace the first whole-nerve factor by its computing action comparison.
symbol semicubical_nerve_comp_first_action_path
  [C : Cat]
  [p q n : τ Nat_grpd]
  (g : τ (@CubeFaceCode q n))
  (f : τ (@CubeFaceCode p q))
  : τ (@=
      (Hom Cat_cat
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C p))
      (@comp_cat_fapp0
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C q)
        (@CubicalLevel_cat C p)
        (@semicubical_nerve_action_func C q p f)
        (@semicubical_nerve_action_func C n q g))
      (@comp_cat_fapp0
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C q)
        (@CubicalLevel_cat C p)
        (@cube_face_action_func C p q f)
        (@semicubical_nerve_action_func C n q g)))
≔ @eq_ap
    (Hom Cat_cat
      (@CubicalLevel_cat C q)
      (@CubicalLevel_cat C p))
    (Hom Cat_cat
      (@CubicalLevel_cat C n)
      (@CubicalLevel_cat C p))
    (λ F0 : τ (Functor
        (@CubicalLevel_cat C q)
        (@CubicalLevel_cat C p)),
      @comp_cat_fapp0
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C q)
        (@CubicalLevel_cat C p)
        F0
        (@semicubical_nerve_action_func C n q g))
    (@semicubical_nerve_action_func C q p f)
    (@cube_face_action_func C p q f)
    (@semicubical_nerve_action_path C q p f);

// Replace the second whole-nerve factor after the first is computing.
symbol semicubical_nerve_comp_second_action_path
  [C : Cat]
  [p q n : τ Nat_grpd]
  (g : τ (@CubeFaceCode q n))
  (f : τ (@CubeFaceCode p q))
  : τ (@=
      (Hom Cat_cat
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C p))
      (@comp_cat_fapp0
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C q)
        (@CubicalLevel_cat C p)
        (@cube_face_action_func C p q f)
        (@semicubical_nerve_action_func C n q g))
      (@comp_cat_fapp0
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C q)
        (@CubicalLevel_cat C p)
        (@cube_face_action_func C p q f)
        (@cube_face_action_func C q n g)))
≔ @eq_ap
    (Hom Cat_cat
      (@CubicalLevel_cat C n)
      (@CubicalLevel_cat C q))
    (Hom Cat_cat
      (@CubicalLevel_cat C n)
      (@CubicalLevel_cat C p))
    (λ G0 : τ (Functor
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C q)),
      @comp_cat_fapp0
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C q)
        (@CubicalLevel_cat C p)
        (@cube_face_action_func C p q f)
        G0)
    (@semicubical_nerve_action_func C n q g)
    (@cube_face_action_func C q n g)
    (@semicubical_nerve_action_path C n q g);

// Generic functoriality of the whole nerve owns composition at the category
// presentation retained by SemiCubePlus_cat.
symbol cube_face_action_category_comp_path
  [C : Cat]
  [p q n : τ Nat_grpd]
  (g : τ (@CubeFaceCode q n))
  (f : τ (@CubeFaceCode p q))
  : τ (@=
      (Hom Cat_cat
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C p))
      (@cube_face_action_func C p n
        (@comp_fapp0 SemiCubePlus_cat p q n g f))
      (@comp_cat_fapp0
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C q)
        (@CubicalLevel_cat C p)
        (@cube_face_action_func C p q f)
        (@cube_face_action_func C q n g)))
≔ @eq_trans
    (Hom Cat_cat
      (@CubicalLevel_cat C n)
      (@CubicalLevel_cat C p))
    (@cube_face_action_func C p n
      (@comp_fapp0 SemiCubePlus_cat p q n g f))
    (@semicubical_nerve_action_func C n p
      (@comp_fapp0 SemiCubePlus_cat p q n g f))
    (@comp_cat_fapp0
      (@CubicalLevel_cat C n)
      (@CubicalLevel_cat C q)
      (@CubicalLevel_cat C p)
      (@cube_face_action_func C p q f)
      (@cube_face_action_func C q n g))
    (@eq_sym
      (Hom Cat_cat
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C p))
      (@semicubical_nerve_action_func C n p
        (@comp_fapp0 SemiCubePlus_cat p q n g f))
      (@cube_face_action_func C p n
        (@comp_fapp0 SemiCubePlus_cat p q n g f))
      (@semicubical_nerve_action_path
        C n p (@comp_fapp0 SemiCubePlus_cat p q n g f)))
    (@eq_trans
      (Hom Cat_cat
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C p))
      (@semicubical_nerve_action_func C n p
        (@comp_fapp0 SemiCubePlus_cat p q n g f))
      (@comp_cat_fapp0
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C q)
        (@CubicalLevel_cat C p)
        (@semicubical_nerve_action_func C q p f)
        (@semicubical_nerve_action_func C n q g))
      (@comp_cat_fapp0
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C q)
        (@CubicalLevel_cat C p)
        (@cube_face_action_func C p q f)
        (@cube_face_action_func C q n g))
      (@fapp1_comp_path
        (Op_cat SemiCubePlus_cat)
        Cat_cat
        (@semicubical_nerve_func C)
        n q p
        f g)
      (@eq_trans
        (Hom Cat_cat
          (@CubicalLevel_cat C n)
          (@CubicalLevel_cat C p))
        (@comp_cat_fapp0
          (@CubicalLevel_cat C n)
          (@CubicalLevel_cat C q)
          (@CubicalLevel_cat C p)
          (@semicubical_nerve_action_func C q p f)
          (@semicubical_nerve_action_func C n q g))
        (@comp_cat_fapp0
          (@CubicalLevel_cat C n)
          (@CubicalLevel_cat C q)
          (@CubicalLevel_cat C p)
          (@cube_face_action_func C p q f)
          (@semicubical_nerve_action_func C n q g))
        (@comp_cat_fapp0
          (@CubicalLevel_cat C n)
          (@CubicalLevel_cat C q)
          (@CubicalLevel_cat C p)
          (@cube_face_action_func C p q f)
          (@cube_face_action_func C q n g))
        (@semicubical_nerve_comp_first_action_path C p q n g f)
        (@semicubical_nerve_comp_second_action_path C p q n g f)));

// Public structural substitution then follows by action on the comparison
// above, followed by the whole nerve's generic composition law.
symbol cube_face_action_comp_path
  [C : Cat]
  [p q n : τ Nat_grpd]
  (g : τ (@CubeFaceCode q n))
  (f : τ (@CubeFaceCode p q))
  : τ (@=
      (Hom Cat_cat
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C p))
      (@cube_face_action_func C p n (@cube_face_comp p q n g f))
      (@comp_cat_fapp0
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C q)
        (@CubicalLevel_cat C p)
        (@cube_face_action_func C p q f)
        (@cube_face_action_func C q n g)))
≔ @eq_trans
    (Hom Cat_cat
      (@CubicalLevel_cat C n)
      (@CubicalLevel_cat C p))
    (@cube_face_action_func C p n (@cube_face_comp p q n g f))
    (@cube_face_action_func C p n
      (@comp_fapp0 SemiCubePlus_cat p q n g f))
    (@comp_cat_fapp0
      (@CubicalLevel_cat C n)
      (@CubicalLevel_cat C q)
      (@CubicalLevel_cat C p)
      (@cube_face_action_func C p q f)
      (@cube_face_action_func C q n g))
    (@eq_ap
      (@CubeFaceCode p n)
      (Hom Cat_cat
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C p))
      (λ h : τ (@CubeFaceCode p n),
        @cube_face_action_func C p n h)
      (@cube_face_comp p q n g f)
      (@comp_fapp0 SemiCubePlus_cat p q n g f)
      (@semi_cube_plus_comp_public_path p q n g f))
    (@cube_face_action_category_comp_path C p q n g f);

assert [C : Cat] (n : τ Nat_grpd) ⊢
  @cube_face_action_identity_path C n
  : τ (@=
      (Hom Cat_cat
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C n))
      (@cube_face_action_func C n n (@cube_face_identity n))
      (@id_func (@CubicalLevel_cat C n)));

assert [C : Cat]
  (p q n : τ Nat_grpd)
  (g : τ (@CubeFaceCode q n))
  (f : τ (@CubeFaceCode p q)) ⊢
  @cube_face_action_comp_path C p q n g f
  : τ (@=
      (Hom Cat_cat
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C p))
      (@cube_face_action_func C p n (@cube_face_comp p q n g f))
      (@comp_cat_fapp0
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C q)
        (@CubicalLevel_cat C p)
        (@cube_face_action_func C p q f)
        (@cube_face_action_func C q n g)));

type @fapp1_func
  (Op_cat SemiCubePlus_cat)
  Cat_cat
  (@semicubical_nerve_func Cat_cat);
