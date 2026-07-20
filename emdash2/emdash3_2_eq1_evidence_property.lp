/*
  Transparent evidence-property layer for native equality-valued
  omega-equivalence.

  The active kernel owns `OmegaEquivAlong`. This one-way derived module
  exposes that record as two independent inverse-and-law homotopy fibres,
  proves record eta through the kernel eliminator, and contracts the evidence
  over every literal `Path_cat` arrow. No primitive, opaque theorem, rewrite
  rule, unification rule, decoder, or proof-erasure principle is introduced.
*/

require open emdash.emdash3_2;
require open emdash.emdash3_2_eq1_hom_action;

// Left-inverse half of equality-valued fixed-arrow evidence.
symbol OmegaEquivLeftView
  [C : Cat]
  [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  : Grpd
≔ `Σ_ l : τ (Hom C y x),
    @= (Hom C x x)
      (@comp_fapp0 C x y x l f)
      (@id C x);

// Right-inverse half of equality-valued fixed-arrow evidence.
symbol OmegaEquivRightView
  [C : Cat]
  [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  : Grpd
≔ `Σ_ r : τ (Hom C y x),
    @= (Hom C y y)
      (@comp_fapp0 C y x y f r)
      (@id C y);

// Transparent constant-family Sigma/product view of the primitive record.
symbol OmegaEquivAlongView
  [C : Cat]
  [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  : Grpd
≔ @Σ_
    (@OmegaEquivLeftView C x y f)
    (λ _ : τ (@OmegaEquivLeftView C x y f),
      @OmegaEquivRightView C x y f);

// Observe the two independent inverse-and-law halves.
symbol omega_equiv_along_view
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  : τ (@OmegaEquivAlongView C x y f)
≔ @Struct_sigma
    (@OmegaEquivLeftView C x y f)
    (λ _ : τ (@OmegaEquivLeftView C x y f),
      @OmegaEquivRightView C x y f)
    (@Struct_sigma
      (Hom C y x)
      (λ l : τ (Hom C y x),
        @= (Hom C x x)
          (@comp_fapp0 C x y x l f)
          (@id C x))
      (@omega_equiv_along_left_inv C x y f u)
      (@omega_equiv_along_left_law C x y f u))
    (@Struct_sigma
      (Hom C y x)
      (λ r : τ (Hom C y x),
        @= (Hom C y y)
          (@comp_fapp0 C y x y f r)
          (@id C y))
      (@omega_equiv_along_right_inv C x y f u)
      (@omega_equiv_along_right_law C x y f u));

// Rebuild native evidence from the transparent product view.
symbol omega_equiv_along_from_view
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (w : τ (@OmegaEquivAlongView C x y f))
  : τ (@OmegaEquivAlong C x y f)
≔ @omega_equiv_along_intro
    C x y f
    (sigma_Fst (sigma_Fst w))
    (sigma_Fst (sigma_Snd w))
    (sigma_Snd (sigma_Fst w))
    (sigma_Snd (sigma_Snd w));

// Native record eta through its generated indexed eliminator.
symbol omega_equiv_along_from_view_view
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  : τ (@=
      (@OmegaEquivAlong C x y f)
      (@omega_equiv_along_from_view C x y f
        (@omega_equiv_along_view C x y f u))
      u)
≔ @omega_equiv_along_ind
    C x y
    (λ f : τ (Hom C x y),
      λ u : τ (@OmegaEquivAlong C x y f),
        @=
          (@OmegaEquivAlong C x y f)
          (@omega_equiv_along_from_view C x y f
            (@omega_equiv_along_view C x y f u))
          u)
    (λ f : τ (Hom C x y),
      λ l : τ (Hom C y x),
      λ r : τ (Hom C y x),
      λ alpha : τ (@=
        (Hom C x x)
        (@comp_fapp0 C x y x l f)
        (@id C x)),
      λ beta : τ (@=
        (Hom C y y)
        (@comp_fapp0 C y x y f r)
        (@id C y)),
      @eq_refl
        (@OmegaEquivAlong C x y f)
        (@Struct_omega_equiv_along_eq
          C x y f l r alpha beta))
    f
    u;

// Contractible left and right halves contract their transparent total view.
symbol omega_equiv_along_view_is_contr
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (hleft : τ (IsContr (@OmegaEquivLeftView C x y f)))
  (hright : τ (IsContr (@OmegaEquivRightView C x y f)))
  : τ (IsContr (@OmegaEquivAlongView C x y f))
≔ @is_contr_sigma
    (@OmegaEquivLeftView C x y f)
    (λ _ : τ (@OmegaEquivLeftView C x y f),
      @OmegaEquivRightView C x y f)
    hleft
    (λ _ : τ (@OmegaEquivLeftView C x y f), hright);

// A contractible structural view contracts the native record by its eta law.
symbol omega_equiv_along_evidence_is_contr_from_view
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (h : τ (IsContr (@OmegaEquivAlongView C x y f)))
  : τ (IsContr (@OmegaEquivAlong C x y f))
≔ @Struct_sigma
    (@OmegaEquivAlong C x y f)
    (λ c : τ (@OmegaEquivAlong C x y f),
      @Pi_grpd
        (@OmegaEquivAlong C x y f)
        (λ u : τ (@OmegaEquivAlong C x y f),
          @= (@OmegaEquivAlong C x y f) c u))
    (@omega_equiv_along_from_view C x y f (is_contr_center h))
    (λ u : τ (@OmegaEquivAlong C x y f),
      @eq_trans
        (@OmegaEquivAlong C x y f)
        (@omega_equiv_along_from_view C x y f (is_contr_center h))
        (@omega_equiv_along_from_view C x y f
          (@omega_equiv_along_view C x y f u))
        u
        (@eq_ap
          (@OmegaEquivAlongView C x y f)
          (@OmegaEquivAlong C x y f)
          (λ w : τ (@OmegaEquivAlongView C x y f),
            @omega_equiv_along_from_view C x y f w)
          (is_contr_center h)
          (@omega_equiv_along_view C x y f u)
          (is_contr_path h (@omega_equiv_along_view C x y f u)))
        (@omega_equiv_along_from_view_view C x y f u));

// At reflexivity, each half is the identity homotopy fibre over reflexivity.
symbol path_refl_left_view_is_contr
  [A : Grpd]
  (x : τ A)
  : τ (IsContr (@OmegaEquivLeftView
      (Path_cat A) x x (@eq_refl A x)))
≔ @type_equiv_fiber
    (@= A x x)
    (@= A x x)
    (@type_equiv_refl (@= A x x))
    (@eq_refl A x);

symbol path_refl_right_view_is_contr
  [A : Grpd]
  (x : τ A)
  : τ (IsContr (@OmegaEquivRightView
      (Path_cat A) x x (@eq_refl A x)))
≔ @type_equiv_fiber
    (@= A x x)
    (@= A x x)
    (@type_equiv_refl (@= A x x))
    (@eq_refl A x);

// The product view is contractible at a reflexive path.
symbol path_refl_equiv_view_is_contr
  [A : Grpd]
  (x : τ A)
  : τ (IsContr (@OmegaEquivAlongView
      (Path_cat A) x x (@eq_refl A x)))
≔ @omega_equiv_along_view_is_contr
    (Path_cat A) x x (@eq_refl A x)
    (@path_refl_left_view_is_contr A x)
    (@path_refl_right_view_is_contr A x);

// Retracting the contractible view along record eta contracts native evidence.
symbol path_refl_equiv_evidence_is_contr
  [A : Grpd]
  (x : τ A)
  : τ (IsContr (@OmegaEquivAlong
      (Path_cat A) x x (@eq_refl A x)))
≔ @omega_equiv_along_evidence_is_contr_from_view
    (Path_cat A) x x (@eq_refl A x)
    (@path_refl_equiv_view_is_contr A x);

// Path induction extends the contraction to every literal path arrow.
symbol path_equiv_evidence_is_contr
  [A : Grpd]
  [y : τ A]
  [x : τ A]
  (p : τ (@= A x y))
  : τ (IsContr (@OmegaEquivAlong (Path_cat A) x y p))
≔ @ind_eqr
    A y
    (λ x : τ A,
      λ p : τ (@= A x y),
        IsContr (@OmegaEquivAlong (Path_cat A) x y p))
    (@path_refl_equiv_evidence_is_contr A y)
    x
    p;

// Equality-valued equivalence evidence over a literal path is a proposition.
symbol path_equiv_evidence_is_prop
  [A : Grpd]
  [x y : τ A]
  (p : τ (@= A x y))
  : τ (IsPropGrpd (@OmegaEquivAlong (Path_cat A) x y p))
≔ @is_contr_is_prop
    (@OmegaEquivAlong (Path_cat A) x y p)
    (@path_equiv_evidence_is_contr A y x p);

// A retract of a proposition-valued classifier is proposition-valued.
symbol retract_is_contr_from_prop_center
  [X Y : Grpd]
  (r : τ X → τ Y)
  (s : τ Y → τ X)
  (epsilon : Π y : τ Y, τ (@= Y (r (s y)) y))
  (hX : τ (IsPropGrpd X))
  (y0 : τ Y)
  : τ (IsContr Y)
≔ @Struct_sigma
    Y
    (λ c : τ Y, @Pi_grpd Y (λ y : τ Y, @= Y c y))
    y0
    (λ y : τ Y,
      @eq_trans
        Y
        y0
        (r (s y0))
        y
        (@eq_sym Y (r (s y0)) y0 (epsilon y0))
        (@eq_trans
          Y
          (r (s y0))
          (r (s y))
          y
          (@eq_ap
            X Y r
            (s y0) (s y)
            (is_contr_center (hX (s y0) (s y))))
          (epsilon y)));

symbol is_prop_retract
  [X Y : Grpd]
  (r : τ X → τ Y)
  (s : τ Y → τ X)
  (epsilon : Π y : τ Y, τ (@= Y (r (s y)) y))
  (hX : τ (IsPropGrpd X))
  : τ (IsPropGrpd Y)
≔ λ y0 : τ Y, λ y1 : τ Y,
    @is_contr_is_prop
      Y
      (@retract_is_contr_from_prop_center X Y r s epsilon hX y0)
      y0
      y1;

// Convert a path between selected representatives back across a retraction.
symbol retract_path_to
  [X Y : Grpd]
  (r : τ X → τ Y)
  (s : τ Y → τ X)
  (epsilon : Π y : τ Y, τ (@= Y (r (s y)) y))
  [y0 y1 : τ Y]
  (q : τ (@= X (s y0) (s y1)))
  : τ (@= Y y0 y1)
≔ @eq_trans
    Y
    y0
    (r (s y0))
    y1
    (@eq_sym Y (r (s y0)) y0 (epsilon y0))
    (@eq_trans
      Y
      (r (s y0))
      (r (s y1))
      y1
      (@eq_ap X Y r (s y0) (s y1) q)
      (epsilon y1));

// Mapping a path into the retract and back is propositionally identity.
symbol retract_path_roundtrip
  [X Y : Grpd]
  (r : τ X → τ Y)
  (s : τ Y → τ X)
  (epsilon : Π y : τ Y, τ (@= Y (r (s y)) y))
  [y0 y1 : τ Y]
  (p : τ (@= Y y0 y1))
  : τ (@=
      (@= Y y0 y1)
      (@retract_path_to X Y r s epsilon y0 y1
        (@eq_ap Y X s y0 y1 p))
      p)
≔ @ind_eqr
    Y y1
    (λ y0 : τ Y,
      λ p : τ (@= Y y0 y1),
        @=
          (@= Y y0 y1)
          (@retract_path_to X Y r s epsilon y0 y1
            (@eq_ap Y X s y0 y1 p))
          p)
    (@eq_sym_trans_self Y (r (s y1)) y1 (epsilon y1))
    y0
    p;

// A retract of a set-valued classifier is set-valued.
symbol is_set_retract
  [X Y : Grpd]
  (r : τ X → τ Y)
  (s : τ Y → τ X)
  (epsilon : Π y : τ Y, τ (@= Y (r (s y)) y))
  (hX : τ (IsSetGrpd X))
  : τ (IsSetGrpd Y)
≔ λ y0 : τ Y, λ y1 : τ Y,
    @is_prop_retract
      (@= X (s y0) (s y1))
      (@= Y y0 y1)
      (λ q : τ (@= X (s y0) (s y1)),
        @retract_path_to X Y r s epsilon y0 y1 q)
      (λ p : τ (@= Y y0 y1), @eq_ap Y X s y0 y1 p)
      (λ p : τ (@= Y y0 y1),
        @retract_path_roundtrip X Y r s epsilon y0 y1 p)
      (hX (s y0) (s y1));

// Groupoidality plus set-valued objects makes every hom classifier a
// proposition, using the selected path retraction rather than a decoder.
symbol groupoidal_hom_is_prop
  [C : Cat]
  (g : τ (@IsGroupoidalCat C))
  (obj_set : τ (IsSetGrpd (Obj C)))
  (x y : τ (Obj C))
  : τ (IsPropGrpd (Hom C x y))
≔ @is_prop_retract
    (@= (Obj C) x y)
    (Hom C x y)
    (λ p : τ (@= (Obj C) x y), @path_to_hom C x y p)
    (λ f : τ (Hom C x y),
      @groupoidal_arrow_to_path C g x y f)
    (λ f : τ (Hom C x y),
      @groupoidal_path_to_arrow_retract C g x y f)
    (obj_set x y);

symbol discrete_hom_is_prop
  [C : Cat]
  (d : τ (IsDiscreteCat C))
  (x y : τ (Obj C))
  : τ (IsPropGrpd (Hom C x y))
≔ @groupoidal_hom_is_prop
    C
    (@discrete_cat_is_groupoidal C d)
    (@is_discrete_cat_obj_set C d)
    x y;

// A chosen native witness centres its left inverse-and-law fibre.
symbol discrete_equiv_left_view_is_contr
  [C : Cat]
  (d : τ (IsDiscreteCat C))
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  : τ (IsContr (@OmegaEquivLeftView C x y f))
≔ @is_contr_sigma
    (Hom C y x)
    (λ l : τ (Hom C y x),
      @= (Hom C x x)
        (@comp_fapp0 C x y x l f)
        (@id C x))
    (@Struct_sigma
      (Hom C y x)
      (λ l0 : τ (Hom C y x),
        @Pi_grpd (Hom C y x)
          (λ l : τ (Hom C y x), @= (Hom C y x) l0 l))
      (@omega_equiv_along_left_inv C x y f u)
      (λ l : τ (Hom C y x),
        is_contr_center
          ((@discrete_hom_is_prop C d y x)
            (@omega_equiv_along_left_inv C x y f u)
            l)))
    (λ l : τ (Hom C y x),
      (@discrete_hom_is_prop C d x x)
        (@comp_fapp0 C x y x l f)
        (@id C x));

// A chosen native witness centres its right inverse-and-law fibre.
symbol discrete_equiv_right_view_is_contr
  [C : Cat]
  (d : τ (IsDiscreteCat C))
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  : τ (IsContr (@OmegaEquivRightView C x y f))
≔ @is_contr_sigma
    (Hom C y x)
    (λ r : τ (Hom C y x),
      @= (Hom C y y)
        (@comp_fapp0 C y x y f r)
        (@id C y))
    (@Struct_sigma
      (Hom C y x)
      (λ r0 : τ (Hom C y x),
        @Pi_grpd (Hom C y x)
          (λ r : τ (Hom C y x), @= (Hom C y x) r0 r))
      (@omega_equiv_along_right_inv C x y f u)
      (λ r : τ (Hom C y x),
        is_contr_center
          ((@discrete_hom_is_prop C d y x)
            (@omega_equiv_along_right_inv C x y f u)
            r)))
    (λ r : τ (Hom C y x),
      (@discrete_hom_is_prop C d y y)
        (@comp_fapp0 C y x y f r)
        (@id C y));

symbol discrete_equiv_evidence_is_contr
  [C : Cat]
  (d : τ (IsDiscreteCat C))
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  : τ (IsContr (@OmegaEquivAlong C x y f))
≔ @omega_equiv_along_evidence_is_contr_from_view
    C x y f
    (@omega_equiv_along_view_is_contr
      C x y f
      (@discrete_equiv_left_view_is_contr C d x y f u)
      (@discrete_equiv_right_view_is_contr C d x y f u));

// Fixed-arrow equality-valued evidence in every zero-dimensional category is a property.
symbol discrete_equiv_evidence_is_prop
  [C : Cat]
  (d : τ (IsDiscreteCat C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  : τ (IsPropGrpd (@OmegaEquivAlong C x y f))
≔ λ u : τ (@OmegaEquivAlong C x y f),
   λ v : τ (@OmegaEquivAlong C x y f),
    (@is_contr_is_prop
      (@OmegaEquivAlong C x y f)
      (@discrete_equiv_evidence_is_contr C d x y f u))
      u v;

// Local set-truncation is the ordinary one-categorical hom condition.
symbol IsLocallySetCat
  (C : Cat)
  : Grpd
≔ @Pi_grpd
    (Obj C)
    (λ x : τ (Obj C),
      @Pi_grpd
        (Obj C)
        (λ y : τ (Obj C), IsSetGrpd (Hom C x y)));

// Elementary categorical uniqueness: any specified left inverse and right
// inverse are equal.
symbol omega_equiv_candidate_left_to_right
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (l r : τ (Hom C y x))
  (alpha : τ (@=
    (Hom C x x)
    (@comp_fapp0 C x y x l f)
    (@id C x)))
  (beta : τ (@=
    (Hom C y y)
    (@comp_fapp0 C y x y f r)
    (@id C y)))
  : τ (@= (Hom C y x) l r)
≔ @eq_trans
    (Hom C y x)
    l
    (@comp_fapp0 C y y x l
      (@comp_fapp0 C y x y f r))
    r
    (@eq_ap
      (Hom C y y)
      (Hom C y x)
      (λ h : τ (Hom C y y), @comp_fapp0 C y y x l h)
      (@id C y)
      (@comp_fapp0 C y x y f r)
      (@eq_sym
        (Hom C y y)
        (@comp_fapp0 C y x y f r)
        (@id C y)
        beta))
    (@eq_trans
      (Hom C y x)
      (@comp_fapp0 C y y x l
        (@comp_fapp0 C y x y f r))
      (@comp_fapp0 C y x x
        (@comp_fapp0 C x y x l f)
        r)
      r
      (@comp_assoc C y x y x l f r)
      (@eq_ap
        (Hom C x x)
        (Hom C y x)
        (λ h : τ (Hom C x x), @comp_fapp0 C y x x h r)
        (@comp_fapp0 C x y x l f)
        (@id C x)
        alpha));

// A proposition-valued family supplies every required dependent pathover.
symbol prop_family_pathover
  [A : Grpd]
  [P : τ A → Grpd]
  (h : Π a : τ A, τ (IsPropGrpd (P a)))
  [a0 a1 : τ A]
  (p : τ (@= A a0 a1))
  (u : τ (P a0))
  (v : τ (P a1))
  : τ (@PathOver A P a0 a1 p u v)
≔ is_contr_center
    ((h a0) u (@ind_eq A a0 a1 p P v));

// In locally set-valued categories, the left-inverse half is contractible
// once any full bi-inverse witness supplies a right inverse.
symbol locally_set_left_view_is_contr
  [C : Cat]
  (h : τ (@IsLocallySetCat C))
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  : τ (IsContr (@OmegaEquivLeftView C x y f))
≔ @Struct_sigma
    (@OmegaEquivLeftView C x y f)
    (λ centre : τ (@OmegaEquivLeftView C x y f),
      @Pi_grpd
        (@OmegaEquivLeftView C x y f)
        (λ w : τ (@OmegaEquivLeftView C x y f),
          @= (@OmegaEquivLeftView C x y f) centre w))
    (@Struct_sigma
      (Hom C y x)
      (λ l : τ (Hom C y x),
        @= (Hom C x x)
          (@comp_fapp0 C x y x l f)
          (@id C x))
      (@omega_equiv_along_left_inv C x y f u)
      (@omega_equiv_along_left_law C x y f u))
    (λ w : τ (@OmegaEquivLeftView C x y f),
      @sigma_ind
        (Hom C y x)
        (λ l : τ (Hom C y x),
          @= (Hom C x x)
            (@comp_fapp0 C x y x l f)
            (@id C x))
        (λ w : τ (@OmegaEquivLeftView C x y f),
          @=
            (@OmegaEquivLeftView C x y f)
            (@Struct_sigma
              (Hom C y x)
              (λ l : τ (Hom C y x),
                @= (Hom C x x)
                  (@comp_fapp0 C x y x l f)
                  (@id C x))
              (@omega_equiv_along_left_inv C x y f u)
              (@omega_equiv_along_left_law C x y f u))
            w)
        (λ l : τ (Hom C y x),
          λ alpha : τ (@=
            (Hom C x x)
            (@comp_fapp0 C x y x l f)
            (@id C x)),
          let p : τ (@= (Hom C y x)
              (@omega_equiv_along_left_inv C x y f u)
              l) ≔
            @eq_trans
              (Hom C y x)
              (@omega_equiv_along_left_inv C x y f u)
              (@omega_equiv_along_right_inv C x y f u)
              l
              (@omega_equiv_candidate_left_to_right
                C x y f
                (@omega_equiv_along_left_inv C x y f u)
                (@omega_equiv_along_right_inv C x y f u)
                (@omega_equiv_along_left_law C x y f u)
                (@omega_equiv_along_right_law C x y f u))
              (@eq_sym
                (Hom C y x)
                l
                (@omega_equiv_along_right_inv C x y f u)
                (@omega_equiv_candidate_left_to_right
                  C x y f
                  l
                  (@omega_equiv_along_right_inv C x y f u)
                  alpha
                  (@omega_equiv_along_right_law C x y f u)))
          in @Struct_sigma
            (@= (Hom C y x)
              (@omega_equiv_along_left_inv C x y f u)
              l)
            (λ q : τ (@= (Hom C y x)
                (@omega_equiv_along_left_inv C x y f u)
                l),
              @PathOver
                (Hom C y x)
                (λ k : τ (Hom C y x),
                  @= (Hom C x x)
                    (@comp_fapp0 C x y x k f)
                    (@id C x))
                (@omega_equiv_along_left_inv C x y f u)
                l q
                (@omega_equiv_along_left_law C x y f u)
                alpha)
            p
            (@prop_family_pathover
              (Hom C y x)
              (λ k : τ (Hom C y x),
                @= (Hom C x x)
                  (@comp_fapp0 C x y x k f)
                  (@id C x))
              (λ k : τ (Hom C y x),
                (h x x)
                  (@comp_fapp0 C x y x k f)
                  (@id C x))
              (@omega_equiv_along_left_inv C x y f u)
              l p
              (@omega_equiv_along_left_law C x y f u)
              alpha))
        w);

// The right-inverse half is dual, using the selected left inverse.
symbol locally_set_right_view_is_contr
  [C : Cat]
  (h : τ (@IsLocallySetCat C))
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  : τ (IsContr (@OmegaEquivRightView C x y f))
≔ @Struct_sigma
    (@OmegaEquivRightView C x y f)
    (λ centre : τ (@OmegaEquivRightView C x y f),
      @Pi_grpd
        (@OmegaEquivRightView C x y f)
        (λ w : τ (@OmegaEquivRightView C x y f),
          @= (@OmegaEquivRightView C x y f) centre w))
    (@Struct_sigma
      (Hom C y x)
      (λ r : τ (Hom C y x),
        @= (Hom C y y)
          (@comp_fapp0 C y x y f r)
          (@id C y))
      (@omega_equiv_along_right_inv C x y f u)
      (@omega_equiv_along_right_law C x y f u))
    (λ w : τ (@OmegaEquivRightView C x y f),
      @sigma_ind
        (Hom C y x)
        (λ r : τ (Hom C y x),
          @= (Hom C y y)
            (@comp_fapp0 C y x y f r)
            (@id C y))
        (λ w : τ (@OmegaEquivRightView C x y f),
          @=
            (@OmegaEquivRightView C x y f)
            (@Struct_sigma
              (Hom C y x)
              (λ r : τ (Hom C y x),
                @= (Hom C y y)
                  (@comp_fapp0 C y x y f r)
                  (@id C y))
              (@omega_equiv_along_right_inv C x y f u)
              (@omega_equiv_along_right_law C x y f u))
            w)
        (λ r : τ (Hom C y x),
          λ beta : τ (@=
            (Hom C y y)
            (@comp_fapp0 C y x y f r)
            (@id C y)),
          let p : τ (@= (Hom C y x)
              (@omega_equiv_along_right_inv C x y f u)
              r) ≔
            @eq_trans
              (Hom C y x)
              (@omega_equiv_along_right_inv C x y f u)
              (@omega_equiv_along_left_inv C x y f u)
              r
              (@eq_sym
                (Hom C y x)
                (@omega_equiv_along_left_inv C x y f u)
                (@omega_equiv_along_right_inv C x y f u)
                (@omega_equiv_candidate_left_to_right
                  C x y f
                  (@omega_equiv_along_left_inv C x y f u)
                  (@omega_equiv_along_right_inv C x y f u)
                  (@omega_equiv_along_left_law C x y f u)
                  (@omega_equiv_along_right_law C x y f u)))
              (@omega_equiv_candidate_left_to_right
                C x y f
                (@omega_equiv_along_left_inv C x y f u)
                r
                (@omega_equiv_along_left_law C x y f u)
                beta)
          in @Struct_sigma
            (@= (Hom C y x)
              (@omega_equiv_along_right_inv C x y f u)
              r)
            (λ q : τ (@= (Hom C y x)
                (@omega_equiv_along_right_inv C x y f u)
                r),
              @PathOver
                (Hom C y x)
                (λ k : τ (Hom C y x),
                  @= (Hom C y y)
                    (@comp_fapp0 C y x y f k)
                    (@id C y))
                (@omega_equiv_along_right_inv C x y f u)
                r q
                (@omega_equiv_along_right_law C x y f u)
                beta)
            p
            (@prop_family_pathover
              (Hom C y x)
              (λ k : τ (Hom C y x),
                @= (Hom C y y)
                  (@comp_fapp0 C y x y f k)
                  (@id C y))
              (λ k : τ (Hom C y x),
                (h y y)
                  (@comp_fapp0 C y x y f k)
                  (@id C y))
              (@omega_equiv_along_right_inv C x y f u)
              r p
              (@omega_equiv_along_right_law C x y f u)
              beta))
        w);

// Separate-left/right equality-valued evidence is proposition-valued in every locally
// set-valued category.
symbol locally_set_equiv_evidence_is_prop
  [C : Cat]
  (h : τ (@IsLocallySetCat C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  : τ (IsPropGrpd (@OmegaEquivAlong C x y f))
≔ λ u : τ (@OmegaEquivAlong C x y f),
   λ v : τ (@OmegaEquivAlong C x y f),
    (@is_contr_is_prop
      (@OmegaEquivAlong C x y f)
      (@omega_equiv_along_evidence_is_contr_from_view
        C x y f
        (@omega_equiv_along_view_is_contr
          C x y f
          (@locally_set_left_view_is_contr C h x y f u)
          (@locally_set_right_view_is_contr C h x y f u))))
      u v;

// A one-dimensional category is locally set-valued by its discrete homs.
symbol one_cat_is_locally_set
  [C : Cat]
  (h : τ (IsNCat (cat_succ cat_zero) C))
  : τ (@IsLocallySetCat C)
≔ λ x : τ (Obj C), λ y : τ (Obj C),
    @is_discrete_cat_obj_set (Hom_cat C x y) (h x y);

// The direct facade is a retract of its transparent Sigma presentation.
symbol omega_equiv_facade_is_set
  [C : Cat]
  [x y : τ (Obj C)]
  (h : τ (IsSetGrpd (@OmegaEquivSigma C x y)))
  : τ (IsSetGrpd (@OmegaEquiv C x y))
≔ @is_set_retract
    (@OmegaEquivSigma C x y)
    (@OmegaEquiv C x y)
    (λ s : τ (@OmegaEquivSigma C x y),
      @omega_sigma_to_facade C x y s)
    (λ e : τ (@OmegaEquiv C x y),
      @omega_facade_to_sigma C x y e)
    (λ e : τ (@OmegaEquiv C x y),
      @omega_facade_roundtrip C x y e)
    h;

// The plan-local equality/facade casts are literal carrier identities.
symbol object_path_cast_roundtrip
  [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (@= (Obj C) x y))
  : τ (@=
      (@= (Obj C) x y)
      (@omega_cast_to_object_path C x y
        (@object_path_cast_to_omega C x y p))
      p)
≔ @eq_refl (@= (Obj C) x y) p;

// Set-truncation transfers from the direct facade back to object equality.
symbol object_path_is_set_from_omega
  [C : Cat]
  [x y : τ (Obj C)]
  (h : τ (IsSetGrpd (@OmegaEquiv C x y)))
  : τ (IsSetGrpd (@= (Obj C) x y))
≔ @is_set_retract
    (@OmegaEquiv C x y)
    (@= (Obj C) x y)
    (λ e : τ (@OmegaEquiv C x y),
      @omega_cast_to_object_path C x y e)
    (λ p : τ (@= (Obj C) x y),
      @object_path_cast_to_omega C x y p)
    (λ p : τ (@= (Obj C) x y),
      @object_path_cast_roundtrip C x y p)
    h;

// The first-class equality-valued Sigma is set-valued in a one-dimensional category:
// its arrow base is a set and its fixed-arrow evidence fibres are properties.
symbol one_cat_omega_sigma_is_set
  [C : Cat]
  (h : τ (IsNCat (cat_succ cat_zero) C))
  (x y : τ (Obj C))
  : τ (IsSetGrpd (@OmegaEquivSigma C x y))
≔ @is_trunc_sigma
    trunc_zero
    (Hom C x y)
    (λ f : τ (Hom C x y), @OmegaEquivAlong C x y f)
    (@is_discrete_cat_obj_set (Hom_cat C x y) (h x y))
    (λ f : τ (Hom C x y),
      @prop_is_trunc_cat_dim
        cat_zero
        (@OmegaEquivAlong C x y f)
        (@locally_set_equiv_evidence_is_prop
          C
          (@one_cat_is_locally_set C h)
          x y f));

/*
  General evidence property from ordinary categorical composition.

  Once one bi-inverse witness exists, composition with its forward arrow is
  an ordinary type equivalence on each inverse-candidate hom classifier.
  The now-transparent quasi-inverse theorem contracts the two homotopy
  fibres over identity. Record eta then contracts native equality-valued evidence.
  This argument is dimension-free and adds no rewrite or unification rule.
*/
symbol omega_equiv_right_as_left_law
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  : τ (@=
      (Hom C x x)
      (@comp_fapp0 C x y x
        (@omega_equiv_along_right_inv C x y f u)
        f)
      (@id C x))
≔ @eq_trans
    (Hom C x x)
    (@comp_fapp0 C x y x
      (@omega_equiv_along_right_inv C x y f u)
      f)
    (@comp_fapp0 C x y x
      (@omega_equiv_along_left_inv C x y f u)
      f)
    (@id C x)
    (@eq_ap
      (Hom C y x)
      (Hom C x x)
      (λ k : τ (Hom C y x), @comp_fapp0 C x y x k f)
      (@omega_equiv_along_right_inv C x y f u)
      (@omega_equiv_along_left_inv C x y f u)
      (@eq_sym
        (Hom C y x)
        (@omega_equiv_along_left_inv C x y f u)
        (@omega_equiv_along_right_inv C x y f u)
        (@omega_equiv_candidate_left_to_right
          C x y f
          (@omega_equiv_along_left_inv C x y f u)
          (@omega_equiv_along_right_inv C x y f u)
          (@omega_equiv_along_left_law C x y f u)
          (@omega_equiv_along_right_law C x y f u))))
    (@omega_equiv_along_left_law C x y f u);

symbol omega_equiv_left_as_right_law
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  : τ (@=
      (Hom C y y)
      (@comp_fapp0 C y x y
        f
        (@omega_equiv_along_left_inv C x y f u))
      (@id C y))
≔ @eq_trans
    (Hom C y y)
    (@comp_fapp0 C y x y
      f
      (@omega_equiv_along_left_inv C x y f u))
    (@comp_fapp0 C y x y
      f
      (@omega_equiv_along_right_inv C x y f u))
    (@id C y)
    (@eq_ap
      (Hom C y x)
      (Hom C y y)
      (λ k : τ (Hom C y x), @comp_fapp0 C y x y f k)
      (@omega_equiv_along_left_inv C x y f u)
      (@omega_equiv_along_right_inv C x y f u)
      (@omega_equiv_candidate_left_to_right
        C x y f
        (@omega_equiv_along_left_inv C x y f u)
        (@omega_equiv_along_right_inv C x y f u)
        (@omega_equiv_along_left_law C x y f u)
        (@omega_equiv_along_right_law C x y f u)))
    (@omega_equiv_along_right_law C x y f u);

symbol omega_equiv_left_comp_map
  [C : Cat]
  [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  (k : τ (Hom C y x))
  : τ (Hom C x x)
≔ @comp_fapp0 C x y x k f;

symbol omega_equiv_left_comp_inverse
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  (h : τ (Hom C x x))
  : τ (Hom C y x)
≔ @comp_fapp0 C y x x h
    (@omega_equiv_along_right_inv C x y f u);

symbol omega_equiv_left_comp_eta
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  (k : τ (Hom C y x))
  : τ (@=
      (Hom C y x)
      (@omega_equiv_left_comp_inverse C x y f u
        (@omega_equiv_left_comp_map C x y f k))
      k)
≔ @eq_trans
    (Hom C y x)
    (@comp_fapp0 C y x x
      (@comp_fapp0 C x y x k f)
      (@omega_equiv_along_right_inv C x y f u))
    (@comp_fapp0 C y y x k
      (@comp_fapp0 C y x y f
        (@omega_equiv_along_right_inv C x y f u)))
    k
    (@eq_sym
      (Hom C y x)
      (@comp_fapp0 C y y x k
        (@comp_fapp0 C y x y f
          (@omega_equiv_along_right_inv C x y f u)))
      (@comp_fapp0 C y x x
        (@comp_fapp0 C x y x k f)
        (@omega_equiv_along_right_inv C x y f u))
      (@comp_assoc C y x y x k f
        (@omega_equiv_along_right_inv C x y f u)))
    (@eq_ap
      (Hom C y y)
      (Hom C y x)
      (λ q : τ (Hom C y y), @comp_fapp0 C y y x k q)
      (@comp_fapp0 C y x y f
        (@omega_equiv_along_right_inv C x y f u))
      (@id C y)
      (@omega_equiv_along_right_law C x y f u));

symbol omega_equiv_left_comp_epsilon
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  (h : τ (Hom C x x))
  : τ (@=
      (Hom C x x)
      (@omega_equiv_left_comp_map C x y f
        (@omega_equiv_left_comp_inverse C x y f u h))
      h)
≔ @eq_trans
    (Hom C x x)
    (@comp_fapp0 C x y x
      (@comp_fapp0 C y x x h
        (@omega_equiv_along_right_inv C x y f u))
      f)
    (@comp_fapp0 C x x x h
      (@comp_fapp0 C x y x
        (@omega_equiv_along_right_inv C x y f u)
        f))
    h
    (@eq_sym
      (Hom C x x)
      (@comp_fapp0 C x x x h
        (@comp_fapp0 C x y x
          (@omega_equiv_along_right_inv C x y f u)
          f))
      (@comp_fapp0 C x y x
        (@comp_fapp0 C y x x h
          (@omega_equiv_along_right_inv C x y f u))
        f)
      (@comp_assoc C x y x x h
        (@omega_equiv_along_right_inv C x y f u) f))
    (@eq_ap
      (Hom C x x)
      (Hom C x x)
      (λ q : τ (Hom C x x), @comp_fapp0 C x x x h q)
      (@comp_fapp0 C x y x
        (@omega_equiv_along_right_inv C x y f u)
        f)
      (@id C x)
      (@omega_equiv_right_as_left_law C x y f u));

symbol omega_equiv_left_comp_by_inverse
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  : τ (@EquivByInverse
      (Hom C y x)
      (Hom C x x)
      (λ k : τ (Hom C y x), @omega_equiv_left_comp_map C x y f k)
      (λ h : τ (Hom C x x), @omega_equiv_left_comp_inverse C x y f u h))
≔ @Product_pair_grpd
    (@Pi_grpd (Hom C y x)
      (λ k : τ (Hom C y x), @=
        (Hom C y x)
        (@omega_equiv_left_comp_inverse C x y f u
          (@omega_equiv_left_comp_map C x y f k))
        k))
    (@Pi_grpd (Hom C x x)
      (λ h : τ (Hom C x x), @=
        (Hom C x x)
        (@omega_equiv_left_comp_map C x y f
          (@omega_equiv_left_comp_inverse C x y f u h))
        h))
    (λ k : τ (Hom C y x), @omega_equiv_left_comp_eta C x y f u k)
    (λ h : τ (Hom C x x), @omega_equiv_left_comp_epsilon C x y f u h);

symbol omega_equiv_left_view_is_contr
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  : τ (IsContr (@OmegaEquivLeftView C x y f))
≔ @is_equiv_map_by_inverse
    (Hom C y x)
    (Hom C x x)
    (λ k : τ (Hom C y x), @omega_equiv_left_comp_map C x y f k)
    (λ h : τ (Hom C x x), @omega_equiv_left_comp_inverse C x y f u h)
    (@omega_equiv_left_comp_by_inverse C x y f u)
    (@id C x);
symbol omega_equiv_right_comp_map
  [C : Cat]
  [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  (k : τ (Hom C y x))
  : τ (Hom C y y)
≔ @comp_fapp0 C y x y f k;

symbol omega_equiv_right_comp_inverse
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  (h : τ (Hom C y y))
  : τ (Hom C y x)
≔ @comp_fapp0 C y y x
    (@omega_equiv_along_left_inv C x y f u)
    h;

symbol omega_equiv_right_comp_eta
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  (k : τ (Hom C y x))
  : τ (@=
      (Hom C y x)
      (@omega_equiv_right_comp_inverse C x y f u
        (@omega_equiv_right_comp_map C x y f k))
      k)
≔ @eq_trans
    (Hom C y x)
    (@comp_fapp0 C y y x
      (@omega_equiv_along_left_inv C x y f u)
      (@comp_fapp0 C y x y f k))
    (@comp_fapp0 C y x x
      (@comp_fapp0 C x y x
        (@omega_equiv_along_left_inv C x y f u)
        f)
      k)
    k
    (@comp_assoc C y x y x
      (@omega_equiv_along_left_inv C x y f u) f k)
    (@eq_ap
      (Hom C x x)
      (Hom C y x)
      (λ q : τ (Hom C x x), @comp_fapp0 C y x x q k)
      (@comp_fapp0 C x y x
        (@omega_equiv_along_left_inv C x y f u)
        f)
      (@id C x)
      (@omega_equiv_along_left_law C x y f u));

symbol omega_equiv_right_comp_epsilon
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  (h : τ (Hom C y y))
  : τ (@=
      (Hom C y y)
      (@omega_equiv_right_comp_map C x y f
        (@omega_equiv_right_comp_inverse C x y f u h))
      h)
≔ @eq_trans
    (Hom C y y)
    (@comp_fapp0 C y x y f
      (@comp_fapp0 C y y x
        (@omega_equiv_along_left_inv C x y f u)
        h))
    (@comp_fapp0 C y y y
      (@comp_fapp0 C y x y f
        (@omega_equiv_along_left_inv C x y f u))
      h)
    h
    (@comp_assoc C y y x y f
      (@omega_equiv_along_left_inv C x y f u) h)
    (@eq_ap
      (Hom C y y)
      (Hom C y y)
      (λ q : τ (Hom C y y), @comp_fapp0 C y y y q h)
      (@comp_fapp0 C y x y f
        (@omega_equiv_along_left_inv C x y f u))
      (@id C y)
      (@omega_equiv_left_as_right_law C x y f u));

symbol omega_equiv_right_comp_by_inverse
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  : τ (@EquivByInverse
      (Hom C y x)
      (Hom C y y)
      (λ k : τ (Hom C y x), @omega_equiv_right_comp_map C x y f k)
      (λ h : τ (Hom C y y), @omega_equiv_right_comp_inverse C x y f u h))
≔ @Product_pair_grpd
    (@Pi_grpd (Hom C y x)
      (λ k : τ (Hom C y x), @=
        (Hom C y x)
        (@omega_equiv_right_comp_inverse C x y f u
          (@omega_equiv_right_comp_map C x y f k))
        k))
    (@Pi_grpd (Hom C y y)
      (λ h : τ (Hom C y y), @=
        (Hom C y y)
        (@omega_equiv_right_comp_map C x y f
          (@omega_equiv_right_comp_inverse C x y f u h))
        h))
    (λ k : τ (Hom C y x), @omega_equiv_right_comp_eta C x y f u k)
    (λ h : τ (Hom C y y), @omega_equiv_right_comp_epsilon C x y f u h);

symbol omega_equiv_right_view_is_contr
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  : τ (IsContr (@OmegaEquivRightView C x y f))
≔ @is_equiv_map_by_inverse
    (Hom C y x)
    (Hom C y y)
    (λ k : τ (Hom C y x), @omega_equiv_right_comp_map C x y f k)
    (λ h : τ (Hom C y y), @omega_equiv_right_comp_inverse C x y f u h)
    (@omega_equiv_right_comp_by_inverse C x y f u)
    (@id C y);

symbol omega_equiv_along_evidence_is_contr
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  : τ (IsContr (@OmegaEquivAlong C x y f))
≔ @omega_equiv_along_evidence_is_contr_from_view
    C x y f
    (@omega_equiv_along_view_is_contr
      C x y f
      (@omega_equiv_left_view_is_contr C x y f u)
      (@omega_equiv_right_view_is_contr C x y f u));

symbol omega_equiv_along_evidence_is_prop
  [C : Cat]
  [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  : τ (IsPropGrpd (@OmegaEquivAlong C x y f))
≔ λ u : τ (@OmegaEquivAlong C x y f),
   λ v : τ (@OmegaEquivAlong C x y f),
    @is_contr_is_prop
      (@OmegaEquivAlong C x y f)
      (@omega_equiv_along_evidence_is_contr C x y f u)
      u v;

/*
  Truncation is closed under explicit retractions.

  The base contracts the retract directly. At a successor, equality in the
  retract is itself a retract of equality between selected representatives;
  the transparent TruncLevel induction then reuses the lower-level theorem.
*/
symbol is_contr_retract
  [X Y : Grpd]
  (r : τ X → τ Y)
  (s : τ Y → τ X)
  (epsilon : Π y : τ Y, τ (@= Y (r (s y)) y))
  (hX : τ (IsContr X))
  : τ (IsContr Y)
≔ @Struct_sigma
    Y
    (λ c : τ Y, @Pi_grpd Y (λ y : τ Y, @= Y c y))
    (r (is_contr_center hX))
    (λ y : τ Y,
      @eq_trans
        Y
        (r (is_contr_center hX))
        (r (s y))
        y
        (@eq_ap X Y r
          (is_contr_center hX)
          (s y)
          (is_contr_path hX (s y)))
        (epsilon y));

symbol RetractTruncClosure
  (n : TruncLevel)
  : Grpd
≔ @Pi_grpd Grpd_grpd
    (λ X : Grpd,
      @Pi_grpd Grpd_grpd
        (λ Y : Grpd,
          @Pi_grpd
            (Function_grpd X Y)
            (λ r : τ X → τ Y,
              @Pi_grpd
                (Function_grpd Y X)
                (λ s : τ Y → τ X,
                  @Pi_grpd
                    (@Pi_grpd Y
                      (λ y : τ Y, @= Y (r (s y)) y))
                    (λ _ : Π y : τ Y,
                      τ (@= Y (r (s y)) y),
                      @Function_grpd
                        (IsTruncGrpd n X)
                        (IsTruncGrpd n Y))))));

symbol is_trunc_retract
  (n : TruncLevel)
  : τ (RetractTruncClosure n)
≔ @ind_TruncLevel
    (λ n : TruncLevel, RetractTruncClosure n)
    (λ X : Grpd,
      λ Y : Grpd,
      λ r : τ X → τ Y,
      λ s : τ Y → τ X,
      λ epsilon : Π y : τ Y, τ (@= Y (r (s y)) y),
      λ hX : τ (IsContr X),
        @is_contr_retract X Y r s epsilon hX)
    (λ n : TruncLevel,
      λ ih : τ (RetractTruncClosure n),
      λ X : Grpd,
      λ Y : Grpd,
      λ r : τ X → τ Y,
      λ s : τ Y → τ X,
      λ epsilon : Π y : τ Y, τ (@= Y (r (s y)) y),
      λ hX : τ (IsTruncGrpd (trunc_succ n) X),
      λ y0 : τ Y,
      λ y1 : τ Y,
        ih
          (@= X (s y0) (s y1))
          (@= Y y0 y1)
          (λ q : τ (@= X (s y0) (s y1)),
            @retract_path_to X Y r s epsilon y0 y1 q)
          (λ p : τ (@= Y y0 y1),
            @eq_ap Y X s y0 y1 p)
          (λ p : τ (@= Y y0 y1),
            @retract_path_roundtrip X Y r s epsilon y0 y1 p)
          (hX (s y0) (s y1)))
    n;

/*
  Unconditional finite directed-dimension object truncation.

  Native equality-valued packages are truncated at the recursively available hom level:
  the arrow base uses the induction hypothesis and every evidence fibre is
  proposition-valued by the dimension-free theorem above. Explicit facade
  and equality casts are retractions, so arbitrary-level retract closure
  transfers the bound back to object equality.
*/
symbol omega_equiv_facade_is_trunc
  (n : TruncLevel)
  [C : Cat]
  [x y : τ (Obj C)]
  (h : τ (IsTruncGrpd n (@OmegaEquivSigma C x y)))
  : τ (IsTruncGrpd n (@OmegaEquiv C x y))
≔ @is_trunc_retract
    n
    (@OmegaEquivSigma C x y)
    (@OmegaEquiv C x y)
    (λ s : τ (@OmegaEquivSigma C x y),
      @omega_sigma_to_facade C x y s)
    (λ e : τ (@OmegaEquiv C x y),
      @omega_facade_to_sigma C x y e)
    (λ e : τ (@OmegaEquiv C x y),
      @omega_facade_roundtrip C x y e)
    h;

symbol object_path_is_trunc_from_omega
  (n : TruncLevel)
  [C : Cat]
  [x y : τ (Obj C)]
  (h : τ (IsTruncGrpd n (@OmegaEquiv C x y)))
  : τ (IsTruncGrpd n (@= (Obj C) x y))
≔ @is_trunc_retract
    n
    (@OmegaEquiv C x y)
    (@= (Obj C) x y)
    (λ e : τ (@OmegaEquiv C x y),
      @omega_cast_to_object_path C x y e)
    (λ p : τ (@= (Obj C) x y),
      @object_path_cast_to_omega C x y p)
    (λ p : τ (@= (Obj C) x y),
      @object_path_cast_roundtrip C x y p)
    h;

symbol NCatObjTruncClosure
  (n : CatDim)
  : Grpd
≔ @Pi_grpd
    (Obj Cat_cat)
    (λ C : Cat,
      @Function_grpd
        (IsNCat n C)
        (IsObjTruncCat (cat_dim_trunc_level n) C));

symbol ncat_obj_trunc
  (n : CatDim)
  : τ (NCatObjTruncClosure n)
≔ @ind_CatDim
    (λ n : CatDim, NCatObjTruncClosure n)
    (λ C : Cat,
      λ h : τ (IsNCat cat_zero C),
        @is_discrete_cat_obj_set C h)
    (λ n : CatDim,
      λ ih : τ (NCatObjTruncClosure n),
      λ C : Cat,
      λ h : τ (IsNCat (cat_succ n) C),
      λ x : τ (Obj C),
      λ y : τ (Obj C),
        @object_path_is_trunc_from_omega
          (cat_dim_trunc_level n)
          C x y
          (@omega_equiv_facade_is_trunc
            (cat_dim_trunc_level n)
            C x y
            (@is_trunc_sigma
              (cat_dim_trunc_level n)
              (Hom C x y)
              (λ f : τ (Hom C x y),
                @OmegaEquivAlong C x y f)
              (ih (Hom_cat C x y) (h x y))
              (λ f : τ (Hom C x y),
                @prop_is_trunc_cat_dim
                  n
                  (@OmegaEquivAlong C x y f)
                  (@omega_equiv_along_evidence_is_prop C x y f)))))
    n;

// Readable one-category specialization routes through the general recursion.
symbol one_cat_obj_trunc
  [C : Cat]
  (h : τ (IsNCat (cat_succ cat_zero) C))
  : τ (IsObjTruncCat
      (cat_dim_trunc_level (cat_succ cat_zero)) C)
≔ @ncat_obj_trunc (cat_succ cat_zero) C h;
