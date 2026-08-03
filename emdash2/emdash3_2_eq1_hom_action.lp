require open emdash.emdash3_2;

/*
  Equality-valued omega-equivalence: native action on next homs.

  This is a one-way derived extension of emdash3_2.lp. It proves that the hom
  action F_1(x,y) of a category-level OmegaEquivAlong witness is itself
  an OmegaEquivAlong witness. The construction is transparent: it adds no
  primitive, opaque theorem, rewrite rule, unification rule, decoder, or
  D0/D0b compatibility dependency.

  The proof replaces separate left and right inverse functors by the left
  inverse equipped with the generic half-adjoint counit. It then uses
  functoriality, naturality, equality-to-transformation comparison, and the
  half-adjoint triangle to prove the two hom-functor cancellation laws.

  Proof-engineering lemmas are protected module implementation details. The
  hom-action proof core exposes omega_equiv_along_fapp1 as its ordinary
  action owner; its projections and the complete protected proof chain remain
  computational. One reusable selected-left-inverse law and public
  groupoidality consumers follow below.
*/

// -----------------------------------------------------------------------------------------------
// Selected inverse functor and its object components

// L : B -> A is the selected left inverse of F.
protected symbol eq1_left_functor
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  : τ (Functor B A)
≔ @omega_equiv_along_left_inv Cat_cat A B F u;

// R : B -> A is the independently supplied right inverse of F.
protected symbol eq1_right_functor
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  : τ (Functor B A)
≔ @omega_equiv_along_right_inv Cat_cat A B F u;

// The left cancellation path L F = id_A, viewed as a transformation.
protected symbol eq1_left_to_transf
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  : τ (@Transf
      A A
      (@comp_cat_fapp0 A B A (eq1_left_functor u) F)
      (@id_func A))
≔ @path_to_hom
    (Functor_cat A A)
    (@comp_cat_fapp0 A B A (eq1_left_functor u) F)
    (@id_func A)
    (@omega_equiv_along_left_law Cat_cat A B F u);

// The reverse transformation id_A => L F.
protected symbol eq1_left_from_transf
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  : τ (@Transf
      A A
      (@id_func A)
      (@comp_cat_fapp0 A B A (eq1_left_functor u) F))
≔ @path_to_hom
    (Functor_cat A A)
    (@id_func A)
    (@comp_cat_fapp0 A B A (eq1_left_functor u) F)
    (@path_sym
      (Obj (Functor_cat A A))
      (@comp_cat_fapp0 A B A (eq1_left_functor u) F)
      (@id_func A)
      (@omega_equiv_along_left_law Cat_cat A B F u));

// Pointwise component L(F x) -> x of the left cancellation.
protected symbol eq1_left_to_component
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x : τ (Obj A))
  : τ (Hom A
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
      x)
≔ @tapp0_fapp0
    A A
    (@comp_cat_fapp0 A B A (eq1_left_functor u) F)
    (@id_func A)
    x
    (eq1_left_to_transf u);

// Pointwise inverse component x -> L(F x).
protected symbol eq1_left_from_component
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x : τ (Obj A))
  : τ (Hom A
      x
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
≔ @tapp0_fapp0
    A A
    (@id_func A)
    (@comp_cat_fapp0 A B A (eq1_left_functor u) F)
    x
    (eq1_left_from_transf u);

// Candidate inverse to F_1(x,y): apply L_1, then conjugate endpoints.
protected symbol eq1_fapp1_left_inv
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x y : τ (Obj A))
  : τ (Functor
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (Hom_cat A x y))
≔ @comp_cat_fapp0
    (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
    (Hom_cat A
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y)))
    (Hom_cat A x y)
    (@Hom_func
      A
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
      x
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y))
      y
      (eq1_left_from_component u x)
      (eq1_left_to_component u y))
    (@fapp1_func
      B A
      (eq1_left_functor u)
      (@fapp0 A B F x)
      (@fapp0 A B F y));

// Separate left/right inverse functors are propositionally equal.
protected symbol eq1_left_right_functor_path
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  : τ (@=
      (Obj (Functor_cat B A))
      (eq1_left_functor u)
      (eq1_right_functor u))
≔ @eq_trans
    (Obj (Functor_cat B A))
    (eq1_left_functor u)
    (@comp_cat_fapp0
      B A A
      (@comp_cat_fapp0
        A B A
        (eq1_left_functor u)
        F)
      (eq1_right_functor u))
    (eq1_right_functor u)
    (@eq_ap
      (Obj (Functor_cat B B))
      (Obj (Functor_cat B A))
      (λ H : τ (Functor B B),
        @comp_cat_fapp0 B B A (eq1_left_functor u) H)
      (@id_func B)
      (@comp_cat_fapp0
        B A B
        F
        (eq1_right_functor u))
      (@eq_sym
        (Obj (Functor_cat B B))
        (@comp_cat_fapp0 B A B F (eq1_right_functor u))
        (@id_func B)
        (@omega_equiv_along_right_law Cat_cat A B F u)))
    (@eq_ap
      (Obj (Functor_cat A A))
      (Obj (Functor_cat B A))
      (λ H : τ (Functor A A),
        @comp_cat_fapp0 B A A H (eq1_right_functor u))
      (@comp_cat_fapp0 A B A (eq1_left_functor u) F)
      (@id_func A)
      (@omega_equiv_along_left_law Cat_cat A B F u));

// The generic half-adjoint counit equips L with an adjusted F L = id_B law.
protected symbol eq1_left_functor_right_law
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  : τ (@=
      (Obj (Functor_cat B B))
      (@comp_cat_fapp0 B A B F (eq1_left_functor u))
      (@id_func B))
≔ @eq_trans
    (Obj (Functor_cat B B))
    (@comp_cat_fapp0 B A B F (eq1_left_functor u))
    (@comp_cat_fapp0 B A B F (eq1_right_functor u))
    (@id_func B)
    (@eq_ap
      (Obj (Functor_cat B A))
      (Obj (Functor_cat B B))
      (λ G : τ (Functor B A), @comp_cat_fapp0 B A B F G)
      (eq1_left_functor u)
      (eq1_right_functor u)
      (eq1_left_right_functor_path u))
    (@omega_equiv_along_right_law Cat_cat A B F u);

// -----------------------------------------------------------------------------------------------
// Equality evaluation and the half-adjoint component equation

// Evaluate a functor equality H = id_A at an object.
protected symbol eq1_functor_path_component
  [A : Cat]
  [H : τ (Functor A A)]
  (q : τ (@=
      (Obj (Functor_cat A A))
      H
      (@id_func A)))
  (x : τ (Obj A))
  : τ (@=
      (Obj A)
      (@fapp0 A A H x)
      x)
≔ @eq_ap
    (Obj (Functor_cat A A))
    (Obj A)
    (λ K : τ (Functor A A), @fapp0 A A K x)
    H
    (@id_func A)
    q;

// Functoriality of eq_ap over path composition.
protected symbol eq1_eq_ap_trans
  [X Y : Grpd]
  (f : τ X → τ Y)
  [x y : τ X]
  (p : τ (@= X x y))
  [z : τ X]
  (q : τ (@= X y z))
  : τ (@=
      (@= Y (f x) (f z))
      (@eq_ap X Y f x z (@eq_trans X x y z p q))
      (@eq_trans
        Y (f x) (f y) (f z)
        (@eq_ap X Y f x y p)
        (@eq_ap X Y f y z q)))
≔ @ind_eqr
    X
    y
    (λ x : τ X,
      λ p : τ (@= X x y),
      @Pi_grpd
        X
        (λ z : τ X,
          @Pi_grpd
            (@= X y z)
            (λ q : τ (@= X y z),
              @=
                (@= Y (f x) (f z))
                (@eq_ap X Y f x z (@eq_trans X x y z p q))
                (@eq_trans
                  Y (f x) (f y) (f z)
                  (@eq_ap X Y f x y p)
                  (@eq_ap X Y f y z q)))))
    (λ z : τ X,
      λ q : τ (@= X y z),
      @eq_refl (@= Y (f y) (f z)) (@eq_ap X Y f y z q))
    x
    p
    z
    q;

// Functoriality of eq_ap over path reversal.
protected symbol eq1_eq_ap_sym
  [X Y : Grpd]
  (f : τ X → τ Y)
  [x y : τ X]
  (p : τ (@= X x y))
  : τ (@=
      (@= Y (f y) (f x))
      (@eq_ap X Y f y x (@eq_sym X x y p))
      (@eq_sym Y (f x) (f y) (@eq_ap X Y f x y p)))
≔ @ind_eqr
    X
    y
    (λ x : τ X,
      λ p : τ (@= X x y),
      @=
        (@= Y (f y) (f x))
        (@eq_ap X Y f y x (@eq_sym X x y p))
        (@eq_sym Y (f x) (f y) (@eq_ap X Y f x y p)))
    (@eq_refl
      (@= Y (f y) (f y))
      (@eq_refl Y (f y)))
    x
    p;

// Pointwise component of the original left cancellation law.
protected symbol eq1_left_path_component
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x : τ (Obj A))
  : τ (@=
      (Obj A)
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
      x)
≔ eq1_functor_path_component
    (@omega_equiv_along_left_law Cat_cat A B F u)
    x;

// Pointwise comparison between the selected left and right inverse functors.
protected symbol eq1_left_right_path_component
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (b : τ (Obj B))
  : τ (@=
      (Obj B)
      (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))
      b)
≔ eq1_functor_path_component
    (eq1_left_functor_right_law u)
    b;

// Standard adjusted counit at an object of B.
protected symbol eq1_adjusted_right_component_path
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (b : τ (Obj B))
  : τ (@=
      (Obj B)
      (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))
      b)
≔ @eq_trans
    (Obj B)
    (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))
    (@fapp0 A B F
      (@fapp0 B A (eq1_left_functor u)
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) b))))
    b
    (@eq_sym
      (Obj B)
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u)
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) b))))
      (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))
      (eq1_left_right_path_component
        u
        (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))))
    (@eq_trans
      (Obj B)
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u)
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) b))))
      (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))
      b
      (@eq_ap
        (Obj A)
        (Obj B)
        (λ z : τ (Obj A), @fapp0 A B F z)
        (@fapp0 B A (eq1_left_functor u)
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) b)))
        (@fapp0 B A (eq1_left_functor u) b)
        (eq1_left_path_component
          u
          (@fapp0 B A (eq1_left_functor u) b)))
      (eq1_left_right_path_component u b));

// Forward triangle path before the generic theorem is applied.
protected symbol eq1_triangle_forward_path
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x : τ (Obj A))
  : τ (@=
      (Obj B)
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
      (@fapp0 A B F x))
≔ @eq_ap
    (Obj A) (Obj B)
    (λ z : τ (Obj A), @fapp0 A B F z)
    (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
    x
    (eq1_left_path_component u x);

// The generic half-adjoint triangle specialized to category objects.
protected symbol eq1_half_adjoint_triangle_point
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x : τ (Obj A))
  : τ (@=
      (@= (Obj B)
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@fapp0 A B F x))
      (eq1_triangle_forward_path u x)
      (eq1_adjusted_right_component_path u (@fapp0 A B F x)))
≔ @half_adjoint_triangle
    (Obj A)
    (Obj B)
    (λ a : τ (Obj A), @fapp0 A B F a)
    (λ b : τ (Obj B),
      @fapp0 B A (eq1_left_functor u) b)
    (λ a : τ (Obj A), eq1_left_path_component u a)
    (λ b : τ (Obj B), eq1_left_right_path_component u b)
    x;

// First functor-level segment of the adjusted counit.
protected symbol eq1_adjusted_right_stage1_path
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  : τ (@=
      (Obj (Functor_cat B B))
      (@comp_cat_fapp0 B A B F (eq1_left_functor u))
      (@comp_cat_fapp0
        B B B
        (@comp_cat_fapp0 B A B F (eq1_left_functor u))
        (@comp_cat_fapp0 B A B F (eq1_left_functor u))))
≔ @eq_ap
    (Obj (Functor_cat B B))
    (Obj (Functor_cat B B))
    (λ K : τ (Functor B B),
      @comp_cat_fapp0
        B B B K
        (@comp_cat_fapp0 B A B F (eq1_left_functor u)))
    (@id_func B)
    (@comp_cat_fapp0 B A B F (eq1_left_functor u))
    (@eq_sym
      (Obj (Functor_cat B B))
      (@comp_cat_fapp0 B A B F (eq1_left_functor u))
      (@id_func B)
      (eq1_left_functor_right_law u));

// Second functor-level segment of the adjusted counit.
protected symbol eq1_adjusted_right_stage2_path
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  : τ (@=
      (Obj (Functor_cat B B))
      (@comp_cat_fapp0
        B B B
        (@comp_cat_fapp0 B A B F (eq1_left_functor u))
        (@comp_cat_fapp0 B A B F (eq1_left_functor u)))
      (@comp_cat_fapp0 B A B F (eq1_left_functor u)))
≔ @eq_ap
    (Obj (Functor_cat A A))
    (Obj (Functor_cat B B))
    (λ H : τ (Functor A A),
      @comp_cat_fapp0
        B A B F
        (@comp_cat_fapp0 B A A H (eq1_left_functor u)))
    (@comp_cat_fapp0 A B A (eq1_left_functor u) F)
    (@id_func A)
    (@omega_equiv_along_left_law Cat_cat A B F u);

// The adjusted counit factored into the two stages and the original law.
protected symbol eq1_adjusted_right_law_factored
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  : τ (@=
      (Obj (Functor_cat B B))
      (@comp_cat_fapp0 B A B F (eq1_left_functor u))
      (@id_func B))
≔ @eq_trans
    (Obj (Functor_cat B B))
    (@comp_cat_fapp0 B A B F (eq1_left_functor u))
    (@comp_cat_fapp0
      B B B
      (@comp_cat_fapp0 B A B F (eq1_left_functor u))
      (@comp_cat_fapp0 B A B F (eq1_left_functor u)))
    (@id_func B)
    (eq1_adjusted_right_stage1_path u)
    (@eq_trans
      (Obj (Functor_cat B B))
      (@comp_cat_fapp0
        B B B
        (@comp_cat_fapp0 B A B F (eq1_left_functor u))
        (@comp_cat_fapp0 B A B F (eq1_left_functor u)))
      (@comp_cat_fapp0 B A B F (eq1_left_functor u))
      (@id_func B)
      (eq1_adjusted_right_stage2_path u)
      (eq1_left_functor_right_law u));

// Evaluation of the first adjusted-counit stage.
protected symbol eq1_adjusted_stage1_component
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (b : τ (Obj B))
  : τ (@=
      (Obj B)
      (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u)
          (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b)))))
≔ @eq_ap
    (Obj (Functor_cat B B))
    (Obj B)
    (λ K : τ (Functor B B), @fapp0 B B K b)
    (@comp_cat_fapp0 B A B F (eq1_left_functor u))
    (@comp_cat_fapp0
      B B B
      (@comp_cat_fapp0 B A B F (eq1_left_functor u))
      (@comp_cat_fapp0 B A B F (eq1_left_functor u)))
    (eq1_adjusted_right_stage1_path u);

// Evaluation of the second adjusted-counit stage.
protected symbol eq1_adjusted_stage2_component
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (b : τ (Obj B))
  : τ (@=
      (Obj B)
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u)
          (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))))
      (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b)))
≔ @eq_ap
    (Obj (Functor_cat B B))
    (Obj B)
    (λ K : τ (Functor B B), @fapp0 B B K b)
    (@comp_cat_fapp0
      B B B
      (@comp_cat_fapp0 B A B F (eq1_left_functor u))
      (@comp_cat_fapp0 B A B F (eq1_left_functor u)))
    (@comp_cat_fapp0 B A B F (eq1_left_functor u))
    (eq1_adjusted_right_stage2_path u);

// The first evaluated stage agrees with its explicit endpoint path.
protected symbol eq1_adjusted_stage1_component_agrees
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (b : τ (Obj B))
  : τ (@=
      (@= (Obj B)
        (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u)
            (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b)))))
      (eq1_adjusted_stage1_component u b)
      (@eq_sym
        (Obj B)
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u)
            (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))))
        (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))
        (eq1_left_right_path_component
          u
          (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b)))))
≔ @eq_trans
    (@= (Obj B)
      (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u)
          (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b)))))
    (eq1_adjusted_stage1_component u b)
    (@eq_ap
      (Obj (Functor_cat B B))
      (Obj B)
      (λ K : τ (Functor B B),
        @fapp0 B B K
          (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b)))
      (@id_func B)
      (@comp_cat_fapp0 B A B F (eq1_left_functor u))
      (@eq_sym
        (Obj (Functor_cat B B))
        (@comp_cat_fapp0 B A B F (eq1_left_functor u))
        (@id_func B)
        (eq1_left_functor_right_law u)))
    (@eq_sym
      (Obj B)
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u)
          (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))))
      (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))
      (eq1_left_right_path_component
        u
        (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))))
    (@eq_ap_comp
      (Obj (Functor_cat B B))
      (Obj (Functor_cat B B))
      (Obj B)
      (λ K : τ (Functor B B),
        @comp_cat_fapp0
          B B B K
          (@comp_cat_fapp0 B A B F (eq1_left_functor u)))
      (λ K : τ (Functor B B), @fapp0 B B K b)
      (@id_func B)
      (@comp_cat_fapp0 B A B F (eq1_left_functor u))
      (@eq_sym
        (Obj (Functor_cat B B))
        (@comp_cat_fapp0 B A B F (eq1_left_functor u))
        (@id_func B)
        (eq1_left_functor_right_law u)))
    (@eq1_eq_ap_sym
      (Obj (Functor_cat B B))
      (Obj B)
      (λ K : τ (Functor B B),
        @fapp0 B B K
          (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b)))
      (@comp_cat_fapp0 B A B F (eq1_left_functor u))
      (@id_func B)
      (eq1_left_functor_right_law u));

// The second evaluated stage agrees with its explicit endpoint path.
protected symbol eq1_adjusted_stage2_component_agrees
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (b : τ (Obj B))
  : τ (@=
      (@= (Obj B)
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u)
            (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))))
        (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b)))
      (eq1_adjusted_stage2_component u b)
      (@eq_ap
        (Obj A) (Obj B)
        (λ z : τ (Obj A), @fapp0 A B F z)
        (@fapp0 B A (eq1_left_functor u)
          (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b)))
        (@fapp0 B A (eq1_left_functor u) b)
        (eq1_left_path_component
          u
          (@fapp0 B A (eq1_left_functor u) b))))
≔ @eq_trans
    (@= (Obj B)
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u)
          (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))))
      (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b)))
    (eq1_adjusted_stage2_component u b)
    (@eq_ap
      (Obj (Functor_cat A A))
      (Obj B)
      (λ H : τ (Functor A A),
        @fapp0 A B F (@fapp0 A A H (@fapp0 B A (eq1_left_functor u) b)))
      (@comp_cat_fapp0 A B A (eq1_left_functor u) F)
      (@id_func A)
      (@omega_equiv_along_left_law Cat_cat A B F u))
    (@eq_ap
      (Obj A) (Obj B)
      (λ z : τ (Obj A), @fapp0 A B F z)
      (@fapp0 B A (eq1_left_functor u)
        (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b)))
      (@fapp0 B A (eq1_left_functor u) b)
      (eq1_left_path_component
        u
        (@fapp0 B A (eq1_left_functor u) b)))
    (@eq_ap_comp
      (Obj (Functor_cat A A))
      (Obj (Functor_cat B B))
      (Obj B)
      (λ H : τ (Functor A A),
        @comp_cat_fapp0
          B A B F
          (@comp_cat_fapp0 B A A H (eq1_left_functor u)))
      (λ K : τ (Functor B B), @fapp0 B B K b)
      (@comp_cat_fapp0 A B A (eq1_left_functor u) F)
      (@id_func A)
      (@omega_equiv_along_left_law Cat_cat A B F u))
    (@eq_sym
      (@= (Obj B)
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u)
            (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))))
        (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b)))
      (@eq_ap
        (Obj A) (Obj B)
        (λ z : τ (Obj A), @fapp0 A B F z)
        (@fapp0 B A (eq1_left_functor u)
          (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b)))
        (@fapp0 B A (eq1_left_functor u) b)
        (eq1_left_path_component
          u
          (@fapp0 B A (eq1_left_functor u) b)))
      (@eq_ap
        (Obj (Functor_cat A A))
        (Obj B)
        (λ H : τ (Functor A A),
          @fapp0 A B F (@fapp0 A A H (@fapp0 B A (eq1_left_functor u) b)))
        (@comp_cat_fapp0 A B A (eq1_left_functor u) F)
        (@id_func A)
        (@omega_equiv_along_left_law Cat_cat A B F u))
      (@eq_ap_comp
        (Obj (Functor_cat A A))
        (Obj A)
        (Obj B)
        (λ H : τ (Functor A A),
          @fapp0 A A H (@fapp0 B A (eq1_left_functor u) b))
        (λ z : τ (Obj A), @fapp0 A B F z)
        (@comp_cat_fapp0 A B A (eq1_left_functor u) F)
        (@id_func A)
        (@omega_equiv_along_left_law Cat_cat A B F u)));

// Direct evaluation of the factored adjusted counit.
protected symbol eq1_adjusted_component_raw
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (b : τ (Obj B))
  : τ (@=
      (Obj B)
      (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))
      b)
≔ eq1_functor_path_component
    (eq1_adjusted_right_law_factored u)
    b;

// Evaluation maps a composite functor path to composite object paths.
protected symbol eq1_functor_path_component_trans
  [A : Cat]
  [H K L : τ (Functor A A)]
  (p : τ (@= (Obj (Functor_cat A A)) H K))
  (q : τ (@= (Obj (Functor_cat A A)) K L))
  (x : τ (Obj A))
  : τ (@=
      (@= (Obj A) (@fapp0 A A H x) (@fapp0 A A L x))
      (@eq_ap
        (Obj (Functor_cat A A))
        (Obj A)
        (λ T : τ (Functor A A), @fapp0 A A T x)
        H L
        (@eq_trans (Obj (Functor_cat A A)) H K L p q))
      (@eq_trans
        (Obj A)
        (@fapp0 A A H x)
        (@fapp0 A A K x)
        (@fapp0 A A L x)
        (@eq_ap
          (Obj (Functor_cat A A))
          (Obj A)
          (λ T : τ (Functor A A), @fapp0 A A T x)
          H K p)
        (@eq_ap
          (Obj (Functor_cat A A))
          (Obj A)
          (λ T : τ (Functor A A), @fapp0 A A T x)
          K L q)))
≔ @eq1_eq_ap_trans
    (Obj (Functor_cat A A))
    (Obj A)
    (λ T : τ (Functor A A), @fapp0 A A T x)
    H K p L q;
// The direct and explicitly staged adjusted-counit components agree.
protected symbol eq1_adjusted_component_agrees
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (b : τ (Obj B))
  : τ (@=
      (@= (Obj B)
        (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))
        b)
      (eq1_adjusted_component_raw u b)
      (eq1_adjusted_right_component_path u b))
≔ begin
  assume A B F u b;
  simplify eq1_adjusted_component_raw;
  simplify eq1_functor_path_component;
  simplify eq1_adjusted_right_law_factored;
  simplify rule off;
  rewrite eq1_functor_path_component_trans
    (eq1_adjusted_right_stage1_path u)
    (@eq_trans
      (Obj (Functor_cat B B))
      (@comp_cat_fapp0
        B B B
        (@comp_cat_fapp0 B A B F (eq1_left_functor u))
        (@comp_cat_fapp0 B A B F (eq1_left_functor u)))
      (@comp_cat_fapp0 B A B F (eq1_left_functor u))
      (@id_func B)
      (eq1_adjusted_right_stage2_path u)
      (eq1_left_functor_right_law u))
    b;
  rewrite eq1_functor_path_component_trans
    (eq1_adjusted_right_stage2_path u)
    (eq1_left_functor_right_law u)
    b;
  change τ (@=
    (@= (Obj B)
      (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))
      b)
    (@eq_trans
      (Obj B)
      (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u)
          (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))))
      b
      (eq1_adjusted_stage1_component u b)
      (@eq_trans
        (Obj B)
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u)
            (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))))
        (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))
        b
        (eq1_adjusted_stage2_component u b)
        (eq1_left_right_path_component u b)))
    (eq1_adjusted_right_component_path u b));
  rewrite eq1_adjusted_stage1_component_agrees u b;
  rewrite eq1_adjusted_stage2_component_agrees u b;
  refine @eq_refl
    (@= (Obj B)
      (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))
      b)
    (eq1_adjusted_right_component_path u b)
end;

// -----------------------------------------------------------------------------------------------
// Equality-to-transformation comparisons

// Forward transformation component induced by a functor path to identity.
protected symbol eq1_path_to_component
  [A : Cat]
  [H : τ (Functor A A)]
  (q : τ (@=
      (Obj (Functor_cat A A))
      H
      (@id_func A)))
  (x : τ (Obj A))
  : τ (Hom A (@fapp0 A A H x) x)
≔ @tapp0_fapp0
    A A H (@id_func A) x
    (@path_to_hom
      (Functor_cat A A)
      H
      (@id_func A)
      q);

// Reverse transformation component induced by a functor path to identity.
protected symbol eq1_path_from_component
  [A : Cat]
  [H : τ (Functor A A)]
  (q : τ (@=
      (Obj (Functor_cat A A))
      H
      (@id_func A)))
  (x : τ (Obj A))
  : τ (Hom A x (@fapp0 A A H x))
≔ @tapp0_fapp0
    A A (@id_func A) H x
    (@path_to_hom
      (Functor_cat A A)
      (@id_func A)
      H
      (@path_sym
        (Obj (Functor_cat A A))
        H
        (@id_func A)
        q));

// The forward transformation component agrees with the evaluated path.
protected symbol eq1_path_to_component_agrees
  [A : Cat]
  [H : τ (Functor A A)]
  (q : τ (@=
      (Obj (Functor_cat A A))
      H
      (@id_func A)))
  (x : τ (Obj A))
  : τ (@=
      (Hom A (@fapp0 A A H x) x)
      (eq1_path_to_component q x)
      (@path_to_hom
        A
        (@fapp0 A A H x)
        x
        (eq1_functor_path_component q x)))
≔ @ind_eqr
    (Obj (Functor_cat A A))
    (@id_func A)
    (λ H : τ (Functor A A),
      λ q : τ (@=
        (Obj (Functor_cat A A)) H (@id_func A)),
      @Pi_grpd
        (Obj A)
        (λ x : τ (Obj A),
          @=
            (Hom A (@fapp0 A A H x) x)
            (eq1_path_to_component q x)
            (@path_to_hom
              A
              (@fapp0 A A H x)
              x
              (eq1_functor_path_component q x))))
    (λ x : τ (Obj A),
      @eq_refl (Hom A x x) (@id A x))
    H
    q
    x;

// The reverse component agrees with reversal of the evaluated path.
protected symbol eq1_path_from_component_eq_sym_agrees
  [A : Cat]
  [H : τ (Functor A A)]
  (q : τ (@=
      (Obj (Functor_cat A A))
      H
      (@id_func A)))
  (x : τ (Obj A))
  : τ (@=
      (Hom A x (@fapp0 A A H x))
      (eq1_path_from_component q x)
      (@path_to_hom
        A
        x
        (@fapp0 A A H x)
        (@eq_sym
          (Obj A)
          (@fapp0 A A H x)
          x
          (eq1_functor_path_component q x))))
≔ @ind_eqr
    (Obj (Functor_cat A A))
    (@id_func A)
    (λ H : τ (Functor A A),
      λ q : τ (@=
        (Obj (Functor_cat A A)) H (@id_func A)),
      @Pi_grpd
        (Obj A)
        (λ x : τ (Obj A),
          @=
            (Hom A x (@fapp0 A A H x))
            (eq1_path_from_component q x)
            (@path_to_hom
              A
              x
              (@fapp0 A A H x)
              (@eq_sym
                (Obj A)
                (@fapp0 A A H x)
                x
                (eq1_functor_path_component q x)))))
    (λ x : τ (Obj A),
      @eq_refl (Hom A x x) (@id A x))
    H
    q
    x;

// Applying F_1 to a path-induced arrow agrees with eq_ap by F_0.
protected symbol eq1_path_to_hom_fapp1_agrees
  [A B : Cat]
  (F : τ (Functor A B))
  [x y : τ (Obj A)]
  (p : τ (@= (Obj A) x y))
  : τ (@=
      (Hom B (@fapp0 A B F x) (@fapp0 A B F y))
      (@fapp1_fapp0
        A B F x y
        (@path_to_hom A x y p))
      (@path_to_hom
        B
        (@fapp0 A B F x)
        (@fapp0 A B F y)
        (@eq_ap
          (Obj A) (Obj B)
          (λ z : τ (Obj A), @fapp0 A B F z)
          x y p)))
≔ @ind_eqr
    (Obj A)
    y
    (λ x : τ (Obj A),
      λ p : τ (@= (Obj A) x y),
      @=
        (Hom B (@fapp0 A B F x) (@fapp0 A B F y))
        (@fapp1_fapp0
          A B F x y
          (@path_to_hom A x y p))
        (@path_to_hom
          B
          (@fapp0 A B F x)
          (@fapp0 A B F y)
          (@eq_ap
            (Obj A) (Obj B)
            (λ z : τ (Obj A), @fapp0 A B F z)
            x y p)))
    (@eq_refl
      (Hom B (@fapp0 A B F y) (@fapp0 A B F y))
      (@id B (@fapp0 A B F y)))
    x
    p;

// The forward hom triangle agrees with the generic triangle path.
protected symbol eq1_triangle_forward_hom_agrees
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x : τ (Obj A))
  : τ (@=
      (Hom B
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@fapp0 A B F x))
      (@fapp1_fapp0
        A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
        x
        (eq1_left_to_component u x))
      (@path_to_hom
        B
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@fapp0 A B F x)
        (eq1_triangle_forward_path u x)))
≔ @eq_trans
    (Hom B
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
      (@fapp0 A B F x))
    (@fapp1_fapp0
      A B F
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
      x
      (eq1_left_to_component u x))
    (@fapp1_fapp0
      A B F
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
      x
      (@path_to_hom
        A
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
        x
        (eq1_left_path_component u x)))
    (@path_to_hom
      B
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
      (@fapp0 A B F x)
      (eq1_triangle_forward_path u x))
    (@eq_ap
      (Hom A
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
        x)
      (Hom B
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@fapp0 A B F x))
      (λ h : τ (Hom A
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
          x),
        @fapp1_fapp0
          A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
          x
          h)
      (eq1_left_to_component u x)
      (@path_to_hom
        A
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
        x
        (eq1_left_path_component u x))
      (eq1_path_to_component_agrees
        (@omega_equiv_along_left_law Cat_cat A B F u)
        x))
    (@eq1_path_to_hom_fapp1_agrees
      A B F
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
      x
      (eq1_left_path_component u x));

// The adjusted counit arrow agrees with its equality-valued component.
protected symbol eq1_adjusted_to_hom_agrees
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (b : τ (Obj B))
  : τ (@=
      (Hom B
        (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))
        b)
      (eq1_path_to_component
        (eq1_adjusted_right_law_factored u) b)
      (@path_to_hom
        B
        (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))
        b
        (eq1_adjusted_right_component_path u b)))
≔ @eq_trans
    (Hom B
      (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))
      b)
    (eq1_path_to_component
      (eq1_adjusted_right_law_factored u) b)
    (@path_to_hom
      B
      (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))
      b
      (eq1_adjusted_component_raw u b))
    (@path_to_hom
      B
      (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))
      b
      (eq1_adjusted_right_component_path u b))
    (eq1_path_to_component_agrees
      (eq1_adjusted_right_law_factored u) b)
    (@eq_ap
      (@= (Obj B)
        (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))
        b)
      (Hom B
        (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))
        b)
      (λ p : τ (@= (Obj B)
          (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))
          b),
        @path_to_hom
          B
          (@fapp0 A B F (@fapp0 B A (eq1_left_functor u) b))
          b
          p)
      (eq1_adjusted_component_raw u b)
      (eq1_adjusted_right_component_path u b)
      (eq1_adjusted_component_agrees u b));

// Forward half-adjoint triangle expressed as a hom equality.
protected symbol eq1_half_adjoint_triangle_hom
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x : τ (Obj A))
  : τ (@=
      (Hom B
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@fapp0 A B F x))
      (@path_to_hom
        B
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@fapp0 A B F x)
        (eq1_triangle_forward_path u x))
      (@path_to_hom
        B
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@fapp0 A B F x)
        (eq1_adjusted_right_component_path
          u (@fapp0 A B F x))))
≔ @eq_ap
    (@= (Obj B)
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
      (@fapp0 A B F x))
    (Hom B
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
      (@fapp0 A B F x))
    (λ p : τ (@= (Obj B)
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@fapp0 A B F x)),
      @path_to_hom
        B
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@fapp0 A B F x)
        p)
    (eq1_triangle_forward_path u x)
    (eq1_adjusted_right_component_path u (@fapp0 A B F x))
    (eq1_half_adjoint_triangle_point u x);

// Forward triangle at a chosen endpoint component.
protected symbol eq1_half_adjoint_triangle_to_component
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x : τ (Obj A))
  : τ (@=
      (Hom B
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@fapp0 A B F x))
      (@fapp1_fapp0
        A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
        x
        (eq1_left_to_component u x))
      (eq1_path_to_component
        (eq1_adjusted_right_law_factored u)
        (@fapp0 A B F x)))
≔ @eq_trans
    (Hom B
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
      (@fapp0 A B F x))
    (@fapp1_fapp0
      A B F
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
      x
      (eq1_left_to_component u x))
    (@path_to_hom
      B
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
      (@fapp0 A B F x)
      (eq1_triangle_forward_path u x))
    (eq1_path_to_component
      (eq1_adjusted_right_law_factored u)
      (@fapp0 A B F x))
    (eq1_triangle_forward_hom_agrees u x)
    (@eq_trans
      (Hom B
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@fapp0 A B F x))
      (@path_to_hom
        B
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@fapp0 A B F x)
        (eq1_triangle_forward_path u x))
      (@path_to_hom
        B
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@fapp0 A B F x)
        (eq1_adjusted_right_component_path
          u (@fapp0 A B F x)))
      (eq1_path_to_component
        (eq1_adjusted_right_law_factored u)
        (@fapp0 A B F x))
      (eq1_half_adjoint_triangle_hom u x)
      (@eq_sym
        (Hom B
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
          (@fapp0 A B F x))
        (eq1_path_to_component
          (eq1_adjusted_right_law_factored u)
          (@fapp0 A B F x))
        (@path_to_hom
          B
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
          (@fapp0 A B F x)
          (eq1_adjusted_right_component_path
            u (@fapp0 A B F x)))
        (eq1_adjusted_to_hom_agrees u (@fapp0 A B F x))));

// Raw forward triangle before endpoint projection normalization.
protected symbol eq1_half_adjoint_triangle_raw
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x : τ (Obj A))
  : τ (@=
      (@= (Obj B)
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@fapp0 A B F x))
      (eq1_triangle_forward_path u x)
      (eq1_adjusted_component_raw u (@fapp0 A B F x)))
≔ @eq_trans
    (@= (Obj B)
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
      (@fapp0 A B F x))
    (eq1_triangle_forward_path u x)
    (eq1_adjusted_right_component_path u (@fapp0 A B F x))
    (eq1_adjusted_component_raw u (@fapp0 A B F x))
    (eq1_half_adjoint_triangle_point u x)
    (@eq_sym
      (@= (Obj B)
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@fapp0 A B F x))
      (eq1_adjusted_component_raw u (@fapp0 A B F x))
      (eq1_adjusted_right_component_path u (@fapp0 A B F x))
      (eq1_adjusted_component_agrees u (@fapp0 A B F x)));

// Reversed half-adjoint triangle path.
protected symbol eq1_half_adjoint_triangle_reverse_path
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x : τ (Obj A))
  : τ (@=
      (@= (Obj B)
        (@fapp0 A B F x)
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))))
      (@eq_sym
        (Obj B)
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@fapp0 A B F x)
        (eq1_triangle_forward_path u x))
      (@eq_sym
        (Obj B)
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@fapp0 A B F x)
        (eq1_adjusted_component_raw u (@fapp0 A B F x))))
≔ @eq_ap
    (@= (Obj B)
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
      (@fapp0 A B F x))
    (@= (Obj B)
      (@fapp0 A B F x)
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))))
    (λ p : τ (@= (Obj B)
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@fapp0 A B F x)),
      @eq_sym
        (Obj B)
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@fapp0 A B F x)
        p)
    (eq1_triangle_forward_path u x)
    (eq1_adjusted_component_raw u (@fapp0 A B F x))
    (eq1_half_adjoint_triangle_raw u x);

// The reversed hom triangle agrees with the reversed generic path.
protected symbol eq1_triangle_reverse_hom_agrees
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x : τ (Obj A))
  : τ (@=
      (Hom B
        (@fapp0 A B F x)
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))))
      (@fapp1_fapp0
        A B F
        x
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
        (eq1_left_from_component u x))
      (@path_to_hom
        B
        (@fapp0 A B F x)
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@eq_sym
          (Obj B)
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
          (@fapp0 A B F x)
          (eq1_triangle_forward_path u x))))
≔ @eq_trans
    (Hom B
      (@fapp0 A B F x)
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))))
    (@fapp1_fapp0
      A B F
      x
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
      (eq1_left_from_component u x))
    (@fapp1_fapp0
      A B F
      x
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
      (@path_to_hom
        A
        x
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
        (@eq_sym
          (Obj A)
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
          x
          (eq1_left_path_component u x))))
    (@path_to_hom
      B
      (@fapp0 A B F x)
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
      (@eq_sym
        (Obj B)
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@fapp0 A B F x)
        (eq1_triangle_forward_path u x)))
    (@eq_ap
      (Hom A
        x
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
      (Hom B
        (@fapp0 A B F x)
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))))
      (λ h : τ (Hom A
          x
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))),
        @fapp1_fapp0
          A B F
          x
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
          h)
      (eq1_left_from_component u x)
      (@path_to_hom
        A
        x
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
        (@eq_sym
          (Obj A)
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
          x
          (eq1_left_path_component u x)))
      (eq1_path_from_component_eq_sym_agrees
        (@omega_equiv_along_left_law Cat_cat A B F u)
        x))
    (@eq_trans
      (Hom B
        (@fapp0 A B F x)
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))))
      (@fapp1_fapp0
        A B F
        x
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
        (@path_to_hom
          A
          x
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
          (@eq_sym
            (Obj A)
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
            x
            (eq1_left_path_component u x))))
      (@path_to_hom
        B
        (@fapp0 A B F x)
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@eq_ap
          (Obj A) (Obj B)
          (λ z : τ (Obj A), @fapp0 A B F z)
          x
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
          (@eq_sym
            (Obj A)
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
            x
            (eq1_left_path_component u x))))
      (@path_to_hom
        B
        (@fapp0 A B F x)
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@eq_sym
          (Obj B)
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
          (@fapp0 A B F x)
          (eq1_triangle_forward_path u x)))
      (@eq1_path_to_hom_fapp1_agrees
        A B F
        x
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
        (@eq_sym
          (Obj A)
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
          x
          (eq1_left_path_component u x)))
      (@eq_ap
        (@= (Obj B)
          (@fapp0 A B F x)
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))))
        (Hom B
          (@fapp0 A B F x)
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))))
        (λ p : τ (@= (Obj B)
            (@fapp0 A B F x)
            (@fapp0 A B F
              (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))),
          @path_to_hom
            B
            (@fapp0 A B F x)
            (@fapp0 A B F
              (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
            p)
        (@eq_ap
          (Obj A) (Obj B)
          (λ z : τ (Obj A), @fapp0 A B F z)
          x
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
          (@eq_sym
            (Obj A)
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
            x
            (eq1_left_path_component u x)))
        (@eq_sym
          (Obj B)
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
          (@fapp0 A B F x)
          (eq1_triangle_forward_path u x))
        (@eq1_eq_ap_sym
          (Obj A) (Obj B)
          (λ z : τ (Obj A), @fapp0 A B F z)
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
          x
          (eq1_left_path_component u x))));

// Reverse triangle at a chosen endpoint component.
protected symbol eq1_half_adjoint_triangle_from_component
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x : τ (Obj A))
  : τ (@=
      (Hom B
        (@fapp0 A B F x)
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))))
      (@fapp1_fapp0
        A B F
        x
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
        (eq1_left_from_component u x))
      (eq1_path_from_component
        (eq1_adjusted_right_law_factored u)
        (@fapp0 A B F x)))
≔ @eq_trans
    (Hom B
      (@fapp0 A B F x)
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))))
    (@fapp1_fapp0
      A B F
      x
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
      (eq1_left_from_component u x))
    (@path_to_hom
      B
      (@fapp0 A B F x)
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
      (@eq_sym
        (Obj B)
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@fapp0 A B F x)
        (eq1_triangle_forward_path u x)))
    (eq1_path_from_component
      (eq1_adjusted_right_law_factored u)
      (@fapp0 A B F x))
    (eq1_triangle_reverse_hom_agrees u x)
    (@eq_trans
      (Hom B
        (@fapp0 A B F x)
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))))
      (@path_to_hom
        B
        (@fapp0 A B F x)
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@eq_sym
          (Obj B)
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
          (@fapp0 A B F x)
          (eq1_triangle_forward_path u x)))
      (@path_to_hom
        B
        (@fapp0 A B F x)
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@eq_sym
          (Obj B)
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
          (@fapp0 A B F x)
          (eq1_adjusted_component_raw u (@fapp0 A B F x))))
      (eq1_path_from_component
        (eq1_adjusted_right_law_factored u)
        (@fapp0 A B F x))
      (@eq_ap
        (@= (Obj B)
          (@fapp0 A B F x)
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))))
        (Hom B
          (@fapp0 A B F x)
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))))
        (λ p : τ (@= (Obj B)
            (@fapp0 A B F x)
            (@fapp0 A B F
              (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))),
          @path_to_hom
            B
            (@fapp0 A B F x)
            (@fapp0 A B F
              (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
            p)
        (@eq_sym
          (Obj B)
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
          (@fapp0 A B F x)
          (eq1_triangle_forward_path u x))
        (@eq_sym
          (Obj B)
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
          (@fapp0 A B F x)
          (eq1_adjusted_component_raw u (@fapp0 A B F x)))
        (eq1_half_adjoint_triangle_reverse_path u x))
      (@eq_sym
        (Hom B
          (@fapp0 A B F x)
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))))
        (eq1_path_from_component
          (eq1_adjusted_right_law_factored u)
          (@fapp0 A B F x))
        (@path_to_hom
          B
          (@fapp0 A B F x)
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
          (@eq_sym
            (Obj B)
            (@fapp0 A B F
              (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
            (@fapp0 A B F x)
            (eq1_adjusted_component_raw u (@fapp0 A B F x))))
        (eq1_path_from_component_eq_sym_agrees
          (eq1_adjusted_right_law_factored u)
          (@fapp0 A B F x))));

// -----------------------------------------------------------------------------------------------
// Hom conjugation and functor-algebra comparison

// Conjugation endofunctor induced by a path H = id.
protected symbol eq1_path_conjugate_hom
  [A : Cat]
  [H : τ (Functor A A)]
  (q : τ (@=
      (Obj (Functor_cat A A))
      H
      (@id_func A)))
  (x y : τ (Obj A))
  : τ (Functor (Hom_cat A x y) (Hom_cat A x y))
≔ @comp_cat_fapp0
    (Hom_cat A x y)
    (Hom_cat A (@fapp0 A A H x) (@fapp0 A A H y))
    (Hom_cat A x y)
    (@Hom_func
      A
      (@fapp0 A A H x)
      x
      (@fapp0 A A H y)
      y
      (eq1_path_from_component q x)
      (eq1_path_to_component q y))
    (@fapp1_func A A H x y);

// Path-induced endpoint conjugation is propositionally the identity functor.
protected symbol eq1_path_conjugate_hom_law
  [A : Cat]
  [H : τ (Functor A A)]
  (q : τ (@=
      (Obj (Functor_cat A A))
      H
      (@id_func A)))
  (x y : τ (Obj A))
  : τ (@=
      (Obj (Functor_cat (Hom_cat A x y) (Hom_cat A x y)))
      (eq1_path_conjugate_hom q x y)
      (@id_func (Hom_cat A x y)))
≔ @ind_eqr
    (Obj (Functor_cat A A))
    (@id_func A)
    (λ H : τ (Obj (Functor_cat A A)),
      λ q : τ (@=
        (Obj (Functor_cat A A))
        H
        (@id_func A)),
      @=
        (Obj (Functor_cat (Hom_cat A x y) (Hom_cat A x y)))
        (eq1_path_conjugate_hom q x y)
        (@id_func (Hom_cat A x y)))
    (@eq_refl
      (Obj (Functor_cat (Hom_cat A x y) (Hom_cat A x y)))
      (@id_func (Hom_cat A x y)))
    H
    q;

// Raw right composite F_1 followed by the selected inverse hom functor.
protected symbol eq1_fapp1_left_right_conjugate_raw
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x y : τ (Obj A))
  : τ (Functor
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y)))
≔ @comp_cat_fapp0
    (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
    (Hom_cat B
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y))))
    (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
    (@Hom_func
      B
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
      (@fapp0 A B F x)
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y)))
      (@fapp0 A B F y)
      (@fapp1_fapp0
        A B F
        x
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
        (eq1_left_from_component u x))
      (@fapp1_fapp0
        A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y))
        y
        (eq1_left_to_component u y)))
    (@fapp1_func
      B B
      (@comp_cat_fapp0 B A B F (eq1_left_functor u))
      (@fapp0 A B F x)
      (@fapp0 A B F y));

// Naturality square for hom action along a functor path.
protected symbol eq1_functor_path_Hom_fapp1_naturality
  [A B : Cat]
  (F : τ (Functor A B))
  [H : τ (Functor A A)]
  (q : τ (@=
      (Obj (Functor_cat A A))
      H
      (@id_func A)))
  (x y : τ (Obj A))
  : τ (@=
      (Obj (Functor_cat
        (Hom_cat A (@fapp0 A A H x) (@fapp0 A A H y))
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))))
      (@comp_cat_fapp0
        (Hom_cat A (@fapp0 A A H x) (@fapp0 A A H y))
        (Hom_cat A x y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (@fapp1_func A B F x y)
        (@Hom_func
          A
          (@fapp0 A A H x) x
          (@fapp0 A A H y) y
          (eq1_path_from_component q x)
          (eq1_path_to_component q y)))
      (@comp_cat_fapp0
        (Hom_cat A (@fapp0 A A H x) (@fapp0 A A H y))
        (Hom_cat B
          (@fapp0 A B F (@fapp0 A A H x))
          (@fapp0 A B F (@fapp0 A A H y)))
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (@Hom_func
          B
          (@fapp0 A B F (@fapp0 A A H x))
          (@fapp0 A B F x)
          (@fapp0 A B F (@fapp0 A A H y))
          (@fapp0 A B F y)
          (@fapp1_fapp0
            A B F
            x
            (@fapp0 A A H x)
            (eq1_path_from_component q x))
          (@fapp1_fapp0
            A B F
            (@fapp0 A A H y)
            y
            (eq1_path_to_component q y)))
        (@fapp1_func
          A B F
          (@fapp0 A A H x)
          (@fapp0 A A H y))))
≔ @ind_eqr
    (Obj (Functor_cat A A))
    (@id_func A)
    (λ H : τ (Functor A A),
      λ q : τ (@=
        (Obj (Functor_cat A A)) H (@id_func A)),
      @Pi_grpd
        (Obj A)
        (λ x : τ (Obj A),
          @Pi_grpd
            (Obj A)
            (λ y : τ (Obj A),
              @=
                (Obj (Functor_cat
                  (Hom_cat A
                    (@fapp0 A A H x)
                    (@fapp0 A A H y))
                  (Hom_cat B
                    (@fapp0 A B F x)
                    (@fapp0 A B F y))))
                (@comp_cat_fapp0
                  (Hom_cat A
                    (@fapp0 A A H x)
                    (@fapp0 A A H y))
                  (Hom_cat A x y)
                  (Hom_cat B
                    (@fapp0 A B F x)
                    (@fapp0 A B F y))
                  (@fapp1_func A B F x y)
                  (@Hom_func
                    A
                    (@fapp0 A A H x) x
                    (@fapp0 A A H y) y
                    (eq1_path_from_component q x)
                    (eq1_path_to_component q y)))
                (@comp_cat_fapp0
                  (Hom_cat A
                    (@fapp0 A A H x)
                    (@fapp0 A A H y))
                  (Hom_cat B
                    (@fapp0 A B F (@fapp0 A A H x))
                    (@fapp0 A B F (@fapp0 A A H y)))
                  (Hom_cat B
                    (@fapp0 A B F x)
                    (@fapp0 A B F y))
                  (@Hom_func
                    B
                    (@fapp0 A B F (@fapp0 A A H x))
                    (@fapp0 A B F x)
                    (@fapp0 A B F (@fapp0 A A H y))
                    (@fapp0 A B F y)
                    (@fapp1_fapp0
                      A B F
                      x
                      (@fapp0 A A H x)
                      (eq1_path_from_component q x))
                    (@fapp1_fapp0
                      A B F
                      (@fapp0 A A H y)
                      y
                      (eq1_path_to_component q y)))
                  (@fapp1_func
                    A B F
                    (@fapp0 A A H x)
                    (@fapp0 A A H y))))))
    (λ x : τ (Obj A),
      λ y : τ (Obj A),
      @eq_refl
        (Obj (Functor_cat
          (Hom_cat A x y)
          (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))))
        (@fapp1_func A B F x y))
    H
    q
    x
    y;

// Intermediate functor produced by hom-action naturality.
protected symbol eq1_fapp1_left_right_naturality_middle
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x y : τ (Obj A))
  : τ (Functor
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y)))
≔ @comp_cat_fapp0
    (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
    (Hom_cat A
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y)))
    (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
    (@comp_cat_fapp0
      (Hom_cat A
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y)))
      (Hom_cat A x y)
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (@fapp1_func A B F x y)
      (@Hom_func
        A
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
        x
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y))
        y
        (eq1_left_from_component u x)
        (eq1_left_to_component u y)))
    (@fapp1_func
      B A
      (eq1_left_functor u)
      (@fapp0 A B F x)
      (@fapp0 A B F y));

// Intermediate endpoint-conjugation functor.
protected symbol eq1_fapp1_left_right_conjugate_middle
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x y : τ (Obj A))
  : τ (Functor
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y)))
≔ @comp_cat_fapp0
    (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
    (Hom_cat A
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y)))
    (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
    (@comp_cat_fapp0
      (Hom_cat A
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y)))
      (Hom_cat B
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y))))
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (@Hom_func
        B
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@fapp0 A B F x)
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y)))
        (@fapp0 A B F y)
        (@fapp1_fapp0
          A B F
          x
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
          (eq1_left_from_component u x))
        (@fapp1_fapp0
          A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y))
          y
          (eq1_left_to_component u y)))
      (@fapp1_func
        A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y))))
    (@fapp1_func
      B A
      (eq1_left_functor u)
      (@fapp0 A B F x)
      (@fapp0 A B F y));

// Associativity comparison from the raw composite to the naturality form.
protected symbol eq1_fapp1_left_right_assoc_step
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x y : τ (Obj A))
  : τ (@=
      (Obj (Functor_cat
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))))
      (@comp_cat_fapp0
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (Hom_cat A x y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (@fapp1_func A B F x y)
        (eq1_fapp1_left_inv u x y))
      (eq1_fapp1_left_right_naturality_middle u x y))
≔ @comp_assoc
    Cat_cat
    (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
    (Hom_cat A
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y)))
    (Hom_cat A x y)
    (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
    (@fapp1_func A B F x y)
    (@Hom_func
      A
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
      x
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y))
      y
      (eq1_left_from_component u x)
      (eq1_left_to_component u y))
    (@fapp1_func
      B A
      (eq1_left_functor u)
      (@fapp0 A B F x)
      (@fapp0 A B F y));

// Naturality comparison between the two intermediate functors.
protected symbol eq1_fapp1_left_right_naturality_step
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x y : τ (Obj A))
  : τ (@=
      (Obj (Functor_cat
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))))
      (eq1_fapp1_left_right_naturality_middle u x y)
      (eq1_fapp1_left_right_conjugate_middle u x y))
≔ @eq_ap
    (Obj (Functor_cat
      (Hom_cat A
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y)))
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))))
    (Obj (Functor_cat
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))))
    (λ K : τ (Functor
        (Hom_cat A
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y)))
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))),
      @comp_cat_fapp0
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (Hom_cat A
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y)))
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        K
        (@fapp1_func
          B A
          (eq1_left_functor u)
          (@fapp0 A B F x)
          (@fapp0 A B F y)))
    (@comp_cat_fapp0
      (Hom_cat A
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y)))
      (Hom_cat A x y)
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (@fapp1_func A B F x y)
      (@Hom_func
        A
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
        x
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y))
        y
        (eq1_left_from_component u x)
        (eq1_left_to_component u y)))
    (@comp_cat_fapp0
      (Hom_cat A
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y)))
      (Hom_cat B
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y))))
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (@Hom_func
        B
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@fapp0 A B F x)
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y)))
        (@fapp0 A B F y)
        (@fapp1_fapp0
          A B F
          x
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
          (eq1_left_from_component u x))
        (@fapp1_fapp0
          A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y))
          y
          (eq1_left_to_component u y)))
      (@fapp1_func
        A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y))))
    (@eq1_functor_path_Hom_fapp1_naturality
      A B F
      (@comp_cat_fapp0 A B A (eq1_left_functor u) F)
      (@omega_equiv_along_left_law Cat_cat A B F u)
      x y);

// Final associativity comparison to raw endpoint conjugation.
protected symbol eq1_fapp1_left_right_raw_assoc_step
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x y : τ (Obj A))
  : τ (@=
      (Obj (Functor_cat
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))))
      (eq1_fapp1_left_right_conjugate_raw u x y)
      (eq1_fapp1_left_right_conjugate_middle u x y))
≔ @comp_assoc
    Cat_cat
    (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
    (Hom_cat A
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y)))
    (Hom_cat B
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y))))
    (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
    (@Hom_func
      B
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
      (@fapp0 A B F x)
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y)))
      (@fapp0 A B F y)
      (@fapp1_fapp0
        A B F
        x
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
        (eq1_left_from_component u x))
      (@fapp1_fapp0
        A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y))
        y
        (eq1_left_to_component u y)))
    (@fapp1_func
      A B F
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y)))
    (@fapp1_func
      B A
      (eq1_left_functor u)
      (@fapp0 A B F x)
      (@fapp0 A B F y));

// The raw right composite equals raw endpoint conjugation propositionally.
protected symbol eq1_fapp1_left_right_raw_path
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x y : τ (Obj A))
  : τ (@=
      (Obj (Functor_cat
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))))
      (@comp_cat_fapp0
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (Hom_cat A x y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (@fapp1_func A B F x y)
        (eq1_fapp1_left_inv u x y))
      (eq1_fapp1_left_right_conjugate_raw u x y))
≔ @eq_trans
    (Obj (Functor_cat
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))))
    (@comp_cat_fapp0
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (Hom_cat A x y)
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (@fapp1_func A B F x y)
      (eq1_fapp1_left_inv u x y))
    (eq1_fapp1_left_right_naturality_middle u x y)
    (eq1_fapp1_left_right_conjugate_raw u x y)
    (eq1_fapp1_left_right_assoc_step u x y)
    (@eq_trans
      (Obj (Functor_cat
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))))
      (eq1_fapp1_left_right_naturality_middle u x y)
      (eq1_fapp1_left_right_conjugate_middle u x y)
      (eq1_fapp1_left_right_conjugate_raw u x y)
      (eq1_fapp1_left_right_naturality_step u x y)
      (@eq_sym
        (Obj (Functor_cat
          (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
          (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))))
        (eq1_fapp1_left_right_conjugate_raw u x y)
        (eq1_fapp1_left_right_conjugate_middle u x y)
        (eq1_fapp1_left_right_raw_assoc_step u x y)));

// -----------------------------------------------------------------------------------------------
// Adjusted endpoint conjugation and final cancellation laws

// Endpoint conjugation obtained from adjusted-counit components.
protected symbol eq1_adjusted_Hom_func_actual
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x y : τ (Obj A))
  : τ (Functor
      (Hom_cat B
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y))))
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y)))
≔ @Hom_func
    B
    (@fapp0 A B F
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
    (@fapp0 A B F x)
    (@fapp0 A B F
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y)))
    (@fapp0 A B F y)
    (@fapp1_fapp0
      A B F
      x
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
      (eq1_left_from_component u x))
    (@fapp1_fapp0
      A B F
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y))
      y
      (eq1_left_to_component u y));

// The same conjugation after replacing its source endpoint path.
protected symbol eq1_adjusted_Hom_func_source_replaced
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x y : τ (Obj A))
  : τ (Functor
      (Hom_cat B
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y))))
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y)))
≔ @Hom_func
    B
    (@fapp0 A B F
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
    (@fapp0 A B F x)
    (@fapp0 A B F
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y)))
    (@fapp0 A B F y)
    (eq1_path_from_component
      (eq1_adjusted_right_law_factored u)
      (@fapp0 A B F x))
    (@fapp1_fapp0
      A B F
      (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y))
      y
      (eq1_left_to_component u y));

// Equality between adjusted conjugation and its canonical path form.
protected symbol eq1_adjusted_Hom_func_path
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x y : τ (Obj A))
  : τ (@=
      (Obj (Functor_cat
        (Hom_cat B
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y))))
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))))
      (eq1_adjusted_Hom_func_actual u x y)
      (@Hom_func
        B
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@fapp0 A B F x)
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y)))
        (@fapp0 A B F y)
        (eq1_path_from_component
          (eq1_adjusted_right_law_factored u)
          (@fapp0 A B F x))
        (eq1_path_to_component
          (eq1_adjusted_right_law_factored u)
          (@fapp0 A B F y))))
≔ @eq_trans
    (Obj (Functor_cat
      (Hom_cat B
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y))))
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))))
    (eq1_adjusted_Hom_func_actual u x y)
    (eq1_adjusted_Hom_func_source_replaced u x y)
    (@Hom_func
      B
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
      (@fapp0 A B F x)
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y)))
      (@fapp0 A B F y)
      (eq1_path_from_component
        (eq1_adjusted_right_law_factored u)
        (@fapp0 A B F x))
      (eq1_path_to_component
        (eq1_adjusted_right_law_factored u)
        (@fapp0 A B F y)))
    (@eq_ap
      (Hom B
        (@fapp0 A B F x)
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))))
      (Obj (Functor_cat
        (Hom_cat B
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y))))
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))))
      (λ g : τ (Hom B
          (@fapp0 A B F x)
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))),
        @Hom_func
          B
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
          (@fapp0 A B F x)
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y)))
          (@fapp0 A B F y)
          g
          (@fapp1_fapp0
            A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y))
            y
            (eq1_left_to_component u y)))
      (@fapp1_fapp0
        A B F
        x
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x))
        (eq1_left_from_component u x))
      (eq1_path_from_component
        (eq1_adjusted_right_law_factored u)
        (@fapp0 A B F x))
      (eq1_half_adjoint_triangle_from_component u x))
    (@eq_ap
      (Hom B
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y)))
        (@fapp0 A B F y))
      (Obj (Functor_cat
        (Hom_cat B
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y))))
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))))
      (λ f : τ (Hom B
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y)))
          (@fapp0 A B F y)),
        @Hom_func
          B
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
          (@fapp0 A B F x)
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y)))
          (@fapp0 A B F y)
          (eq1_path_from_component
            (eq1_adjusted_right_law_factored u)
            (@fapp0 A B F x))
          f)
      (@fapp1_fapp0
        A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y))
        y
        (eq1_left_to_component u y))
      (eq1_path_to_component
        (eq1_adjusted_right_law_factored u)
        (@fapp0 A B F y))
      (eq1_half_adjoint_triangle_to_component u y));

// Raw endpoint conjugation equals adjusted endpoint conjugation.
protected symbol eq1_fapp1_left_right_raw_adjusted_path
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x y : τ (Obj A))
  : τ (@=
      (Obj (Functor_cat
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))))
      (eq1_fapp1_left_right_conjugate_raw u x y)
      (eq1_path_conjugate_hom
        (eq1_adjusted_right_law_factored u)
        (@fapp0 A B F x)
        (@fapp0 A B F y)))
≔ @eq_ap
    (Obj (Functor_cat
      (Hom_cat B
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
        (@fapp0 A B F
          (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y))))
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))))
    (Obj (Functor_cat
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))))
    (λ K : τ (Functor
        (Hom_cat B
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y))))
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))),
      @comp_cat_fapp0
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (Hom_cat B
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
          (@fapp0 A B F
            (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y))))
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        K
        (@fapp1_func
          B B
          (@comp_cat_fapp0 B A B F (eq1_left_functor u))
          (@fapp0 A B F x)
          (@fapp0 A B F y)))
    (eq1_adjusted_Hom_func_actual u x y)
    (@Hom_func
      B
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F x)))
      (@fapp0 A B F x)
      (@fapp0 A B F
        (@fapp0 B A (eq1_left_functor u) (@fapp0 A B F y)))
      (@fapp0 A B F y)
      (eq1_path_from_component
        (eq1_adjusted_right_law_factored u)
        (@fapp0 A B F x))
      (eq1_path_to_component
        (eq1_adjusted_right_law_factored u)
        (@fapp0 A B F y)))
    (eq1_adjusted_Hom_func_path u x y);

// Right cancellation: F_1 followed by its selected inverse equals identity.
protected symbol eq1_fapp1_left_right_law
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x y : τ (Obj A))
  : τ (@=
      (Obj (Functor_cat
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))))
      (@comp_cat_fapp0
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (Hom_cat A x y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (@fapp1_func A B F x y)
        (eq1_fapp1_left_inv u x y))
      (@id_func
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))))
≔ begin
  assume A B F u x y;
  rewrite eq1_fapp1_left_right_raw_path u x y;
  rewrite eq1_fapp1_left_right_raw_adjusted_path u x y;
  refine eq1_path_conjugate_hom_law
    (eq1_adjusted_right_law_factored u)
    (@fapp0 A B F x)
    (@fapp0 A B F y)
end;

// Left cancellation follows from conjugating the original left law.
protected symbol eq1_fapp1_left_left_law
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x y : τ (Obj A))
  : τ (@=
      (Obj (Functor_cat (Hom_cat A x y) (Hom_cat A x y)))
      (@comp_cat_fapp0
        (Hom_cat A x y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (Hom_cat A x y)
        (eq1_fapp1_left_inv u x y)
        (@fapp1_func A B F x y))
      (@id_func (Hom_cat A x y)))
≔ eq1_path_conjugate_hom_law
    (@omega_equiv_along_left_law Cat_cat A B F u)
    x y;

// -----------------------------------------------------------------------------------------------
// Public owners

// The selected left inverse of a Cat-level equivalence also cancels on the right.
symbol omega_equiv_along_cat_left_inv_right_law
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  : τ (@=
      (Obj (Functor_cat B B))
      (@comp_cat_fapp0
        B A B
        F
        (@omega_equiv_along_left_inv Cat_cat A B F u))
      (@id_func B))
≔ eq1_left_functor_right_law u;

// An equality-valued omega-equivalence acts by equivalences on every next hom.
symbol omega_equiv_along_fapp1
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x y : τ (Obj A))
  : τ (@OmegaEquivAlong
      Cat_cat
      (Hom_cat A x y)
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (@fapp1_func A B F x y))
≔ @omega_equiv_along_intro
    Cat_cat
    (Hom_cat A x y)
    (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
    (@fapp1_func A B F x y)
    (eq1_fapp1_left_inv u x y)
    (eq1_fapp1_left_inv u x y)
    (eq1_fapp1_left_left_law u x y)
    (eq1_fapp1_left_right_law u x y);

/*
  General internal groupoidality acts homwise.

  The selected equality-valued witness for Core(C) -> C acts directly through the native
  equality-valued next-hom owner. No D0/D0b conversion, decoder, eliminator,
  rewrite rule, or unification equation is introduced.
*/
symbol groupoidal_core_homwise
  [C : Cat]
  (g : τ (@IsGroupoidalCat C))
  (x y : τ (Obj C))
  : τ (@OmegaEquivAlong
      Cat_cat
      (Path_cat (@= (Obj C) x y))
      (Hom_cat C x y)
      (@core_incl_hom_func C x y))
≔ @omega_equiv_along_fapp1
    (Core_cat C)
    C
    (Core_incl_func C)
    g
    x
    y;

// The selected right inverse reads a directed arrow as an object path.
symbol groupoidal_arrow_to_path_func
  [C : Cat]
  (g : τ (@IsGroupoidalCat C))
  (x y : τ (Obj C))
  : τ (Functor
      (Hom_cat C x y)
      (Path_cat (@= (Obj C) x y)))
≔ @omega_equiv_along_right_inv
    Cat_cat
    (Path_cat (@= (Obj C) x y))
    (Hom_cat C x y)
    (@core_incl_hom_func C x y)
    (@groupoidal_core_homwise C g x y);

// Apply the selected inverse functor to read one directed arrow as a path.
symbol groupoidal_arrow_to_path
  [C : Cat]
  (g : τ (@IsGroupoidalCat C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  : τ (@= (Obj C) x y)
≔ @fapp0
    (Hom_cat C x y)
    (Path_cat (@= (Obj C) x y))
    (@groupoidal_arrow_to_path_func C g x y)
    f;

// Re-including the selected path is propositionally the original arrow.
symbol groupoidal_arrow_section
  [C : Cat]
  (g : τ (@IsGroupoidalCat C))
  (x y : τ (Obj C))
  : τ (@=
      (Hom Cat_cat (Hom_cat C x y) (Hom_cat C x y))
      (@comp_fapp0
        Cat_cat
        (Hom_cat C x y)
        (Path_cat (@= (Obj C) x y))
        (Hom_cat C x y)
        (@core_incl_hom_func C x y)
        (@groupoidal_arrow_to_path_func C g x y))
      (@id Cat_cat (Hom_cat C x y)))
≔ @omega_equiv_along_right_law
    Cat_cat
    (Path_cat (@= (Obj C) x y))
    (Hom_cat C x y)
    (@core_incl_hom_func C x y)
    (@groupoidal_core_homwise C g x y);

// Pointwise, re-including the selected path recovers the original arrow.
symbol groupoidal_path_to_arrow_retract
  [C : Cat]
  (g : τ (@IsGroupoidalCat C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  : τ (@=
      (Hom C x y)
      (@fapp0
        (Path_cat (@= (Obj C) x y))
        (Hom_cat C x y)
        (@core_incl_hom_func C x y)
        (@groupoidal_arrow_to_path C g x y f))
      f)
≔ @eq_ap
    (Hom Cat_cat (Hom_cat C x y) (Hom_cat C x y))
    (Hom C x y)
    (λ F : τ (Hom Cat_cat (Hom_cat C x y) (Hom_cat C x y)),
      @fapp0 (Hom_cat C x y) (Hom_cat C x y) F f)
    (@comp_fapp0
      Cat_cat
      (Hom_cat C x y)
      (Path_cat (@= (Obj C) x y))
      (Hom_cat C x y)
      (@core_incl_hom_func C x y)
      (@groupoidal_arrow_to_path_func C g x y))
    (@id Cat_cat (Hom_cat C x y))
    (@groupoidal_arrow_section C g x y);

/*
  Discrete-category homwise path selection.

  The kernel stores only object sethood and native groupoidality. This
  one-way extension derives the homwise equivalence and selected path reader
  from the general groupoidality action; no D0/D1 conversion is involved.
*/
symbol discrete_core_homwise
  [C : Cat]
  (d : τ (IsDiscreteCat C))
  (x y : τ (Obj C))
  : τ (@OmegaEquivAlong
      Cat_cat
      (Path_cat (@= (Obj C) x y))
      (Hom_cat C x y)
      (@core_incl_hom_func C x y))
≔ @groupoidal_core_homwise
    C
    (@is_discrete_cat_core_equiv C d)
    x
    y;

// Selected native inverse functor on a core-inclusion hom action.
symbol discrete_core_hom_inv_func
  [C : Cat]
  (d : τ (IsDiscreteCat C))
  (x y : τ (Obj C))
  : τ (Functor
      (Hom_cat C x y)
      (Path_cat (@= (Obj C) x y)))
≔ @groupoidal_arrow_to_path_func
    C
    (@is_discrete_cat_core_equiv C d)
    x
    y;

// Read a directed arrow as its selected object path.
symbol hom_to_path
  [C : Cat]
  (d : τ (IsDiscreteCat C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  : τ (@= (Obj C) x y)
≔ @groupoidal_arrow_to_path
    C
    (@is_discrete_cat_core_equiv C d)
    x
    y
    f;

// The selected inverse followed by the core action is propositionally idle.
symbol discrete_core_hom_left_law
  [C : Cat]
  (d : τ (IsDiscreteCat C))
  (x y : τ (Obj C))
  : τ (@=
      (Hom Cat_cat
        (Path_cat (@= (Obj C) x y))
        (Path_cat (@= (Obj C) x y)))
      (@comp_cat_fapp0
        (Path_cat (@= (Obj C) x y))
        (Hom_cat C x y)
        (Path_cat (@= (Obj C) x y))
        (@discrete_core_hom_inv_func C d x y)
        (@core_incl_hom_func C x y))
      (@id Cat_cat (Path_cat (@= (Obj C) x y))))
≔ @omega_equiv_along_left_law
    Cat_cat
    (Path_cat (@= (Obj C) x y))
    (Hom_cat C x y)
    (@core_incl_hom_func C x y)
    (@discrete_core_homwise C d x y);

// Reading an included object path recovers that path.
symbol hom_to_path_path_to_hom
  [C : Cat]
  (d : τ (IsDiscreteCat C))
  [x y : τ (Obj C)]
  (p : τ (@= (Obj C) x y))
  : τ (@=
      (@= (Obj C) x y)
      (@hom_to_path C d x y (@path_to_hom C x y p))
      p)
≔ @discrete_cat_path_proof
    C d x y
    (@hom_to_path C d x y (@path_to_hom C x y p))
    p;

// Re-including the selected path recovers the original arrow as equality.
symbol path_to_hom_hom_to_path_path
  [C : Cat]
  (d : τ (IsDiscreteCat C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  : τ (@=
      (Hom C x y)
      (@path_to_hom C x y (@hom_to_path C d x y f))
      f)
≔ @groupoidal_path_to_arrow_retract
    C
    (@is_discrete_cat_core_equiv C d)
    x
    y
    f;

// The former directed round-trip surface is the image of the native path.
symbol path_to_hom_hom_to_path
  [C : Cat]
  (d : τ (IsDiscreteCat C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  : τ (Hom
      (Hom_cat C x y)
      (@path_to_hom C x y (@hom_to_path C d x y f))
      f)
≔ @path_to_hom
    (Hom_cat C x y)
    (@path_to_hom C x y (@hom_to_path C d x y f))
    f
    (@path_to_hom_hom_to_path_path C d x y f);

// A OneCat iterates the native discrete core action one hom level further.
symbol one_cat_hom_core_homwise
  (X : τ OneCat)
  (x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X)))
  (f g : τ (Hom (@ncat_carrier (cat_succ cat_zero) X) x y))
  : τ (@OmegaEquivAlong
      Cat_cat
      (Path_cat (@=
        (Hom (@ncat_carrier (cat_succ cat_zero) X) x y)
        f
        g))
      (Hom_cat
        (Hom_cat (@ncat_carrier (cat_succ cat_zero) X) x y)
        f
        g)
      (@core_incl_hom_func
        (Hom_cat (@ncat_carrier (cat_succ cat_zero) X) x y)
        f
        g))
≔ @discrete_core_homwise
    (Hom_cat (@ncat_carrier (cat_succ cat_zero) X) x y)
    (@one_cat_hom_discrete X x y)
    f
    g;

// Selected inverse arrow obtained from the groupoidality-selected path.
symbol groupoidal_arrow_inverse
  [C : Cat]
  (g : τ (@IsGroupoidalCat C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  : τ (Hom C y x)
≔ @path_to_hom
    C y x
    (@path_sym
      (Obj C)
      x y
      (@groupoidal_arrow_to_path C g x y f));

// The selected inverse cancels the original arrow on the left.
symbol groupoidal_arrow_left_law
  [C : Cat]
  (g : τ (@IsGroupoidalCat C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  : τ (@=
      (Hom C x x)
      (@comp_fapp0 C x y x
        (@groupoidal_arrow_inverse C g x y f)
        f)
      (@id C x))
≔ @eq_trans
    (Hom C x x)
    (@comp_fapp0 C x y x
      (@groupoidal_arrow_inverse C g x y f)
      f)
    (@comp_fapp0 C x y x
      (@groupoidal_arrow_inverse C g x y f)
      (@path_to_hom C x y
        (@groupoidal_arrow_to_path C g x y f)))
    (@id C x)
    (@eq_sym
      (Hom C x x)
      (@comp_fapp0 C x y x
        (@groupoidal_arrow_inverse C g x y f)
        (@path_to_hom C x y
          (@groupoidal_arrow_to_path C g x y f)))
      (@comp_fapp0 C x y x
        (@groupoidal_arrow_inverse C g x y f)
        f)
      (@eq_ap
        (Hom C x y)
        (Hom C x x)
        (λ h : τ (Hom C x y),
          @comp_fapp0 C x y x
            (@groupoidal_arrow_inverse C g x y f)
            h)
        (@path_to_hom C x y
          (@groupoidal_arrow_to_path C g x y f))
        f
        (@groupoidal_path_to_arrow_retract C g x y f)))
    (@object_path_equiv_left_law
      C x y
      (@groupoidal_arrow_to_path C g x y f));

// The selected inverse cancels the original arrow on the right.
symbol groupoidal_arrow_right_law
  [C : Cat]
  (g : τ (@IsGroupoidalCat C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  : τ (@=
      (Hom C y y)
      (@comp_fapp0 C y x y
        f
        (@groupoidal_arrow_inverse C g x y f))
      (@id C y))
≔ @eq_trans
    (Hom C y y)
    (@comp_fapp0 C y x y
      f
      (@groupoidal_arrow_inverse C g x y f))
    (@comp_fapp0 C y x y
      (@path_to_hom C x y
        (@groupoidal_arrow_to_path C g x y f))
      (@groupoidal_arrow_inverse C g x y f))
    (@id C y)
    (@eq_sym
      (Hom C y y)
      (@comp_fapp0 C y x y
        (@path_to_hom C x y
          (@groupoidal_arrow_to_path C g x y f))
        (@groupoidal_arrow_inverse C g x y f))
      (@comp_fapp0 C y x y
        f
        (@groupoidal_arrow_inverse C g x y f))
      (@eq_ap
        (Hom C x y)
        (Hom C y y)
        (λ h : τ (Hom C x y),
          @comp_fapp0 C y x y
            h
            (@groupoidal_arrow_inverse C g x y f))
        (@path_to_hom C x y
          (@groupoidal_arrow_to_path C g x y f))
        f
        (@groupoidal_path_to_arrow_retract C g x y f)))
    (@object_path_equiv_right_law
      C x y
      (@groupoidal_arrow_to_path C g x y f));

// Every arrow in an internally groupoidal category has explicit equality-valued evidence.
symbol groupoidal_arrow_equiv_along
  [C : Cat]
  (g : τ (@IsGroupoidalCat C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  : τ (@OmegaEquivAlong C x y f)
≔ @omega_equiv_along_intro
    C x y f
    (@groupoidal_arrow_inverse C g x y f)
    (@groupoidal_arrow_inverse C g x y f)
    (@groupoidal_arrow_left_law C g x y f)
    (@groupoidal_arrow_right_law C g x y f);

// Pointwise classifier saying that every directed arrow carries native equality-valued
// equivalence evidence. This does not itself package the coherent inverse
// omega-functor C -> Core(C) required by IsGroupoidalCat.
symbol AllArrowsEquiv
  (C : Cat)
  : Grpd
≔ @Pi_grpd
    (Obj C)
    (λ x : τ (Obj C),
      @Pi_grpd
        (Obj C)
        (λ y : τ (Obj C),
          @Pi_grpd
            (Hom C x y)
            (λ f : τ (Hom C x y),
              @OmegaEquivAlong C x y f)));

// Internal groupoidality supplies pointwise equivalence evidence for all
// arrows through the selected native homwise inverse.
symbol groupoidal_all_arrows_equiv
  [C : Cat]
  (g : τ (@IsGroupoidalCat C))
  : τ (@AllArrowsEquiv C)
≔ λ x : τ (Obj C),
    λ y : τ (Obj C),
      λ f : τ (Hom C x y),
        @groupoidal_arrow_equiv_along C g x y f;

/*
  Structured transport along a groupoidal arrow is an equivalence of fibres.

  This is the existing displayed functor action equipped with the image of the
  arrow's explicit equality-valued evidence; it adds no decoder and no transport rule.
*/
symbol groupoidal_fibre_transport_equiv
  [C : Cat]
  (g : τ (@IsGroupoidalCat C))
  (D : τ (Catd C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  : τ (@OmegaEquivAlong
      Cat_cat
      (Fibre_cat D x)
      (Fibre_cat D y)
      (@fapp1_fapp0 C Cat_cat D x y f))
≔ @omega_equiv_along_fapp1_fapp0
    C
    Cat_cat
    D
    x y f
    (@groupoidal_arrow_equiv_along C g x y f);
