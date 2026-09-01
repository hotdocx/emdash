/*
  Set-target extensionality for category-indexed groupoidification.

  Two maps h,k : Groupoidify(C) -> S into a set are equal when they agree on
  every point represented by the whole unit C -> Path(Groupoidify(C)). The
  construction remains whole:

    pointwise unit paths
      -> one transformation between the restrictions of h and k
      -> first Hom action of groupoidify extension
      -> extension/restriction eta at h and k
      -> h = k.

  Restriction is intentionally the existing transparent whole functor. Its
  point observation is derived by applying object evaluation to the existing
  whole restriction comparison; no extra precomposition rewrite is installed.
  This module introduces neither dependent groupoidification induction nor
  source action for Groupoidify.
*/

require open emdash.emdash3_2_groupoidification_universality;
require open emdash.emdash3_2_set_path_pointwise_transformation;

// Pointwise agreement of two maps on every object represented by the unit.
symbol GroupoidifySetUnitPaths
  [C : Cat]
  [S : Grpd]
  (h k : τ (@Function_grpd (@Groupoidify C) S))
  : Grpd
≔ @Pi_grpd
    (Obj C)
    (λ x : τ (Obj C),
      @= S
        (h (@fapp0 C (Path_cat (@Groupoidify C))
          (@groupoidify_unit_func C) x))
        (k (@fapp0 C (Path_cat (@Groupoidify C))
          (@groupoidify_unit_func C) x)));

// Point observation derived from the existing whole restriction comparison.
symbol groupoidify_restrict_point_path
  [C : Cat]
  [S : Grpd]
  (h : τ (@Function_grpd (@Groupoidify C) S))
  (x : τ (Obj C))
  : τ (@= S
      (@fapp0 C (Path_cat S) (@groupoidify_restrict_at C S h) x)
      (h (@fapp0 C (Path_cat (@Groupoidify C))
        (@groupoidify_unit_func C) x)))
≔ @eq_ap
    (Functor C (Path_cat S))
    S
    (λ F : τ (Functor C (Path_cat S)),
      @fapp0 C (Path_cat S) F x)
    (@groupoidify_restrict_at C S h)
    (@comp_cat_fapp0
      C (Path_cat (@Groupoidify C)) (Path_cat S)
      (@path_map_func (@Groupoidify C) S h)
      (@groupoidify_unit_func C))
    (@groupoidify_restrict_at_path C S h);

// Recenter unit agreement at the actual object projections of restriction.
symbol groupoidify_set_restrict_pointwise_data
  [C : Cat]
  [S : Grpd]
  [h k : τ (@Function_grpd (@Groupoidify C) S)]
  (p : τ (@GroupoidifySetUnitPaths C S h k))
  : τ (@SetPathPointwiseData
      C S
      (@groupoidify_restrict_at C S h)
      (@groupoidify_restrict_at C S k))
≔ λ x : τ (Obj C),
    @eq_trans
      S
      (@fapp0 C (Path_cat S) (@groupoidify_restrict_at C S h) x)
      (h (@fapp0 C (Path_cat (@Groupoidify C))
        (@groupoidify_unit_func C) x))
      (@fapp0 C (Path_cat S) (@groupoidify_restrict_at C S k) x)
      (@groupoidify_restrict_point_path C S h x)
      (@eq_trans
        S
        (h (@fapp0 C (Path_cat (@Groupoidify C))
          (@groupoidify_unit_func C) x))
        (k (@fapp0 C (Path_cat (@Groupoidify C))
          (@groupoidify_unit_func C) x))
        (@fapp0 C (Path_cat S) (@groupoidify_restrict_at C S k) x)
        (p x)
        (@eq_sym S
          (@fapp0 C (Path_cat S) (@groupoidify_restrict_at C S k) x)
          (k (@fapp0 C (Path_cat (@Groupoidify C))
            (@groupoidify_unit_func C) x))
          (@groupoidify_restrict_point_path C S k x)));

// Whole transformation between the two restricted path-valued functors.
symbol groupoidify_set_restrict_transf
  [C : Cat]
  [S : Grpd]
  (S_set : τ (IsSetGrpd S))
  [h k : τ (@Function_grpd (@Groupoidify C) S)]
  (p : τ (@GroupoidifySetUnitPaths C S h k))
  : τ (@Transf
      C (Path_cat S)
      (@groupoidify_restrict_at C S h)
      (@groupoidify_restrict_at C S k))
≔ @set_path_pointwise_transf
    C S S_set
    (@groupoidify_restrict_at C S h)
    (@groupoidify_restrict_at C S k)
    (@groupoidify_set_restrict_pointwise_data C S h k p);

// First Hom action of extension sends the whole transformation to a map path.
symbol groupoidify_set_extend_path
  [C : Cat]
  [S : Grpd]
  (S_set : τ (IsSetGrpd S))
  [h k : τ (@Function_grpd (@Groupoidify C) S)]
  (p : τ (@GroupoidifySetUnitPaths C S h k))
  : τ (@=
      (@Function_grpd (@Groupoidify C) S)
      (@groupoidify_extend_at C S (@groupoidify_restrict_at C S h))
      (@groupoidify_extend_at C S (@groupoidify_restrict_at C S k)))
≔ @fapp1_fapp0
    (@Functor_cat C (Path_cat S))
    (@Hom_cat Grpd_cat (@Groupoidify C) S)
    (@groupoidify_extend_func C S)
    (@groupoidify_restrict_at C S h)
    (@groupoidify_restrict_at C S k)
    (@groupoidify_set_restrict_transf C S S_set h k p);

// Set-target map extensionality from agreement on the whole unit.
symbol groupoidify_set_map_ext
  [C : Cat]
  [S : Grpd]
  (S_set : τ (IsSetGrpd S))
  [h k : τ (@Function_grpd (@Groupoidify C) S)]
  (p : τ (@GroupoidifySetUnitPaths C S h k))
  : τ (@= (@Function_grpd (@Groupoidify C) S) h k)
≔ @eq_trans
    (@Function_grpd (@Groupoidify C) S)
    h
    (@groupoidify_extend_at C S (@groupoidify_restrict_at C S h))
    k
    (@eq_sym
      (@Function_grpd (@Groupoidify C) S)
      (@groupoidify_extend_at C S (@groupoidify_restrict_at C S h))
      h
      (@groupoidify_extend_restrict_eta_at_path C S h))
    (@eq_trans
      (@Function_grpd (@Groupoidify C) S)
      (@groupoidify_extend_at C S (@groupoidify_restrict_at C S h))
      (@groupoidify_extend_at C S (@groupoidify_restrict_at C S k))
      k
      (@groupoidify_set_extend_path C S S_set h k p)
      (@groupoidify_extend_restrict_eta_at_path C S k));

// Point observation of set-target map extensionality at an arbitrary point.
symbol groupoidify_set_map_ext_at
  [C : Cat]
  [S : Grpd]
  (S_set : τ (IsSetGrpd S))
  [h k : τ (@Function_grpd (@Groupoidify C) S)]
  (p : τ (@GroupoidifySetUnitPaths C S h k))
  (u : τ (@Groupoidify C))
  : τ (@= S (h u) (k u))
≔ @PiHapply
    (@Groupoidify C)
    (λ _ : τ (@Groupoidify C), S)
    h k
    (@groupoidify_set_map_ext C S S_set h k p)
    u;

// Unit-point agreement for curried binary maps into a set.
symbol GroupoidifySetBinaryUnitPaths
  [C D : Cat]
  [S : Grpd]
  (h k : τ (@Function_grpd
      (@Groupoidify C)
      (@Function_grpd (@Groupoidify D) S)))
  : Grpd
≔ @Pi_grpd (Obj C)
    (λ x : τ (Obj C),
      @Pi_grpd (Obj D)
        (λ y : τ (Obj D),
          @= S
            (h (@fapp0 C (Path_cat (@Groupoidify C))
                (@groupoidify_unit_func C) x)
              (@fapp0 D (Path_cat (@Groupoidify D))
                (@groupoidify_unit_func D) y))
            (k (@fapp0 C (Path_cat (@Groupoidify C))
                (@groupoidify_unit_func C) x)
              (@fapp0 D (Path_cat (@Groupoidify D))
                (@groupoidify_unit_func D) y))));

// Curried binary extensionality, derived by two unary whole extensions.
symbol groupoidify_set_binary_map_ext_at
  [C D : Cat]
  [S : Grpd]
  (S_set : τ (IsSetGrpd S))
  [h k : τ (@Function_grpd
      (@Groupoidify C)
      (@Function_grpd (@Groupoidify D) S))]
  (p : τ (@GroupoidifySetBinaryUnitPaths C D S h k))
  (u : τ (@Groupoidify C))
  (v : τ (@Groupoidify D))
  : τ (@= S (h u v) (k u v))
≔ @groupoidify_set_map_ext_at
    C S S_set
    (λ u : τ (@Groupoidify C), h u v)
    (λ u : τ (@Groupoidify C), k u v)
    (λ x : τ (Obj C),
      @groupoidify_set_map_ext_at
        D S S_set
        (h (@fapp0 C (Path_cat (@Groupoidify C))
          (@groupoidify_unit_func C) x))
        (k (@fapp0 C (Path_cat (@Groupoidify C))
          (@groupoidify_unit_func C) x))
        (p x)
        v)
    u;

// Unit-point agreement for curried ternary maps into a set.
symbol GroupoidifySetTernaryUnitPaths
  [C D E : Cat]
  [S : Grpd]
  (h k : τ (@Function_grpd
      (@Groupoidify C)
      (@Function_grpd
        (@Groupoidify D)
        (@Function_grpd (@Groupoidify E) S))))
  : Grpd
≔ @Pi_grpd (Obj C)
    (λ x : τ (Obj C),
      @Pi_grpd (Obj D)
        (λ y : τ (Obj D),
          @Pi_grpd (Obj E)
            (λ z : τ (Obj E),
              @= S
                (h (@fapp0 C (Path_cat (@Groupoidify C))
                    (@groupoidify_unit_func C) x)
                  (@fapp0 D (Path_cat (@Groupoidify D))
                    (@groupoidify_unit_func D) y)
                  (@fapp0 E (Path_cat (@Groupoidify E))
                    (@groupoidify_unit_func E) z))
                (k (@fapp0 C (Path_cat (@Groupoidify C))
                    (@groupoidify_unit_func C) x)
                  (@fapp0 D (Path_cat (@Groupoidify D))
                    (@groupoidify_unit_func D) y)
                  (@fapp0 E (Path_cat (@Groupoidify E))
                    (@groupoidify_unit_func E) z)))));

// Curried ternary extensionality, derived from unary and binary extensions.
symbol groupoidify_set_ternary_map_ext_at
  [C D E : Cat]
  [S : Grpd]
  (S_set : τ (IsSetGrpd S))
  [h k : τ (@Function_grpd
      (@Groupoidify C)
      (@Function_grpd
        (@Groupoidify D)
        (@Function_grpd (@Groupoidify E) S)))]
  (p : τ (@GroupoidifySetTernaryUnitPaths C D E S h k))
  (u : τ (@Groupoidify C))
  (v : τ (@Groupoidify D))
  (w : τ (@Groupoidify E))
  : τ (@= S (h u v w) (k u v w))
≔ @groupoidify_set_map_ext_at
    C S S_set
    (λ u : τ (@Groupoidify C), h u v w)
    (λ u : τ (@Groupoidify C), k u v w)
    (λ x : τ (Obj C),
      @groupoidify_set_binary_map_ext_at
        D E S S_set
        (h (@fapp0 C (Path_cat (@Groupoidify C))
          (@groupoidify_unit_func C) x))
        (k (@fapp0 C (Path_cat (@Groupoidify C))
          (@groupoidify_unit_func C) x))
        (p x)
        v w)
    u;
