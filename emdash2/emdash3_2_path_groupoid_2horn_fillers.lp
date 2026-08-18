/*
  Algebraic two-horn fillers for the strict 2-nerve of a path groupoid.

  The generic presheaf-facing restriction is the existing precomposition by
  each horn inclusion.  The selected path-groupoid consumer is presented by
  one coherent triangle carrier and three horn carriers. Inner filling is
  path composition; outer filling uses inverses. A right-J composition gives
  the horn-2 dual the appropriate judgmental endpoint, while an explicit path
  proves agreement with the ordinary left-J `eq_trans` operation.

  Horn-specific Sigma eliminators and J-derived cancellation lift the object
  computations to actual section paths. Restriction and filler functions are
  then lifted with `path_map_func`, retaining equality and every higher action.

  This is a bounded algebraic 2-nerve slice. It does not construct an
  all-dimensional nerve presheaf, identify these carriers with the full
  presheaf mapping categories, prove a generic Kan theorem, or add a tactic,
  solver, rewrite rule, or unification rule.
*/

require open emdash.emdash3_2_simplex2_sieves;

// Generic restriction along any selected partial two-simplex inclusion.
symbol simplex2_partial_restrict
  (kind : τ Simplex2SieveKind)
  (X : τ (@Psh SemiDeltaPlus_cat))
  : τ (Functor
      (Hom_cat
        (@Psh_cat SemiDeltaPlus_cat)
        (@StandardSimplex (succ (succ (succ zero))))
        X)
      (Hom_cat
        (@Psh_cat SemiDeltaPlus_cat)
        (@simplex2_sieve_extension_psh kind)
        X))
≔ @ordinary_sieve_local_precomp
    SemiDeltaPlus_cat
    (succ (succ (succ zero)))
    (@simplex2_sieve kind)
    X;

/*
  Right-oriented path composition, judgmental in its second argument. It is
  propositionally the same path operation as eq_trans, whose J orientation is
  judgmental in the first argument.
*/
symbol eq_trans_right
  [G : Grpd]
  [x y z : τ G]
  (p : τ (@= G x y))
  (q : τ (@= G y z))
  : τ (@= G x z)
≔ (@ind_eqr
      G z
      (λ y0 : τ G,
        λ _ : τ (@= G y0 z),
          @Function_grpd (@= G x y0) (@= G x z))
      (λ r : τ (@= G x z), r)
      y q) p;

symbol eq_trans_right_agrees
  [G : Grpd]
  [x y z : τ G]
  (p : τ (@= G x y))
  (q : τ (@= G y z))
  : τ (@=
      (@= G x z)
      (@eq_trans_right G x y z p q)
      (@eq_trans G x y z p q))
≔ @ind_eqr
    G z
    (λ y0 : τ G,
      λ q0 : τ (@= G y0 z),
        @Pi_grpd
          (@= G x y0)
          (λ p0 : τ (@= G x y0),
            @=
              (@= G x z)
              (@eq_trans_right G x y0 z p0 q0)
              (@eq_trans G x y0 z p0 q0)))
    (λ p0 : τ (@= G x z),
      @eq_sym
        (@= G x z)
        (@eq_trans G x z z p0 (@eq_refl G z))
        p0
        (@eq_trans_right_unit G x z p0))
    y q p;

// Coherent strict-nerve triangle: vertices plus composable edges 01 and 12.
symbol PathNerve2Simplex
  (G : Grpd)
  : Grpd
≔ `Σ_ x0 : τ G,
   `Σ_ x1 : τ G,
   `Σ_ x2 : τ G,
      @Product_grpd (@= G x0 x1) (@= G x1 x2);

// Horn 0 retains edges 01 and 02.
symbol PathNerve2HornZero
  (G : Grpd)
  : Grpd
≔ `Σ_ x0 : τ G,
   `Σ_ x1 : τ G,
   `Σ_ x2 : τ G,
      @Product_grpd (@= G x0 x1) (@= G x0 x2);

// Inner horn 1 retains the composable pair itself.
symbol PathNerve2HornOne
  (G : Grpd)
  : Grpd
≔ @PathNerve2Simplex G;

// Horn 2 retains edges 02 and 12.
symbol PathNerve2HornTwo
  (G : Grpd)
  : Grpd
≔ `Σ_ x0 : τ G,
   `Σ_ x1 : τ G,
   `Σ_ x2 : τ G,
      @Product_grpd (@= G x0 x2) (@= G x1 x2);

symbol path_nerve2_simplex_intro
  [G : Grpd]
  (x0 x1 x2 : τ G)
  (p01 : τ (@= G x0 x1))
  (p12 : τ (@= G x1 x2))
  : τ (@PathNerve2Simplex G)
≔ Struct_sigma x0
    (Struct_sigma x1
      (Struct_sigma x2
        (@Product_pair_grpd
          (@= G x0 x1) (@= G x1 x2) p01 p12)));

symbol path_nerve2_horn_zero_intro
  [G : Grpd]
  (x0 x1 x2 : τ G)
  (p01 : τ (@= G x0 x1))
  (p02 : τ (@= G x0 x2))
  : τ (@PathNerve2HornZero G)
≔ Struct_sigma x0
    (Struct_sigma x1
      (Struct_sigma x2
        (@Product_pair_grpd
          (@= G x0 x1) (@= G x0 x2) p01 p02)));

symbol path_nerve2_horn_two_intro
  [G : Grpd]
  (x0 x1 x2 : τ G)
  (p02 : τ (@= G x0 x2))
  (p12 : τ (@= G x1 x2))
  : τ (@PathNerve2HornTwo G)
≔ Struct_sigma x0
    (Struct_sigma x1
      (Struct_sigma x2
        (@Product_pair_grpd
          (@= G x0 x2) (@= G x1 x2) p02 p12)));

// Shared nested-Sigma vertex projections.
symbol path_nerve2_x0
  [G : Grpd]
  [A : τ G → Grpd]
  (s : @τΣ_ G A)
  : τ G
≔ sigma_Fst s;

// Concrete projections for the simplex.
symbol path_nerve2_simplex_x0 [G : Grpd]
  (s : τ (@PathNerve2Simplex G)) : τ G
≔ sigma_Fst s;

symbol path_nerve2_simplex_x1 [G : Grpd]
  (s : τ (@PathNerve2Simplex G)) : τ G
≔ sigma_Fst (sigma_Snd s);

symbol path_nerve2_simplex_x2 [G : Grpd]
  (s : τ (@PathNerve2Simplex G)) : τ G
≔ sigma_Fst (sigma_Snd (sigma_Snd s));

symbol path_nerve2_simplex_p01 [G : Grpd]
  (s : τ (@PathNerve2Simplex G))
  : τ (@= G
      (@path_nerve2_simplex_x0 G s)
      (@path_nerve2_simplex_x1 G s))
≔ sigma_Fst (sigma_Snd (sigma_Snd (sigma_Snd s)));

symbol path_nerve2_simplex_p12 [G : Grpd]
  (s : τ (@PathNerve2Simplex G))
  : τ (@= G
      (@path_nerve2_simplex_x1 G s)
      (@path_nerve2_simplex_x2 G s))
≔ sigma_Snd (sigma_Snd (sigma_Snd (sigma_Snd s)));

symbol path_nerve2_simplex_p02 [G : Grpd]
  (s : τ (@PathNerve2Simplex G))
  : τ (@= G
      (@path_nerve2_simplex_x0 G s)
      (@path_nerve2_simplex_x2 G s))
≔ @eq_trans
    G
    (@path_nerve2_simplex_x0 G s)
    (@path_nerve2_simplex_x1 G s)
    (@path_nerve2_simplex_x2 G s)
    (@path_nerve2_simplex_p01 G s)
    (@path_nerve2_simplex_p12 G s);

// Horn 0 projections.
symbol path_nerve2_horn_zero_x0 [G : Grpd]
  (h : τ (@PathNerve2HornZero G)) : τ G
≔ sigma_Fst h;

symbol path_nerve2_horn_zero_x1 [G : Grpd]
  (h : τ (@PathNerve2HornZero G)) : τ G
≔ sigma_Fst (sigma_Snd h);

symbol path_nerve2_horn_zero_x2 [G : Grpd]
  (h : τ (@PathNerve2HornZero G)) : τ G
≔ sigma_Fst (sigma_Snd (sigma_Snd h));

symbol path_nerve2_horn_zero_p01 [G : Grpd]
  (h : τ (@PathNerve2HornZero G))
  : τ (@= G
      (@path_nerve2_horn_zero_x0 G h)
      (@path_nerve2_horn_zero_x1 G h))
≔ sigma_Fst (sigma_Snd (sigma_Snd (sigma_Snd h)));

symbol path_nerve2_horn_zero_p02 [G : Grpd]
  (h : τ (@PathNerve2HornZero G))
  : τ (@= G
      (@path_nerve2_horn_zero_x0 G h)
      (@path_nerve2_horn_zero_x2 G h))
≔ sigma_Snd (sigma_Snd (sigma_Snd (sigma_Snd h)));

// Horn 2 projections.
symbol path_nerve2_horn_two_x0 [G : Grpd]
  (h : τ (@PathNerve2HornTwo G)) : τ G
≔ sigma_Fst h;

symbol path_nerve2_horn_two_x1 [G : Grpd]
  (h : τ (@PathNerve2HornTwo G)) : τ G
≔ sigma_Fst (sigma_Snd h);

symbol path_nerve2_horn_two_x2 [G : Grpd]
  (h : τ (@PathNerve2HornTwo G)) : τ G
≔ sigma_Fst (sigma_Snd (sigma_Snd h));

symbol path_nerve2_horn_two_p02 [G : Grpd]
  (h : τ (@PathNerve2HornTwo G))
  : τ (@= G
      (@path_nerve2_horn_two_x0 G h)
      (@path_nerve2_horn_two_x2 G h))
≔ sigma_Fst (sigma_Snd (sigma_Snd (sigma_Snd h)));

symbol path_nerve2_horn_two_p12 [G : Grpd]
  (h : τ (@PathNerve2HornTwo G))
  : τ (@= G
      (@path_nerve2_horn_two_x1 G h)
      (@path_nerve2_horn_two_x2 G h))
≔ sigma_Snd (sigma_Snd (sigma_Snd (sigma_Snd h)));

// Restriction functions.
symbol path_nerve2_restrict_zero [G : Grpd]
  : τ (@Function_grpd
      (@PathNerve2Simplex G)
      (@PathNerve2HornZero G))
≔ λ s : τ (@PathNerve2Simplex G),
    @path_nerve2_horn_zero_intro
      G
      (@path_nerve2_simplex_x0 G s)
      (@path_nerve2_simplex_x1 G s)
      (@path_nerve2_simplex_x2 G s)
      (@path_nerve2_simplex_p01 G s)
      (@path_nerve2_simplex_p02 G s);

symbol path_nerve2_restrict_one [G : Grpd]
  : τ (@Function_grpd
      (@PathNerve2Simplex G)
      (@PathNerve2HornOne G))
≔ λ s : τ (@PathNerve2Simplex G), s;

symbol path_nerve2_restrict_two [G : Grpd]
  : τ (@Function_grpd
      (@PathNerve2Simplex G)
      (@PathNerve2HornTwo G))
≔ λ s : τ (@PathNerve2Simplex G),
    @path_nerve2_horn_two_intro
      G
      (@path_nerve2_simplex_x0 G s)
      (@path_nerve2_simplex_x1 G s)
      (@path_nerve2_simplex_x2 G s)
      (@eq_trans_right
        G
        (@path_nerve2_simplex_x0 G s)
        (@path_nerve2_simplex_x1 G s)
        (@path_nerve2_simplex_x2 G s)
        (@path_nerve2_simplex_p01 G s)
        (@path_nerve2_simplex_p12 G s))
      (@path_nerve2_simplex_p12 G s);

// Algebraic filler functions: composition for the inner horn, inverses outside.
symbol path_nerve2_fill_zero [G : Grpd]
  : τ (@Function_grpd
      (@PathNerve2HornZero G)
      (@PathNerve2Simplex G))
≔ λ h : τ (@PathNerve2HornZero G),
    @path_nerve2_simplex_intro
      G
      (@path_nerve2_horn_zero_x0 G h)
      (@path_nerve2_horn_zero_x1 G h)
      (@path_nerve2_horn_zero_x2 G h)
      (@path_nerve2_horn_zero_p01 G h)
      (@eq_trans
        G
        (@path_nerve2_horn_zero_x1 G h)
        (@path_nerve2_horn_zero_x0 G h)
        (@path_nerve2_horn_zero_x2 G h)
        (@eq_sym
          G
          (@path_nerve2_horn_zero_x0 G h)
          (@path_nerve2_horn_zero_x1 G h)
          (@path_nerve2_horn_zero_p01 G h))
        (@path_nerve2_horn_zero_p02 G h));

symbol path_nerve2_fill_one [G : Grpd]
  : τ (@Function_grpd
      (@PathNerve2HornOne G)
      (@PathNerve2Simplex G))
≔ λ h : τ (@PathNerve2HornOne G), h;

symbol path_nerve2_fill_two [G : Grpd]
  : τ (@Function_grpd
      (@PathNerve2HornTwo G)
      (@PathNerve2Simplex G))
≔ λ h : τ (@PathNerve2HornTwo G),
    @path_nerve2_simplex_intro
      G
      (@path_nerve2_horn_two_x0 G h)
      (@path_nerve2_horn_two_x1 G h)
      (@path_nerve2_horn_two_x2 G h)
      (@eq_trans_right
        G
        (@path_nerve2_horn_two_x0 G h)
        (@path_nerve2_horn_two_x2 G h)
        (@path_nerve2_horn_two_x1 G h)
        (@path_nerve2_horn_two_p02 G h)
        (@eq_sym
          G
          (@path_nerve2_horn_two_x1 G h)
          (@path_nerve2_horn_two_x2 G h)
          (@path_nerve2_horn_two_p12 G h)))
      (@path_nerve2_horn_two_p12 G h);

// Cancellation proving that the horn-0 filler retains its supplied edge 02.
symbol path_nerve2_horn_zero_cancel
  [G : Grpd]
  [x0 x1 : τ G]
  (p01 : τ (@= G x0 x1))
  [x2 : τ G]
  (p02 : τ (@= G x0 x2))
  : τ (@=
      (@= G x0 x2)
      (@eq_trans
        G x0 x1 x2 p01
        (@eq_trans G x1 x0 x2 (@eq_sym G x0 x1 p01) p02))
      p02)
≔ @ind_eqr
    G x1
    (λ x00 : τ G,
      λ p010 : τ (@= G x00 x1),
        @Pi_grpd G
          (λ x20 : τ G,
            @Pi_grpd
              (@= G x00 x20)
              (λ p020 : τ (@= G x00 x20),
                @=
                  (@= G x00 x20)
                  (@eq_trans
                    G x00 x1 x20 p010
                    (@eq_trans
                      G x1 x00 x20
                      (@eq_sym G x00 x1 p010)
                      p020))
                  p020)))
    (λ x20 : τ G,
      λ p020 : τ (@= G x1 x20),
        @eq_refl (@= G x1 x20) p020)
    x0 p01 x2 p02;

// Right-J cancellation proving that the horn-2 filler retains edge 02.
symbol path_nerve2_horn_two_cancel
  [G : Grpd]
  [x1 x2 : τ G]
  (p12 : τ (@= G x1 x2))
  [x0 : τ G]
  (p02 : τ (@= G x0 x2))
  : τ (@=
      (@= G x0 x2)
      (@eq_trans_right
        G x0 x1 x2
        (@eq_trans_right
          G x0 x2 x1 p02 (@eq_sym G x1 x2 p12))
        p12)
      p02)
≔ @ind_eqr
    G x2
    (λ x10 : τ G,
      λ p120 : τ (@= G x10 x2),
        @Pi_grpd G
          (λ x00 : τ G,
            @Pi_grpd
              (@= G x00 x2)
              (λ p020 : τ (@= G x00 x2),
                @=
                  (@= G x00 x2)
                  (@eq_trans_right
                    G x00 x10 x2
                    (@eq_trans_right
                      G x00 x2 x10
                      p020
                      (@eq_sym G x10 x2 p120))
                    p120)
                  p020)))
    (λ x00 : τ G,
      λ p020 : τ (@= G x00 x2),
        @eq_refl (@= G x00 x2) p020)
    x1 p12 x0 p02;

// Constructor-complete eliminator for horn 0's nested Sigma presentation.
symbol path_nerve2_horn_zero_ind
  [G : Grpd]
  (Q : τ (@PathNerve2HornZero G) → Grpd)
  (c : Π x0 : τ G,
       Π x1 : τ G,
       Π x2 : τ G,
       Π p01 : τ (@= G x0 x1),
       Π p02 : τ (@= G x0 x2),
       τ (Q (@path_nerve2_horn_zero_intro
         G x0 x1 x2 p01 p02)))
  (h : τ (@PathNerve2HornZero G))
  : τ (Q h)
≔ @sigma_ind
    G
    (λ x0 : τ G,
      `Σ_ x1 : τ G,
      `Σ_ x2 : τ G,
        @Product_grpd (@= G x0 x1) (@= G x0 x2))
    Q
    (λ x0 : τ G,
      λ t1 : @τΣ_ G (λ x1 : τ G,
        `Σ_ x2 : τ G,
          @Product_grpd (@= G x0 x1) (@= G x0 x2)),
        @sigma_ind
          G
          (λ x1 : τ G,
            `Σ_ x2 : τ G,
              @Product_grpd (@= G x0 x1) (@= G x0 x2))
          (λ t10 : @τΣ_ G (λ x1 : τ G,
            `Σ_ x2 : τ G,
              @Product_grpd (@= G x0 x1) (@= G x0 x2)),
            Q (Struct_sigma x0 t10))
          (λ x1 : τ G,
            λ t2 : @τΣ_ G (λ x2 : τ G,
              @Product_grpd (@= G x0 x1) (@= G x0 x2)),
              @sigma_ind
                G
                (λ x2 : τ G,
                  @Product_grpd (@= G x0 x1) (@= G x0 x2))
                (λ t20 : @τΣ_ G (λ x2 : τ G,
                  @Product_grpd (@= G x0 x1) (@= G x0 x2)),
                  Q (Struct_sigma x0 (Struct_sigma x1 t20)))
                (λ x2 : τ G,
                  λ edges : τ (@Product_grpd
                    (@= G x0 x1) (@= G x0 x2)),
                    @sigma_ind
                      (@= G x0 x1)
                      (λ _ : τ (@= G x0 x1), @= G x0 x2)
                      (λ edges0 : @τΣ_
                        (@= G x0 x1)
                        (λ _ : τ (@= G x0 x1), @= G x0 x2),
                        Q (Struct_sigma x0
                          (Struct_sigma x1
                            (Struct_sigma x2 edges0))))
                      (λ p01 : τ (@= G x0 x1),
                        λ p02 : τ (@= G x0 x2),
                          c x0 x1 x2 p01 p02)
                      edges)
                t2)
          t1)
    h;

// Constructor-complete eliminator for horn 2.
symbol path_nerve2_horn_two_ind
  [G : Grpd]
  (Q : τ (@PathNerve2HornTwo G) → Grpd)
  (c : Π x0 : τ G,
       Π x1 : τ G,
       Π x2 : τ G,
       Π p02 : τ (@= G x0 x2),
       Π p12 : τ (@= G x1 x2),
       τ (Q (@path_nerve2_horn_two_intro
         G x0 x1 x2 p02 p12)))
  (h : τ (@PathNerve2HornTwo G))
  : τ (Q h)
≔ @sigma_ind
    G
    (λ x0 : τ G,
      `Σ_ x1 : τ G,
      `Σ_ x2 : τ G,
        @Product_grpd (@= G x0 x2) (@= G x1 x2))
    Q
    (λ x0 : τ G,
      λ t1 : @τΣ_ G (λ x1 : τ G,
        `Σ_ x2 : τ G,
          @Product_grpd (@= G x0 x2) (@= G x1 x2)),
        @sigma_ind
          G
          (λ x1 : τ G,
            `Σ_ x2 : τ G,
              @Product_grpd (@= G x0 x2) (@= G x1 x2))
          (λ t10 : @τΣ_ G (λ x1 : τ G,
            `Σ_ x2 : τ G,
              @Product_grpd (@= G x0 x2) (@= G x1 x2)),
            Q (Struct_sigma x0 t10))
          (λ x1 : τ G,
            λ t2 : @τΣ_ G (λ x2 : τ G,
              @Product_grpd (@= G x0 x2) (@= G x1 x2)),
              @sigma_ind
                G
                (λ x2 : τ G,
                  @Product_grpd (@= G x0 x2) (@= G x1 x2))
                (λ t20 : @τΣ_ G (λ x2 : τ G,
                  @Product_grpd (@= G x0 x2) (@= G x1 x2)),
                  Q (Struct_sigma x0 (Struct_sigma x1 t20)))
                (λ x2 : τ G,
                  λ edges : τ (@Product_grpd
                    (@= G x0 x2) (@= G x1 x2)),
                    @sigma_ind
                      (@= G x0 x2)
                      (λ _ : τ (@= G x0 x2), @= G x1 x2)
                      (λ edges0 : @τΣ_
                        (@= G x0 x2)
                        (λ _ : τ (@= G x0 x2), @= G x1 x2),
                        Q (Struct_sigma x0
                          (Struct_sigma x1
                            (Struct_sigma x2 edges0))))
                      (λ p02 : τ (@= G x0 x2),
                        λ p12 : τ (@= G x1 x2),
                          c x0 x1 x2 p02 p12)
                      edges)
                t2)
          t1)
    h;

// Equality of horn constructors when only edge 02 changes.
symbol path_nerve2_horn_zero_p02_path
  [G : Grpd]
  (x0 x1 x2 : τ G)
  (p01 : τ (@= G x0 x1))
  (p02 p02' : τ (@= G x0 x2))
  (q : τ (@= (@= G x0 x2) p02 p02'))
  : τ (@=
      (@PathNerve2HornZero G)
      (@path_nerve2_horn_zero_intro G x0 x1 x2 p01 p02)
      (@path_nerve2_horn_zero_intro G x0 x1 x2 p01 p02'))
≔ @eq_ap
    (@= G x0 x2)
    (@PathNerve2HornZero G)
    (λ r : τ (@= G x0 x2),
      @path_nerve2_horn_zero_intro G x0 x1 x2 p01 r)
    p02 p02' q;

symbol path_nerve2_horn_two_p02_path
  [G : Grpd]
  (x0 x1 x2 : τ G)
  (p02 p02' : τ (@= G x0 x2))
  (p12 : τ (@= G x1 x2))
  (q : τ (@= (@= G x0 x2) p02 p02'))
  : τ (@=
      (@PathNerve2HornTwo G)
      (@path_nerve2_horn_two_intro G x0 x1 x2 p02 p12)
      (@path_nerve2_horn_two_intro G x0 x1 x2 p02' p12))
≔ @eq_ap
    (@= G x0 x2)
    (@PathNerve2HornTwo G)
    (λ r : τ (@= G x0 x2),
      @path_nerve2_horn_two_intro G x0 x1 x2 r p12)
    p02 p02' q;

// Pointwise section laws for all three algebraic horn restrictions.
symbol path_nerve2_fill_zero_section_point
  [G : Grpd]
  (h : τ (@PathNerve2HornZero G))
  : τ (@=
      (@PathNerve2HornZero G)
      (@path_nerve2_restrict_zero G
        (@path_nerve2_fill_zero G h))
      h)
≔ @path_nerve2_horn_zero_ind
    G
    (λ h0 : τ (@PathNerve2HornZero G),
      @=
        (@PathNerve2HornZero G)
        (@path_nerve2_restrict_zero G
          (@path_nerve2_fill_zero G h0))
        h0)
    (λ x0 : τ G,
      λ x1 : τ G,
      λ x2 : τ G,
      λ p01 : τ (@= G x0 x1),
      λ p02 : τ (@= G x0 x2),
        @path_nerve2_horn_zero_p02_path
          G x0 x1 x2 p01
          (@eq_trans
            G x0 x1 x2 p01
            (@eq_trans G x1 x0 x2 (@eq_sym G x0 x1 p01) p02))
          p02
          (@path_nerve2_horn_zero_cancel
            G x0 x1 p01 x2 p02))
    h;

symbol path_nerve2_fill_one_section_point
  [G : Grpd]
  (h : τ (@PathNerve2HornOne G))
  : τ (@=
      (@PathNerve2HornOne G)
      (@path_nerve2_restrict_one G
        (@path_nerve2_fill_one G h))
      h)
≔ @eq_refl (@PathNerve2HornOne G) h;

symbol path_nerve2_fill_two_section_point
  [G : Grpd]
  (h : τ (@PathNerve2HornTwo G))
  : τ (@=
      (@PathNerve2HornTwo G)
      (@path_nerve2_restrict_two G
        (@path_nerve2_fill_two G h))
      h)
≔ @path_nerve2_horn_two_ind
    G
    (λ h0 : τ (@PathNerve2HornTwo G),
      @=
        (@PathNerve2HornTwo G)
        (@path_nerve2_restrict_two G
          (@path_nerve2_fill_two G h0))
        h0)
    (λ x0 : τ G,
      λ x1 : τ G,
      λ x2 : τ G,
      λ p02 : τ (@= G x0 x2),
      λ p12 : τ (@= G x1 x2),
        @path_nerve2_horn_two_p02_path
          G x0 x1 x2
          (@eq_trans_right
            G x0 x1 x2
            (@eq_trans_right
              G x0 x2 x1 p02 (@eq_sym G x1 x2 p12))
            p12)
          p02 p12
          (@path_nerve2_horn_two_cancel
            G x1 x2 p12 x0 p02))
    h;

// Whole function paths package the algebraic section laws.
symbol path_nerve2_fill_zero_section
  (G : Grpd)
  : τ (@=
      (@Function_grpd
        (@PathNerve2HornZero G)
        (@PathNerve2HornZero G))
      (λ h : τ (@PathNerve2HornZero G),
        @path_nerve2_restrict_zero G
          (@path_nerve2_fill_zero G h))
      (λ h : τ (@PathNerve2HornZero G), h))
≔ @PiFunext
    (@PathNerve2HornZero G)
    (λ _ : τ (@PathNerve2HornZero G),
      @PathNerve2HornZero G)
    (λ h : τ (@PathNerve2HornZero G),
      @path_nerve2_restrict_zero G
        (@path_nerve2_fill_zero G h))
    (λ h : τ (@PathNerve2HornZero G), h)
    (λ h : τ (@PathNerve2HornZero G),
      @path_nerve2_fill_zero_section_point G h);

symbol path_nerve2_fill_one_section
  (G : Grpd)
  : τ (@=
      (@Function_grpd
        (@PathNerve2HornOne G)
        (@PathNerve2HornOne G))
      (λ h : τ (@PathNerve2HornOne G),
        @path_nerve2_restrict_one G
          (@path_nerve2_fill_one G h))
      (λ h : τ (@PathNerve2HornOne G), h))
≔ @eq_refl
    (@Function_grpd
      (@PathNerve2HornOne G)
      (@PathNerve2HornOne G))
    (λ h : τ (@PathNerve2HornOne G), h);

symbol path_nerve2_fill_two_section
  (G : Grpd)
  : τ (@=
      (@Function_grpd
        (@PathNerve2HornTwo G)
        (@PathNerve2HornTwo G))
      (λ h : τ (@PathNerve2HornTwo G),
        @path_nerve2_restrict_two G
          (@path_nerve2_fill_two G h))
      (λ h : τ (@PathNerve2HornTwo G), h))
≔ @PiFunext
    (@PathNerve2HornTwo G)
    (λ _ : τ (@PathNerve2HornTwo G),
      @PathNerve2HornTwo G)
    (λ h : τ (@PathNerve2HornTwo G),
      @path_nerve2_restrict_two G
        (@path_nerve2_fill_two G h))
    (λ h : τ (@PathNerve2HornTwo G), h)
    (λ h : τ (@PathNerve2HornTwo G),
      @path_nerve2_fill_two_section_point G h);

// Whole restriction functors, parallel to the whole filler functors.
symbol path_nerve2_restrict_zero_func (G : Grpd)
  : τ (Functor
      (Path_cat (@PathNerve2Simplex G))
      (Path_cat (@PathNerve2HornZero G)))
≔ @path_map_func
    (@PathNerve2Simplex G)
    (@PathNerve2HornZero G)
    (@path_nerve2_restrict_zero G);

symbol path_nerve2_restrict_one_func (G : Grpd)
  : τ (Functor
      (Path_cat (@PathNerve2Simplex G))
      (Path_cat (@PathNerve2HornOne G)))
≔ @path_map_func
    (@PathNerve2Simplex G)
    (@PathNerve2HornOne G)
    (@path_nerve2_restrict_one G);

symbol path_nerve2_restrict_two_func (G : Grpd)
  : τ (Functor
      (Path_cat (@PathNerve2Simplex G))
      (Path_cat (@PathNerve2HornTwo G)))
≔ @path_map_func
    (@PathNerve2Simplex G)
    (@PathNerve2HornTwo G)
    (@path_nerve2_restrict_two G);

// Whole path-category lifts retain equality and every higher action.
symbol path_nerve2_fill_zero_func (G : Grpd)
  : τ (Functor
      (Path_cat (@PathNerve2HornZero G))
      (Path_cat (@PathNerve2Simplex G)))
≔ @path_map_func
    (@PathNerve2HornZero G)
    (@PathNerve2Simplex G)
    (@path_nerve2_fill_zero G);

symbol path_nerve2_fill_one_func (G : Grpd)
  : τ (Functor
      (Path_cat (@PathNerve2HornOne G))
      (Path_cat (@PathNerve2Simplex G)))
≔ @path_map_func
    (@PathNerve2HornOne G)
    (@PathNerve2Simplex G)
    (@path_nerve2_fill_one G);

symbol path_nerve2_fill_two_func (G : Grpd)
  : τ (Functor
      (Path_cat (@PathNerve2HornTwo G))
      (Path_cat (@PathNerve2Simplex G)))
≔ @path_map_func
    (@PathNerve2HornTwo G)
    (@PathNerve2Simplex G)
    (@path_nerve2_fill_two G);
