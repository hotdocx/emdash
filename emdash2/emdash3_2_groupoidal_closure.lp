/*
  First rule-free groupoidal-closure comparison.

  The core of Product_cat(Path_cat(A),Path_cat(B)) is definitionally
  Path_cat(Product_grpd(A,B)).  Consequently the existing Core inclusion is
  the canonical comparison

    Path(A x B) -> Path(A) x Path(B).

  This module proves that its actual hom action is an equivalence by splitting
  the stable ProductPathView into two ordinary paths and joining such a pair
  through the constant-family PathOver bridge.  It packages the result as one
  identity-on-objects, homwise-equivalence certificate.  The current kernel
  has no generic constructor turning that data into a coherent inverse whole
  functor, so this module deliberately does not postulate an
  OmegaEquivAlong(Cat_cat), add a category-head rewrite, or add a unifier.
*/

require open emdash.emdash3_2;

// Product of the two Path-category realizations.
symbol PathProduct_cat
  (A B : Grpd)
  : Cat
≔ Product_cat (Path_cat A) (Path_cat B);

// Source hom carrier of the comparison.
symbol PathProductHom_grpd
  [A B : Grpd]
  (p q : τ (Product_grpd A B))
  : Grpd
≔ @= (Product_grpd A B) p q;

// Componentwise target hom carrier of the comparison.
symbol PathProductComponentHom_grpd
  [A B : Grpd]
  (p q : τ (Product_grpd A B))
  : Grpd
≔ @Product_grpd
    (@= A (sigma_Fst p) (sigma_Fst q))
    (@= B (sigma_Snd p) (sigma_Snd q));

/*
  Canonical comparison.  Core_cat(Path(A) x Path(B)) unfolds to the stated
  source, so no new functor constructor or action rule is required.
*/
symbol path_product_compare_func
  [A B : Grpd]
  : τ (@Functor
      (Path_cat (Product_grpd A B))
      (@PathProduct_cat A B))
≔ @Core_incl_func (@PathProduct_cat A B);

// Read the actual comparison arrow action at fixed endpoints.
symbol path_product_compare_hom
  [A B : Grpd]
  [p q : τ (Product_grpd A B)]
  (w : τ (@PathProductHom_grpd A B p q))
  : τ (@PathProductComponentHom_grpd A B p q)
≔ @fapp1_fapp0
    (Path_cat (Product_grpd A B))
    (@PathProduct_cat A B)
    (@path_product_compare_func A B)
    p q w;

// Reading a constant-family PathOver built from q returns q.
symbol product_const_pathover_path_const
  [A B : Grpd]
  [x y : τ A]
  [u v : τ B]
  (p : τ (x = y))
  (q : τ (u = v))
  : τ (@=
      (@= B u v)
      (@const_pathover_path A B x y u v p
        (@const_pathover A B x y u v p q))
      q)
≔ @ind_eqr A y
    (λ x : τ A, λ p : τ (x = y),
      @Pi_grpd B (λ u : τ B,
        @Pi_grpd B (λ v : τ B,
          @Pi_grpd (@= B u v) (λ q : τ (@= B u v),
            @=
              (@= B u v)
              (@const_pathover_path A B x y u v p
                (@const_pathover A B x y u v p q))
              q))))
    (λ u : τ B, λ v : τ B, λ q : τ (u = v),
      @eq_refl (@= B u v) q)
    x p u v q;

// Rebuilding a constant-family PathOver after reading it is neutral.
symbol product_const_pathover_const_path
  [A B : Grpd]
  [x y : τ A]
  [u v : τ B]
  (p : τ (x = y))
  (q : τ (@PathOver A (λ _ : τ A, B) x y p u v))
  : τ (@=
      (@PathOver A (λ _ : τ A, B) x y p u v)
      (@const_pathover A B x y u v p
        (@const_pathover_path A B x y u v p q))
      q)
≔ @ind_eqr A y
    (λ x : τ A, λ p : τ (x = y),
      @Pi_grpd B (λ u : τ B,
        @Pi_grpd B (λ v : τ B,
          @Pi_grpd
            (@PathOver A (λ _ : τ A, B) x y p u v)
            (λ q : τ (@PathOver A (λ _ : τ A, B) x y p u v),
              @=
                (@PathOver A (λ _ : τ A, B) x y p u v)
                (@const_pathover A B x y u v p
                  (@const_pathover_path A B x y u v p q))
                q))))
    (λ u : τ B, λ v : τ B,
      λ q : τ (@PathOver A (λ _ : τ A, B) y y (eq_refl y) u v),
        @eq_refl (@= B u v) q)
    x p u v q;

// Split a product path into its two ordinary component paths.
symbol path_product_split
  [A B : Grpd]
  [p q : τ (Product_grpd A B)]
  (w : τ (@PathProductHom_grpd A B p q))
  : τ (@PathProductComponentHom_grpd A B p q)
≔ @Product_pair_grpd
    (@= A (sigma_Fst p) (sigma_Fst q))
    (@= B (sigma_Snd p) (sigma_Snd q))
    (@product_path_base A B p q w)
    (@const_pathover_path
      A B
      (sigma_Fst p) (sigma_Fst q)
      (sigma_Snd p) (sigma_Snd q)
      (@product_path_base A B p q w)
      (@product_path_fibre A B p q w));

// Join two ordinary component paths into the stable Product path view.
symbol path_product_join
  [A B : Grpd]
  [p q : τ (Product_grpd A B)]
  (h : τ (@PathProductComponentHom_grpd A B p q))
  : τ (@PathProductHom_grpd A B p q)
≔ @product_path_intro
    A B p q
    (sigma_Fst h)
    (@const_pathover
      A B
      (sigma_Fst p) (sigma_Fst q)
      (sigma_Snd p) (sigma_Snd q)
      (sigma_Fst h)
      (sigma_Snd h));

// Splitting after joining is pointwise the identity pair.
symbol path_product_split_join
  [A B : Grpd]
  [p q : τ (Product_grpd A B)]
  (h : τ (@PathProductComponentHom_grpd A B p q))
  : τ (@=
      (@PathProductComponentHom_grpd A B p q)
      (@path_product_split A B p q
        (@path_product_join A B p q h))
      h)
≔ @sigma_ind
    (@= A (sigma_Fst p) (sigma_Fst q))
    (λ _ : τ (@= A (sigma_Fst p) (sigma_Fst q)),
      @= B (sigma_Snd p) (sigma_Snd q))
    (λ h : τ (@PathProductComponentHom_grpd A B p q),
      @=
        (@PathProductComponentHom_grpd A B p q)
        (@path_product_split A B p q
          (@path_product_join A B p q h))
        h)
    (λ base : τ (@= A (sigma_Fst p) (sigma_Fst q)),
      λ fibre : τ (@= B (sigma_Snd p) (sigma_Snd q)),
        @eq_ap
          (@= B (sigma_Snd p) (sigma_Snd q))
          (@PathProductComponentHom_grpd A B p q)
          (λ r : τ (@= B (sigma_Snd p) (sigma_Snd q)),
            @Product_pair_grpd
              (@= A (sigma_Fst p) (sigma_Fst q))
              (@= B (sigma_Snd p) (sigma_Snd q))
              base r)
          (@const_pathover_path
            A B
            (sigma_Fst p) (sigma_Fst q)
            (sigma_Snd p) (sigma_Snd q)
            base
            (@const_pathover
              A B
              (sigma_Fst p) (sigma_Fst q)
              (sigma_Snd p) (sigma_Snd q)
              base fibre))
          fibre
          (@product_const_pathover_path_const
            A B
            (sigma_Fst p) (sigma_Fst q)
            (sigma_Snd p) (sigma_Snd q)
            base fibre))
    h;

// Joining after splitting is pointwise the identity product path.
symbol path_product_join_split
  [A B : Grpd]
  [p q : τ (Product_grpd A B)]
  (w : τ (@PathProductHom_grpd A B p q))
  : τ (@=
      (@PathProductHom_grpd A B p q)
      (@path_product_join A B p q
        (@path_product_split A B p q w))
      w)
≔ @product_path_ind
    A B p q
    (λ w : τ (@ProductPathView A B p q),
      @=
        (@PathProductHom_grpd A B p q)
        (@path_product_join A B p q
          (@path_product_split A B p q w))
        w)
    (λ base : τ (@= A (sigma_Fst p) (sigma_Fst q)),
      λ fibre : τ (@PathOver
        A (λ _ : τ A, B)
        (sigma_Fst p) (sigma_Fst q) base
        (sigma_Snd p) (sigma_Snd q)),
        @eq_ap
          (@PathOver
            A (λ _ : τ A, B)
            (sigma_Fst p) (sigma_Fst q) base
            (sigma_Snd p) (sigma_Snd q))
          (@PathProductHom_grpd A B p q)
          (λ r : τ (@PathOver
            A (λ _ : τ A, B)
            (sigma_Fst p) (sigma_Fst q) base
            (sigma_Snd p) (sigma_Snd q)),
            @product_path_intro A B p q base r)
          (@const_pathover
            A B
            (sigma_Fst p) (sigma_Fst q)
            (sigma_Snd p) (sigma_Snd q)
            base
            (@const_pathover_path
              A B
              (sigma_Fst p) (sigma_Fst q)
              (sigma_Snd p) (sigma_Snd q)
              base fibre))
          fibre
          (@product_const_pathover_const_path
            A B
            (sigma_Fst p) (sigma_Fst q)
            (sigma_Snd p) (sigma_Snd q)
            base fibre))
    w;

/*
  The actual Core-inclusion hom action agrees with explicit splitting.  The
  reflexive case is proved inside the stable Product path classifier; it does
  not need a whole-category conversion rule.
*/
symbol path_product_compare_hom_agrees
  [A B : Grpd]
  [p q : τ (Product_grpd A B)]
  (w : τ (@PathProductHom_grpd A B p q))
  : τ (@=
      (@PathProductComponentHom_grpd A B p q)
      (@path_product_compare_hom A B p q w)
      (@path_product_split A B p q w))
≔ @ind_eqr
    (Product_grpd A B)
    q
    (λ p : τ (Product_grpd A B),
      λ w : τ (@= (Product_grpd A B) p q),
        @=
          (@PathProductComponentHom_grpd A B p q)
          (@path_product_compare_hom A B p q w)
          (@path_product_split A B p q w))
    (@product_path_intro
      (@= A (sigma_Fst q) (sigma_Fst q))
      (@= B (sigma_Snd q) (sigma_Snd q))
      (@id (@PathProduct_cat A B) q)
      (@path_product_split A B q q
        (@eq_refl (Product_grpd A B) q))
      (@eq_refl
        (@= A (sigma_Fst q) (sigma_Fst q))
        (@eq_refl A (sigma_Fst q)))
      (@pathover_refl
        (@= A (sigma_Fst q) (sigma_Fst q))
        (λ _ : τ (@= A (sigma_Fst q) (sigma_Fst q)),
          @= B (sigma_Snd q) (sigma_Snd q))
        (@eq_refl A (sigma_Fst q))
        (@eq_refl B (sigma_Snd q))))
    p w;

// Joining the actual comparison action recovers the source product path.
symbol path_product_compare_hom_left
  [A B : Grpd]
  [p q : τ (Product_grpd A B)]
  (w : τ (@PathProductHom_grpd A B p q))
  : τ (@=
      (@PathProductHom_grpd A B p q)
      (@path_product_join A B p q
        (@path_product_compare_hom A B p q w))
      w)
≔ @eq_trans
    (@PathProductHom_grpd A B p q)
    (@path_product_join A B p q
      (@path_product_compare_hom A B p q w))
    (@path_product_join A B p q
      (@path_product_split A B p q w))
    w
    (@eq_ap
      (@PathProductComponentHom_grpd A B p q)
      (@PathProductHom_grpd A B p q)
      (λ h : τ (@PathProductComponentHom_grpd A B p q),
        @path_product_join A B p q h)
      (@path_product_compare_hom A B p q w)
      (@path_product_split A B p q w)
      (@path_product_compare_hom_agrees A B p q w))
    (@path_product_join_split A B p q w);

// The actual comparison action after joining recovers the component pair.
symbol path_product_compare_hom_right
  [A B : Grpd]
  [p q : τ (Product_grpd A B)]
  (h : τ (@PathProductComponentHom_grpd A B p q))
  : τ (@=
      (@PathProductComponentHom_grpd A B p q)
      (@path_product_compare_hom A B p q
        (@path_product_join A B p q h))
      h)
≔ @eq_trans
    (@PathProductComponentHom_grpd A B p q)
    (@path_product_compare_hom A B p q
      (@path_product_join A B p q h))
    (@path_product_split A B p q
      (@path_product_join A B p q h))
    h
    (@path_product_compare_hom_agrees
      A B p q (@path_product_join A B p q h))
    (@path_product_split_join A B p q h);

// Explicit quasi-inverse evidence for the actual comparison hom action.
symbol path_product_compare_hom_by_inverse
  [A B : Grpd]
  (p q : τ (Product_grpd A B))
  : τ (@EquivByInverse
      (@PathProductHom_grpd A B p q)
      (@PathProductComponentHom_grpd A B p q)
      (λ w : τ (@PathProductHom_grpd A B p q),
        @path_product_compare_hom A B p q w)
      (λ h : τ (@PathProductComponentHom_grpd A B p q),
        @path_product_join A B p q h))
≔ @Product_pair_grpd
    (@Pi_grpd
      (@PathProductHom_grpd A B p q)
      (λ w : τ (@PathProductHom_grpd A B p q),
        @= (@PathProductHom_grpd A B p q)
          (@path_product_join A B p q
            (@path_product_compare_hom A B p q w))
          w))
    (@Pi_grpd
      (@PathProductComponentHom_grpd A B p q)
      (λ h : τ (@PathProductComponentHom_grpd A B p q),
        @= (@PathProductComponentHom_grpd A B p q)
          (@path_product_compare_hom A B p q
            (@path_product_join A B p q h))
          h))
    (λ w : τ (@PathProductHom_grpd A B p q),
      @path_product_compare_hom_left A B p q w)
    (λ h : τ (@PathProductComponentHom_grpd A B p q),
      @path_product_compare_hom_right A B p q h);

// Every actual comparison hom action is an explicit type equivalence.
symbol path_product_compare_hom_type_equiv
  [A B : Grpd]
  (p q : τ (Product_grpd A B))
  : τ (@TypeEquiv
      (@PathProductHom_grpd A B p q)
      (@PathProductComponentHom_grpd A B p q))
≔ @Struct_sigma
    (@Function_grpd
      (@PathProductHom_grpd A B p q)
      (@PathProductComponentHom_grpd A B p q))
    (λ f : τ (@Function_grpd
      (@PathProductHom_grpd A B p q)
      (@PathProductComponentHom_grpd A B p q)),
      @IsEquivMap
        (@PathProductHom_grpd A B p q)
        (@PathProductComponentHom_grpd A B p q)
        f)
    (λ w : τ (@PathProductHom_grpd A B p q),
      @path_product_compare_hom A B p q w)
    (@is_equiv_map_by_inverse
      (@PathProductHom_grpd A B p q)
      (@PathProductComponentHom_grpd A B p q)
      (λ w : τ (@PathProductHom_grpd A B p q),
        @path_product_compare_hom A B p q w)
      (λ h : τ (@PathProductComponentHom_grpd A B p q),
        @path_product_join A B p q h)
      (@path_product_compare_hom_by_inverse A B p q));

/*
  Whole closure certificate: the named comparison fixes every object and is
  a TypeEquiv on every hom carrier.  This is the first constructive
  preservation data expected of the categorical equivalence; recursive whole
  hom comparison and coherent-inverse-functor packaging remain absent.
*/
symbol PathProductComparisonEvidence
  [A B : Grpd]
  : Grpd
≔ @Product_grpd
    (@Pi_grpd
      (Product_grpd A B)
      (λ p : τ (Product_grpd A B),
        @= (Product_grpd A B)
          (@fapp0
            (Path_cat (Product_grpd A B))
            (@PathProduct_cat A B)
            (@path_product_compare_func A B)
            p)
          p))
    (@Pi_grpd
      (Product_grpd A B)
      (λ p : τ (Product_grpd A B),
        @Pi_grpd
          (Product_grpd A B)
          (λ q : τ (Product_grpd A B),
            @TypeEquiv
              (@PathProductHom_grpd A B p q)
              (@PathProductComponentHom_grpd A B p q))));

// Canonical whole identity-on-objects and homwise-equivalence evidence.
symbol path_product_comparison_evidence
  [A B : Grpd]
  : τ (@PathProductComparisonEvidence A B)
≔ @Product_pair_grpd
    (@Pi_grpd
      (Product_grpd A B)
      (λ p : τ (Product_grpd A B),
        @= (Product_grpd A B)
          (@fapp0
            (Path_cat (Product_grpd A B))
            (@PathProduct_cat A B)
            (@path_product_compare_func A B)
            p)
          p))
    (@Pi_grpd
      (Product_grpd A B)
      (λ p : τ (Product_grpd A B),
        @Pi_grpd
          (Product_grpd A B)
          (λ q : τ (Product_grpd A B),
            @TypeEquiv
              (@PathProductHom_grpd A B p q)
              (@PathProductComponentHom_grpd A B p q))))
    (λ p : τ (Product_grpd A B),
      @eq_refl (Product_grpd A B) p)
    (λ p : τ (Product_grpd A B),
      λ q : τ (Product_grpd A B),
        @path_product_compare_hom_type_equiv A B p q);

// Readable object-identity projection of the whole certificate.
symbol path_product_comparison_object_path
  [A B : Grpd]
  (p : τ (Product_grpd A B))
  : τ (@= (Product_grpd A B)
      (@fapp0
        (Path_cat (Product_grpd A B))
        (@PathProduct_cat A B)
        (@path_product_compare_func A B)
        p)
      p)
≔ sigma_Fst (@path_product_comparison_evidence A B) p;

// Readable hom-equivalence projection of the whole certificate.
symbol path_product_comparison_hom_equiv
  [A B : Grpd]
  (p q : τ (Product_grpd A B))
  : τ (@TypeEquiv
      (@PathProductHom_grpd A B p q)
      (@PathProductComponentHom_grpd A B p q))
≔ sigma_Snd (@path_product_comparison_evidence A B) p q;
