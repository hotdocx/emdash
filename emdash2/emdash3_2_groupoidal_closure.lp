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

/*
  Product-path transport and the structured-J comparison.

  A path of pairs is assembled from its two coordinate paths.  For a
  product-indexed family, primitive right-J transport along that path agrees
  propositionally with either sequential coordinate factorization.  The two
  routes therefore form a coherence diamond.  The existing structured
  Path-category transport and PathOut induction remain presentations of the
  same primitive eliminator; no second J or computation rule is introduced.
*/
// Path of pairs from paths in each coordinate.
symbol product_pair_path
  [A B : Grpd]
  [a0 a1 : τ A]
  [b0 b1 : τ B]
  (p : τ (a0 = a1))
  (q : τ (b0 = b1))
  : τ (@=
      (Product_grpd A B)
      (@Product_pair_grpd A B a0 b0)
      (@Product_pair_grpd A B a1 b1))
≔ @path_product_join
    A B
    (@Product_pair_grpd A B a0 b0)
    (@Product_pair_grpd A B a1 b1)
    (@Product_pair_grpd
      (@= A a0 a1)
      (@= B b0 b1)
      p q);

// Splitting product reflexivity gives the pair of coordinate reflexivities.
symbol path_product_split_refl
  [A B : Grpd]
  (a : τ A)
  (b : τ B)
  : τ (@=
      (@PathProductComponentHom_grpd
        A B
        (@Product_pair_grpd A B a b)
        (@Product_pair_grpd A B a b))
      (@path_product_split
        A B
        (@Product_pair_grpd A B a b)
        (@Product_pair_grpd A B a b)
        (@eq_refl
          (Product_grpd A B)
          (@Product_pair_grpd A B a b)))
      (@Product_pair_grpd
        (@= A a a)
        (@= B b b)
        (@eq_refl A a)
        (@eq_refl B b)))
≔ @product_path_intro
    (@= A a a)
    (@= B b b)
    (@path_product_split
      A B
      (@Product_pair_grpd A B a b)
      (@Product_pair_grpd A B a b)
      (@eq_refl
        (Product_grpd A B)
        (@Product_pair_grpd A B a b)))
    (@Product_pair_grpd
      (@= A a a)
      (@= B b b)
      (@eq_refl A a)
      (@eq_refl B b))
    (@eq_refl (@= A a a) (@eq_refl A a))
    (@pathover_refl
      (@= A a a)
      (λ _ : τ (@= A a a), @= B b b)
      (@eq_refl A a)
      (@eq_refl B b));

// The pair of coordinate reflexivities represents product reflexivity.
symbol product_pair_path_refl
  [A B : Grpd]
  (a : τ A)
  (b : τ B)
  : τ (@=
      (@PathProductHom_grpd
        A B
        (@Product_pair_grpd A B a b)
        (@Product_pair_grpd A B a b))
      (@product_pair_path A B a a b b
        (@eq_refl A a)
        (@eq_refl B b))
      (@eq_refl
        (Product_grpd A B)
        (@Product_pair_grpd A B a b)))
≔ @eq_trans
    (@PathProductHom_grpd
      A B
      (@Product_pair_grpd A B a b)
      (@Product_pair_grpd A B a b))
    (@product_pair_path A B a a b b
      (@eq_refl A a)
      (@eq_refl B b))
    (@path_product_join
      A B
      (@Product_pair_grpd A B a b)
      (@Product_pair_grpd A B a b)
      (@path_product_split
        A B
        (@Product_pair_grpd A B a b)
        (@Product_pair_grpd A B a b)
        (@eq_refl
          (Product_grpd A B)
          (@Product_pair_grpd A B a b))))
    (@eq_refl
      (Product_grpd A B)
      (@Product_pair_grpd A B a b))
    (@eq_ap
      (@PathProductComponentHom_grpd
        A B
        (@Product_pair_grpd A B a b)
        (@Product_pair_grpd A B a b))
      (@PathProductHom_grpd
        A B
        (@Product_pair_grpd A B a b)
        (@Product_pair_grpd A B a b))
      (λ h : τ (@PathProductComponentHom_grpd
        A B
        (@Product_pair_grpd A B a b)
        (@Product_pair_grpd A B a b)),
        @path_product_join
          A B
          (@Product_pair_grpd A B a b)
          (@Product_pair_grpd A B a b)
          h)
      (@Product_pair_grpd
        (@= A a a)
        (@= B b b)
        (@eq_refl A a)
        (@eq_refl B b))
      (@path_product_split
        A B
        (@Product_pair_grpd A B a b)
        (@Product_pair_grpd A B a b)
        (@eq_refl
          (Product_grpd A B)
          (@Product_pair_grpd A B a b)))
      (@eq_sym
        (@PathProductComponentHom_grpd
          A B
          (@Product_pair_grpd A B a b)
          (@Product_pair_grpd A B a b))
        (@path_product_split
          A B
          (@Product_pair_grpd A B a b)
          (@Product_pair_grpd A B a b)
          (@eq_refl
            (Product_grpd A B)
            (@Product_pair_grpd A B a b)))
        (@Product_pair_grpd
          (@= A a a)
          (@= B b b)
          (@eq_refl A a)
          (@eq_refl B b))
        (@path_product_split_refl A B a b)))
    (@path_product_join_split
      A B
      (@Product_pair_grpd A B a b)
      (@Product_pair_grpd A B a b)
      (@eq_refl
        (Product_grpd A B)
        (@Product_pair_grpd A B a b)));

// Primitive forward transport along one path in the product.
symbol product_path_transport
  [A B : Grpd]
  (P : τ (Product_grpd A B) → Grpd)
  [s t : τ (Product_grpd A B)]
  (r : τ (s = t))
  (u : τ (P s))
  : τ (P t)
≔ (@ind_eqr
      (Product_grpd A B)
      t
      (λ s : τ (Product_grpd A B), λ _ : τ (s = t),
        @Function_grpd (P s) (P t))
      (λ v : τ (P t), v)
      s r)
    u;

// Transport along the pair of reflexive coordinate paths is neutral.
symbol product_path_transport_pair_refl
  [A B : Grpd]
  (P : τ (Product_grpd A B) → Grpd)
  (a : τ A)
  (b : τ B)
  (u : τ (P (@Product_pair_grpd A B a b)))
  : τ (@=
      (P (@Product_pair_grpd A B a b))
      (@product_path_transport
        A B P
        (@Product_pair_grpd A B a b)
        (@Product_pair_grpd A B a b)
        (@product_pair_path A B a a b b
          (@eq_refl A a)
          (@eq_refl B b))
        u)
      u)
≔ @eq_ap
    (@PathProductHom_grpd
      A B
      (@Product_pair_grpd A B a b)
      (@Product_pair_grpd A B a b))
    (P (@Product_pair_grpd A B a b))
    (λ r : τ (@PathProductHom_grpd
      A B
      (@Product_pair_grpd A B a b)
      (@Product_pair_grpd A B a b)),
      @product_path_transport
        A B P
        (@Product_pair_grpd A B a b)
        (@Product_pair_grpd A B a b)
        r u)
    (@product_pair_path A B a a b b
      (@eq_refl A a)
      (@eq_refl B b))
    (@eq_refl
      (Product_grpd A B)
      (@Product_pair_grpd A B a b))
    (@product_pair_path_refl A B a b);

// Direct transport along the simultaneously paired coordinate path.
symbol product_transport_direct
  [A B : Grpd]
  (P : τ (Product_grpd A B) → Grpd)
  [a0 a1 : τ A]
  [b0 b1 : τ B]
  (p : τ (a0 = a1))
  (q : τ (b0 = b1))
  (u : τ (P (@Product_pair_grpd A B a0 b0)))
  : τ (P (@Product_pair_grpd A B a1 b1))
≔ @product_path_transport
    A B P
    (@Product_pair_grpd A B a0 b0)
    (@Product_pair_grpd A B a1 b1)
    (@product_pair_path A B a0 a1 b0 b1 p q)
    u;

// Sequential transport in the constant-Sigma order: A first, then B.
symbol product_transport_base_then_fibre
  [A B : Grpd]
  (P : τ (Product_grpd A B) → Grpd)
  [a0 a1 : τ A]
  [b0 b1 : τ B]
  (p : τ (a0 = a1))
  (q : τ (b0 = b1))
  (u : τ (P (@Product_pair_grpd A B a0 b0)))
  : τ (P (@Product_pair_grpd A B a1 b1))
≔ @product_path_transport
    A B P
    (@Product_pair_grpd A B a1 b0)
    (@Product_pair_grpd A B a1 b1)
    (@product_pair_path A B a1 a1 b0 b1
      (@eq_refl A a1) q)
    (@product_path_transport
      A B P
      (@Product_pair_grpd A B a0 b0)
      (@Product_pair_grpd A B a1 b0)
      (@product_pair_path A B a0 a1 b0 b0
        p (@eq_refl B b0))
      u);

// The other sequential route: B first, then A.
symbol product_transport_fibre_then_base
  [A B : Grpd]
  (P : τ (Product_grpd A B) → Grpd)
  [a0 a1 : τ A]
  [b0 b1 : τ B]
  (p : τ (a0 = a1))
  (q : τ (b0 = b1))
  (u : τ (P (@Product_pair_grpd A B a0 b0)))
  : τ (P (@Product_pair_grpd A B a1 b1))
≔ @product_path_transport
    A B P
    (@Product_pair_grpd A B a0 b1)
    (@Product_pair_grpd A B a1 b1)
    (@product_pair_path A B a0 a1 b1 b1
      p (@eq_refl B b1))
    (@product_path_transport
      A B P
      (@Product_pair_grpd A B a0 b0)
      (@Product_pair_grpd A B a0 b1)
      (@product_pair_path A B a0 a0 b0 b1
        (@eq_refl A a0) q)
      u);

// The base-first sequential route is neutral at coordinate reflexivity.
symbol product_transport_base_then_fibre_refl
  [A B : Grpd]
  (P : τ (Product_grpd A B) → Grpd)
  (a : τ A)
  (b : τ B)
  (u : τ (P (@Product_pair_grpd A B a b)))
  : τ (@=
      (P (@Product_pair_grpd A B a b))
      (@product_transport_base_then_fibre
        A B P a a b b
        (@eq_refl A a) (@eq_refl B b) u)
      u)
≔ @eq_trans
    (P (@Product_pair_grpd A B a b))
    (@product_transport_base_then_fibre
      A B P a a b b
      (@eq_refl A a) (@eq_refl B b) u)
    (@product_path_transport
      A B P
      (@Product_pair_grpd A B a b)
      (@Product_pair_grpd A B a b)
      (@product_pair_path A B a a b b
        (@eq_refl A a) (@eq_refl B b))
      u)
    u
    (@product_path_transport_pair_refl
      A B P a b
      (@product_path_transport
        A B P
        (@Product_pair_grpd A B a b)
        (@Product_pair_grpd A B a b)
        (@product_pair_path A B a a b b
          (@eq_refl A a) (@eq_refl B b))
        u))
    (@product_path_transport_pair_refl A B P a b u);

// The fibre-first sequential route is also neutral at reflexivity.
symbol product_transport_fibre_then_base_refl
  [A B : Grpd]
  (P : τ (Product_grpd A B) → Grpd)
  (a : τ A)
  (b : τ B)
  (u : τ (P (@Product_pair_grpd A B a b)))
  : τ (@=
      (P (@Product_pair_grpd A B a b))
      (@product_transport_fibre_then_base
        A B P a a b b
        (@eq_refl A a) (@eq_refl B b) u)
      u)
≔ @eq_trans
    (P (@Product_pair_grpd A B a b))
    (@product_transport_fibre_then_base
      A B P a a b b
      (@eq_refl A a) (@eq_refl B b) u)
    (@product_path_transport
      A B P
      (@Product_pair_grpd A B a b)
      (@Product_pair_grpd A B a b)
      (@product_pair_path A B a a b b
        (@eq_refl A a) (@eq_refl B b))
      u)
    u
    (@product_path_transport_pair_refl
      A B P a b
      (@product_path_transport
        A B P
        (@Product_pair_grpd A B a b)
        (@Product_pair_grpd A B a b)
        (@product_pair_path A B a a b b
          (@eq_refl A a) (@eq_refl B b))
        u))
    (@product_path_transport_pair_refl A B P a b u);

// Direct transport agrees with the canonical A-then-B factorization.
symbol product_transport_direct_agrees_base_then_fibre
  [A B : Grpd]
  (P : τ (Product_grpd A B) → Grpd)
  [a0 a1 : τ A]
  [b0 b1 : τ B]
  (p : τ (a0 = a1))
  (q : τ (b0 = b1))
  (u : τ (P (@Product_pair_grpd A B a0 b0)))
  : τ (@=
      (P (@Product_pair_grpd A B a1 b1))
      (@product_transport_direct A B P a0 a1 b0 b1 p q u)
      (@product_transport_base_then_fibre
        A B P a0 a1 b0 b1 p q u))
≔ (@ind_eqr
      A
      a1
      (λ a0 : τ A, λ p : τ (a0 = a1),
        @Pi_grpd B (λ b0 : τ B,
          @Pi_grpd (@= B b0 b1) (λ q : τ (@= B b0 b1),
            @Pi_grpd
              (P (@Product_pair_grpd A B a0 b0))
              (λ u : τ (P (@Product_pair_grpd A B a0 b0)),
                @=
                  (P (@Product_pair_grpd A B a1 b1))
                  (@product_transport_direct
                    A B P a0 a1 b0 b1 p q u)
                  (@product_transport_base_then_fibre
                    A B P a0 a1 b0 b1 p q u)))))
      (λ b0 : τ B,
        λ q : τ (@= B b0 b1),
        λ u : τ (P (@Product_pair_grpd A B a1 b0)),
          (@ind_eqr
            B
            b1
            (λ b0 : τ B, λ q : τ (b0 = b1),
              @Pi_grpd
                (P (@Product_pair_grpd A B a1 b0))
                (λ u : τ (P (@Product_pair_grpd A B a1 b0)),
                  @=
                    (P (@Product_pair_grpd A B a1 b1))
                    (@product_transport_direct
                      A B P a1 a1 b0 b1 (@eq_refl A a1) q u)
                    (@product_transport_base_then_fibre
                      A B P a1 a1 b0 b1 (@eq_refl A a1) q u)))
            (λ u : τ (P (@Product_pair_grpd A B a1 b1)),
              @eq_trans
                (P (@Product_pair_grpd A B a1 b1))
                (@product_transport_direct
                  A B P a1 a1 b1 b1
                  (@eq_refl A a1) (@eq_refl B b1) u)
                u
                (@product_transport_base_then_fibre
                  A B P a1 a1 b1 b1
                  (@eq_refl A a1) (@eq_refl B b1) u)
                (@product_path_transport_pair_refl A B P a1 b1 u)
                (@eq_sym
                  (P (@Product_pair_grpd A B a1 b1))
                  (@product_transport_base_then_fibre
                    A B P a1 a1 b1 b1
                    (@eq_refl A a1) (@eq_refl B b1) u)
                  u
                  (@product_transport_base_then_fibre_refl
                    A B P a1 b1 u)))
            b0 q)
          u)
      a0 p)
    b0 q u;

// Direct transport also agrees with the B-then-A factorization.
symbol product_transport_direct_agrees_fibre_then_base
  [A B : Grpd]
  (P : τ (Product_grpd A B) → Grpd)
  [a0 a1 : τ A]
  [b0 b1 : τ B]
  (p : τ (a0 = a1))
  (q : τ (b0 = b1))
  (u : τ (P (@Product_pair_grpd A B a0 b0)))
  : τ (@=
      (P (@Product_pair_grpd A B a1 b1))
      (@product_transport_direct A B P a0 a1 b0 b1 p q u)
      (@product_transport_fibre_then_base
        A B P a0 a1 b0 b1 p q u))
≔ (@ind_eqr
      A
      a1
      (λ a0 : τ A, λ p : τ (a0 = a1),
        @Pi_grpd B (λ b0 : τ B,
          @Pi_grpd (@= B b0 b1) (λ q : τ (@= B b0 b1),
            @Pi_grpd
              (P (@Product_pair_grpd A B a0 b0))
              (λ u : τ (P (@Product_pair_grpd A B a0 b0)),
                @=
                  (P (@Product_pair_grpd A B a1 b1))
                  (@product_transport_direct
                    A B P a0 a1 b0 b1 p q u)
                  (@product_transport_fibre_then_base
                    A B P a0 a1 b0 b1 p q u)))))
      (λ b0 : τ B,
        λ q : τ (@= B b0 b1),
        λ u : τ (P (@Product_pair_grpd A B a1 b0)),
          (@ind_eqr
            B
            b1
            (λ b0 : τ B, λ q : τ (b0 = b1),
              @Pi_grpd
                (P (@Product_pair_grpd A B a1 b0))
                (λ u : τ (P (@Product_pair_grpd A B a1 b0)),
                  @=
                    (P (@Product_pair_grpd A B a1 b1))
                    (@product_transport_direct
                      A B P a1 a1 b0 b1 (@eq_refl A a1) q u)
                    (@product_transport_fibre_then_base
                      A B P a1 a1 b0 b1 (@eq_refl A a1) q u)))
            (λ u : τ (P (@Product_pair_grpd A B a1 b1)),
              @eq_trans
                (P (@Product_pair_grpd A B a1 b1))
                (@product_transport_direct
                  A B P a1 a1 b1 b1
                  (@eq_refl A a1) (@eq_refl B b1) u)
                u
                (@product_transport_fibre_then_base
                  A B P a1 a1 b1 b1
                  (@eq_refl A a1) (@eq_refl B b1) u)
                (@product_path_transport_pair_refl A B P a1 b1 u)
                (@eq_sym
                  (P (@Product_pair_grpd A B a1 b1))
                  (@product_transport_fibre_then_base
                    A B P a1 a1 b1 b1
                    (@eq_refl A a1) (@eq_refl B b1) u)
                  u
                  (@product_transport_fibre_then_base_refl
                    A B P a1 b1 u)))
            b0 q)
          u)
      a0 p)
    b0 q u;

// The two sequential routes form the expected coherent transport diamond.
symbol product_transport_coherence_diamond
  [A B : Grpd]
  (P : τ (Product_grpd A B) → Grpd)
  [a0 a1 : τ A]
  [b0 b1 : τ B]
  (p : τ (a0 = a1))
  (q : τ (b0 = b1))
  (u : τ (P (@Product_pair_grpd A B a0 b0)))
  : τ (@=
      (P (@Product_pair_grpd A B a1 b1))
      (@product_transport_base_then_fibre
        A B P a0 a1 b0 b1 p q u)
      (@product_transport_fibre_then_base
        A B P a0 a1 b0 b1 p q u))
≔ @eq_trans
    (P (@Product_pair_grpd A B a1 b1))
    (@product_transport_base_then_fibre
      A B P a0 a1 b0 b1 p q u)
    (@product_transport_direct A B P a0 a1 b0 b1 p q u)
    (@product_transport_fibre_then_base
      A B P a0 a1 b0 b1 p q u)
    (@eq_sym
      (P (@Product_pair_grpd A B a1 b1))
      (@product_transport_direct A B P a0 a1 b0 b1 p q u)
      (@product_transport_base_then_fibre
        A B P a0 a1 b0 b1 p q u)
      (@product_transport_direct_agrees_base_then_fibre
        A B P a0 a1 b0 b1 p q u))
    (@product_transport_direct_agrees_fibre_then_base
      A B P a0 a1 b0 b1 p q u);

// Path-valued categorical realization of a product-indexed Grpd family.
symbol ProductPathFamily_catd
  [A B : Grpd]
  (P : τ (Product_grpd A B) → Grpd)
  : τ (@Catd (Path_cat (Product_grpd A B)))
≔ @path_lift_fapp0
    (Product_grpd A B)
    Cat_cat
    (λ z : τ (Product_grpd A B), Path_cat (P z));

// Existing displayed action along the product path.
symbol product_path_structured_transport
  [A B : Grpd]
  (P : τ (Product_grpd A B) → Grpd)
  [s t : τ (Product_grpd A B)]
  (u : τ (P s))
  (r : τ (s = t))
  : τ (P t)
≔ @path_cat_structured_transport
    (Product_grpd A B)
    (@ProductPathFamily_catd A B P)
    s t u r;

// Existing structured PathOut induction evaluated at the product path.
symbol product_path_structured_induction
  [A B : Grpd]
  (P : τ (Product_grpd A B) → Grpd)
  [s t : τ (Product_grpd A B)]
  (u : τ (P s))
  (r : τ (s = t))
  : τ (P t)
≔ @path_cat_path_ind_app
    (Product_grpd A B)
    (@ProductPathFamily_catd A B P)
    s t u r;

// Structured displayed transport agrees with primitive right-J transport.
symbol product_path_structured_transport_agrees_primitive
  [A B : Grpd]
  (P : τ (Product_grpd A B) → Grpd)
  [s t : τ (Product_grpd A B)]
  (u : τ (P s))
  (r : τ (s = t))
  : τ (@=
      (P t)
      (@product_path_structured_transport A B P s t u r)
      (@product_path_transport A B P s t r u))
≔ @path_cat_structured_transport_agrees_ind_eqr
    (Product_grpd A B)
    (@ProductPathFamily_catd A B P)
    s t u r;

// Structured PathOut induction agrees with the same primitive transport.
symbol product_path_structured_induction_agrees_primitive
  [A B : Grpd]
  (P : τ (Product_grpd A B) → Grpd)
  [s t : τ (Product_grpd A B)]
  (u : τ (P s))
  (r : τ (s = t))
  : τ (@=
      (P t)
      (@product_path_structured_induction A B P s t u r)
      (@product_path_transport A B P s t r u))
≔ @path_cat_path_ind_app_agrees_ind_eqr
    (Product_grpd A B)
    (@ProductPathFamily_catd A B P)
    s t u r;
