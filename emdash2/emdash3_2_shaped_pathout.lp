/*
  Fixed-source PathOut action of a shaped unit-profunctor cell.

  A shaped cell

    r : Unit_prof(I) -> Prof_reindex(Unit_prof(A),F,G)

  is natural in both endpoints.  Fixing its first endpoint x0 therefore gives
  a displayed map Rep_I(x0) -> G^*Rep_A(F[x0]); Sigma totalization sends
  (x,p) to (G[x],r[p]) and retains the complete higher action.  This is a
  generic equipment/dependent-hom bridge, not simplex-specific syntax.

  The two proof-time comparisons below are deliberately owned by this late
  extension.  Early placement in the kernel changes unrelated, non-transitive
  proof-time search even though its warning inventory is unchanged.  Runtime
  preserves both Pullback_catd histories.
*/

require open emdash.emdash3_2;

// Stable Cat-valued precomposition is propositionally the ordinary composite
// functor.  Keeping this comparison whole avoids a hot `fapp0` rule and makes
// every higher action available through the existing equality/PathOver
// interface.
symbol cat_precomp_composite_path
  [W X Z : Cat]
  (F : τ (Functor W X))
  (G : τ (Functor X Z))
  : τ (@=
      (Obj (Functor_cat W Z))
      (@hom_precomp_along_fapp0
        Cat_cat Cat_cat (@id Cat_cat Cat_cat)
        Z W X F G)
      (@comp_cat_fapp0 W X Z G F))
≔ @eq_refl
    (Obj (Functor_cat W Z))
    (@hom_precomp_along_fapp0
      Cat_cat Cat_cat (@id Cat_cat Cat_cat)
      Z W X F G);

// Object observation of the whole comparison: (G o F)[w] = G[F[w]].
symbol cat_precomp_composite_component_path
  [W X Z : Cat]
  (F : τ (Functor W X))
  (G : τ (Functor X Z))
  (w : τ (Obj W))
  : τ (@=
      (Obj Z)
      (@fapp0 W Z
        (@hom_precomp_along_fapp0
          Cat_cat Cat_cat (@id Cat_cat Cat_cat)
          Z W X F G)
        w)
      (@fapp0 X Z G (@fapp0 W X F w)))
≔ @eq_ap
    (Obj (Functor_cat W Z))
    (Obj Z)
    (λ H : τ (Obj (Functor_cat W Z)), @fapp0 W Z H w)
    (@hom_precomp_along_fapp0
      Cat_cat Cat_cat (@id Cat_cat Cat_cat)
      Z W X F G)
    (@comp_cat_fapp0 W X Z G F)
    (@cat_precomp_composite_path W X Z F G);

// Existing product-pair telescope at x0: x |-> (x0,x).
symbol shaped_fixed_source_pair_func
  [I : Cat]
  (x0 : τ (Obj I))
  : τ (Functor I (Product_cat (Op_cat I) I))
≔ @fapp0
    (Op_cat I)
    (Functor_cat I (Product_cat (Op_cat I) I))
    (@Product_pair_tele_func (Op_cat I) I)
    x0;

// Reindexed unit-hom target before fixing the first endpoint.
symbol shaped_unit_target_catd
  [I A : Cat]
  (F G : τ (Functor I A))
  : τ (Catd (Product_cat (Op_cat I) I))
≔ @Prof_reindex A I A I (@Unit_prof A) F G;

// Pulling Unit_prof(I) back along x |-> (x0,x) is Rep_I(x0).
unif_rule
  @Pullback_catd
    _
    (Product_cat (Op_cat $I) $I)
    (@Unit_prof $I)
    (Struct_sigma
      (@Const_func $I (Op_cat $I) $x0)
      (@id Cat_cat $I))
  ≡ @hom_ $I $I (@id Cat_cat $I) $x0
  ↪ [ tt ≡ tt ];

// The corresponding target pullback is Hom_A(F[x0],G(-)).
unif_rule
  @Pullback_catd
    _
    (Product_cat (Op_cat $I) $I)
    (@Prof_reindex $A $I $A $I (@Unit_prof $A) $F $G)
    (Struct_sigma
      (@Const_func $I (Op_cat $I) $x0)
      (@id Cat_cat $I))
  ≡ @hom_ $A $I $G (@fapp0 $I $A $F $x0)
  ↪ [ tt ≡ tt ];

// Typed evidence exercises the two proof-time comparisons directly.
symbol shaped_fixed_source_unit_path
  [I : Cat]
  (x0 : τ (Obj I))
  : τ (@=
      (Obj (@Catd_cat I))
      (@Pullback_catd
        I (Product_cat (Op_cat I) I)
        (@Unit_prof I)
        (@shaped_fixed_source_pair_func I x0))
      (@Rep_catd I x0))
≔ @eq_refl
    (Obj (@Catd_cat I))
    (@Pullback_catd
      I (Product_cat (Op_cat I) I)
      (@Unit_prof I)
      (@shaped_fixed_source_pair_func I x0));

symbol shaped_fixed_source_target_path
  [I A : Cat]
  (F G : τ (Functor I A))
  (x0 : τ (Obj I))
  : τ (@=
      (Obj (@Catd_cat I))
      (@Pullback_catd
        I (Product_cat (Op_cat I) I)
        (@shaped_unit_target_catd I A F G)
        (@shaped_fixed_source_pair_func I x0))
      (@hom_ A I G (@fapp0 I A F x0)))
≔ @eq_refl
    (Obj (@Catd_cat I))
    (@Pullback_catd
      I (Product_cat (Op_cat I) I)
      (@shaped_unit_target_catd I A F G)
      (@shaped_fixed_source_pair_func I x0));

// Fixed-source displayed action of the shaped cell.
symbol shaped_unit_fixed_funcd
  [I A : Cat]
  (F G : τ (Functor I A))
  (r : τ (@Prof_hom I A A F (@Unit_prof A) G))
  (x0 : τ (Obj I))
  : τ (Functord
      (@Rep_catd I x0)
      (@hom_ A I G (@fapp0 I A F x0)))
≔ @fapp1_fapp0
    (@Catd_cat (Product_cat (Op_cat I) I))
    (@Catd_cat I)
    (@Pullback_catd_func
      I
      (Product_cat (Op_cat I) I)
      (@shaped_fixed_source_pair_func I x0))
    (@Unit_prof I)
    (@shaped_unit_target_catd I A F G)
    r;

// Whole PathOut action: (x,p) |-> (G[x],r[p]).
symbol shaped_pathout_func
  [I A : Cat]
  (F G : τ (Functor I A))
  (r : τ (@Prof_hom I A A F (@Unit_prof A) G))
  (x0 : τ (Obj I))
  : τ (Functor
      (@PathOut_cat I x0)
      (@PathOut_cat A (@fapp0 I A F x0)))
≔ @comp_cat_fapp0
    (@PathOut_cat I x0)
    (@Sigma_cat I (@hom_ A I G (@fapp0 I A F x0)))
    (@PathOut_cat A (@fapp0 I A F x0))
    (@sigma_pullback_total_func
      I A G (@Rep_catd A (@fapp0 I A F x0)))
    (@sigma_map_func
      I
      (@Rep_catd I x0)
      (@hom_ A I G (@fapp0 I A F x0))
      (@shaped_unit_fixed_funcd I A F G r x0));

// Readable fixed-(x0,x) component of the original shaped cell.
symbol shaped_pathout_component
  [I A : Cat]
  (F G : τ (Functor I A))
  (r : τ (@Prof_hom I A A F (@Unit_prof A) G))
  (x0 x : τ (Obj I))
  : τ (Functor
      (Hom_cat I x0 x)
      (Hom_cat A
        (@fapp0 I A F x0)
        (@fapp0 I A G x)))
≔ @tapp0_fapp0
    (Product_cat (Op_cat I) I)
    Cat_cat
    (@Unit_prof I)
    (@Prof_reindex A I A I (@Unit_prof A) F G)
    (Struct_sigma x0 x)
    r;

// Judgmental object observation of the whole PathOut action.
symbol shaped_pathout_object_beta
  [I A : Cat]
  (F G : τ (Functor I A))
  (r : τ (@Prof_hom I A A F (@Unit_prof A) G))
  (x0 x : τ (Obj I))
  (p : τ (Hom I x0 x))
  : τ (@=
      (Obj (@PathOut_cat A (@fapp0 I A F x0)))
      (@fapp0
        (@PathOut_cat I x0)
        (@PathOut_cat A (@fapp0 I A F x0))
        (@shaped_pathout_func I A F G r x0)
        (Struct_sigma x p))
      (Struct_sigma
        (@fapp0 I A G x)
        (@fapp0
          (Hom_cat I x0 x)
          (Hom_cat A (@fapp0 I A F x0) (@fapp0 I A G x))
          (@shaped_pathout_component I A F G r x0 x)
          p)))
≔ @eq_refl
    (Obj (@PathOut_cat A (@fapp0 I A F x0)))
    (Struct_sigma
      (@fapp0 I A G x)
      (@fapp0
        (Hom_cat I x0 x)
        (Hom_cat A (@fapp0 I A F x0) (@fapp0 I A G x))
        (@shaped_pathout_component I A F G r x0 x)
        p));

// Explicit retained hom action for recursive consumers.
symbol shaped_pathout_hom_func
  [I A : Cat]
  (F G : τ (Functor I A))
  (r : τ (@Prof_hom I A A F (@Unit_prof A) G))
  (x0 : τ (Obj I))
  (u v : τ (Obj (@PathOut_cat I x0)))
  : τ (Functor
      (Hom_cat (@PathOut_cat I x0) u v)
      (Hom_cat
        (@PathOut_cat A (@fapp0 I A F x0))
        (@fapp0
          (@PathOut_cat I x0)
          (@PathOut_cat A (@fapp0 I A F x0))
          (@shaped_pathout_func I A F G r x0)
          u)
        (@fapp0
          (@PathOut_cat I x0)
          (@PathOut_cat A (@fapp0 I A F x0))
          (@shaped_pathout_func I A F G r x0)
          v)))
≔ @fapp1_func
    (@PathOut_cat I x0)
    (@PathOut_cat A (@fapp0 I A F x0))
    (@shaped_pathout_func I A F G r x0)
    u v;
