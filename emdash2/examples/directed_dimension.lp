/*
  Reviewer milestone: recursive directed dimension uses the exact discrete
  base and remains distinct from object truncation.

  `OneCat` packages categories whose hom-categories are discrete. The final
  assertion iterates the promoted core-inclusion adequacy theorem one hom
  level further, without adding ordinary-iso univalence or runtime eta.
*/

require open emdash.emdash3_2_eq1_hom_action;

assert (n : TruncLevel) [C : Cat] ⊢
  IsObjTruncCat n C
  ≡ IsTruncGrpd n (Obj C);

assert (n : CatDim) ⊢
  cat_dim_trunc_level n
  : TruncLevel;

assert ⊢
  cat_dim_trunc_level cat_zero
  ≡ trunc_zero;

assert (n : CatDim) ⊢
  cat_dim_trunc_level (cat_succ n)
  ≡ trunc_succ (cat_dim_trunc_level n);

assert ⊢
  cat_dim_trunc_level (cat_succ cat_zero)
  ≡ trunc_one;

assert [C : Cat] ⊢
  IsNCat cat_zero C
  ≡ IsDiscreteCat C;

assert (n : CatDim) [C : Cat] ⊢
  IsNCat (cat_succ n) C
  ≡ @Pi_grpd (Obj C)
      (λ x : τ (Obj C),
        @Pi_grpd (Obj C)
          (λ y : τ (Obj C),
            IsNCat n (Hom_cat C x y)));

assert (n : CatDim)
  (C : Cat)
  (h : τ (IsNCat n C)) ⊢
  @ncat_carrier n (@Struct_ncat n C h)
  ≡ C;

assert (n : CatDim)
  (C : Cat)
  (h : τ (IsNCat n C)) ⊢
  @ncat_evidence n (@Struct_ncat n C h)
  ≡ h;

assert (X : τ OneCat)
  (x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))) ⊢
  @one_cat_hom_discrete X x y
  : τ (IsDiscreteCat
      (Hom_cat (@ncat_carrier (cat_succ cat_zero) X) x y));

assert (X : τ OneCat)
  (x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X)))
  (f g : τ (Hom (@ncat_carrier (cat_succ cat_zero) X) x y)) ⊢
  @one_cat_hom_core_homwise X x y f g
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
        g));

// Object truncation is not the directed zero-dimensional contract.
assertnot [C : Cat] ⊢
  IsObjTruncCat trunc_zero C
  ≡ IsNCat cat_zero C;

// The index map states the target level but does not construct its evidence.
assertnot (n : CatDim)
  [C : Cat]
  (h : τ (IsNCat n C)) ⊢
  h
  : τ (IsObjTruncCat (cat_dim_trunc_level n) C);

// Dimension codes remain distinct at the package boundary.
assertnot ⊢ ZeroCat ≡ OneCat;

// Evidence-retaining packages have no runtime eta.
assertnot (n : CatDim)
  (X : τ (NCat n)) ⊢
  X
  ≡ @Struct_ncat n
      (@ncat_carrier n X)
      (@ncat_evidence n X);
