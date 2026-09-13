/* Whole-family cancellation uses the original transformation as data. */
require open emdash.emdash3_2_one_cat_adjunction_families;

assert (B R L : Cat)
  (R1 : τ (IsNCat (cat_succ cat_zero) R))
  (L1 : τ (IsNCat (cat_succ cat_zero) L))
  (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G))
  (A : τ (Functor B R)) (D : τ (Functor B L))
  (h : τ (Obj (Hom_cat (Functor_cat B L) (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D))) ⊢ @fapp0 _ _
    (@one_cat_adjunction_family_untranspose_func B R L R1 L1 F G J A D) (@fapp0 _ _
    (@one_cat_adjunction_family_transpose_func B R L R1 L1 F G J A D) h) ≡ h;

assert (B R L : Cat)
  (R1 : τ (IsNCat (cat_succ cat_zero) R))
  (L1 : τ (IsNCat (cat_succ cat_zero) L))
  (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G))
  (A : τ (Functor B R)) (D : τ (Functor B L))
  ⊢ @comp_cat_fapp0 (Hom_cat (Functor_cat B L) (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D) (Hom_cat (Functor_cat B R)
    A (@fapp0 _ _ (@comp_cat_cov_func B L R G) D)) (Hom_cat (Functor_cat B L) (@fapp0 _ _ (@comp_cat_cov_func B R L F)
    A) D) (@one_cat_adjunction_family_untranspose_func B R L R1 L1 F G J A D) (@one_cat_adjunction_family_transpose_func
    B R L R1 L1 F G J A D) ≡ @id_func (Hom_cat (Functor_cat B L) (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D);

// Native postcomposition endpoints keep the existing cancellation owner.
// Whole inverse cancellation projects to the next native Hom functor.
assert (B R L : Cat)
  (R1 : τ (IsNCat (cat_succ cat_zero) R))
  (L1 : τ (IsNCat (cat_succ cat_zero) L))
  (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G))
  (A : τ (Functor B R)) (D : τ (Functor B L))
  (h k : τ (Obj (Hom_cat (Functor_cat B L) (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D)))
  ⊢ @fapp1_func _ _ (@comp_cat_fapp0 (Hom_cat (Functor_cat B L) (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D) (Hom_cat
    (Functor_cat B R) A (@fapp0 _ _ (@comp_cat_cov_func B L R G) D)) (Hom_cat (Functor_cat B L) (@fapp0 _ _
    (@comp_cat_cov_func B R L F) A) D) (@one_cat_adjunction_family_untranspose_func B R L R1 L1 F G J A D)
    (@one_cat_adjunction_family_transpose_func B R L R1 L1 F G J A D)) h k
    ≡ @id_func (Hom_cat (Hom_cat (Functor_cat B L) (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D) h k);

assertnot (B R L : Cat)
  (R1 : τ (IsNCat (cat_succ cat_zero) R))
  (L1 : τ (IsNCat (cat_succ cat_zero) L))
  (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G))
  (A : τ (Functor B R)) (D : τ (Functor B L))
  (h k : τ (Obj (Hom_cat (Functor_cat B L) (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D)))
  ⊢ eq_refl (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func B R L R1 L1 F G J A D) (@fapp0 _ _
    (@one_cat_adjunction_family_transpose_func B R L R1 L1 F G J A D) h))
    : τ (@= (Obj (Hom_cat (Functor_cat B L) (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D)) (@fapp0 _ _
      (@one_cat_adjunction_family_untranspose_func B R L R1 L1 F G J A D) (@fapp0 _ _
      (@one_cat_adjunction_family_transpose_func B R L R1 L1 F G J A D) h)) k);

assert (B R L : Cat)
  (R1 : τ (IsNCat (cat_succ cat_zero) R))
  (L1 : τ (IsNCat (cat_succ cat_zero) L))
  (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G))
  (A : τ (Functor B R)) (D : τ (Functor B L))
  (h : τ (Obj (Hom_cat (Functor_cat B R) A (@fapp0 _ _ (@comp_cat_cov_func B L R G) D)))) ⊢ @fapp0 _ _
    (@one_cat_adjunction_family_transpose_func B R L R1 L1 F G J A D) (@fapp0 _ _
    (@one_cat_adjunction_family_untranspose_func B R L R1 L1 F G J A D) h) ≡ h;

assert (B R L : Cat)
  (R1 : τ (IsNCat (cat_succ cat_zero) R))
  (L1 : τ (IsNCat (cat_succ cat_zero) L))
  (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G))
  (A : τ (Functor B R)) (D : τ (Functor B L))
  ⊢ @comp_cat_fapp0 (Hom_cat (Functor_cat B R) A (@fapp0 _ _ (@comp_cat_cov_func B L R G) D)) (Hom_cat (Functor_cat B L)
    (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D) (Hom_cat (Functor_cat B R) A (@fapp0 _ _ (@comp_cat_cov_func B L R G)
    D)) (@one_cat_adjunction_family_transpose_func B R L R1 L1 F G J A D) (@one_cat_adjunction_family_untranspose_func B
    R L R1 L1 F G J A D) ≡ @id_func (Hom_cat (Functor_cat B R) A (@fapp0 _ _ (@comp_cat_cov_func B L R G) D));

// Native postcomposition endpoints keep the existing cancellation owner.
// Whole inverse cancellation projects to the next native Hom functor.
assert (B R L : Cat)
  (R1 : τ (IsNCat (cat_succ cat_zero) R))
  (L1 : τ (IsNCat (cat_succ cat_zero) L))
  (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G))
  (A : τ (Functor B R)) (D : τ (Functor B L))
  (h k : τ (Obj (Hom_cat (Functor_cat B R) A (@fapp0 _ _ (@comp_cat_cov_func B L R G) D))))
  ⊢ @fapp1_func _ _ (@comp_cat_fapp0 (Hom_cat (Functor_cat B R) A (@fapp0 _ _ (@comp_cat_cov_func B L R G) D)) (Hom_cat
    (Functor_cat B L) (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D) (Hom_cat (Functor_cat B R) A (@fapp0 _ _
    (@comp_cat_cov_func B L R G) D)) (@one_cat_adjunction_family_transpose_func B R L R1 L1 F G J A D)
    (@one_cat_adjunction_family_untranspose_func B R L R1 L1 F G J A D)) h k
    ≡ @id_func (Hom_cat (Hom_cat (Functor_cat B R) A (@fapp0 _ _ (@comp_cat_cov_func B L R G) D)) h k);

assertnot (B R L : Cat)
  (R1 : τ (IsNCat (cat_succ cat_zero) R))
  (L1 : τ (IsNCat (cat_succ cat_zero) L))
  (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G))
  (A : τ (Functor B R)) (D : τ (Functor B L))
  (h k : τ (Obj (Hom_cat (Functor_cat B R) A (@fapp0 _ _ (@comp_cat_cov_func B L R G) D))))
  ⊢ eq_refl (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func B R L R1 L1 F G J A D) (@fapp0 _ _
    (@one_cat_adjunction_family_untranspose_func B R L R1 L1 F G J A D) h))
    : τ (@= (Obj (Hom_cat (Functor_cat B R) A (@fapp0 _ _ (@comp_cat_cov_func B L R G) D))) (@fapp0 _ _
      (@one_cat_adjunction_family_transpose_func B R L R1 L1 F G J A D) (@fapp0 _ _
      (@one_cat_adjunction_family_untranspose_func B R L R1 L1 F G J A D) h)) k);

// A component is one whole prewhiskered original cell.
assert (B R L : Cat)
  (R1 : τ (IsNCat (cat_succ cat_zero) R))
  (L1 : τ (IsNCat (cat_succ cat_zero) L))
  (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G))
  (A : τ (Functor B R)) (D : τ (Functor B L))
  ⊢ @tapp0_fapp0 _ _ _ _ A (@unit_adj_transf _ _ _ _ (@one_cat_postcomp_adjunction B R L R1 L1 F G J))
    ≡ @fapp0 _ _ (@comp_cat_con_fapp1_func B R R A (@id_func R) (@comp_cat_fapp0 R L R G F))
      (@unit_adj_transf R L F G J);

assert (B R L : Cat)
  (R1 : τ (IsNCat (cat_succ cat_zero) R))
  (L1 : τ (IsNCat (cat_succ cat_zero) L))
  (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G))
  (A : τ (Functor B R)) (D : τ (Functor B L)) (b : τ (Obj B))
  ⊢ @tapp0_fapp0 _ _ _ _ b
      (@tapp0_fapp0 _ _ _ _ A (@unit_adj_transf _ _ _ _ (@one_cat_postcomp_adjunction B R L R1 L1 F G J)))
    ≡ @tapp0_fapp0 _ _ _ _ (@fapp0 _ _ A b) (@unit_adj_transf R L F G J);

// A component is one whole prewhiskered original cell.
assert (B R L : Cat)
  (R1 : τ (IsNCat (cat_succ cat_zero) R))
  (L1 : τ (IsNCat (cat_succ cat_zero) L))
  (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G))
  (A : τ (Functor B R)) (D : τ (Functor B L))
  ⊢ @tapp0_fapp0 _ _ _ _ D (@counit_adj_transf _ _ _ _ (@one_cat_postcomp_adjunction B R L R1 L1 F G J))
    ≡ @fapp0 _ _ (@comp_cat_con_fapp1_func B L L D (@comp_cat_fapp0 L R L F G) (@id_func L))
      (@counit_adj_transf R L F G J);

assert (B R L : Cat)
  (R1 : τ (IsNCat (cat_succ cat_zero) R))
  (L1 : τ (IsNCat (cat_succ cat_zero) L))
  (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G))
  (A : τ (Functor B R)) (D : τ (Functor B L)) (b : τ (Obj B))
  ⊢ @tapp0_fapp0 _ _ _ _ b
      (@tapp0_fapp0 _ _ _ _ D (@counit_adj_transf _ _ _ _ (@one_cat_postcomp_adjunction B R L R1 L1 F G J)))
    ≡ @tapp0_fapp0 _ _ _ _ (@fapp0 _ _ D b) (@counit_adj_transf R L F G J);

// The whole cell, including action on a nonidentity family transformation.
assert (B R L : Cat)
  (R1 : τ (IsNCat (cat_succ cat_zero) R))
  (L1 : τ (IsNCat (cat_succ cat_zero) L))
  (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G)) ⊢ (@unit_adj_transf _ _ _ _ (@one_cat_postcomp_adjunction B R L R1 L1 F G J)) ≡
    (@comp_cat_cov_func_func_transf B R R (@id_func R) (@comp_cat_fapp0 R L R G F) (@unit_adj_transf R L F G J));
assert (B R L : Cat)
  (R1 : τ (IsNCat (cat_succ cat_zero) R))
  (L1 : τ (IsNCat (cat_succ cat_zero) L))
  (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G))
  (A D : τ (Functor B R)) (h : τ (@Transf B R A D))
  ⊢ @tapp1_fapp0 _ _ _ _ A D (@unit_adj_transf _ _ _ _ (@one_cat_postcomp_adjunction B R L R1 L1 F G J)) h
    ≡ @tapp1_fapp0 _ _ _ _ A D (@comp_cat_cov_func_func_transf B R R (@id_func R) (@comp_cat_fapp0 R L R G F)
      (@unit_adj_transf R L F G J)) h;

// The whole cell, including action on a nonidentity family transformation.
assert (B R L : Cat)
  (R1 : τ (IsNCat (cat_succ cat_zero) R))
  (L1 : τ (IsNCat (cat_succ cat_zero) L))
  (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G)) ⊢ (@counit_adj_transf _ _ _ _ (@one_cat_postcomp_adjunction B R L R1 L1 F G J)) ≡
    (@comp_cat_cov_func_func_transf B L L (@comp_cat_fapp0 L R L F G) (@id_func L) (@counit_adj_transf R L F G J));
assert (B R L : Cat)
  (R1 : τ (IsNCat (cat_succ cat_zero) R))
  (L1 : τ (IsNCat (cat_succ cat_zero) L))
  (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G))
  (A D : τ (Functor B L)) (h : τ (@Transf B L A D))
  ⊢ @tapp1_fapp0 _ _ _ _ A D (@counit_adj_transf _ _ _ _ (@one_cat_postcomp_adjunction B R L R1 L1 F G J)) h
    ≡ @tapp1_fapp0 _ _ _ _ A D (@comp_cat_cov_func_func_transf B L L (@comp_cat_fapp0 L R L F G) (@id_func L)
      (@counit_adj_transf R L F G J)) h;

// The original whole semantic comparison remains usable at native endpoints.
assert (B R L : Cat)
  (R1 : τ (IsNCat (cat_succ cat_zero) R))
  (L1 : τ (IsNCat (cat_succ cat_zero) L))
  (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G)) (A : τ (Functor B R)) (D : τ (Functor B L))
  ⊢ eq_refl (@one_cat_adjunction_family_transpose_func B R L R1 L1 F G J A D) : τ (@= (Functor (Hom_cat (Functor_cat B
    L) (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D) (Hom_cat (Functor_cat B R) A (@fapp0 _ _ (@comp_cat_cov_func B L R
    G) D))) (@one_cat_adjunction_family_transpose_func B R L R1 L1 F G J A D) (@adjunction_transpose_semantic_func
    (Functor_cat B R) (Functor_cat B L) (@comp_cat_cov_func B R L F) (@comp_cat_cov_func B L R G)
    (@one_cat_postcomp_adjunction B R L R1 L1 F G J) A D));
assertnot (B R L : Cat)
  (R1 : τ (IsNCat (cat_succ cat_zero) R))
  (L1 : τ (IsNCat (cat_succ cat_zero) L))
  (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G)) (A : τ (Functor B R)) (D : τ (Functor B L))
  (other : τ (Functor (Hom_cat (Functor_cat B L) (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D) (Hom_cat (Functor_cat B
    R) A (@fapp0 _ _ (@comp_cat_cov_func B L R G) D))))
  ⊢ eq_refl (@one_cat_adjunction_family_transpose_func B R L R1 L1 F G J A D) : τ (@= (Functor (Hom_cat (Functor_cat B
    L) (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D) (Hom_cat (Functor_cat B R) A (@fapp0 _ _ (@comp_cat_cov_func B L R
    G) D))) (@one_cat_adjunction_family_transpose_func B R L R1 L1 F G J A D) other);

// The original whole semantic comparison remains usable at native endpoints.
assert (B R L : Cat)
  (R1 : τ (IsNCat (cat_succ cat_zero) R))
  (L1 : τ (IsNCat (cat_succ cat_zero) L))
  (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G)) (A : τ (Functor B R)) (D : τ (Functor B L))
  ⊢ eq_refl (@one_cat_adjunction_family_untranspose_func B R L R1 L1 F G J A D) : τ (@= (Functor (Hom_cat (Functor_cat B
    R) A (@fapp0 _ _ (@comp_cat_cov_func B L R G) D)) (Hom_cat (Functor_cat B L) (@fapp0 _ _ (@comp_cat_cov_func B R L
    F) A) D)) (@one_cat_adjunction_family_untranspose_func B R L R1 L1 F G J A D) (@adjunction_untranspose_semantic_func
    (Functor_cat B R) (Functor_cat B L) (@comp_cat_cov_func B R L F) (@comp_cat_cov_func B L R G)
    (@one_cat_postcomp_adjunction B R L R1 L1 F G J) A D));
assertnot (B R L : Cat)
  (R1 : τ (IsNCat (cat_succ cat_zero) R))
  (L1 : τ (IsNCat (cat_succ cat_zero) L))
  (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G)) (A : τ (Functor B R)) (D : τ (Functor B L))
  (other : τ (Functor (Hom_cat (Functor_cat B R) A (@fapp0 _ _ (@comp_cat_cov_func B L R G) D)) (Hom_cat (Functor_cat B
    L) (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D)))
  ⊢ eq_refl (@one_cat_adjunction_family_untranspose_func B R L R1 L1 F G J A D) : τ (@= (Functor (Hom_cat (Functor_cat B
    R) A (@fapp0 _ _ (@comp_cat_cov_func B L R G) D)) (Hom_cat (Functor_cat B L) (@fapp0 _ _ (@comp_cat_cov_func B R L
    F) A) D)) (@one_cat_adjunction_family_untranspose_func B R L R1 L1 F G J A D) other);
