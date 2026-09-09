require open emdash.emdash3_2_adjunction_mates;

assert (R L : Cat) (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G)) (X : τ (Obj R)) (Y : τ (Obj L))
  (h : τ (Hom L (@fapp0 R L F X) Y))
  ⊢ @fapp0 _ _ (@adjunction_untranspose_func R L F G J X Y)
      (@fapp0 _ _ (@adjunction_transpose_func R L F G J X Y) h) ≡ h;

assert (R L : Cat) (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G)) (X : τ (Obj R)) (Y : τ (Obj L))
  (k : τ (Hom R X (@fapp0 L R G Y)))
  ⊢ @fapp0 _ _ (@adjunction_transpose_func R L F G J X Y)
      (@fapp0 _ _ (@adjunction_untranspose_func R L F G J X Y) k) ≡ k;

assert (R L : Cat) (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G)) (X : τ (Obj R)) (Y : τ (Obj L))
  ⊢ @comp_cat_fapp0 _ _ _
      (@adjunction_untranspose_func R L F G J X Y)
      (@adjunction_transpose_func R L F G J X Y)
    ≡ @id_func (Hom_cat L (@fapp0 R L F X) Y);

assert (R L : Cat) (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G)) (X : τ (Obj R)) (Y : τ (Obj L))
  ⊢ @comp_cat_fapp0 _ _ _
      (@adjunction_transpose_func R L F G J X Y)
      (@adjunction_untranspose_func R L F G J X Y)
    ≡ @id_func (Hom_cat R X (@fapp0 L R G Y));

// Point cancellation overlap: three alternating mates, either cut first.
assert (R L : Cat) (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G)) (X : τ (Obj R)) (Y : τ (Obj L)) (h : τ (Obj (Hom_cat L (@fapp0 R L F X) Y))) ⊢
  @fapp0 (Hom_cat L (@fapp0 R L F X) Y) (Hom_cat R X (@fapp0 L R G Y)) (@adjunction_transpose_func R L F G J X Y)
    (@fapp0 (Hom_cat R X (@fapp0 L R G Y)) (Hom_cat L (@fapp0 R L F X) Y) (@adjunction_untranspose_func R L F G J X Y) (@fapp0 (Hom_cat L (@fapp0 R L F X) Y) (Hom_cat R X (@fapp0 L R G Y)) (@adjunction_transpose_func R L F G J X Y) h))
  ≡ @fapp0 (Hom_cat L (@fapp0 R L F X) Y) (Hom_cat R X (@fapp0 L R G Y)) (@adjunction_transpose_func R L F G J X Y) h;

assert (R L : Cat) (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G)) (X : τ (Obj R)) (Y : τ (Obj L)) (h : τ (Obj (Hom_cat R X (@fapp0 L R G Y)))) ⊢
  @fapp0 (Hom_cat R X (@fapp0 L R G Y)) (Hom_cat L (@fapp0 R L F X) Y) (@adjunction_untranspose_func R L F G J X Y)
    (@fapp0 (Hom_cat L (@fapp0 R L F X) Y) (Hom_cat R X (@fapp0 L R G Y)) (@adjunction_transpose_func R L F G J X Y) (@fapp0 (Hom_cat R X (@fapp0 L R G Y)) (Hom_cat L (@fapp0 R L F X) Y) (@adjunction_untranspose_func R L F G J X Y) h))
  ≡ @fapp0 (Hom_cat R X (@fapp0 L R G Y)) (Hom_cat L (@fapp0 R L F X) Y) (@adjunction_untranspose_func R L F G J X Y) h;

// Typed equality invokes the unifier; the runtime head remains formal.
assert (R L : Cat) (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G)) (X : τ (Obj R)) (Y : τ (Obj L)) ⊢ eq_refl (@adjunction_transpose_func R L F G J X Y)
  : τ (@= (Functor (Hom_cat L (@fapp0 R L F X) Y) (Hom_cat R X (@fapp0 L R G Y))) (@adjunction_transpose_func R L F G J X Y) (@adjunction_transpose_semantic_func R L F G J X Y));
assert (R L : Cat) (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G)) (X : τ (Obj R)) (Y : τ (Obj L)) (h : τ (Obj (Hom_cat L (@fapp0 R L F X) Y))) ⊢ eq_refl (@fapp0 _ _ (@adjunction_transpose_func R L F G J X Y) h)
  : τ (@= (Obj (Hom_cat R X (@fapp0 L R G Y))) (@fapp0 _ _ (@adjunction_transpose_func R L F G J X Y) h) (@fapp0 _ _ (@adjunction_transpose_semantic_func R L F G J X Y) h));
assertnot (R L : Cat) (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G)) (X : τ (Obj R)) (Y : τ (Obj L)) ⊢ (@adjunction_transpose_func R L F G J X Y) ≡ @adjunction_transpose_semantic_func R L F G J X Y;
assertnot (R L : Cat) (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G)) (X : τ (Obj R)) (Y : τ (Obj L)) (other : τ (Functor (Hom_cat L (@fapp0 R L F X) Y) (Hom_cat R X (@fapp0 L R G Y)))) ⊢ eq_refl (@adjunction_transpose_func R L F G J X Y)
  : τ (@= (Functor (Hom_cat L (@fapp0 R L F X) Y) (Hom_cat R X (@fapp0 L R G Y))) (@adjunction_transpose_func R L F G J X Y) other);
assertnot (R L : Cat) (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G)) (X : τ (Obj R)) (Y : τ (Obj L)) (h k : τ (Obj (Hom_cat L (@fapp0 R L F X) Y))) ⊢ eq_refl (@fapp0 _ _ (@adjunction_transpose_func R L F G J X Y) h)
  : τ (@= (Obj (Hom_cat R X (@fapp0 L R G Y))) (@fapp0 _ _ (@adjunction_transpose_func R L F G J X Y) h) (@fapp0 _ _ (@adjunction_transpose_semantic_func R L F G J X Y) k));

type λ R : Cat, λ L : Cat, λ F : τ (Functor R L), λ G : τ (Functor L R),
  λ J : τ (@Adjunction R L F G), λ X : τ (Obj R), λ Y : τ (Obj L),
  λ h : τ (Obj (Hom_cat L (@fapp0 R L F X) Y)), λ k : τ (Obj (Hom_cat L (@fapp0 R L F X) Y)),
  @fapp1_func _ _ (@adjunction_transpose_func R L F G J X Y) h k;

// Typed equality invokes the unifier; the runtime head remains formal.
assert (R L : Cat) (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G)) (X : τ (Obj R)) (Y : τ (Obj L)) ⊢ eq_refl (@adjunction_untranspose_func R L F G J X Y)
  : τ (@= (Functor (Hom_cat R X (@fapp0 L R G Y)) (Hom_cat L (@fapp0 R L F X) Y)) (@adjunction_untranspose_func R L F G J X Y) (@adjunction_untranspose_semantic_func R L F G J X Y));
assert (R L : Cat) (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G)) (X : τ (Obj R)) (Y : τ (Obj L)) (h : τ (Obj (Hom_cat R X (@fapp0 L R G Y)))) ⊢ eq_refl (@fapp0 _ _ (@adjunction_untranspose_func R L F G J X Y) h)
  : τ (@= (Obj (Hom_cat L (@fapp0 R L F X) Y)) (@fapp0 _ _ (@adjunction_untranspose_func R L F G J X Y) h) (@fapp0 _ _ (@adjunction_untranspose_semantic_func R L F G J X Y) h));
assertnot (R L : Cat) (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G)) (X : τ (Obj R)) (Y : τ (Obj L)) ⊢ (@adjunction_untranspose_func R L F G J X Y) ≡ @adjunction_untranspose_semantic_func R L F G J X Y;
assertnot (R L : Cat) (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G)) (X : τ (Obj R)) (Y : τ (Obj L)) (other : τ (Functor (Hom_cat R X (@fapp0 L R G Y)) (Hom_cat L (@fapp0 R L F X) Y))) ⊢ eq_refl (@adjunction_untranspose_func R L F G J X Y)
  : τ (@= (Functor (Hom_cat R X (@fapp0 L R G Y)) (Hom_cat L (@fapp0 R L F X) Y)) (@adjunction_untranspose_func R L F G J X Y) other);
assertnot (R L : Cat) (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G)) (X : τ (Obj R)) (Y : τ (Obj L)) (h k : τ (Obj (Hom_cat R X (@fapp0 L R G Y)))) ⊢ eq_refl (@fapp0 _ _ (@adjunction_untranspose_func R L F G J X Y) h)
  : τ (@= (Obj (Hom_cat L (@fapp0 R L F X) Y)) (@fapp0 _ _ (@adjunction_untranspose_func R L F G J X Y) h) (@fapp0 _ _ (@adjunction_untranspose_semantic_func R L F G J X Y) k));

type λ R : Cat, λ L : Cat, λ F : τ (Functor R L), λ G : τ (Functor L R),
  λ J : τ (@Adjunction R L F G), λ X : τ (Obj R), λ Y : τ (Obj L),
  λ h : τ (Obj (Hom_cat R X (@fapp0 L R G Y))), λ k : τ (Obj (Hom_cat R X (@fapp0 L R G Y))),
  @fapp1_func _ _ (@adjunction_untranspose_func R L F G J X Y) h k;

// Actual terminal-category corner of the terminal-section warning family.
assert (J : τ (@Adjunction Terminal_cat Terminal_cat (@id_func Terminal_cat) (@id_func Terminal_cat))) ⊢
  @comp_cat_fapp0 _ _ _
    (@adjunction_untranspose_func _ _ _ _ J Terminal_obj Terminal_obj)
    (@adjunction_transpose_func _ _ _ _ J Terminal_obj Terminal_obj)
  ≡ @id_func Terminal_cat;
assert (J : τ (@Adjunction Terminal_cat Terminal_cat (@id_func Terminal_cat) (@id_func Terminal_cat))) ⊢
  @comp_cat_fapp0 _ _ _
    (@adjunction_transpose_func _ _ _ _ J Terminal_obj Terminal_obj)
    (@adjunction_untranspose_func _ _ _ _ J Terminal_obj Terminal_obj)
  ≡ @id_func Terminal_cat;

// A generic hom-prof comparison does not have constant-terminal source.
assertnot (R L : Cat) (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G)) (X : τ (Obj R)) (Y : τ (Obj L)) (Z : Cat) ⊢
  @defiso_to _ _ _ (@Adjunction_hom_prof_comparison R L F G J)
  : τ (@Transf (Product_cat (Op_cat R) L) Cat_cat
      (@Const_catd (Product_cat (Op_cat R) L) Terminal_cat)
      (@Const_catd (Product_cat (Op_cat R) L) Z));

// Transparent unit/counit definitions compute before usability.
assert (R L : Cat) (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G)) (X : τ (Obj R)) (Y : τ (Obj L))
  (h : τ (Hom L (@fapp0 R L F X) Y))
  ⊢ @fapp0 _ _ (@adjunction_transpose_semantic_func R L F G J X Y) h
    ≡ @comp_fapp0 R X (@fapp0 L R G (@fapp0 R L F X)) (@fapp0 L R G Y)
      (@fapp1_fapp0 L R G (@fapp0 R L F X) Y h)
      (@tapp0_fapp0 R R (@id_func R) (@comp_cat_fapp0 R L R G F)
        X (@unit_adj_transf R L F G J));

assert (R L : Cat) (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G)) (X : τ (Obj R)) (Y : τ (Obj L))
  (k : τ (Hom R X (@fapp0 L R G Y)))
  ⊢ @fapp0 _ _ (@adjunction_untranspose_semantic_func R L F G J X Y) k
    ≡ @comp_fapp0 L (@fapp0 R L F X) (@fapp0 R L F (@fapp0 L R G Y)) Y
      (@tapp0_fapp0 L L (@comp_cat_fapp0 L R L F G) (@id_func L)
        Y (@counit_adj_transf R L F G J))
      (@fapp1_fapp0 R L F X (@fapp0 L R G Y) k);

assert (R L : Cat) (F : τ (Functor R L)) (G : τ (Functor L R))
  (J : τ (@Adjunction R L F G)) (X : τ (Obj R)) (Y : τ (Obj L))
  (h : τ (Hom L (@fapp0 R L F X) Y)) ⊢
  eq_refl (@fapp0 _ _ (@adjunction_transpose_func R L F G J X Y) h)
  : τ (@= (Hom R X (@fapp0 L R G Y))
      (@fapp0 _ _ (@adjunction_transpose_func R L F G J X Y) h)
      (@fapp0 _ _ (@adjunction_transpose_semantic_func R L F G J X Y) h));
