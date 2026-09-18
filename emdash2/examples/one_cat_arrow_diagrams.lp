/* Native squares become actual arrow-diagram transformations in a OneCat. */
require open emdash.emdash3_2_one_cat_arrow_diagrams;

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [X Y : τ (Obj C)] (u : τ (Hom C X Y)) ⊢
  @tapp0_fapp0 _ _ _ _ (@lax_edge C X Y u)
    (@one_cat_arrow_universal_transf C C1) ≡ u;

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [X Y : τ (Obj C)] (u : τ (Hom C X Y)) ⊢
  @fapp0 WalkingArrow_cat C
    (@fapp0 _ _ (@one_cat_arrow_diagram_func C C1) (@lax_edge C X Y u))
    walking_arrow_src ≡ X;
assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [X Y : τ (Obj C)] (u : τ (Hom C X Y)) ⊢
  @fapp0 WalkingArrow_cat C
    (@fapp0 _ _ (@one_cat_arrow_diagram_func C C1) (@lax_edge C X Y u))
    walking_arrow_tgt ≡ Y;
assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [X Y : τ (Obj C)] (u : τ (Hom C X Y)) ⊢
  @fapp1_fapp0 WalkingArrow_cat C
    (@fapp0 _ _ (@one_cat_arrow_diagram_func C C1) (@lax_edge C X Y u))
    walking_arrow_src walking_arrow_tgt walking_arrow_generator ≡ u;


assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [X0 X1 Y0 Y1 : τ (Obj C)]
  (u : τ (Hom C X0 Y0)) (v : τ (Hom C X1 Y1))
  (a : τ (Hom C X0 X1)) (b : τ (Hom C Y0 Y1))
  (alpha : τ (Obj (@homdc_fibre C C (@hom_int C C (@id_func C))
    X0 X1 Y0 Y1 u v a b))) ⊢
  @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_src
    (@fapp1_fapp0 (@LaxArrow_cat C) (Functor_cat WalkingArrow_cat C)
      (@one_cat_arrow_diagram_func C C1)
      (@lax_edge C X0 Y0 u) (@lax_edge C X1 Y1 v)
      (@lax_square C X0 X1 Y0 Y1 u v a b alpha)) ≡ a;

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [X0 X1 Y0 Y1 : τ (Obj C)]
  (u : τ (Hom C X0 Y0)) (v : τ (Hom C X1 Y1))
  (a : τ (Hom C X0 X1)) (b : τ (Hom C Y0 Y1))
  (alpha : τ (Obj (@homdc_fibre C C (@hom_int C C (@id_func C))
    X0 X1 Y0 Y1 u v a b))) ⊢
  @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_tgt
    (@fapp1_fapp0 (@LaxArrow_cat C) (Functor_cat WalkingArrow_cat C)
      (@one_cat_arrow_diagram_func C C1)
      (@lax_edge C X0 Y0 u) (@lax_edge C X1 Y1 v)
      (@lax_square C X0 X1 Y0 Y1 u v a b alpha)) ≡ b;

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (z : τ (Obj (@LaxArrow_cat C))) ⊢
  @fapp1_fapp0 _ _ (@one_cat_arrow_diagram_func C C1) z z (@id (@LaxArrow_cat C) z)
  ≡ @id (Functor_cat WalkingArrow_cat C) (@fapp0 _ _ (@one_cat_arrow_diagram_func C C1) z);

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [z0 z1 z2 : τ (Obj (@LaxArrow_cat C))]
  (a : τ (Hom (@LaxArrow_cat C) z0 z1)) (b : τ (Hom (@LaxArrow_cat C) z1 z2)) ⊢
  @comp_fapp0 (Functor_cat WalkingArrow_cat C) _ _ _
    (@fapp1_fapp0 _ _ (@one_cat_arrow_diagram_func C C1) z1 z2 b)
    (@fapp1_fapp0 _ _ (@one_cat_arrow_diagram_func C C1) z0 z1 a)
  ≡ @fapp1_fapp0 _ _ (@one_cat_arrow_diagram_func C C1) z0 z2
      (@comp_fapp0 (@LaxArrow_cat C) z0 z1 z2 b a);

// The new owner does not convert arbitrary category cells to equality.
assertnot (C : Cat) (x y : τ (Obj C)) (f g : τ (Hom C x y))
  (alpha : τ (Hom (Hom_cat C x y) f g)) ⊢
  alpha : τ (@= (Hom C x y) f g);

type λ C : Cat, λ C1 : τ (IsNCat (cat_succ cat_zero) C),
  λ z0 : τ (Obj (@LaxArrow_cat C)), λ z1 : τ (Obj (@LaxArrow_cat C)),
  λ a : τ (Hom (@LaxArrow_cat C) z0 z1), λ b : τ (Hom (@LaxArrow_cat C) z0 z1),
  @fapp1_func _ _ (@fapp1_func _ _ (@one_cat_arrow_diagram_func C C1) z0 z1) a b;

// Constructor-visible identity retains the universal edge after opposite normalization.
assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (x y : τ (Obj C)) (u : τ (Hom C x y)) ⊢
  @tapp1_fapp0 (@LaxArrow_cat C) C (@cubical_src_func C) (@cubical_tgt_func C)
    (@lax_edge C x y u) (@lax_edge C x y u) (@one_cat_arrow_universal_transf C C1)
    (@id (@LaxArrow_cat C) (@lax_edge C x y u)) ≡ u;
