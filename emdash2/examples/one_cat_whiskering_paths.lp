/* Retained Hom owners and the whole ordinary whiskering comparison. */
require open emdash.emdash3_2_one_cat_whiskering_paths;

assert [Q : Cat] (x x0 y y0 : τ (Obj Q))
  (g : τ (Hom Q x0 x)) (f : τ (Hom Q y y0))
  (h k : τ (Hom Q x y)) ⊢ @eq_refl (Functor (Hom_cat (Hom_cat Q x y) h k) (Hom_cat (Hom_cat Q x0 y0) (@Hom_fapp0 Q x
    x0 y y0 g f h) (@Hom_fapp0 Q x x0 y y0 g f k))) (@fapp1_func (Hom_cat Q x y) (Hom_cat Q x0 y0) (@Hom_func Q x x0 y
    y0 g f) h k) : τ (@= (Functor (Hom_cat (Hom_cat Q x y) h k) (Hom_cat (Hom_cat Q x0 y0) (@Hom_fapp0 Q x x0 y y0 g f
    h) (@Hom_fapp0 Q x x0 y y0 g f k))) (@fapp1_func (Hom_cat Q x y) (Hom_cat Q x0 y0) (@Hom_func Q x x0 y y0 g f) h
    k) (@comp_cat_fapp0 (Hom_cat (Hom_cat Q x y) h k) (Hom_cat (Hom_cat Q x0 y) (@hom_precomp_along_fapp0 Q Q
    (@id_func Q) y x0 x g h) (@hom_precomp_along_fapp0 Q Q (@id_func Q) y x0 x g k)) (Hom_cat (Hom_cat Q x0 y0)
    (@Hom_fapp0 Q x x0 y y0 g f h) (@Hom_fapp0 Q x x0 y y0 g f k)) (@hom_postcomp_fapp1_func Q Q (@id_func Q) x0 y y0
    f (@hom_precomp_along_fapp0 Q Q (@id_func Q) y x0 x g h) (@hom_precomp_along_fapp0 Q Q (@id_func Q) y x0 x g k))
    (@hom_precomp_along_fapp1_func Q Q (@id_func Q) y x0 x g h k)));

assert [Q : Cat] (x x0 y y0 : τ (Obj Q))
  (g : τ (Hom Q x0 x)) (f : τ (Hom Q y y0))
  (h k : τ (Hom Q x y)) ⊢ @eq_refl (Functor (Hom_cat (Hom_cat Q x y) h k) (Hom_cat (Hom_cat Q x0 y0) (@Hom_fapp0 Q x
    x0 y y0 g f h) (@Hom_fapp0 Q x x0 y y0 g f k))) (@fapp1_func (Hom_cat Q x y) (Hom_cat Q x0 y0) (@Hom_func Q x x0 y
    y0 g f) h k) : τ (@= (Functor (Hom_cat (Hom_cat Q x y) h k) (Hom_cat (Hom_cat Q x0 y0) (@Hom_fapp0 Q x x0 y y0 g f
    h) (@Hom_fapp0 Q x x0 y y0 g f k))) (@fapp1_func (Hom_cat Q x y) (Hom_cat Q x0 y0) (@Hom_func Q x x0 y y0 g f) h
    k) (@comp_cat_fapp0 (Hom_cat (Hom_cat Q x y) h k) (Hom_cat (Hom_cat Q x y0) (@hom_postcomp_fapp0 Q Q (@id_func Q)
    x y y0 f h) (@hom_postcomp_fapp0 Q Q (@id_func Q) x y y0 f k)) (Hom_cat (Hom_cat Q x0 y0) (@Hom_fapp0 Q x x0 y y0
    g f h) (@Hom_fapp0 Q x x0 y y0 g f k)) (@hom_precomp_along_fapp1_func Q Q (@id_func Q) y0 x0 x g
    (@hom_postcomp_fapp0 Q Q (@id_func Q) x y y0 f h) (@hom_postcomp_fapp0 Q Q (@id_func Q) x y y0 f k))
    (@hom_postcomp_fapp1_func Q Q (@id_func Q) x y y0 f h k)));

assert [A B E C : Cat] (D : τ (Functor B A)) (V : τ (Functor E C)) (F : τ (Functor A E)) ⊢ @eq_refl (Functor B C)
  (@Hom_fapp0 Cat_cat A B E C D V F) : τ (@= (Functor B C) (@Hom_fapp0 Cat_cat A B E C D V F) (@comp_cat_fapp0 B A C
  (@comp_cat_fapp0 A E C V F) D));

assertnot [A B E C : Cat] (D : τ (Functor B A)) (V : τ (Functor E C)) (F : τ (Functor A E)) ⊢ (@Hom_fapp0 Cat_cat A B
  E C D V F) ≡ (@comp_cat_fapp0 B A C (@comp_cat_fapp0 A E C V F) D);

assertnot [A B E C : Cat] (D : τ (Functor B A)) (V : τ (Functor E C)) (F : τ (Functor A E)) (D0 : τ (Functor B A)) ⊢
  @eq_refl (Functor B C) (@Hom_fapp0 Cat_cat A B E C D V F) : τ (@= (Functor B C) (@Hom_fapp0 Cat_cat A B E C D V F)
  (@comp_cat_fapp0 B A C (@comp_cat_fapp0 A E C V F) D0));

assertnot [A B E C : Cat] (D : τ (Functor B A)) (V : τ (Functor E C)) (F : τ (Functor A E)) (V0 : τ (Functor E C)) ⊢
  @eq_refl (Functor B C) (@Hom_fapp0 Cat_cat A B E C D V F) : τ (@= (Functor B C) (@Hom_fapp0 Cat_cat A B E C D V F)
  (@comp_cat_fapp0 B A C (@comp_cat_fapp0 A E C V0 F) D));

assertnot [A B E C : Cat] (D : τ (Functor B A)) (V : τ (Functor E C)) (F : τ (Functor A E)) (F0 : τ (Functor A E)) ⊢
  @eq_refl (Functor B C) (@Hom_fapp0 Cat_cat A B E C D V F) : τ (@= (Functor B C) (@Hom_fapp0 Cat_cat A B E C D V F)
  (@comp_cat_fapp0 B A C (@comp_cat_fapp0 A E C V F0) D));

// The three identity corners retain the existing primitive degeneration rules.
assert [A E C : Cat] (V : τ (Functor E C)) (F : τ (Functor A E))
  ⊢ @eq_refl (Functor A C) (@Hom_fapp0 Cat_cat A A E C (@id_func A) V F)
    : τ (@= (Functor A C) (@Hom_fapp0 Cat_cat A A E C (@id_func A) V F) (@comp_cat_fapp0 A E C V F));
assert [A B E : Cat] (D : τ (Functor B A)) (F : τ (Functor A E))
  ⊢ @eq_refl (Functor B E) (@Hom_fapp0 Cat_cat A B E E D (@id_func E) F)
    : τ (@= (Functor B E) (@Hom_fapp0 Cat_cat A B E E D (@id_func E) F) (@comp_cat_fapp0 B A E F D));
assert [A B C : Cat] (D : τ (Functor B A)) (V : τ (Functor A C))
  ⊢ @eq_refl (Functor B C) (@Hom_fapp0 Cat_cat A B A C D V (@id_func A))
    : τ (@= (Functor B C) (@Hom_fapp0 Cat_cat A B A C D V (@id_func A)) (@comp_cat_fapp0 B A C V D));

// The ordinary whole transformation is retained on both sides.
assert [A B E C : Cat] (E1 : τ (IsNCat (cat_succ cat_zero) E)) (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (D : τ (Functor B A)) (V : τ (Functor E C)) (F G : τ (Functor A E)) (alpha : τ (@Transf A E F G))
  ⊢ (@one_cat_whiskering_path A B E C E1 C1 D V F G alpha) : τ (@= (@Transf B C (@comp_cat_fapp0 B A C
    (@comp_cat_fapp0 A E C V F) D) (@comp_cat_fapp0 B A C (@comp_cat_fapp0 A E C V G) D)) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func B E C V (@comp_cat_fapp0 B A E F D) (@comp_cat_fapp0 B A E G D)) (@fapp0 _ _
    (@comp_cat_con_fapp1_func B A E D F G) alpha)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B A C D (@comp_cat_fapp0 A E
    C V F) (@comp_cat_fapp0 A E C V G)) (@fapp0 _ _ (@comp_cat_cov_fapp1_func A E C V F G) alpha)));
assertnot [A B E C : Cat] (E1 : τ (IsNCat (cat_succ cat_zero) E)) (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (D : τ (Functor B A)) (V : τ (Functor E C)) (F G : τ (Functor A E)) (alpha : τ (@Transf A E F G)) (alpha0 : τ
    (@Transf A E F G))
  ⊢ (@one_cat_whiskering_path A B E C E1 C1 D V F G alpha) : τ (@= (@Transf B C (@comp_cat_fapp0 B A C
    (@comp_cat_fapp0 A E C V F) D) (@comp_cat_fapp0 B A C (@comp_cat_fapp0 A E C V G) D)) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func B E C V (@comp_cat_fapp0 B A E F D) (@comp_cat_fapp0 B A E G D)) (@fapp0 _ _
    (@comp_cat_con_fapp1_func B A E D F G) alpha)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B A C D (@comp_cat_fapp0 A E
    C V F) (@comp_cat_fapp0 A E C V G)) (@fapp0 _ _ (@comp_cat_cov_fapp1_func A E C V F G) alpha0)));
