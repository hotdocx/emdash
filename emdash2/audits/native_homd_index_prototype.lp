/* NON-LIBRARY native shared-index ingredient on the preferred Op prefix.
   The prefix ends before homd_int. Strict reference interpretation only;
   arbitrary lax-family duality and the full omega target remain unqualified.
   No new primitive, rewrite or unification rule is introduced. */
require open emdash.emdash3_2;

// H_x(d)=Hom_Z(x,pi(d)); the original D remains over Z.
symbol native_index_hom_catd [Z : Cat] (D : τ (Catd Z)) (x : τ (Obj Z))
  : τ (Catd (@Sigma_cat Z D))
≔ @hom_ Z (@Sigma_cat Z D) (@Sigma_proj1_func Z D) x;

symbol native_index_inner_cat [Z : Cat] (D : τ (Catd Z)) (x : τ (Obj Z)) : Cat
≔ @Sigma_cat (CoAbove2_cat (@Sigma_cat Z D))
    (@Op_catd (@Sigma_cat Z D) (@native_index_hom_catd Z D x));

// Supporting target index, derived from existing carrier owners.
symbol native_index_cat [Z : Cat] (D : τ (Catd Z)) (x : τ (Obj Z)) : Cat
≔ CoAbove2_cat (@native_index_inner_cat Z D x);

symbol native_index_point [Z : Cat] (D : τ (Catd Z)) (x : τ (Obj Z))
  (d : τ (Obj (@Sigma_cat Z D)))
  (a : τ (Hom Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d)))
  : τ (Obj (@native_index_cat Z D x))
≔ Struct_sigma d a;

// Whole projection uses only the two first projections and strict duality.
symbol native_index_projection_func [Z : Cat] (D : τ (Catd Z)) (x : τ (Obj Z))
  : τ (Functor (@native_index_cat Z D x) Z)
≔ @comp_cat_fapp0 (@native_index_cat Z D x) (@Sigma_cat Z D) Z
    (@Sigma_proj1_func Z D)
    (@CoAbove2_func (@native_index_inner_cat Z D x) (CoAbove2_cat (@Sigma_cat Z D))
      (@Sigma_proj1_func (CoAbove2_cat (@Sigma_cat Z D))
        (@Op_catd (@Sigma_cat Z D) (@native_index_hom_catd Z D x))));

symbol native_index_point_projection [Z : Cat] (D : τ (Catd Z))
  (x y : τ (Obj Z)) (v : τ (Obj (Fibre_cat D y))) (a : τ (Hom Z x y))
  : τ (@= (Obj Z)
      (@fapp0 (@native_index_cat Z D x) Z (@native_index_projection_func Z D x)
        (@native_index_point Z D x (Struct_sigma y v) a)) y)
≔ @eq_refl (Obj Z) y;

// Typed opposite-arrow view prevents premature decomposition of a compound
// opposite Hom. This is definitional object decoding, not an endpoint cast.
symbol native_index_op_arrow [A : Cat] (u v : τ (Obj A))
  (h : τ (Hom A v u)) : τ (Hom (Op_cat A) u v)
≔ h;

// Inverse typed view for observing the same retained triangle.
symbol native_index_unop_arrow [A : Cat] (u v : τ (Obj A))
  (h : τ (Hom (Op_cat A) u v)) : τ (Hom A v u)
≔ h;

// A target index arrow retains a total arrow m and the correctly oriented
// triangle b⇒pi(m)∘a. Its carrier uses no homd_int/displayed-action owner.
symbol native_index_arrow [Z : Cat] (D : τ (Catd Z)) (x : τ (Obj Z))
  (d e : τ (Obj (@Sigma_cat Z D)))
  (a : τ (Hom Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d)))
  (b : τ (Hom Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e)))
  (m : τ (Hom (@Sigma_cat Z D) d e))
  (theta : τ (Hom (Hom_cat Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e)) b
    (@comp_fapp0 Z x
      (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d)
      (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e)
      (@fapp1_fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d e m) a)))
  : τ (Hom (@native_index_cat Z D x)
      (@native_index_point Z D x d a) (@native_index_point Z D x e b))
≔ @sigma_arrow_intro (CoAbove2_cat (@Sigma_cat Z D))
    (@Op_catd (@Sigma_cat Z D) (@native_index_hom_catd Z D x))
    (@native_index_point Z D x d a) (@native_index_point Z D x e b)
    m (@native_index_op_arrow
        (Hom_cat Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e))
        (@hom_postcomp_fapp0 Z (@Sigma_cat Z D) (@Sigma_proj1_func Z D) x d e m a)
        b theta);

symbol native_index_arrow_projection [Z : Cat] (D : τ (Catd Z)) (x : τ (Obj Z))
  (d e : τ (Obj (@Sigma_cat Z D)))
  (a : τ (Hom Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d)))
  (b : τ (Hom Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e)))
  (m : τ (Hom (@Sigma_cat Z D) d e))
  (theta : τ (Hom (Hom_cat Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e)) b
    (@comp_fapp0 Z x
      (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d)
      (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e)
      (@fapp1_fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d e m) a)))
  : τ (@= (Hom Z
      (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d)
      (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e))
      (@fapp1_fapp0 (@native_index_cat Z D x) Z (@native_index_projection_func Z D x)
        (@native_index_point Z D x d a) (@native_index_point Z D x e b)
        (@native_index_arrow Z D x d e a b m theta))
      (@fapp1_fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d e m))
≔ @eq_refl (Hom Z
      (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d)
      (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e))
    (@fapp1_fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d e m);

// The first projection remains iterable over Hom of the new index.
assert [Z : Cat] (D : τ (Catd Z)) (x : τ (Obj Z))
  (a b : τ (Obj (@native_index_cat Z D x)))
  (f g : τ (Hom (@native_index_cat Z D x) a b)) ⊢
  @fapp1_func _ _
    (@fapp1_func (@native_index_cat Z D x) Z (@native_index_projection_func Z D x) a b) f g
  : τ (Functor (Hom_cat (Hom_cat (@native_index_cat Z D x) a b) f g)
      (Hom_cat
        (Hom_cat Z
          (@fapp0 (@native_index_cat Z D x) Z (@native_index_projection_func Z D x) a)
          (@fapp0 (@native_index_cat Z D x) Z (@native_index_projection_func Z D x) b))
        (@fapp1_fapp0 (@native_index_cat Z D x) Z (@native_index_projection_func Z D x) a b f)
        (@fapp1_fapp0 (@native_index_cat Z D x) Z (@native_index_projection_func Z D x) a b g)));

// Original endpoint Hom requires dimension-1 transposition in u.
symbol native_source_hom [C : Cat] (z : τ (Obj C))
  : τ (Functor (Transpose_cat C) Cat_cat)
≔ @hom_con C z C (@id_func C);

symbol native_source_restrict [C : Cat] (z x y : τ (Obj C)) (p : τ (Hom C x y))
  : τ (Functor (Hom_cat C y z) (Hom_cat C x z))
≔ @fapp1_fapp0 (Transpose_cat C) Cat_cat (@native_source_hom C z) y x p;

symbol native_source_comparison [C : Cat] (z x y : τ (Obj C))
  (p q : τ (Hom C x y)) (alpha : τ (Hom (Hom_cat C x y) p q))
  : τ (Transf (@native_source_restrict C z x y p) (@native_source_restrict C z x y q))
≔ @fapp1_fapp0 (Hom_cat C x y) (Functor_cat (Hom_cat C y z) (Hom_cat C x z))
    (@fapp1_func (Transpose_cat C) Cat_cat (@native_source_hom C z) y x) p q alpha;

symbol native_source_comparison_at_identity [C : Cat] (x y : τ (Obj C))
  (p q : τ (Hom C x y)) (alpha : τ (Hom (Hom_cat C x y) p q))
  : τ (Hom (Hom_cat C x y) p q)
≔ @tapp0_fapp0 (Hom_cat C y y) (Hom_cat C x y)
    (@native_source_restrict C y x y p) (@native_source_restrict C y x y q)
    (@id C y) (@native_source_comparison C y x y p q alpha);

assertnot [C : Cat] (z : τ (Obj C)) ⊢
  @native_source_hom C z : τ (Functor (Op_cat C) Cat_cat);

assertnot [C : Cat] (x y : τ (Obj C))
  (p q : τ (Hom C x y)) (alpha : τ (Hom (Hom_cat C x y) p q)) ⊢
  @native_source_comparison_at_identity C x y p q alpha
  : τ (Hom (Hom_cat C x y) q p);

assertnot [Z : Cat] (D : τ (Catd Z)) (x : τ (Obj Z))
  (d e : τ (Obj (@Sigma_cat Z D)))
  (a : τ (Hom Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d)))
  (b : τ (Hom Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e)))
  (m : τ (Hom (@Sigma_cat Z D) d e))
  (theta_reversed : τ (Hom (Hom_cat Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e))
    (@comp_fapp0 Z x
      (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d)
      (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e)
      (@fapp1_fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d e m) a) b)) ⊢
  @native_index_arrow Z D x d e a b m theta_reversed
  : τ (Hom (@native_index_cat Z D x)
      (@native_index_point Z D x d a) (@native_index_point Z D x e b));

// Constructor beta also retains the original triangle, not just its base.
symbol native_index_arrow_triangle [Z : Cat] (D : τ (Catd Z)) (x : τ (Obj Z))
  (d e : τ (Obj (@Sigma_cat Z D)))
  (a : τ (Hom Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d)))
  (b : τ (Hom Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e)))
  (m : τ (Hom (@Sigma_cat Z D) d e))
  (theta : τ (Hom (Hom_cat Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e)) b
    (@comp_fapp0 Z x
      (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d)
      (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e)
      (@fapp1_fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d e m) a)))
  : τ (@= (Hom (Hom_cat Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e)) b
    (@comp_fapp0 Z x
      (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d)
      (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e)
      (@fapp1_fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d e m) a))
      (@native_index_unop_arrow
        (Hom_cat Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e))
        (@hom_postcomp_fapp0 Z (@Sigma_cat Z D) (@Sigma_proj1_func Z D) x d e m a) b
        (@sigma_arrow_fibre (CoAbove2_cat (@Sigma_cat Z D))
        (@Op_catd (@Sigma_cat Z D) (@native_index_hom_catd Z D x))
        (@native_index_point Z D x d a) (@native_index_point Z D x e b)
        (@native_index_arrow Z D x d e a b m theta))) theta)
≔ @eq_refl (Hom (Hom_cat Z x (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e)) b
    (@comp_fapp0 Z x
      (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d)
      (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) e)
      (@fapp1_fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d e m) a)) theta;
