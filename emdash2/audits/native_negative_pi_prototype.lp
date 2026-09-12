/* NON-LIBRARY prototype over the preferred total-Op/CoAbove2 prefix.
   The active nucleus does not yet have that basis. This derived operator is
   a target-design ingredient, not a full repaired kernel or Homd target.
   Reproduce with scripts/check_native_negative_pi.sh. There is deliberately
   no unrestricted covariant NPi functor on the old lax Catd(K) carrier. */
require open emdash.emdash3_2;

symbol native_negative_pi_cat [K : Cat] (E : τ (Catd K)) : Cat
≔ Op_cat (@Pi_cat (CoAbove2_cat K) (@Op_catd K E));

/* A map is an actual displayed map between the dual families. Arbitrary
   lax maps E→D cannot be reused by reversing their comparison cells. */
symbol native_negative_pi_map_func [K : Cat] (E D : τ (Catd K))
  : τ (Functor
      (Op_cat (@Functord_cat (CoAbove2_cat K) (@Op_catd K E) (@Op_catd K D)))
      (Functor_cat (@native_negative_pi_cat K E) (@native_negative_pi_cat K D)))
≔ @comp_cat_fapp0
    (Op_cat (@Functord_cat (CoAbove2_cat K) (@Op_catd K E) (@Op_catd K D)))
    (Op_cat (Functor_cat
      (@Pi_cat (CoAbove2_cat K) (@Op_catd K E))
      (@Pi_cat (CoAbove2_cat K) (@Op_catd K D))))
    (Functor_cat (@native_negative_pi_cat K E) (@native_negative_pi_cat K D))
    (@fapp1_func (CoAbove2_cat Cat_cat) Cat_cat op
      (@Pi_cat (CoAbove2_cat K) (@Op_catd K E))
      (@Pi_cat (CoAbove2_cat K) (@Op_catd K D)))
    (@Op_func
      (@Functord_cat (CoAbove2_cat K) (@Op_catd K E) (@Op_catd K D))
      (Functor_cat (@Pi_cat (CoAbove2_cat K) (@Op_catd K E))
        (@Pi_cat (CoAbove2_cat K) (@Op_catd K D)))
      (@fapp1_func (Catd_cat (CoAbove2_cat K)) Cat_cat
        (@Pi_func (CoAbove2_cat K)) (@Op_catd K E) (@Op_catd K D)));

symbol native_negative_pi_map_path [K : Cat] (E D : τ (Catd K))
  (G : τ (@Functord (CoAbove2_cat K) (@Op_catd K E) (@Op_catd K D)))
  (s : τ (Obj (@native_negative_pi_cat K E)))
  : τ (@= (Obj (@native_negative_pi_cat K D))
      (@fapp0 (@native_negative_pi_cat K E) (@native_negative_pi_cat K D)
        (@fapp0 _ _ (@native_negative_pi_map_func K E D) G) s)
      (@section_postcomp_sec (CoAbove2_cat K) (@Op_catd K E) (@Op_catd K D) G s))
≔ @eq_refl (Obj (@native_negative_pi_cat K D))
    (@section_postcomp_sec (CoAbove2_cat K) (@Op_catd K E) (@Op_catd K D) G s);

symbol native_negative_pi_constant_to (K C : Cat)
  : τ (Functor (@native_negative_pi_cat K (@Const_catd K C))
      (Functor_cat (Transpose_cat K) C))
≔ @fapp1_func (CoAbove2_cat Cat_cat) Cat_cat op
    (CoAbove2_cat K) (Op_cat C);

symbol native_negative_pi_constant_intro [Z C : Cat]
  (F : τ (Functor Z C))
  : τ (Obj (@native_negative_pi_cat (Transpose_cat Z)
      (@Const_catd (Transpose_cat Z) C)))
≔ @Op_func Z C F;

symbol native_negative_pi_constant_read [Z C : Cat]
  (F : τ (Functor Z C)) : τ (Functor Z C)
≔ @fapp0 _ _ (@native_negative_pi_constant_to (Transpose_cat Z) C)
    (@native_negative_pi_constant_intro Z C F);

assertnot [K : Cat] (E D : τ (Catd K)) (F : τ (@Functord K E D)) ⊢
  @fapp0 _ _ (@native_negative_pi_map_func K E D) F
  : τ (Functor (@native_negative_pi_cat K E) (@native_negative_pi_cat K D));

assert [Z C : Cat] (F : τ (Functor Z C)) ⊢
  @native_negative_pi_constant_read Z C F ≡ F;

symbol native_negative_pi_arrow_path [Z C : Cat]
  (F : τ (Functor Z C)) (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  : τ (@= (Hom C (@fapp0 Z C F x) (@fapp0 Z C F y))
      (@fapp1_fapp0 Z C (@native_negative_pi_constant_read Z C F) x y p)
      (@fapp1_fapp0 Z C F x y p))
≔ @eq_refl (Hom C (@fapp0 Z C F x) (@fapp0 Z C F y))
    (@fapp1_fapp0 Z C F x y p);

assert [Z C : Cat] (F : τ (Functor Z C))
  (x y : τ (Obj Z)) (p q : τ (Hom Z x y)) ⊢
  @fapp1_func _ _ (@fapp1_func Z C (@native_negative_pi_constant_read Z C F) x y) p q
  : τ (Functor (Hom_cat (Hom_cat Z x y) p q)
      (Hom_cat (Hom_cat C (@fapp0 Z C F x) (@fapp0 Z C F y))
        (@fapp1_fapp0 Z C F x y p) (@fapp1_fapp0 Z C F x y q)));

assertnot [Z C : Cat] (F : τ (Functor Z C)) ⊢
  @native_negative_pi_constant_read Z C F : τ (Functor (Transpose_cat Z) C);
