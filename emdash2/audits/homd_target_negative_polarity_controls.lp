/* NON-LIBRARY full-source polarity isolation, retaining old op/Sigma.
   The negative native target gives forward Hom action. These controls check
   whole/point computation and retained Hom action, not global soundness. */
require open emdash.emdash3_2;

symbol homd_target_negative_section [Z C : Cat] (F : τ (Functor Z C))
  (x : τ (Obj Z)) (u : τ (Obj C))
  : τ (Obj (@Homd_negative_pi_cat (Op_cat Z)
      (@Homd_target_section_catd Z (@Const_catd Z Terminal_cat) x)))
≔ @homd_src_sec Z (@Const_catd Z Terminal_cat) (@Const_catd Z C) F x u;

symbol negative_arrow_view [A : Cat] (a b : τ (Obj A))
  (f : τ (Hom (Op_cat A) a b)) : τ (Hom A b a)
≔ f;

symbol negative_section_action [Z C : Cat] (F : τ (Functor Z C))
  (x y : τ (Obj Z)) (u : τ (Obj C)) (p : τ (Hom Z x y))
  : τ (Hom
      (Fibre_cat (@Homd_target_section_catd Z (@Const_catd Z Terminal_cat) x) x)
      (@piapp0 (Op_cat Z)
        (@Op_catd (Op_cat Z) (@Homd_target_section_catd Z (@Const_catd Z Terminal_cat) x))
        (@homd_target_negative_section Z C F x u) x)
      (@piapp1_src_obj (Op_cat Z)
        (@Op_catd (Op_cat Z) (@Homd_target_section_catd Z (@Const_catd Z Terminal_cat) x))
        (@homd_target_negative_section Z C F x u) y x p))
≔ @negative_arrow_view
    (Fibre_cat (@Homd_target_section_catd Z (@Const_catd Z Terminal_cat) x) x)
    (@piapp1_src_obj (Op_cat Z)
      (@Op_catd (Op_cat Z) (@Homd_target_section_catd Z (@Const_catd Z Terminal_cat) x))
      (@homd_target_negative_section Z C F x u) y x p)
    (@piapp0 (Op_cat Z)
      (@Op_catd (Op_cat Z) (@Homd_target_section_catd Z (@Const_catd Z Terminal_cat) x))
      (@homd_target_negative_section Z C F x u) x)
    (@piapp1_fapp0 (Op_cat Z)
      (@Op_catd (Op_cat Z) (@Homd_target_section_catd Z (@Const_catd Z Terminal_cat) x))
      (@homd_target_negative_section Z C F x u) y x p);

symbol negative_forward_functor [Z C : Cat] (F : τ (Functor Z C))
  (x y : τ (Obj Z)) (u : τ (Obj C)) (p : τ (Hom Z x y))
  : τ (Functor (Hom_cat C u (@fapp0 Z C F x))
      (Hom_cat C u (@fapp0 Z C F y)))
≔ @fapp1_fapp0
    (Functor_cat (Op_cat (Hom_cat Z x x)) Cat_cat) Cat_cat
    (@fapp0_func (Op_cat (Hom_cat Z x x)) Cat_cat (@id Z x)) _ _
    (@fapp1_fapp0
      (Functor_cat Terminal_cat (Functor_cat (Op_cat (Hom_cat Z x x)) Cat_cat))
      (Functor_cat (Op_cat (Hom_cat Z x x)) Cat_cat)
      (@fapp0_func Terminal_cat (Functor_cat (Op_cat (Hom_cat Z x x)) Cat_cat) Terminal_obj)
      _ _ (@negative_section_action Z C F x y u p));

symbol negative_forward_application [Z C : Cat] (F : τ (Functor Z C))
  (x y : τ (Obj Z)) (u : τ (Obj C)) (p : τ (Hom Z x y))
  (h : τ (Hom C u (@fapp0 Z C F x)))
  : τ (@= (Hom C u (@fapp0 Z C F y))
      (@fapp0 (Hom_cat C u (@fapp0 Z C F x)) (Hom_cat C u (@fapp0 Z C F y))
        (@negative_forward_functor Z C F x y u p) h)
      (@comp_fapp0 C u (@fapp0 Z C F x) (@fapp0 Z C F y)
        (@fapp1_fapp0 Z C F x y p) h))
≔ @eq_refl (Hom C u (@fapp0 Z C F y))
    (@comp_fapp0 C u (@fapp0 Z C F x) (@fapp0 Z C F y)
      (@fapp1_fapp0 Z C F x y p) h);

// Whole observation of the constructor beta; the represented family remains
// the ordinary owner of the resulting Hom action.
symbol negative_forward_whole [Z C : Cat] (F : τ (Functor Z C))
  (x y : τ (Obj Z)) (u : τ (Obj C)) (p : τ (Hom Z x y))
  : τ (@= (Functor (Hom_cat C u (@fapp0 Z C F x))
      (Hom_cat C u (@fapp0 Z C F y)))
      (@negative_forward_functor Z C F x y u p)
      (@fapp1_fapp0 Z Cat_cat (@hom_ C Z F u) x y p))
≔ @eq_refl (Functor (Hom_cat C u (@fapp0 Z C F x))
      (Hom_cat C u (@fapp0 Z C F y)))
    (@fapp1_fapp0 Z Cat_cat (@hom_ C Z F u) x y p);

symbol negative_forward_hom_action [Z C : Cat] (F : τ (Functor Z C))
  (x y : τ (Obj Z)) (u : τ (Obj C)) (p : τ (Hom Z x y))
  (h k : τ (Hom C u (@fapp0 Z C F x)))
  : τ (@= (Functor
      (Hom_cat (Hom_cat C u (@fapp0 Z C F x)) h k)
      (Hom_cat (Hom_cat C u (@fapp0 Z C F y))
        (@comp_fapp0 C u (@fapp0 Z C F x) (@fapp0 Z C F y)
          (@fapp1_fapp0 Z C F x y p) h)
        (@comp_fapp0 C u (@fapp0 Z C F x) (@fapp0 Z C F y)
          (@fapp1_fapp0 Z C F x y p) k)))
      (@fapp1_func (Hom_cat C u (@fapp0 Z C F x))
        (Hom_cat C u (@fapp0 Z C F y))
        (@negative_forward_functor Z C F x y u p) h k)
      (@fapp1_func (Hom_cat C u (@fapp0 Z C F x))
        (Hom_cat C u (@fapp0 Z C F y))
        (@fapp1_fapp0 Z Cat_cat (@hom_ C Z F u) x y p) h k))
≔ @eq_refl (Functor
      (Hom_cat (Hom_cat C u (@fapp0 Z C F x)) h k)
      (Hom_cat (Hom_cat C u (@fapp0 Z C F y))
        (@comp_fapp0 C u (@fapp0 Z C F x) (@fapp0 Z C F y)
          (@fapp1_fapp0 Z C F x y p) h)
        (@comp_fapp0 C u (@fapp0 Z C F x) (@fapp0 Z C F y)
          (@fapp1_fapp0 Z C F x y p) k)))
    (@fapp1_func (Hom_cat C u (@fapp0 Z C F x))
      (Hom_cat C u (@fapp0 Z C F y))
      (@fapp1_fapp0 Z Cat_cat (@hom_ C Z F u) x y p) h k);

// Nonidentity p is retained when the represented source arrow is identity.
symbol negative_forward_retains_arrow [C : Cat]
  (x y : τ (Obj C)) (p : τ (Hom C x y))
  : τ (@= (Hom C x y)
      (@fapp0 (Hom_cat C x x) (Hom_cat C x y)
        (@negative_forward_functor C C (@id_func C) x y x p) (@id C x)) p)
≔ @eq_refl (Hom C x y) p;

assertnot [Z C : Cat] (F : τ (Functor Z C))
  (x y : τ (Obj Z)) (u : τ (Obj C)) (p : τ (Hom Z x y)) ⊢
  @negative_forward_functor Z C F x y u p
  : τ (Functor (Hom_cat C u (@fapp0 Z C F y))
      (Hom_cat C u (@fapp0 Z C F x)));

assertnot [Z C : Cat] (F : τ (Functor Z C))
  (x : τ (Obj Z)) (u : τ (Obj C)) ⊢
  @homd_src_sec Z (@Const_catd Z Terminal_cat) (@Const_catd Z C) F x u
  : τ (Obj (@Pi_cat (Op_cat Z)
      (@Homd_target_section_catd Z (@Const_catd Z Terminal_cat) x)));

symbol negative_native_component [K : Cat] [D E : τ (Catd K)]
  (F : τ (@Functord K D E)) (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x))) (y : τ (Obj K))
  : τ (Functor (Fibre_cat D y) (Functor_cat (Op_cat (Hom_cat K x y)) Cat_cat))
≔ @fapp0
    (@Homd_negative_pi_cat (Op_cat K) (@Homd_target_section_catd K D x))
    (Fibre_cat (@Homd_target_section_catd K D x) y)
    (@homd_negative_eval_func (Op_cat K) (@Homd_target_section_catd K D x) y)
    (@homd_src_sec K D E F x u);

symbol negative_native_component_path [K : Cat] [D E : τ (Catd K)]
  (F : τ (@Functord K D E)) (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x))) (y : τ (Obj K))
  : τ (@= (Functor (Fibre_cat D y) (Functor_cat (Op_cat (Hom_cat K x y)) Cat_cat))
      (@negative_native_component K D E F x u y)
      (@homd_tgt_func K D E F x u y))
≔ @eq_refl (Functor (Fibre_cat D y) (Functor_cat (Op_cat (Hom_cat K x y)) Cat_cat))
    (@homd_tgt_func K D E F x u y);

symbol negative_native_endpoint_path [K : Cat] [D E : τ (Catd K)]
  (F : τ (@Functord K D E)) (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x))) (y : τ (Obj K))
  (v : τ (Obj (Fibre_cat D y)))
  : τ (@= (Functor (Op_cat (Hom_cat K x y)) Cat_cat)
      (@fapp0 (Fibre_cat D y) (Functor_cat (Op_cat (Hom_cat K x y)) Cat_cat)
        (@negative_native_component K D E F x u y) v)
      (@homd_ K D E F x u y v))
≔ @eq_refl (Functor (Op_cat (Hom_cat K x y)) Cat_cat)
    (@homd_ K D E F x u y v);

assert [K : Cat] [D E : τ (Catd K)] (F : τ (@Functord K D E))
  (x : τ (Obj K)) (u : τ (Obj (Fibre_cat E x))) (y : τ (Obj K))
  (v w : τ (Obj (Fibre_cat D y))) ⊢
  @fapp1_func (Fibre_cat D y) (Functor_cat (Op_cat (Hom_cat K x y)) Cat_cat)
    (@negative_native_component K D E F x u y) v w
  : τ (Functor (Hom_cat (Fibre_cat D y) v w)
      (Hom_cat (Functor_cat (Op_cat (Hom_cat K x y)) Cat_cat)
        (@homd_ K D E F x u y v) (@homd_ K D E F x u y w)));
