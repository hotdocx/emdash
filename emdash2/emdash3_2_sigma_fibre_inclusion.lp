/* A fixed fibre enters the existing Sigma via constant base change.
   The generic constant-pullback and totalization owners supply computation. */
require open emdash.emdash3_2;

symbol sigma_fibre_inclusion_func [K : Cat] (E : τ (Catd K)) (k : τ (Obj K))
  : τ (Functor (Fibre_cat E k) (@Sigma_cat K E))
≔ @comp_cat_fapp0 (Fibre_cat E k)
    (@Sigma_cat Terminal_cat (@Pullback_catd Terminal_cat K E (@Const_func Terminal_cat K k)))
    (@Sigma_cat K E)
    (@sigma_pullback_total_func Terminal_cat K (@Const_func Terminal_cat K k) E)
    (@Product_pair_grpd (Functor (Fibre_cat E k) Terminal_cat) (Functor (Fibre_cat E k) (Fibre_cat E k))
      (@Const_func (Fibre_cat E k) Terminal_cat Terminal_obj) (@id_func (Fibre_cat E k)));
