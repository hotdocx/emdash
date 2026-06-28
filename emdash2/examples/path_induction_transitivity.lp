/*
  Reviewer milestone: path induction as transitivity/composition.

  This shows the application layer: the fixed-source path-induction theorem
  computes to the composition section, and evaluating that section at a base
  arrow gives the expected stable postcomposition normal form. The ordinary
  categorical-composition surface remains available proof-time through the
  `hom_postcomp_fapp0`/`comp_fapp0` unification bridge.
*/

require open emdash.emdash3_2;

assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @path_ind_sec
    Z
    x
    (@CompMotive_catd Z x)
    (@id_funcd Z (@Rep_catd Z x))
    ≡ @path_comp_sec Z x;

assert [Z : Cat] (x y : τ (Obj Z))
  (p : τ (Hom Z x y)) ⊢
  @fapp0
    (@Functord_cat Z (@Rep_catd Z x) (@Rep_catd Z x))
    (@Functord_cat Z (@Rep_catd Z y) (@Rep_catd Z x))
    (@CompTarget_fapp1_func Z x x y p)
    (@id_funcd Z (@Rep_catd Z x))
    ≡ @path_comp_func Z x y p;

assert [Z : Cat] (x y z : τ (Obj Z))
  (p : τ (Hom Z x y)) (q : τ (Hom Z y z)) ⊢
  @fapp0
    (Fibre_cat (@Rep_catd Z y) z)
    (Fibre_cat (@Rep_catd Z x) z)
    (@tapp0_fapp0 Z Cat_cat
      (@Rep_catd Z y)
      (@Rep_catd Z x)
      z
      (@path_comp_func Z x y p))
    q
    ≡ @hom_postcomp_fapp0 Z Z (@id_func Z) x y z q p;

symbol path_induction_transitivity_comp_view
  [Z : Cat]
  [x y z : τ (Obj Z)]
  (p : τ (Hom Z x y))
  (q : τ (Hom Z y z))
  : τ (
      @fapp0
        (Fibre_cat (@Rep_catd Z y) z)
        (Fibre_cat (@Rep_catd Z x) z)
        (@tapp0_fapp0 Z Cat_cat
          (@Rep_catd Z y)
          (@Rep_catd Z x)
          z
          (@path_comp_func Z x y p))
        q
      =
      @comp_fapp0 Z x y z q p)
≔ eq_refl (@hom_postcomp_fapp0 Z Z (@id_func Z) x y z q p);
