flag "eta_equality" on;
flag "print_implicits" on;
flag "print_contexts" on;
flag "print_domains" on;
flag "print_meta_args" on;
require open emdash.emdash3_2;

assert [K : Cat] (E D : τ (Catd K))
  (FF GG : τ (Functord E D))
  (epsilon epsilon' : τ (@Transfd K E D FF GG))
  (m : τ (Hom (@Transfd_cat K E D FF GG) epsilon epsilon')) ⊢
  fapp0
    (@tdapp1_int_fapp1_func_transfd
      K E D FF GG epsilon epsilon')
    m
  :
  τ (Hom
    (@Transfd_cat
      K
      (@Op_catd K E)
      (@Homd_target_catd K E)
      (@homd_int K E E (@id_funcd K E))
      (@comp_catd_fapp0
        K
        (@Op_catd K E)
        (@Op_catd K D)
        (@Homd_target_catd K E)
        (@homd_int K E D GG)
        (@Op_funcd K E D FF)))
    (@tdapp1_int_fapp0_transfd K E D FF GG epsilon)
    (@tdapp1_int_fapp0_transfd K E D FF GG epsilon'));

assert [K : Cat] (E D : τ (Catd K))
  (FF GG : τ (Functord E D))
  (epsilon epsilon' : τ (@Transfd K E D FF GG))
  (m : τ (Hom (@Transfd_cat K E D FF GG) epsilon epsilon')) ⊢
  fapp0
    (@fapp1_func
      _
      _
      (@tdapp1_int_func_transfd K E D FF GG)
      epsilon
      epsilon')
    m
  ≡
  fapp0
    (@tdapp1_int_fapp1_func_transfd
      K E D FF GG epsilon epsilon')
    m;
