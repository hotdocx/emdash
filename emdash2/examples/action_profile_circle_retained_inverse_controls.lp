/* Preserve both original inverse choices through the named strict Path action. */
require open emdash.emdash3_2_circle_hit;

assert ⊢
  @omega_equiv_along_left_inv Cat_cat
    (Hom_cat Circle_cat circle_base circle_base) (Path_cat Integer_grpd)
    circle_hom_integer_func circle_hom_integer_cat_evidence
  ≡ @path_map_func Integer_grpd (@= Circle_grpd circle_base circle_base)
      (@omega_equiv_along_left_inv Grpd_cat (@= Circle_grpd circle_base circle_base) Integer_grpd
        circle_loop_encode_function (@omega_equiv_evidence Grpd_cat (@= Circle_grpd circle_base circle_base) Integer_grpd circle_loop_integer_omega_equiv));

assert ⊢
  @omega_equiv_along_right_inv Cat_cat
    (Hom_cat Circle_cat circle_base circle_base) (Path_cat Integer_grpd)
    circle_hom_integer_func circle_hom_integer_cat_evidence
  ≡ @path_map_func Integer_grpd (@= Circle_grpd circle_base circle_base)
      (@omega_equiv_along_right_inv Grpd_cat (@= Circle_grpd circle_base circle_base) Integer_grpd
        circle_loop_encode_function (@omega_equiv_evidence Grpd_cat (@= Circle_grpd circle_base circle_base) Integer_grpd circle_loop_integer_omega_equiv));

type λ p : τ (@= Circle_grpd circle_base circle_base), λ q : τ (@= Circle_grpd circle_base circle_base),
  @fapp1_func (Hom_cat Circle_cat circle_base circle_base)
    (Path_cat Integer_grpd) circle_hom_integer_func p q;
