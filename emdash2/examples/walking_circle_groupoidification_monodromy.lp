/* Focused reviewer for the universe-valued monodromy consumer. */

require open emdash.emdash3_2_walking_circle_monodromy;

assert [A : Grpd]
  (e : τ (TypeEquiv A A)) ⊢
  @walking_circle_monodromy_generator A e
  ≡ @grpd_equiv_path A A e;

assert [A : Grpd]
  (e : τ (TypeEquiv A A)) ⊢
  @walking_circle_monodromy_circle_family A e
  ≡ @circle_rec
      Grpd_grpd
      A
      (@grpd_equiv_path A A e);

assert [A : Grpd]
  (e : τ (TypeEquiv A A)) ⊢
  @walking_circle_monodromy_base_path A e
  : τ (@= Grpd_grpd
      (@walking_circle_monodromy_circle_family A e circle_base)
      A);

assert [A : Grpd]
  (e : τ (TypeEquiv A A)) ⊢
  @walking_circle_monodromy_loop_path A e
  : τ (@=
      (@= Grpd_grpd A A)
      (@eq_ap
        Circle_grpd Grpd_grpd
        (@walking_circle_monodromy_circle_family A e)
        circle_base circle_base circle_loop)
      (@grpd_equiv_path A A e));

assert [A : Grpd]
  (e : τ (TypeEquiv A A)) ⊢
  @walking_circle_monodromy_restriction_path A e
  : τ (@=
      (Functor WalkingEnd_cat (Path_cat Grpd_grpd))
      (@walking_circle_restrict_at
        Grpd_grpd (@walking_circle_monodromy_circle_family A e))
      (@walking_circle_monodromy_walking_func A e));

assert [A : Grpd]
  (e : τ (TypeEquiv A A))
  (a : τ A) ⊢
  @walking_circle_monodromy_transport_path A e a
  : τ (@= A
      (@coe_grpd
        A A
        (@eq_ap
          Circle_grpd Grpd_grpd
          (@walking_circle_monodromy_circle_family A e)
          circle_base circle_base circle_loop)
        a)
      (@type_equiv_to A A e a));

assertnot [A : Grpd]
  (e : τ (TypeEquiv A A)) ⊢
  walking_circle_monodromy_circle_family A e
  : τ (@Function_grpd Circle_grpd A);
