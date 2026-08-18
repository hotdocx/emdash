/*
  Universe-valued monodromy from WalkingEnd--Circle universality.

  A self-equivalence e : A ~= A gives, by univalence, a loop of groupoids.
  The canonical WalkingEnd representation carries A at its base and that loop
  at its generator.  The whole groupoidification inverse extends it to a
  Circle-indexed family, while the whole beta path recovers the original
  WalkingEnd representation after restriction.  Transport around the Circle
  loop computes propositionally to e.to.

  This module is a rule-free consumer of the universality theorem.  It adds no
  independent Circle code family, univalence principle, or groupoidification
  axiom.
*/

require open emdash.emdash3_2_walking_circle_universality;

// Univalence turns the selected automorphism into a universe path.
symbol walking_circle_monodromy_generator
  [A : Grpd]
  (e : τ (TypeEquiv A A))
  : τ (@= Grpd_grpd A A)
≔ @grpd_equiv_path A A e;

// Canonical WalkingEnd representation of A and its selected automorphism.
symbol walking_circle_monodromy_walking_func
  [A : Grpd]
  (e : τ (TypeEquiv A A))
  : τ (Functor WalkingEnd_cat (Path_cat Grpd_grpd))
≔ @walking_end_rec_func
    (Path_cat Grpd_grpd)
    A
    (@walking_circle_monodromy_generator A e);

/*
  Circle-indexed groupoid family selected by the whole inverse.  Its body
  computes to circle_rec(Grpd_grpd,A,grpd_equiv_path(e)).
*/
symbol walking_circle_monodromy_circle_family
  [A : Grpd]
  (e : τ (TypeEquiv A A))
  : τ (@Function_grpd Circle_grpd Grpd_grpd)
≔ @walking_circle_extend_at
    Grpd_grpd
    (@walking_circle_monodromy_walking_func A e);

// The family value at the Circle base is A.
symbol walking_circle_monodromy_base_path
  [A : Grpd]
  (e : τ (TypeEquiv A A))
  : τ (@= Grpd_grpd
      (@walking_circle_monodromy_circle_family A e circle_base)
      A)
≔ @eq_trans
    Grpd_grpd
    (@walking_circle_monodromy_circle_family A e circle_base)
    (@fapp0
      WalkingEnd_cat (Path_cat Grpd_grpd)
      (@walking_circle_monodromy_walking_func A e)
      walking_base)
    A
    (@walking_circle_extend_beta_base
      Grpd_grpd (@walking_circle_monodromy_walking_func A e))
    (@walking_end_rec_beta_base
      (Path_cat Grpd_grpd)
      A
      (@walking_circle_monodromy_generator A e));

// The family monodromy is the univalence path of e.
symbol walking_circle_monodromy_loop_path
  [A : Grpd]
  (e : τ (TypeEquiv A A))
  : τ (@=
      (@= Grpd_grpd A A)
      (@eq_ap
        Circle_grpd Grpd_grpd
        (@walking_circle_monodromy_circle_family A e)
        circle_base circle_base circle_loop)
      (@grpd_equiv_path A A e))
≔ @eq_trans
    (@= Grpd_grpd A A)
    (@eq_ap
      Circle_grpd Grpd_grpd
      (@walking_circle_monodromy_circle_family A e)
      circle_base circle_base circle_loop)
    (@fapp1_fapp0
      WalkingEnd_cat (Path_cat Grpd_grpd)
      (@walking_circle_monodromy_walking_func A e)
      walking_base walking_base walking_loop)
    (@grpd_equiv_path A A e)
    (@walking_circle_extend_beta_loop
      Grpd_grpd (@walking_circle_monodromy_walking_func A e))
    (@walking_end_rec_beta_loop_ordinary
      (Path_cat Grpd_grpd)
      A
      (@walking_circle_monodromy_generator A e));

// Whole universality recovers the original representation after restriction.
symbol walking_circle_monodromy_restriction_path
  [A : Grpd]
  (e : τ (TypeEquiv A A))
  : τ (@=
      (Functor WalkingEnd_cat (Path_cat Grpd_grpd))
      (@walking_circle_restrict_at
        Grpd_grpd (@walking_circle_monodromy_circle_family A e))
      (@walking_circle_monodromy_walking_func A e))
≔ @walking_circle_restrict_extend_beta_at_path
    Grpd_grpd
    (@walking_circle_monodromy_walking_func A e);

// Transport around the actual family loop applies the selected automorphism.
symbol walking_circle_monodromy_transport_path
  [A : Grpd]
  (e : τ (TypeEquiv A A))
  (a : τ A)
  : τ (@= A
      (@coe_grpd
        A A
        (@eq_ap
          Circle_grpd Grpd_grpd
          (@walking_circle_monodromy_circle_family A e)
          circle_base circle_base circle_loop)
        a)
      (@type_equiv_to A A e a))
≔ @eq_trans
    A
    (@coe_grpd
      A A
      (@eq_ap
        Circle_grpd Grpd_grpd
        (@walking_circle_monodromy_circle_family A e)
        circle_base circle_base circle_loop)
      a)
    (@coe_grpd A A (@grpd_equiv_path A A e) a)
    (@type_equiv_to A A e a)
    (@eq_ap
      (@= Grpd_grpd A A)
      A
      (λ p : τ (@= Grpd_grpd A A), @coe_grpd A A p a)
      (@eq_ap
        Circle_grpd Grpd_grpd
        (@walking_circle_monodromy_circle_family A e)
        circle_base circle_base circle_loop)
      (@grpd_equiv_path A A e)
      (@walking_circle_monodromy_loop_path A e))
    (@grpd_equiv_path_coe A A e a);
