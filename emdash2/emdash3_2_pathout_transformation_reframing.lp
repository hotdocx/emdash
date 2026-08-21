/*
  Generic source reframe for totalizing the pre/right laxity cell.

  The formal internal-action source and the constructor-visible Sigma source
  retain different stable owners.  This module connects them through existing
  first-class paths: stable postcomposition, raw composition, general
  precomposition, the Cat-valued telescope, and whole Functord transport.  It
  neither identifies the genuinely lax endpoints nor adds a runtime rule or
  proof-time unifier.
*/

require open emdash.emdash3_2_shaped_pathout;
require open emdash.emdash3_2_path_pseudo_laxity;

symbol pathout_sigma_source
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj A))
  (p : τ (Hom A x y))
  : τ (Obj (Hom_cat B
      (@fapp0 A B F x)
      (@fapp0 A B G y)))
≔ @hom_postcomp_fapp0
    B B (@id_func B)
    (@fapp0 A B F x)
    (@fapp0 A B F y)
    (@fapp0 A B G y)
    (@tapp0_fapp0 A B F G y epsilon)
    (@fapp1_fapp0 A B F x y p);

symbol pathout_general_pre_source
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj A))
  (p : τ (Hom A x y))
  : τ (Obj (Hom_cat B
      (@fapp0 A B F x)
      (@fapp0 A B G y)))
≔ @hom_precomp_along_fapp0
    A B F (@fapp0 A B G y)
    x y p
    (@tapp0_fapp0 A B F G y epsilon);

symbol pathout_raw_source
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj A))
  (p : τ (Hom A x y))
  : τ (Obj (Hom_cat B
      (@fapp0 A B F x)
      (@fapp0 A B G y)))
≔ @comp_fapp0
    B
    (@fapp0 A B F x)
    (@fapp0 A B F y)
    (@fapp0 A B G y)
    (@tapp0_fapp0 A B F G y epsilon)
    (@fapp1_fapp0 A B F x y p);

symbol pathout_sigma_raw_path
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj A))
  (p : τ (Hom A x y))
  : τ (@=
      (Obj (Hom_cat B
        (@fapp0 A B F x)
        (@fapp0 A B G y)))
      (@pathout_sigma_source A B F G epsilon x y p)
      (@pathout_raw_source A B F G epsilon x y p))
≔ @path_pseudo_laxity_postcomp_comp_path
    B B (@id_func B)
    (@fapp0 A B F x)
    (@fapp0 A B F y)
    (@fapp0 A B G y)
    (@tapp0_fapp0 A B F G y epsilon)
    (@fapp1_fapp0 A B F x y p);

symbol pathout_general_pre_raw_path
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj A))
  (p : τ (Hom A x y))
  : τ (@=
      (Obj (Hom_cat B
        (@fapp0 A B F x)
        (@fapp0 A B G y)))
      (@pathout_general_pre_source A B F G epsilon x y p)
      (@pathout_raw_source A B F G epsilon x y p))
≔ eq_refl (@pathout_general_pre_source A B F G epsilon x y p);

// Existing proof-time post/pre comparison, packaged as equality evidence.
symbol pathout_sigma_general_pre_path
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj A))
  (p : τ (Hom A x y))
  : τ (@=
      (Obj (Hom_cat B
        (@fapp0 A B F x)
        (@fapp0 A B G y)))
      (@pathout_sigma_source A B F G epsilon x y p)
      (@pathout_general_pre_source A B F G epsilon x y p))
≔ @eq_trans
    (Obj (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y)))
    (@pathout_sigma_source A B F G epsilon x y p)
    (@pathout_raw_source A B F G epsilon x y p)
    (@pathout_general_pre_source A B F G epsilon x y p)
    (@pathout_sigma_raw_path A B F G epsilon x y p)
    (@eq_sym
      (Obj (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y)))
      (@pathout_general_pre_source A B F G epsilon x y p)
      (@pathout_raw_source A B F G epsilon x y p)
      (@pathout_general_pre_raw_path A B F G epsilon x y p));

symbol pathout_lhs_tele
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj A))
  : τ (Functor
      (Hom_cat (Op_cat A) y x)
      (Functor_cat
        (@Fibre_cat
          (Op_cat A)
          (@hom_con A y A (@id_func A))
          y)
        (@Fibre_cat
          (Op_cat A)
          (@hom_con B (@fapp0 A B G y) A F)
          x)))
≔ @functord_transport_lhs_tele_func
    (Op_cat A)
    (@hom_con A y A (@id_func A))
    (@hom_con B (@fapp0 A B G y) A F)
    (@tapp1_con_at_transf A B F G epsilon y)
    y x;

symbol pathout_lhs_tele_at_p
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj A))
  (p : τ (Hom A x y))
  : τ (Functor
      (Hom_cat A y y)
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y)))
≔ @fapp0
    (Hom_cat A x y)
    (Functor_cat
      (Hom_cat A y y)
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y)))
    (@pathout_lhs_tele A B F G epsilon x y)
    p;

symbol pathout_lhs_tele_source
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj A))
  (p : τ (Hom A x y))
  : τ (Obj (Hom_cat B
      (@fapp0 A B F x)
      (@fapp0 A B G y)))
≔ @fapp0
    (Hom_cat A y y)
    (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
    (@pathout_lhs_tele_at_p A B F G epsilon x y p)
    (@id A y);

// The cold whole Cat-precomposition comparison identifies the stable
// precomposition component with the same telescope source.
symbol pathout_general_pre_lhs_tele_path
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj A))
  (p : τ (Hom A x y))
  : τ (@=
      (Obj (Hom_cat B
        (@fapp0 A B F x)
        (@fapp0 A B G y)))
      (@pathout_general_pre_source A B F G epsilon x y p)
      (@pathout_lhs_tele_source A B F G epsilon x y p))
≔ @eq_sym
    (Obj (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y)))
    (@pathout_lhs_tele_source A B F G epsilon x y p)
    (@pathout_general_pre_source A B F G epsilon x y p)
    (@cat_precomp_composite_component_path
      (Hom_cat A y y)
      (Hom_cat B (@fapp0 A B F y) (@fapp0 A B G y))
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
      (@tapp1_func A B F G y y epsilon)
      (@hom_precomp_along_func
        A B F (@fapp0 A B G y) x y p)
      (@id A y));

symbol pathout_transport_at_p
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj A))
  (p : τ (Hom A x y))
  : τ (Functor
      (Hom_cat A y y)
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y)))
≔ @functord_transport_func
    (Op_cat A)
    (@hom_con A y A (@id_func A))
    (@hom_con B (@fapp0 A B G y) A F)
    (@tapp1_con_at_transf A B F G epsilon y)
    y x p;

symbol pathout_top_lhs_func
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj A))
  (p : τ (Hom A x y))
  : τ (Functor
      (Hom_cat A y y)
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y)))
≔ @functord_transport_lhs_func
    (Op_cat A)
    (@hom_con A y A (@id_func A))
    (@hom_con B (@fapp0 A B G y) A F)
    (@tapp1_con_at_transf A B F G epsilon y)
    y x p;

symbol pathout_lhs_tele_transport_path
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj A))
  (p : τ (Hom A x y))
  : τ (@=
      (Obj (Functor_cat
        (Hom_cat A y y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))))
      (@pathout_lhs_tele_at_p A B F G epsilon x y p)
      (@pathout_transport_at_p A B F G epsilon x y p))
≔ @eq_ap
    (Hom Cat_cat
      (Hom_cat A x y)
      (Functor_cat
        (Hom_cat A y y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))))
    (Obj (Functor_cat
      (Hom_cat A y y)
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))))
    (λ H : τ (Functor
        (Hom_cat A x y)
        (Functor_cat
          (Hom_cat A y y)
          (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y)))),
      @fapp0
        (Hom_cat A x y)
        (Functor_cat
          (Hom_cat A y y)
          (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y)))
        H p)
    (@pathout_lhs_tele A B F G epsilon x y)
    (@tapp1_func
      (Op_cat A) Cat_cat
      (@hom_con A y A (@id_func A))
      (@hom_con B (@fapp0 A B G y) A F)
      y x (@tapp1_con_at_transf A B F G epsilon y))
    (@functord_transport_lhs_tele_agrees
      (Op_cat A)
      (@hom_con A y A (@id_func A))
      (@hom_con B (@fapp0 A B G y) A F)
      (@tapp1_con_at_transf A B F G epsilon y)
      y x);

symbol pathout_top_lhs_transport_path
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj A))
  (p : τ (Hom A x y))
  : τ (@=
      (Obj (Functor_cat
        (Hom_cat A y y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))))
      (@pathout_top_lhs_func A B F G epsilon x y p)
      (@pathout_transport_at_p A B F G epsilon x y p))
≔ @functord_transport_lhs_agrees
    (Op_cat A)
    (@hom_con A y A (@id_func A))
    (@hom_con B (@fapp0 A B G y) A F)
    (@tapp1_con_at_transf A B F G epsilon y)
    y x p;

symbol pathout_lhs_tele_top_path
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj A))
  (p : τ (Hom A x y))
  : τ (@=
      (Obj (Functor_cat
        (Hom_cat A y y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))))
      (@pathout_lhs_tele_at_p A B F G epsilon x y p)
      (@pathout_top_lhs_func A B F G epsilon x y p))
≔ @eq_trans
    (Obj (Functor_cat
      (Hom_cat A y y)
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))))
    (@pathout_lhs_tele_at_p A B F G epsilon x y p)
    (@pathout_transport_at_p A B F G epsilon x y p)
    (@pathout_top_lhs_func A B F G epsilon x y p)
    (@pathout_lhs_tele_transport_path A B F G epsilon x y p)
    (@eq_sym
      (Obj (Functor_cat
        (Hom_cat A y y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))))
      (@pathout_top_lhs_func A B F G epsilon x y p)
      (@pathout_transport_at_p A B F G epsilon x y p)
      (@pathout_top_lhs_transport_path A B F G epsilon x y p));

symbol pathout_lhs_tele_top_source_path
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj A))
  (p : τ (Hom A x y))
  : τ (@=
      (Obj (Hom_cat B
        (@fapp0 A B F x)
        (@fapp0 A B G y)))
      (@pathout_lhs_tele_source A B F G epsilon x y p)
      (@fapp0
        (Hom_cat A y y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
        (@pathout_top_lhs_func A B F G epsilon x y p)
        (@id A y)))
≔ @eq_ap
    (Obj (Functor_cat
      (Hom_cat A y y)
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))))
    (Obj (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y)))
    (λ H : τ (Functor
        (Hom_cat A y y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))),
      @fapp0
        (Hom_cat A y y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
        H (@id A y))
    (@pathout_lhs_tele_at_p A B F G epsilon x y p)
    (@pathout_top_lhs_func A B F G epsilon x y p)
    (@pathout_lhs_tele_top_path A B F G epsilon x y p);

// Complete represented-source path to the formal source of the extracted
// pre/right laxity cell.
symbol pathout_sigma_top_source_path
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj A))
  (p : τ (Hom A x y))
  : τ (@=
      (Obj (Hom_cat B
        (@fapp0 A B F x)
        (@fapp0 A B G y)))
      (@pathout_sigma_source A B F G epsilon x y p)
      (@fapp0
        (Hom_cat A y y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
        (@pathout_top_lhs_func A B F G epsilon x y p)
        (@id A y)))
≔ @eq_trans
    (Obj (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y)))
    (@pathout_sigma_source A B F G epsilon x y p)
    (@pathout_general_pre_source A B F G epsilon x y p)
    (@fapp0
      (Hom_cat A y y)
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
      (@pathout_top_lhs_func A B F G epsilon x y p)
      (@id A y))
    (@pathout_sigma_general_pre_path A B F G epsilon x y p)
    (@eq_trans
      (Obj (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y)))
      (@pathout_general_pre_source A B F G epsilon x y p)
      (@pathout_lhs_tele_source A B F G epsilon x y p)
      (@fapp0
        (Hom_cat A y y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
        (@pathout_top_lhs_func A B F G epsilon x y p)
        (@id A y))
      (@pathout_general_pre_lhs_tele_path A B F G epsilon x y p)
      (@pathout_lhs_tele_top_source_path A B F G epsilon x y p));
