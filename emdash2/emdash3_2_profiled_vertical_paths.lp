/* Profiled vertical equations on the original raw carriers. Admission
   views are used internally; only equality proofs are transported. */
require open emdash.emdash3_2_gray_profiles;

symbol profiled_vertical_post_raw_path
  [A B : Cat] [F G H : τ (Functor A B)]
  (epsilon : τ (@Transf A B F G)) (eta : τ (@Transf A B G H))
  (PN : τ (@IsPreStrictTransfor A B G H eta))
  [X Y : τ (Obj A)] (p : τ (Hom A X Y))
  : τ (@= (Hom B (@fapp0 A B F X) (@fapp0 A B H Y)) (@comp_fapp0 B (@fapp0 A B F X) (@fapp0 A B G Y) (@fapp0 A B H Y) (@tapp0_fapp0 A B G H Y eta) (@tapp1_fapp0 A B F G X Y epsilon p)) (@tapp1_fapp0 A B F H X Y (@comp_fapp0 (Functor_cat A B) F G H eta epsilon) p))
≔ (@ind_eq (@Transf A B G H) eta (@lax_transfor A B G H (@make_lax_transfor A B G H eta PN))
      (@eq_sym (@Transf A B G H) (@lax_transfor A B G H (@make_lax_transfor A B G H eta PN)) eta (@make_lax_transfor_carrier_path A B G H eta PN))
      (λ eta0 : τ (@Transf A B G H), @= (Hom B (@fapp0 A B F X) (@fapp0 A B H Y)) (@comp_fapp0 B (@fapp0 A B F X) (@fapp0 A B G Y) (@fapp0 A B H Y) (@tapp0_fapp0 A B G H Y eta0) (@tapp1_fapp0 A B F G X Y epsilon p)) (@tapp1_fapp0 A B F H X Y (@comp_fapp0 (Functor_cat A B) F G H eta0 epsilon) p))
      (@eq_refl (Hom B (@fapp0 A B F X) (@fapp0 A B H Y)) (@comp_fapp0 B (@fapp0 A B F X) (@fapp0 A B G Y) (@fapp0 A B H Y) (@tapp0_fapp0 A B G H Y (@lax_transfor A B G H (@make_lax_transfor A B G H eta PN))) (@tapp1_fapp0 A B F G X Y epsilon p))));

symbol profiled_vertical_pre_raw_path
  [A B : Cat] [F G H : τ (Functor A B)]
  (epsilon : τ (@Transf A B F G)) (eta : τ (@Transf A B G H))
  (PE : τ (@IsStrictTransfor A B F G epsilon))
  [X Y : τ (Obj A)] (p : τ (Hom A X Y))
  : τ (@= (Hom B (@fapp0 A B F X) (@fapp0 A B H Y)) (@comp_fapp0 B (@fapp0 A B F X) (@fapp0 A B G X) (@fapp0 A B H Y) (@tapp1_fapp0 A B G H X Y eta p) (@tapp0_fapp0 A B F G X epsilon)) (@tapp1_fapp0 A B F H X Y (@comp_fapp0 (Functor_cat A B) F G H eta epsilon) p))
≔ (@ind_eq (@Transf A B F G) epsilon (@strict_transfor A B F G (@make_strict_transfor A B F G epsilon PE))
      (@eq_sym (@Transf A B F G) (@strict_transfor A B F G (@make_strict_transfor A B F G epsilon PE)) epsilon (@make_strict_transfor_carrier_path A B F G epsilon PE))
      (λ epsilon0 : τ (@Transf A B F G), @= (Hom B (@fapp0 A B F X) (@fapp0 A B H Y)) (@comp_fapp0 B (@fapp0 A B F X) (@fapp0 A B G X) (@fapp0 A B H Y) (@tapp1_fapp0 A B G H X Y eta p) (@tapp0_fapp0 A B F G X epsilon0)) (@tapp1_fapp0 A B F H X Y (@comp_fapp0 (Functor_cat A B) F G H eta epsilon0) p))
      (@eq_refl (Hom B (@fapp0 A B F X) (@fapp0 A B H Y)) (@comp_fapp0 B (@fapp0 A B F X) (@fapp0 A B G X) (@fapp0 A B H Y) (@tapp1_fapp0 A B G H X Y eta p) (@tapp0_fapp0 A B F G X (@strict_transfor A B F G (@make_strict_transfor A B F G epsilon PE))))));

symbol profiled_vertical_both_raw_path
  [A B : Cat] [F G H : τ (Functor A B)]
  (epsilon : τ (@Transf A B F G)) (eta : τ (@Transf A B G H))
  (PE : τ (@IsStrictTransfor A B F G epsilon))
  (PN : τ (@IsPreStrictTransfor A B G H eta))
  [X Y Z : τ (Obj A)] (p : τ (Hom A X Y)) (q : τ (Hom A Y Z))
  : τ (@= (Hom B (@fapp0 A B F X) (@fapp0 A B H Z)) (@comp_fapp0 B (@fapp0 A B F X) (@fapp0 A B G Y) (@fapp0 A B H Z) (@tapp1_fapp0 A B G H Y Z eta q) (@tapp1_fapp0 A B F G X Y epsilon p)) (@tapp1_fapp0 A B F H X Z (@comp_fapp0 (Functor_cat A B) F G H eta epsilon) (@comp_fapp0 A X Y Z q p)))
≔ (@ind_eq (@Transf A B F G) epsilon (@strict_transfor A B F G (@make_strict_transfor A B F G epsilon PE))
      (@eq_sym (@Transf A B F G) (@strict_transfor A B F G (@make_strict_transfor A B F G epsilon PE)) epsilon (@make_strict_transfor_carrier_path A B F G epsilon PE))
      (λ epsilon0 : τ (@Transf A B F G), @= (Hom B (@fapp0 A B F X) (@fapp0 A B H Z)) (@comp_fapp0 B (@fapp0 A B F X) (@fapp0 A B G Y) (@fapp0 A B H Z) (@tapp1_fapp0 A B G H Y Z eta q) (@tapp1_fapp0 A B F G X Y epsilon0 p)) (@tapp1_fapp0 A B F H X Z (@comp_fapp0 (Functor_cat A B) F G H eta epsilon0) (@comp_fapp0 A X Y Z q p)))
      (@ind_eq (@Transf A B G H) eta (@lax_transfor A B G H (@make_lax_transfor A B G H eta PN))
      (@eq_sym (@Transf A B G H) (@lax_transfor A B G H (@make_lax_transfor A B G H eta PN)) eta (@make_lax_transfor_carrier_path A B G H eta PN))
      (λ eta0 : τ (@Transf A B G H), @= (Hom B (@fapp0 A B F X) (@fapp0 A B H Z)) (@comp_fapp0 B (@fapp0 A B F X) (@fapp0 A B G Y) (@fapp0 A B H Z) (@tapp1_fapp0 A B G H Y Z eta0 q) (@tapp1_fapp0 A B F G X Y (@strict_transfor A B F G (@make_strict_transfor A B F G epsilon PE)) p)) (@tapp1_fapp0 A B F H X Z (@comp_fapp0 (Functor_cat A B) F G H eta0 (@strict_transfor A B F G (@make_strict_transfor A B F G epsilon PE))) (@comp_fapp0 A X Y Z q p)))
      (@eq_refl (Hom B (@fapp0 A B F X) (@fapp0 A B H Z)) (@comp_fapp0 B (@fapp0 A B F X) (@fapp0 A B G Y) (@fapp0 A B H Z) (@tapp1_fapp0 A B G H Y Z (@lax_transfor A B G H (@make_lax_transfor A B G H eta PN)) q) (@tapp1_fapp0 A B F G X Y (@strict_transfor A B F G (@make_strict_transfor A B F G epsilon PE)) p)))));
