/* Direct identity evaluation of Yoneda precomposition. This uses raw H;
   the existing presheaf-composition path, with no naturality path or
   output-section strictness supplied. */
require open emdash.emdash3_2_presheaves;

symbol yoneda_precomposition_value_path
  [K : Cat] (X : τ (@Psh K)) [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (H : τ (Hom (@Psh_cat K) (@yoneda_psh K U) X))
  : τ (@= (Obj (@Fibre_cat (Op_cat K) X V))
    (@fapp0 (@Hom_cat K V V) (@Fibre_cat (Op_cat K) X V)
      (@tapp0_fapp0 (Op_cat K) Cat_cat (@yoneda_psh K V) X V
        (@comp_fapp0 (@Psh_cat K) (@yoneda_psh K V) (@yoneda_psh K U) X
          H (@fapp1_fapp0 K (@Psh_cat K) (@yoneda_psh_func K) V U p)))
      (@id K V))
    (@fapp0 (@Hom_cat K V U) (@Fibre_cat (Op_cat K) X V)
      (@tapp0_fapp0 (Op_cat K) Cat_cat (@yoneda_psh K U) X V H) p))
≔ @eq_ap
    (Hom (@Psh_cat K) (@yoneda_psh K V) X)
    (Obj (@Fibre_cat (Op_cat K) X V))
    (λ H0 : τ (Hom (@Psh_cat K) (@yoneda_psh K V) X),
      @fapp0 (@Hom_cat K V V) (@Fibre_cat (Op_cat K) X V)
        (@tapp0_fapp0 (Op_cat K) Cat_cat (@yoneda_psh K V) X V H0) (@id K V))
    (@comp_fapp0 (@Psh_cat K) (@yoneda_psh K V) (@yoneda_psh K U) X H (@fapp1_fapp0 K (@Psh_cat K) (@yoneda_psh_func K) V U p))
    (@comp_catd_fapp0 (Op_cat K) (@yoneda_psh K V) (@yoneda_psh K U) X H (@fapp1_fapp0 K (@Psh_cat K) (@yoneda_psh_func K) V U p))
    (@psh_comp_representation_agrees K (@yoneda_psh K V) (@yoneda_psh K U) X H (@fapp1_fapp0 K (@Psh_cat K) (@yoneda_psh_func K) V U p));
