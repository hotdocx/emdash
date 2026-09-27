/* Actual normalized sym-evaluation consumer of the scoped comparison. */
require open emdash.emdash3_2_walking_arrow_native_observation;

assert [I C : Cat] [i j : τ (Obj I)] (u : τ (Hom I i j))
  (p : τ (@IsLaxTransfor (Functor_cat I C) C
    (@diagram_evaluation_at_func I C i) (@diagram_evaluation_at_func I C j)
    (@diagram_evaluation_transf I C i j u)))
  (d : τ (Functor I C)) ⊢
  @eq_refl (Hom C (@fapp0 I C d i) (@fapp0 I C d j)) (@tapp0_fapp0 (Functor_cat I C) C
      (@diagram_evaluation_at_func I C i) (@diagram_evaluation_at_func I C j) d
      (@lax_transfor (Functor_cat I C) C
        (@diagram_evaluation_at_func I C i) (@diagram_evaluation_at_func I C j)
        (@make_lax_transfor (Functor_cat I C) C
          (@diagram_evaluation_at_func I C i) (@diagram_evaluation_at_func I C j)
          (@diagram_evaluation_transf I C i j u) p)))
  : τ (@= (Hom C (@fapp0 I C d i) (@fapp0 I C d j)) (@tapp0_fapp0 (Functor_cat I C) C
      (@diagram_evaluation_at_func I C i) (@diagram_evaluation_at_func I C j) d
      (@lax_transfor (Functor_cat I C) C
        (@diagram_evaluation_at_func I C i) (@diagram_evaluation_at_func I C j)
        (@make_lax_transfor (Functor_cat I C) C
          (@diagram_evaluation_at_func I C i) (@diagram_evaluation_at_func I C j)
          (@diagram_evaluation_transf I C i j u) p))) (@fapp1_fapp0 I C d i j u));

assertnot [I C : Cat] [i j : τ (Obj I)] (u : τ (Hom I i j))
  (p : τ (@IsLaxTransfor (Functor_cat I C) C
    (@diagram_evaluation_at_func I C i) (@diagram_evaluation_at_func I C j)
    (@diagram_evaluation_transf I C i j u)))
  (d : τ (Functor I C)) ⊢
  (@tapp0_fapp0 (Functor_cat I C) C
      (@diagram_evaluation_at_func I C i) (@diagram_evaluation_at_func I C j) d
      (@lax_transfor (Functor_cat I C) C
        (@diagram_evaluation_at_func I C i) (@diagram_evaluation_at_func I C j)
        (@make_lax_transfor (Functor_cat I C) C
          (@diagram_evaluation_at_func I C i) (@diagram_evaluation_at_func I C j)
          (@diagram_evaluation_transf I C i j u) p))) ≡ @fapp1_fapp0 I C d i j u;

assertnot [I C : Cat] [i j : τ (Obj I)] (u : τ (Hom I i j))
  (p : τ (@IsLaxTransfor (Functor_cat I C) C
    (@diagram_evaluation_at_func I C i) (@diagram_evaluation_at_func I C j)
    (@diagram_evaluation_transf I C i j u)))
  (d : τ (Functor I C)) (v : τ (Hom I i j)) ⊢
  @eq_refl (Hom C (@fapp0 I C d i) (@fapp0 I C d j)) (@tapp0_fapp0 (Functor_cat I C) C
      (@diagram_evaluation_at_func I C i) (@diagram_evaluation_at_func I C j) d
      (@lax_transfor (Functor_cat I C) C
        (@diagram_evaluation_at_func I C i) (@diagram_evaluation_at_func I C j)
        (@make_lax_transfor (Functor_cat I C) C
          (@diagram_evaluation_at_func I C i) (@diagram_evaluation_at_func I C j)
          (@diagram_evaluation_transf I C i j u) p)))
  : τ (@= (Hom C (@fapp0 I C d i) (@fapp0 I C d j)) (@tapp0_fapp0 (Functor_cat I C) C
      (@diagram_evaluation_at_func I C i) (@diagram_evaluation_at_func I C j) d
      (@lax_transfor (Functor_cat I C) C
        (@diagram_evaluation_at_func I C i) (@diagram_evaluation_at_func I C j)
        (@make_lax_transfor (Functor_cat I C) C
          (@diagram_evaluation_at_func I C i) (@diagram_evaluation_at_func I C j)
          (@diagram_evaluation_transf I C i j u) p))) (@fapp1_fapp0 I C d i j v));
