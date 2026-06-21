require open emdash.emdash3_2;

// Same internalized representable functor, without broad hom_postcomp rules.
symbol ReviewCore_Hom_prof_func [J B : Cat]
  : τ (Functor
      (Functor_cat J B)
      (Prof_cat B J));

rule fapp0 (@ReviewCore_Hom_prof_func $J $B) $G
  ↪ @Hom_prof $J $B $G;

symbol ReviewCore_Hom_prof_func_fapp1_func [J B : Cat]
  [G H : τ (Functor J B)]
  : τ (Functor
      (Transf_cat G H)
      (Functord_cat
        (@Hom_prof J B G)
        (@Hom_prof J B H)));

rule @fapp1_func _ _
      (@ReviewCore_Hom_prof_func $J $B)
      $G $H
  ↪ @ReviewCore_Hom_prof_func_fapp1_func $J $B $G $H;

symbol ReviewCore_Hom_prof_func_transf [J B : Cat]
  [G H : τ (Functor J B)]
  (eta : τ (Transf G H))
  : τ (Functord
      (@Hom_prof J B G)
      (@Hom_prof J B H));

rule fapp0
      (@ReviewCore_Hom_prof_func_fapp1_func $J $B $G $H)
      $eta
  ↪ @ReviewCore_Hom_prof_func_transf $J $B $G $H $eta;

rule @fapp1_fapp0 _ _
      (@ReviewCore_Hom_prof_func $J $B)
      $G $H $eta
  ↪ @ReviewCore_Hom_prof_func_transf $J $B $G $H $eta;

rule @tapp0_fapp0
      _ Cat_cat _ _ $bj
      (@ReviewCore_Hom_prof_func_transf $J $B $G $H $eta)
  ↪ @hom_postcomp_func
      $B $B (@id_func $B)
      (sigma_Fst $bj)
      (@fapp0 $J $B $G (sigma_Snd $bj))
      (@fapp0 $J $B $H (sigma_Snd $bj))
      (@tapp0_fapp0
        $J $B $G $H
        (sigma_Snd $bj)
        $eta);

rule @ReviewCore_Hom_prof_func_transf
      $J $B $G $G
      (@id _ $G)
  ↪ @id_funcd
      (Product_cat (Op_cat $B) $J)
      (@Hom_prof $J $B $G);

rule @comp_catd_fapp0
      _ _ _ _
      (@ReviewCore_Hom_prof_func_transf $J $B $H $K $eta)
      (@ReviewCore_Hom_prof_func_transf $J $B $G $H $epsilon)
  ↪ @ReviewCore_Hom_prof_func_transf
      $J $B $G $K
      (@comp_fapp0
        (Functor_cat $J $B)
        $G $H $K
        $eta $epsilon);

assert [J B : Cat] (G : τ (Functor J B)) ⊢
  fapp0 (@ReviewCore_Hom_prof_func J B) G
  ≡ @Hom_prof J B G;

assert [J B : Cat] [G H : τ (Functor J B)]
  (eta : τ (Transf G H)) ⊢
  @fapp1_fapp0
    (Functor_cat J B)
    (Prof_cat B J)
    (@ReviewCore_Hom_prof_func J B)
    G H eta
  ≡ @ReviewCore_Hom_prof_func_transf J B G H eta;

assert [J B : Cat] [G H : τ (Functor J B)]
  (eta : τ (Transf G H))
  (b : τ (Obj B))
  (j : τ (Obj J)) ⊢
  @tapp0_fapp0
    (Product_cat (Op_cat B) J)
    Cat_cat
    (@Hom_prof J B G)
    (@Hom_prof J B H)
    (Struct_sigma b j)
    (@ReviewCore_Hom_prof_func_transf J B G H eta)
  ≡ @hom_postcomp_func
      B B (@id_func B) b
      (@fapp0 J B G j)
      (@fapp0 J B H j)
      (@tapp0_fapp0 J B G H j eta);

assert [J B : Cat] (G : τ (Functor J B)) ⊢
  @ReviewCore_Hom_prof_func_transf
    J B G G
    (@id (Functor_cat J B) G)
  ≡ @id_funcd
      (Product_cat (Op_cat B) J)
      (@Hom_prof J B G);

assert [J B : Cat] [G H K : τ (Functor J B)]
  (epsilon : τ (Transf G H))
  (eta : τ (Transf H K)) ⊢
  @comp_catd_fapp0
    (Product_cat (Op_cat B) J)
    (@Hom_prof J B G)
    (@Hom_prof J B H)
    (@Hom_prof J B K)
    (@ReviewCore_Hom_prof_func_transf J B H K eta)
    (@ReviewCore_Hom_prof_func_transf J B G H epsilon)
  ≡ @ReviewCore_Hom_prof_func_transf
      J B G K
      (@comp_fapp0
        (Functor_cat J B)
        G H K eta epsilon);
