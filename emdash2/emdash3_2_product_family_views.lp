/* Whole product-family observations with unchanged runtime owners.
   Proof-time projections cover literal diagonals and the existing composite
   and constant normal forms, retaining their original data. The paired-component view compares every endpoint,
   cell and parameter. Its semantics are exhibited by the derived product
   component path below; it is not a new universality primitive. */
require open emdash.emdash3_2_groupoidal_closure;

// The product diagonal pairs the identity functor with itself.
symbol product_diagonal_func (C : Cat) : τ (Functor C (Product_cat C C))
≔ Struct_sigma (@id_func C) (@id_func C);

// Source and diagonal constructor retain the exact functor being projected.
unif_rule @sigma_Fst _ _ (@comp_fapp0 Cat_cat _ $C (Product_cat $C $C)
    (Struct_sigma (@id Cat_cat $C) (@id Cat_cat $C)) $F)
  ≡ $G ↪ [ $F ≡ $G ];
unif_rule @sigma_Snd _ _ (@comp_fapp0 Cat_cat _ $C (Product_cat $C $C)
    (Struct_sigma (@id Cat_cat $C) (@id Cat_cat $C)) $F)
  ≡ $G ↪ [ $F ≡ $G ];

// Projected native postcomposition retains its original runtime owner.
unif_rule @sigma_Fst _ _
    (@hom_postcomp_fapp0 Cat_cat Cat_cat (@id Cat_cat Cat_cat) _ $C (Product_cat $C $C)
      (Struct_sigma (@id Cat_cat $C) (@id Cat_cat $C)) $F)
  ≡ $G ↪ [ $F ≡ $G ];
unif_rule @sigma_Snd _ _
    (@hom_postcomp_fapp0 Cat_cat Cat_cat (@id Cat_cat Cat_cat) _ $C (Product_cat $C $C)
      (Struct_sigma (@id Cat_cat $C) (@id Cat_cat $C)) $F)
  ≡ $G ↪ [ $F ≡ $G ];

// Proof-time raw-composition projections after existing associativity has acted.
// Compare both original factors; do not install a runtime distribution rule.
unif_rule @sigma_Fst _ _
    (@comp_fapp0 Cat_cat $A $B (Product_cat $C _) $H $F)
  ≡ @comp_fapp0 Cat_cat $A0 $B0 $C0 $H0 $F0
  ↪ [ $A ≡ $A0; $B ≡ $B0; $C ≡ $C0;
      sigma_Fst $H ≡ $H0; $F ≡ $F0 ];
unif_rule @sigma_Snd _ _
    (@comp_fapp0 Cat_cat $A $B (Product_cat _ $D) $H $F)
  ≡ @comp_fapp0 Cat_cat $A0 $B0 $D0 $H0 $F0
  ↪ [ $A ≡ $A0; $B ≡ $B0; $D ≡ $D0;
      sigma_Snd $H ≡ $H0; $F ≡ $F0 ];

// Existing constant-composition normal forms retain their selected coordinate.
unif_rule @sigma_Fst _ _
    (@Const_func $A (Product_cat $C _) (Struct_sigma $x _))
  ≡ @Const_func $A0 $C0 $x0
  ↪ [ $A ≡ $A0; $C ≡ $C0; $x ≡ $x0 ];
unif_rule @sigma_Snd _ _
    (@Const_func $A (Product_cat _ $D) (Struct_sigma _ $y))
  ≡ @Const_func $A0 $D0 $y0
  ↪ [ $A ≡ $A0; $D ≡ $D0; $y ≡ $y0 ];

// Component projections reconstruct the same product arrow by the existing path interface.
symbol product_transf_component_path [B C D : Cat]
  (F G : τ (Functor B (Product_cat C D)))
  (eta : τ (@Transf B (Product_cat C D) F G)) (b : τ (Obj B))
  : τ (@= (Hom (Product_cat C D) (@fapp0 B (Product_cat C D) F b)
        (@fapp0 B (Product_cat C D) G b))
      (@tapp0_fapp0 B (Product_cat C D) F G b eta)
      (@Product_pair
        (Hom_cat C (@fapp0 B C (sigma_Fst F) b) (@fapp0 B C (sigma_Fst G) b))
        (Hom_cat D (@fapp0 B D (sigma_Snd F) b) (@fapp0 B D (sigma_Snd G) b))
        (@tapp0_fapp0 B C (sigma_Fst F) (sigma_Fst G) b (sigma_Fst eta))
        (@tapp0_fapp0 B D (sigma_Snd F) (sigma_Snd G) b (sigma_Snd eta))))
≔ @path_product_join
    (Hom C (@fapp0 B C (sigma_Fst F) b) (@fapp0 B C (sigma_Fst G) b))
    (Hom D (@fapp0 B D (sigma_Snd F) b) (@fapp0 B D (sigma_Snd G) b))
    (@tapp0_fapp0 B (Product_cat C D) F G b eta)
    (@Product_pair
      (Hom_cat C (@fapp0 B C (sigma_Fst F) b) (@fapp0 B C (sigma_Fst G) b))
      (Hom_cat D (@fapp0 B D (sigma_Snd F) b) (@fapp0 B D (sigma_Snd G) b))
      (@tapp0_fapp0 B C (sigma_Fst F) (sigma_Fst G) b (sigma_Fst eta))
      (@tapp0_fapp0 B D (sigma_Snd F) (sigma_Snd G) b (sigma_Snd eta)))
    (Struct_sigma
      (eq_refl (@tapp0_fapp0 B C (sigma_Fst F) (sigma_Fst G) b (sigma_Fst eta)))
      (eq_refl (@tapp0_fapp0 B D (sigma_Snd F) (sigma_Snd G) b (sigma_Snd eta))));

// Both component cells, every endpoint family, and the parameter are compared.
unif_rule @tapp0_fapp0 $B (Product_cat $C $D) $F $G $b (Struct_sigma $f $g)
  ≡ @Struct_sigma _ _
      (@tapp0_fapp0 $B0 $C0 $F0 $G0 $b0 $f0)
      (@tapp0_fapp0 $B1 $D0 $F1 $G1 $b1 $g0)
  ↪ [ $B ≡ $B0; $B ≡ $B1; $C ≡ $C0; $D ≡ $D0;
      sigma_Fst $F ≡ $F0; sigma_Snd $F ≡ $F1;
      sigma_Fst $G ≡ $G0; sigma_Snd $G ≡ $G1;
      $b ≡ $b0; $b ≡ $b1; $f ≡ $f0; $g ≡ $g0 ];
