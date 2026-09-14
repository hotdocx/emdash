/* Explicit ordinary biproduct presentation at the original product functor.
   AdditiveCategory has the pointwise copairing laws. Today's opaque
   Adjunction interface needs this structural/model assembly operation;
   it is not asserted as a derivation from the current beta interface. */
require open emdash.emdash3_2_one_cat_biproduct_injections;

// The same Prod is left adjoint to the same diagonal.
injective symbol one_cat_biproduct_adjunction [C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  : τ (@Adjunction (Product_cat C C) C Prod (@product_diagonal_func C));

// Unit: the whole pair of injections already constructed by the product mate.
rule @unit_adj_transf _ _ _ _ (@one_cat_biproduct_adjunction $C $C1 $Prod $t $A $T0)
  ↪ @Struct_sigma
      (@Transf (Product_cat $C $C) $C (@Product_projL_func $C $C) $Prod)
      (λ _ : τ (@Transf (Product_cat $C $C) $C (@Product_projL_func $C $C) $Prod),
        @Transf (Product_cat $C $C) $C (@Product_projR_func $C $C) $Prod)
      (@one_cat_biproduct_inj1 $C $C1 $Prod $t $A $T0)
      (@one_cat_biproduct_inj2 $C $C1 $Prod $t $A $T0);

// Counit component: the original selected codiagonal [id_X,id_X].
rule @tapp0_fapp0 _ _ _ _ $X
    (@counit_adj_transf _ _ _ _ (@one_cat_biproduct_adjunction $C _ $Prod $t $A _))
  ↪ @additive_copair_fapp0 $C $Prod $t $A $X $X $X (@id $C $X) (@id $C $X);
