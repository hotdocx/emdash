/* Proof-time constant postcomposition at the canonical Cat horizontal head.
   Ordinary consumers use the current constant-composition presentation;
   broader lax/profile qualification is deferred with that presentation.
   No arbitrary pointwise extensionality or new functoriality axiom is added. */
require open emdash.emdash3_2_diagram_evaluation;

// Existing Cat-level postcomposition on a constant transformation.
// The identity second component distinguishes this from general horizontal action.
// lhs-audit: keep 1 -- the Cat horizontal-action carrier is the actual discriminator
unif_rule @comp_prod_fapp1_fapp0 Cat_cat $K $A $B
    (@Struct_sigma _ _ (@Const_func $K $A $x) $F)
    (@Struct_sigma _ _ (@Const_func $K $A $y) $F)
    (@Struct_sigma _ _ (@Const_transf $K $A $x $y $f) (@id _ $F))
  ≡ @Const_transf $K1 $B1 $u $v $g
  ↪ [ $K1 ≡ $K; $B1 ≡ $B;
      $u ≡ (@fapp0 $A $B $F $x); $v ≡ (@fapp0 $A $B $F $y);
      $g ≡ (@fapp1_fapp0 $A $B $F $x $y $f) ];
