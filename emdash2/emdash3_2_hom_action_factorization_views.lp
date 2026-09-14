/* Next-Hom views of the two existing Hom_func factorizations.
   These are sufficient congruence/projection comparisons; all original
   endpoint arrows and both input objects are retained. No runtime fold. */
require open emdash.emdash3_2;

// Hom(g,f)[h,k] after precomposition followed by postcomposition.
unif_rule @fapp1_func _ _ (@Hom_func $A $x $x' $y $y' $g $f) $h $k
  ≡ @comp_fapp0 Cat_cat _ _ _
      (@hom_postcomp_fapp1_func $A $A (@id Cat_cat $A) $x' $y $y' $f $ph $pk)
      (@hom_precomp_along_fapp1_func $A $A (@id Cat_cat $A) $y $x' $x $g $h $k)
  ↪ [ $ph ≡ (@hom_precomp_along_fapp0 $A $A (@id Cat_cat $A) $y $x' $x $g $h);
      $pk ≡ (@hom_precomp_along_fapp0 $A $A (@id Cat_cat $A) $y $x' $x $g $k) ];

// Hom(g,f)[h,k] after postcomposition followed by precomposition.
unif_rule @fapp1_func _ _ (@Hom_func $A $x $x' $y $y' $g $f) $h $k
  ≡ @comp_fapp0 Cat_cat _ _ _
      (@hom_precomp_along_fapp1_func $A $A (@id Cat_cat $A) $y' $x' $x $g $ph $pk)
      (@hom_postcomp_fapp1_func $A $A (@id Cat_cat $A) $x $y $y' $f $h $k)
  ↪ [ $ph ≡ (@hom_postcomp_fapp0 $A $A (@id Cat_cat $A) $x $y $y' $f $h);
      $pk ≡ (@hom_postcomp_fapp0 $A $A (@id Cat_cat $A) $x $y $y' $f $k) ];

// Raw Cat composition is the third presentation of the same rigid point.
// Keep the established left-associated functor-composition normal form.
unif_rule @Hom_fapp0 Cat_cat $A $B $E $C $D $V $F
  ≡ @comp_fapp0 Cat_cat $B $A $C
      (@comp_fapp0 Cat_cat $A $E $C $V $F) $D
  ↪ [ tt ≡ tt ];

// The identity middle functor erases one factor of the raw triple.
// This is the existing Hom middle-identity degeneration at its raw view.
unif_rule @Hom_fapp0 Cat_cat $A $B $A $C $D $V (@id Cat_cat $A)
  ≡ @comp_fapp0 Cat_cat $B $A $C $V $D
  ↪ [ tt ≡ tt ];
