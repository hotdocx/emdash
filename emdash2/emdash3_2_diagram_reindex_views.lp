/* Proof-time accumulation of the existing whole evaluation comparison.
   Runtime evaluation and composition owners remain unchanged. */
require open emdash.emdash3_2_diagram_evaluation;

// (ev_i∘F)∘D ≐ F(−)[i]∘D, retaining both original functors and the shape point.
unif_rule @comp_fapp0 Cat_cat _ _ _
    (@comp_fapp0 Cat_cat _ _ _ (@sym_fapp0_func _ $I $C (@id Cat_cat _) $i) $F) $D
  ≡ @comp_fapp0 Cat_cat _ _ _ (@sym_fapp0_func _ $I1 $C1 $F1 $i1) $D1
  ↪ [ $I1 ≡ $I; $C1 ≡ $C; $F1 ≡ $F; $D1 ≡ $D; $i1 ≡ $i ];

// The same whole h has the same shape observation under native/raw composed parents.
unif_rule @sym_transf_tapp0_transf _ $I $C
    (@hom_postcomp_fapp0 Cat_cat Cat_cat (@id Cat_cat Cat_cat) _ _ _ $F $X) $G $h $i
  ≡ @sym_transf_tapp0_transf _ $I1 $C1
      (@comp_fapp0 Cat_cat _ _ _ $F1 $X1) $G1 $h1 $i1
  ↪ [ $I1 ≡ $I; $C1 ≡ $C; $F1 ≡ $F; $X1 ≡ $X; $G1 ≡ $G; $h1 ≡ $h; $i1 ≡ $i ];
