require open emdash.emdash3_2;

/* Proof-time use of the existing category unit laws across equal functor presentations. */

// The category, both unit endpoints and original arrow are explicit obligations.
// lhs-audit: keep 1 -- scope the view to composition in the existing functor category.
unif_rule @comp_fapp0 (Functor_cat $B $C) $X $Y _ $g (@id $D $I)
  ≡ $h
  ↪ [ $D ≡ Functor_cat $B $C; $X ≡ $Y; $Y ≡ $I; $g ≡ $h ];

// The left unit likewise retains its classifier, endpoints and original arrow.
// lhs-audit: keep 1 -- scope the view to composition in the existing functor category.
unif_rule @comp_fapp0 (Functor_cat $B $C) _ $Y $Z (@id $D $I) $f
  ≡ $g
  ↪ [ $D ≡ Functor_cat $B $C; $Y ≡ $Z; $Y ≡ $I; $f ≡ $g ];
