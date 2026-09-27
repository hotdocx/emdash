require open emdash.emdash3_2;

// Source-style stable projections retain the whole inverse until cancellation.
injective symbol defiso_at_to [K D : Cat] [F G : τ (Functor K D)]
  (I : τ (@DefIso (Functor_cat K D) F G)) (x : τ (Obj K))
  : τ (Hom D (@fapp0 K D F x) (@fapp0 K D G x));
injective symbol defiso_at_from [K D : Cat] [F G : τ (Functor K D)]
  (I : τ (@DefIso (Functor_cat K D) F G)) (x : τ (Obj K))
  : τ (Hom D (@fapp0 K D G x) (@fapp0 K D F x));

// These are proof-time agreements, not premature runtime decoders.
unif_rule @defiso_at_to $K $D $F $G $I $x
  ≡ @tapp0_fapp0 $K $D $F $G $x (@defiso_to (Functor_cat $K $D) $F $G $I)
  ↪ [ tt ≡ tt ];
unif_rule @defiso_at_from $K $D $F $G $I $x
  ≡ @tapp0_fapp0 $K $D $G $F $x (@defiso_from (Functor_cat $K $D) $F $G $I)
  ↪ [ tt ≡ tt ];

injective symbol defiso_at [K D : Cat] [F G : τ (Functor K D)]
  (I : τ (@DefIso (Functor_cat K D) F G)) (x : τ (Obj K))
  : τ (@DefIso D (@fapp0 K D F x) (@fapp0 K D G x));
rule @defiso_to _ _ _ (@defiso_at $K $D $F $G $I $x)
  ↪ @defiso_at_to $K $D $F $G $I $x
with @defiso_from _ _ _ (@defiso_at $K $D $F $G $I $x)
  ↪ @defiso_at_from $K $D $F $G $I $x;

// Preserve the canonical identity observation without exposing composite I.
rule @defiso_at_to $K $D $F $F (@defiso_refl _ $F) $x
  ↪ @id $D (@fapp0 $K $D $F $x)
with @defiso_at_from $K $D $F $F (@defiso_refl _ $F) $x
  ↪ @id $D (@fapp0 $K $D $F $x);

rule @comp_fapp0 _ _ _ _
  (@defiso_at_from $K $D $F $G $I $x)
  (@defiso_at_to $K $D $F $G $I $x)
  ↪ @id $D (@fapp0 $K $D $F $x)
with @comp_fapp0 _ _ _ _
  (@defiso_at_to $K $D $F $G $I $x)
  (@defiso_at_from $K $D $F $G $I $x)
  ↪ @id $D (@fapp0 $K $D $G $x);

rule @hom_postcomp_fapp0 $D $D (@id Cat_cat $D) _ _ _
  (@defiso_at_from $K $D $F $G $I $x)
  (@defiso_at_to $K $D $F $G $I $x)
  ↪ @id $D (@fapp0 $K $D $F $x)
with @hom_postcomp_fapp0 $D $D (@id Cat_cat $D) _ _ _
  (@defiso_at_to $K $D $F $G $I $x)
  (@defiso_at_from $K $D $F $G $I $x)
  ↪ @id $D (@fapp0 $K $D $G $x);

rule @hom_postcomp_fapp0 $D $D (@id Cat_cat $D) $W _ _
  (@defiso_at_from $K $D $F $G $I $x)
  (@hom_postcomp_fapp0 $D $D (@id Cat_cat $D) $W _ _
    (@defiso_at_to $K $D $F $G $I $x) $h)
  ↪ $h
with @hom_postcomp_fapp0 $D $D (@id Cat_cat $D) $W _ _
  (@defiso_at_to $K $D $F $G $I $x)
  (@hom_postcomp_fapp0 $D $D (@id Cat_cat $D) $W _ _
    (@defiso_at_from $K $D $F $G $I $x) $h)
  ↪ $h;

// Cat-valued point projections join whole inverse cancellation and fapp0.
// The literal Cat_cat parameter identifies functor-valued components.
rule @fapp0 _ _ (@defiso_at_from $K Cat_cat $F $G $I $x)
  (@fapp0 _ _ (@defiso_at_to $K Cat_cat $F $G $I $x) $a)
  ↪ $a
with @fapp0 _ _ (@defiso_at_to $K Cat_cat $F $G $I $x)
  (@fapp0 _ _ (@defiso_at_from $K Cat_cat $F $G $I $x) $a)
  ↪ $a;

symbol defiso_at_to_path [K D : Cat] [F G : τ (Functor K D)]
  (I : τ (@DefIso (Functor_cat K D) F G)) (x : τ (Obj K))
  : τ (@= (Hom D (@fapp0 K D F x) (@fapp0 K D G x))
      (@defiso_at_to K D F G I x)
      (@tapp0_fapp0 K D F G x (@defiso_to (Functor_cat K D) F G I)))
≔ @eq_refl (Hom D (@fapp0 K D F x) (@fapp0 K D G x))
    (@defiso_at_to K D F G I x);

symbol defiso_at_from_path [K D : Cat] [F G : τ (Functor K D)]
  (I : τ (@DefIso (Functor_cat K D) F G)) (x : τ (Obj K))
  : τ (@= (Hom D (@fapp0 K D G x) (@fapp0 K D F x))
      (@defiso_at_from K D F G I x)
      (@tapp0_fapp0 K D G F x (@defiso_from (Functor_cat K D) F G I)))
≔ @eq_refl (Hom D (@fapp0 K D G x) (@fapp0 K D F x))
    (@defiso_at_from K D F G I x);

// Sufficient congruence when an evaluated inverse is applied through two
// native Hom presentations. This compares every input; it is not injectivity.
unif_rule @fapp0 $A $B (@defiso_at_to $K $D $F $G $I $x) $u
  ≡ @fapp0 $A1 $B1 (@defiso_at_to $K1 $D1 $F1 $G1 $I1 $x1) $u1
  ↪ [ $A1 ≡ $A; $B1 ≡ $B; $K1 ≡ $K; $D1 ≡ $D;
      $F1 ≡ $F; $G1 ≡ $G; $I1 ≡ $I; $x1 ≡ $x; $u1 ≡ $u ];

// Sufficient congruence when an evaluated inverse is applied through two
// native Hom presentations. This compares every input; it is not injectivity.
unif_rule @fapp0 $A $B (@defiso_at_from $K $D $F $G $I $x) $u
  ≡ @fapp0 $A1 $B1 (@defiso_at_from $K1 $D1 $F1 $G1 $I1 $x1) $u1
  ↪ [ $A1 ≡ $A; $B1 ≡ $B; $K1 ≡ $K; $D1 ≡ $D;
      $F1 ≡ $F; $G1 ≡ $G; $I1 ≡ $I; $x1 ≡ $x; $u1 ≡ $u ];
