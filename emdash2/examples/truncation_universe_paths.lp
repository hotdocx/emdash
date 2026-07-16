/*
  Reviewer milestone: carrier/evidence paths in truncated-universe packages.

  A package path is represented by a carrier path plus a dependent path
  between its retained truncation witnesses. Proposition-valued evidence
  reconstructs the second field, so carrier-path projection is an ordinary
  TypeEquiv. Both inverse laws remain propositional rather than runtime eta.
*/

require open emdash.emdash3_2;

assert (n : TruncLevel)
  (X Y : τ (TruncGrpdU n)) ⊢
  TruncGrpdPathView n X Y
  : Grpd;

assert (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= Grpd_grpd
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y))) ⊢
  @trunc_grpd_path_from_carrier n X Y p
  : τ (@= (TruncGrpdU n) X Y);

assert (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= Grpd_grpd
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y))) ⊢
  @trunc_grpd_carrier_path_from_carrier n X Y p
  : τ (@=
      (@= Grpd_grpd
        (trunc_grpd_carrier X)
        (trunc_grpd_carrier Y))
      (@trunc_grpd_carrier_path
        n X Y (@trunc_grpd_path_from_carrier n X Y p))
      p);

assert (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= (TruncGrpdU n) X Y)) ⊢
  @trunc_grpd_path_from_carrier_carrier_path n X Y p
  : τ (@=
      (@= (TruncGrpdU n) X Y)
      (@trunc_grpd_path_from_carrier
        n X Y (@trunc_grpd_carrier_path n X Y p))
      p);

assert (n : TruncLevel)
  (X : τ (TruncGrpdU n)) ⊢
  @trunc_grpd_path_from_carrier_refl n X
  : τ (@=
      (@= (TruncGrpdU n) X X)
      (@trunc_grpd_path_from_carrier
        n X X (@eq_refl Grpd_grpd (trunc_grpd_carrier X)))
      (@eq_refl (TruncGrpdU n) X));

assert (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)] ⊢
  @trunc_grpd_carrier_path_type_equiv n X Y
  : τ (TypeEquiv
      (@= (TruncGrpdU n) X Y)
      (@= Grpd_grpd
        (trunc_grpd_carrier X)
        (trunc_grpd_carrier Y)));

assert (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= (TruncGrpdU n) X Y)) ⊢
  type_equiv_to (@trunc_grpd_carrier_path_type_equiv n X Y) p
  ≡ @trunc_grpd_carrier_path n X Y p;

assert (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= Grpd_grpd
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y))) ⊢
  type_equiv_from (@trunc_grpd_carrier_path_type_equiv n X Y) p
  ≡ @trunc_grpd_path_from_carrier n X Y p;

// Neither inverse law is promoted to runtime cancellation.
assertnot (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= Grpd_grpd
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y))) ⊢
  @trunc_grpd_carrier_path
    n X Y (@trunc_grpd_path_from_carrier n X Y p)
  ≡ p;

assertnot (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= (TruncGrpdU n) X Y)) ⊢
  @trunc_grpd_path_from_carrier
    n X Y (@trunc_grpd_carrier_path n X Y p)
  ≡ p;

// The generic path-view round trip is also propositional.
assertnot (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= (TruncGrpdU n) X Y)) ⊢
  @trunc_grpd_path_decode
    n X Y (@trunc_grpd_path_encode n X Y p)
  ≡ p;

