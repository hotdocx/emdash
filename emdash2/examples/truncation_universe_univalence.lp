/*
  Reviewer milestone: restricted univalence for truncated-universe packages.

  Package equality is equivalent to ordinary TypeEquiv data for the retained
  carriers by composing carrier-path control with the canonical ambient
  decoder. The result is not direct observational universe identity and does
  not establish the (n+1)-truncation theorem for TruncGrpdU(n).
*/

require open emdash.emdash3_2;

assert [A B : Grpd] ⊢
  @grpd_univalence_type_equiv A B
  : τ (TypeEquiv (@= Grpd_grpd A B) (TypeEquiv A B));

assert (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)] ⊢
  @trunc_grpd_univalence_type_equiv n X Y
  : τ (TypeEquiv
      (@= (TruncGrpdU n) X Y)
      (TypeEquiv
        (trunc_grpd_carrier X)
        (trunc_grpd_carrier Y)));

assert (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= (TruncGrpdU n) X Y)) ⊢
  type_equiv_to (@trunc_grpd_univalence_type_equiv n X Y) p
  ≡ @idtoequiv_grpd
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y)
      (@trunc_grpd_carrier_path n X Y p);

assert (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (e : τ (TypeEquiv
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y))) ⊢
  type_equiv_from (@trunc_grpd_univalence_type_equiv n X Y) e
  ≡ @trunc_grpd_path_from_carrier
      n X Y
      (@grpd_equiv_path
        (trunc_grpd_carrier X)
        (trunc_grpd_carrier Y)
        e);

assert (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= (TruncGrpdU n) X Y)) ⊢
  @trunc_grpd_equiv_path_idtoequiv n X Y p
  : τ (@=
      (@= (TruncGrpdU n) X Y)
      (@trunc_grpd_equiv_path
        n X Y (@trunc_grpd_idtoequiv n X Y p))
      p);

assert (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (e : τ (TypeEquiv
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y))) ⊢
  @trunc_grpd_idtoequiv_equiv_path n X Y e
  : τ (@=
      (TypeEquiv
        (trunc_grpd_carrier X)
        (trunc_grpd_carrier Y))
      (@trunc_grpd_idtoequiv
        n X Y (@trunc_grpd_equiv_path n X Y e))
      e);

assert (n : TruncLevel)
  (X : τ (TruncGrpdU n)) ⊢
  @trunc_grpd_idtoequiv
    n X X (@eq_refl (TruncGrpdU n) X)
  ≡ @type_equiv_refl (trunc_grpd_carrier X);

assert (n : TruncLevel)
  (X : τ (TruncGrpdU n)) ⊢
  @trunc_grpd_equiv_path_refl n X
  : τ (@=
      (@= (TruncGrpdU n) X X)
      (@trunc_grpd_equiv_path
        n X X (@type_equiv_refl (trunc_grpd_carrier X)))
      (@eq_refl (TruncGrpdU n) X));

// Both inverse laws remain propositional rather than runtime cancellation.
assertnot (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= (TruncGrpdU n) X Y)) ⊢
  @trunc_grpd_equiv_path
    n X Y (@trunc_grpd_idtoequiv n X Y p)
  ≡ p;

assertnot (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (e : τ (TypeEquiv
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y))) ⊢
  @trunc_grpd_idtoequiv
    n X Y (@trunc_grpd_equiv_path n X Y e)
  ≡ e;

// The inverse reflexive law is also propositional.
assertnot (n : TruncLevel)
  (X : τ (TruncGrpdU n)) ⊢
  @trunc_grpd_equiv_path
    n X X (@type_equiv_refl (trunc_grpd_carrier X))
  ≡ @eq_refl (TruncGrpdU n) X;

