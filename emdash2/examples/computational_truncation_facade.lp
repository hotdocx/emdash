/*
  Focused reviewer for the classified n-type facade.

  Objects of NType_cat(n) are exactly the existing retained-evidence
  TruncGrpdU(n) packages.  Homs, identity, and composition delegate to the
  decoded ambient carriers, while one whole inclusion computes on objects.
  The negative checks retain the classifier and level boundaries.
*/

require open emdash.emdash3_2_truncation_reflector;

assert (n : TruncLevel) ⊢
  NType_cat n
  : Cat;

assert (n : TruncLevel) ⊢
  Obj (@NType_cat n)
  ≡ TruncGrpdU n;

assert
  (n : TruncLevel)
  (X Y : τ (Obj (@NType_cat n))) ⊢
  Hom_cat (@NType_cat n) X Y
  ≡ Hom_cat
      Grpd_cat
      (@trunc_grpd_carrier n X)
      (@trunc_grpd_carrier n Y);

assert
  (n : TruncLevel)
  (X : τ (Obj (@NType_cat n))) ⊢
  @id (@NType_cat n) X
  : τ (Hom
      Grpd_cat
      (@trunc_grpd_carrier n X)
      (@trunc_grpd_carrier n X));

assert
  (n : TruncLevel)
  (X Y Z : τ (Obj (@NType_cat n)))
  (f : τ (Hom (@NType_cat n) X Y))
  (g : τ (Hom (@NType_cat n) Y Z)) ⊢
  @comp_fapp0 (@NType_cat n) X Y Z g f
  : τ (Hom
      Grpd_cat
      (@trunc_grpd_carrier n X)
      (@trunc_grpd_carrier n Z));

assert
  (n : TruncLevel)
  (X : τ (Obj (@NType_cat n))) ⊢
  @fapp0
    (@NType_cat n)
    Grpd_cat
    (@ntype_include_grpd_func n)
    X
  ≡ @trunc_grpd_carrier n X;

assert
  (n : TruncLevel)
  (X : τ (Obj (@NType_cat n))) ⊢
  @ElNType n X
  ≡ @trunc_grpd_carrier n X;

// Distinct truncation levels do not collapse to one facade.
assertnot ⊢
  @NType_cat trunc_minus_one
  ≡ @NType_cat trunc_zero;

// An arbitrary object of a foreign category is not accepted as an n-type
// code merely because both categories share the generic Obj interface.
assertnot
  (n : TruncLevel)
  (C : Cat)
  (X : τ (Obj C)) ⊢
  X : τ (Obj (@NType_cat n));

// A code classified at one level is not silently reindexed to another.
assertnot
  (X : τ (TruncGrpdU trunc_minus_one)) ⊢
  X : τ (Obj (@NType_cat trunc_zero));

/*
  The reflector result is intrinsically classified. Decoding and retained
  evidence compute through the existing package projections.
*/
assert (n : TruncLevel) (A : Grpd) ⊢
  @Trunc_ntype n A
  : τ (Obj (@NType_cat n));

assert (n : TruncLevel) (A : Grpd) ⊢
  @trunc_grpd_carrier n (@Trunc_ntype n A)
  ≡ @Trunc_grpd n A;

assert (n : TruncLevel) (A : Grpd) ⊢
  @trunc_grpd_evidence n (@Trunc_ntype n A)
  ≡ @trunc_ntype_is_truncated n A;

assert (n : TruncLevel) [A : Grpd]
  (a : τ A) ⊢
  @trunc_intro n A a
  : τ (@ElNType n (@Trunc_ntype n A));

// Intrinsic induction computes on points of every classified motive.
assert (n : TruncLevel) [A : Grpd]
  (P : τ (@Trunc_grpd n A) → τ (Obj (@NType_cat n)))
  (d : Π a : τ A,
    τ (@ElNType n (P (@trunc_intro n A a))))
  (a : τ A) ⊢
  @trunc_ind n A P d (@trunc_intro n A a)
  ≡ d a;

// The ambient adapter packages explicitly supplied fibrewise evidence.
assert (n : TruncLevel) [A : Grpd]
  (D : τ (@Trunc_grpd n A) → Grpd)
  (hD : Π z : τ (@Trunc_grpd n A),
    τ (IsTruncGrpd n (D z)))
  (d : Π a : τ A,
    τ (D (@trunc_intro n A a)))
  (a : τ A) ⊢
  @trunc_ind_ambient n A D hD d (@trunc_intro n A a)
  ≡ d a;

assert (n : TruncLevel) [A : Grpd]
  (B : τ (Obj (@NType_cat n)))
  (d : τ A → τ (@ElNType n B))
  (a : τ A) ⊢
  @trunc_rec n A B d (@trunc_intro n A a)
  ≡ d a;

assert (n : TruncLevel) [A B : Grpd]
  (hB : τ (IsTruncGrpd n B))
  (d : τ A → τ B)
  (a : τ A) ⊢
  @trunc_rec_ambient n A B hB d (@trunc_intro n A a)
  ≡ d a;

// A raw Grpd-valued motive is not accepted by intrinsic induction.
assertnot (n : TruncLevel) [A : Grpd]
  (D : τ (@Trunc_grpd n A) → Grpd)
  (d : Π a : τ A,
    τ (D (@trunc_intro n A a)))
  (z : τ (@Trunc_grpd n A)) ⊢
  @trunc_ind n A D d z
  : τ (D z);

// Successor-level evidence is too weak for elimination at level n.
assertnot (n : TruncLevel) [A : Grpd]
  (D : τ (@Trunc_grpd n A) → Grpd)
  (hD : Π z : τ (@Trunc_grpd n A),
    τ (IsTruncGrpd (trunc_succ n) (D z)))
  (d : Π a : τ A,
    τ (D (@trunc_intro n A a)))
  (z : τ (@Trunc_grpd n A)) ⊢
  @trunc_ind_ambient n A D hD d z
  : τ (D z);

/*
  Map action comes from recursion; the existing Path action retains it as one
  iterable whole Hom functor.
*/
assert (n : TruncLevel) [A B : Grpd]
  (f : τ (@Function_grpd A B))
  (a : τ A) ⊢
  @trunc_map n A B f (@trunc_intro n A a)
  ≡ @trunc_intro n B (f a);

assert (n : TruncLevel) [A B : Grpd]
  (f : τ (@Function_grpd A B)) ⊢
  @fapp0
    (Hom_cat Grpd_cat A B)
    (Hom_cat (@NType_cat n) (@Trunc_ntype n A) (@Trunc_ntype n B))
    (@trunc_map_func n A B)
    f
  ≡ λ z : τ (@Trunc_grpd n A), @trunc_map n A B f z;

// Identity and composition are derived from restricted induction.
assert (n : TruncLevel) (A : Grpd) ⊢
  @trunc_map_id_path n A
  : τ (@=
      (@Function_grpd (@Trunc_grpd n A) (@Trunc_grpd n A))
      (λ z : τ (@Trunc_grpd n A),
        @trunc_map n A A (@grpd_id_function A) z)
      (λ z : τ (@Trunc_grpd n A), z));

assert (n : TruncLevel) [A B C : Grpd]
  (g : τ (@Function_grpd B C))
  (f : τ (@Function_grpd A B)) ⊢
  @trunc_map_comp_path n A B C g f
  : τ (@=
      (@Function_grpd (@Trunc_grpd n A) (@Trunc_grpd n C))
      (λ z : τ (@Trunc_grpd n A),
        @trunc_map n A C (@grpd_comp_function A B C g f) z)
      (λ z : τ (@Trunc_grpd n A),
        @trunc_map n B C g (@trunc_map n A B f z)));

assert (n : TruncLevel) (A : Grpd) ⊢
  @fapp0 Grpd_cat (@NType_cat n) (@Truncation_func n) A
  ≡ @Trunc_ntype n A;

assert (n : TruncLevel) (A B : Grpd) ⊢
  @truncation_hom_action n A B
  : τ (@=
      (Obj (@Functor_cat
        (Hom_cat Grpd_cat A B)
        (Hom_cat
          (@NType_cat n)
          (@Trunc_ntype n A)
          (@Trunc_ntype n B))))
      (@fapp1_func Grpd_cat (@NType_cat n)
        (@Truncation_func n) A B)
      (@trunc_map_func n A B));

// One subsequent equality action remains at the generic Path-map owner.
assert (n : TruncLevel) [A B : Grpd]
  (f g : τ (@Function_grpd A B)) ⊢
  @fapp1_func
    (Hom_cat Grpd_cat A B)
    (Hom_cat (@NType_cat n) (@Trunc_ntype n A) (@Trunc_ntype n B))
    (@trunc_map_func n A B)
    f g
  : τ (@Functor
      (@Path_cat (@= (@Function_grpd A B) f g))
      (@Path_cat (@=
        (@Function_grpd (@Trunc_grpd n A) (@Trunc_grpd n B))
        (@trunc_map_family n A B f)
        (@trunc_map_family n A B g))));

// Equality action retains its actual target endpoint.
assertnot (n : TruncLevel) [A B : Grpd]
  (f g h : τ (@Function_grpd A B))
  (q : τ (@= (@Function_grpd A B) f g)) ⊢
  @fapp1_fapp0
    (Hom_cat Grpd_cat A B)
    (Hom_cat (@NType_cat n) (@Trunc_ntype n A) (@Trunc_ntype n B))
    (@trunc_map_func n A B)
    f g q
  : τ (@=
      (@Function_grpd (@Trunc_grpd n A) (@Trunc_grpd n B))
      (@trunc_map_family n A B f)
      (@trunc_map_family n A B h));
