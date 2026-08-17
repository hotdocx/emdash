/*
  Classified computational homotopy truncation.

  This first slice realizes the category of n-types directly through the
  existing TruncGrpdU(n) carrier/evidence package.  The classified truncation
  result, restricted eliminator, and recursor-derived whole action are owned
  here; the downstream Circle-connectedness module is their first concrete
  HoTT consumer.

  The category facade follows the active Cat-valued sheaf realization: object
  data compute to the selected package, Homs/identity/composition delegate to
  the ambient category, and one whole inclusion exposes decoded carriers.
  No package conversion pair, proof erasure, unrestricted eliminator, or
  generic HIT schema is introduced by this slice.
*/

require open emdash.emdash3_2;

// Category whose objects are classifiers equipped with n-truncation evidence.
injective symbol NType_cat
  (n : TruncLevel)
  : Cat;

// The selected object realization is the existing retained-evidence package.
rule Obj (@NType_cat $n)
  ↪ TruncGrpdU $n;

// Maps of n-types are the ambient maps between their decoded carriers.
rule Hom_cat (@NType_cat $n) $X $Y
  ↪ Hom_cat
      Grpd_cat
      (@trunc_grpd_carrier $n $X)
      (@trunc_grpd_carrier $n $Y);

// Identity delegates to the ambient groupoid/type category.
rule @id (@NType_cat $n) $X
  ↪ @id Grpd_cat (@trunc_grpd_carrier $n $X);

// Composition delegates to the ambient groupoid/type category.
// lhs-audit: keep 2,3,4 -- each carrier projection is used on the RHS.
rule @comp_fapp0
      (@NType_cat $n) $X $Y $Z $g $f
  ↪ @comp_fapp0
      Grpd_cat
      (@trunc_grpd_carrier $n $X)
      (@trunc_grpd_carrier $n $Y)
      (@trunc_grpd_carrier $n $Z)
      $g $f;

// Whole inclusion of classified n-types into ambient groupoid/type objects.
injective symbol ntype_include_grpd_func
  (n : TruncLevel)
  : τ (@Functor (@NType_cat n) Grpd_cat);

// The inclusion exposes the retained package carrier on objects.
rule @fapp0 _ _ (@ntype_include_grpd_func $n) $X
  ↪ @trunc_grpd_carrier $n $X;

// Readable decoding of a classified n-type to its ambient carrier.
symbol ElNType
  [n : TruncLevel]
  (X : τ (Obj (@NType_cat n)))
  : Grpd
≔ @trunc_grpd_carrier n X;

/*
  Classified truncation reflector.

  The primitive result is a code in NType_cat(n), not an ambient Grpd later
  paired with evidence. Its carrier and evidence project to stable owners.
*/
injective symbol Trunc_grpd
  (n : TruncLevel)
  (A : Grpd)
  : Grpd;

injective symbol Trunc_ntype
  (n : TruncLevel)
  (A : Grpd)
  : τ (Obj (@NType_cat n));

constant symbol trunc_ntype_is_truncated
  (n : TruncLevel)
  (A : Grpd)
  : τ (IsTruncGrpd n (@Trunc_grpd n A));

// Decoding the classified result exposes its stable ambient carrier.
rule @trunc_grpd_carrier $n (@Trunc_ntype $n $A)
  ↪ @Trunc_grpd $n $A;

// The existing package-evidence projection retains the reflector evidence.
rule @trunc_grpd_evidence $n (@Trunc_ntype $n $A)
  ↪ @trunc_ntype_is_truncated $n $A;

// Point constructor of the classified truncation.
injective symbol trunc_intro
  [n : TruncLevel]
  [A : Grpd]
  (a : τ A)
  : τ (@Trunc_grpd n A);

/*
  Intrinsic restricted induction. The motive lands directly in NType_cat(n),
  so no separate admissibility proof can be forgotten or mismatched.
*/
injective symbol trunc_ind
  [n : TruncLevel]
  [A : Grpd]
  (P : τ (@Trunc_grpd n A) → τ (Obj (@NType_cat n)))
  (d : Π a : τ A,
    τ (@ElNType n (P (@trunc_intro n A a))))
  (z : τ (@Trunc_grpd n A))
  : τ (@ElNType n (P z));

// Point-constructor beta is the selected runtime computation.
rule @trunc_ind $n $A _ $d (@trunc_intro $n $A $a)
  ↪ $d $a;

/*
  Transparent ambient convenience induction. It merely packages each fibre
  with the supplied evidence and reduces through the intrinsic eliminator.
*/
symbol trunc_ind_ambient
  [n : TruncLevel]
  [A : Grpd]
  (D : τ (@Trunc_grpd n A) → Grpd)
  (hD : Π z : τ (@Trunc_grpd n A),
    τ (IsTruncGrpd n (D z)))
  (d : Π a : τ A,
    τ (D (@trunc_intro n A a)))
  (z : τ (@Trunc_grpd n A))
  : τ (D z)
≔ @trunc_ind
    n A
    (λ z : τ (@Trunc_grpd n A),
      @Struct_trunc_grpd n (D z) (hD z))
    d z;

// Nondependent recursion into an already classified n-type.
symbol trunc_rec
  [n : TruncLevel]
  [A : Grpd]
  (B : τ (Obj (@NType_cat n)))
  (d : τ A → τ (@ElNType n B))
  (z : τ (@Trunc_grpd n A))
  : τ (@ElNType n B)
≔ @trunc_ind
    n A
    (λ _ : τ (@Trunc_grpd n A), B)
    d z;

// Ambient nondependent recursion, still requiring explicit n-truncation.
symbol trunc_rec_ambient
  [n : TruncLevel]
  [A B : Grpd]
  (hB : τ (IsTruncGrpd n B))
  (d : τ A → τ B)
  (z : τ (@Trunc_grpd n A))
  : τ B
≔ @trunc_ind_ambient
    n A
    (λ _ : τ (@Trunc_grpd n A), B)
    (λ _ : τ (@Trunc_grpd n A), hB)
    d z;

/*
  Functorial action derived from the restricted recursor.

  The deliberately weak same-level path bound lets induction prove the map
  laws uniformly at every truncation level. No proof erasure is involved.
*/
symbol SameLevelPathTruncClosure
  (n : TruncLevel)
  : Grpd
≔ @Pi_grpd Grpd_grpd
    (λ A : Grpd,
      @Function_grpd
        (IsTruncGrpd n A)
        (@Pi_grpd A
          (λ x : τ A,
            @Pi_grpd A
              (λ y : τ A,
                IsTruncGrpd n (@= A x y)))));

symbol is_trunc_path_same_level
  (n : TruncLevel)
  : τ (@SameLevelPathTruncClosure n)
≔ @ind_TruncLevel
    (λ n : TruncLevel, @SameLevelPathTruncClosure n)
    (λ A : Grpd,
      λ h : τ (IsTruncGrpd trunc_minus_two A),
      λ x : τ A,
      λ y : τ A,
        @is_contr_is_prop A h x y)
    (λ n : TruncLevel,
      λ _ : τ (@SameLevelPathTruncClosure n),
      λ A : Grpd,
      λ h : τ (IsTruncGrpd (trunc_succ n) A),
      λ x : τ A,
      λ y : τ A,
        @is_trunc_grpd_succ n (@= A x y) (h x y))
    n;

// Pointwise map, transparently derived by recursion into Trunc_ntype(n,B).
symbol trunc_map
  [n : TruncLevel]
  [A B : Grpd]
  (f : τ (@Function_grpd A B))
  (z : τ (@Trunc_grpd n A))
  : τ (@Trunc_grpd n B)
≔ @trunc_rec
    n A
    (@Trunc_ntype n B)
    (λ a : τ A, @trunc_intro n B (f a))
    z;

// The entire recursor-derived map family between function spaces.
symbol trunc_map_family
  [n : TruncLevel]
  (A B : Grpd)
  : τ (@Function_grpd
      (@Function_grpd A B)
      (@Function_grpd (@Trunc_grpd n A) (@Trunc_grpd n B)))
≔ λ f : τ (@Function_grpd A B),
    λ z : τ (@Trunc_grpd n A),
      @trunc_map n A B f z;

/*
  Whole Hom action. Since both ambient Hom categories are Path categories,
  the existing path_map_func supplies equality action and every next hom.
*/
symbol trunc_map_func
  [n : TruncLevel]
  (A B : Grpd)
  : τ (@Functor
      (Hom_cat Grpd_cat A B)
      (Hom_cat
        (@NType_cat n)
        (@Trunc_ntype n A)
        (@Trunc_ntype n B)))
≔ @path_map_func
    (@Function_grpd A B)
    (@Function_grpd (@Trunc_grpd n A) (@Trunc_grpd n B))
    (@trunc_map_family n A B);

// Pointwise identity law, proved by restricted induction into a path family.
symbol trunc_map_id_point_path
  [n : TruncLevel]
  [A : Grpd]
  (z : τ (@Trunc_grpd n A))
  : τ (@=
      (@Trunc_grpd n A)
      (@trunc_map n A A (@grpd_id_function A) z)
      z)
≔ @trunc_ind_ambient
    n A
    (λ z : τ (@Trunc_grpd n A),
      @= (@Trunc_grpd n A)
        (@trunc_map n A A (@grpd_id_function A) z)
        z)
    (λ z : τ (@Trunc_grpd n A),
      @is_trunc_path_same_level
        n
        (@Trunc_grpd n A)
        (@trunc_ntype_is_truncated n A)
        (@trunc_map n A A (@grpd_id_function A) z)
        z)
    (λ a : τ A,
      @eq_refl (@Trunc_grpd n A) (@trunc_intro n A a))
    z;

// Whole identity law between the induced functions.
symbol trunc_map_id_path
  [n : TruncLevel]
  (A : Grpd)
  : τ (@=
      (@Function_grpd (@Trunc_grpd n A) (@Trunc_grpd n A))
      (λ z : τ (@Trunc_grpd n A),
        @trunc_map n A A (@grpd_id_function A) z)
      (λ z : τ (@Trunc_grpd n A), z))
≔ @PiFunext
    (@Trunc_grpd n A)
    (λ _ : τ (@Trunc_grpd n A), @Trunc_grpd n A)
    (λ z : τ (@Trunc_grpd n A),
      @trunc_map n A A (@grpd_id_function A) z)
    (λ z : τ (@Trunc_grpd n A), z)
    (λ z : τ (@Trunc_grpd n A),
      @trunc_map_id_point_path n A z);

// Pointwise composition law, again derived by restricted induction.
symbol trunc_map_comp_point_path
  [n : TruncLevel]
  [A B C : Grpd]
  (g : τ (@Function_grpd B C))
  (f : τ (@Function_grpd A B))
  (z : τ (@Trunc_grpd n A))
  : τ (@=
      (@Trunc_grpd n C)
      (@trunc_map n A C (@grpd_comp_function A B C g f) z)
      (@trunc_map n B C g (@trunc_map n A B f z)))
≔ @trunc_ind_ambient
    n A
    (λ z : τ (@Trunc_grpd n A),
      @= (@Trunc_grpd n C)
        (@trunc_map n A C (@grpd_comp_function A B C g f) z)
        (@trunc_map n B C g (@trunc_map n A B f z)))
    (λ z : τ (@Trunc_grpd n A),
      @is_trunc_path_same_level
        n
        (@Trunc_grpd n C)
        (@trunc_ntype_is_truncated n C)
        (@trunc_map n A C (@grpd_comp_function A B C g f) z)
        (@trunc_map n B C g (@trunc_map n A B f z)))
    (λ a : τ A,
      @eq_refl
        (@Trunc_grpd n C)
        (@trunc_intro n C (g (f a))))
    z;

// Whole composition law between the induced functions.
symbol trunc_map_comp_path
  [n : TruncLevel]
  [A B C : Grpd]
  (g : τ (@Function_grpd B C))
  (f : τ (@Function_grpd A B))
  : τ (@=
      (@Function_grpd (@Trunc_grpd n A) (@Trunc_grpd n C))
      (λ z : τ (@Trunc_grpd n A),
        @trunc_map n A C (@grpd_comp_function A B C g f) z)
      (λ z : τ (@Trunc_grpd n A),
        @trunc_map n B C g (@trunc_map n A B f z)))
≔ @PiFunext
    (@Trunc_grpd n A)
    (λ _ : τ (@Trunc_grpd n A), @Trunc_grpd n C)
    (λ z : τ (@Trunc_grpd n A),
      @trunc_map n A C (@grpd_comp_function A B C g f) z)
    (λ z : τ (@Trunc_grpd n A),
      @trunc_map n B C g (@trunc_map n A B f z))
    (λ z : τ (@Trunc_grpd n A),
      @trunc_map_comp_point_path n A B C g f z);

/*
  Classifier-level reflector. Its object action computes, while one path
  selects the recursor-derived whole Hom action. No competing capped runtime
  rule is installed against generic strict functoriality.
*/
injective symbol Truncation_func
  (n : TruncLevel)
  : τ (@Functor Grpd_cat (@NType_cat n));

rule @fapp0 Grpd_cat _ (@Truncation_func $n) $A
  ↪ @Trunc_ntype $n $A;

constant symbol truncation_hom_action
  (n : TruncLevel)
  (A B : Grpd)
  : τ (@=
      (Obj (@Functor_cat
        (Hom_cat Grpd_cat A B)
        (Hom_cat
          (@NType_cat n)
          (@Trunc_ntype n A)
          (@Trunc_ntype n B))))
      (@fapp1_func
        Grpd_cat
        (@NType_cat n)
        (@Truncation_func n)
        A B)
      (@trunc_map_func n A B));
