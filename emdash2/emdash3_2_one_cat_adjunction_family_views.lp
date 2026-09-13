/* Proof-time views of native whole-family adjunction mates.
   The four comparison helpers preserve the existing runtime owners.
   Congruence is sufficient: corresponding operands and endpoints must
   compare. This does not assert mathematical injectivity of composition.
   Whole formula agreement and reconstruction are derived through the
   original Hom comparison and its same selected inverse. */
require open emdash.emdash3_2_one_cat_adjunction_families;

// Congruence for a pair of Cat horizontal actions in a whole mate formula.
// Both operand heads are guarded so the generic associativity rule remains
// the owner when either operand is itself a vertical composite.
unif_rule @comp_fapp0 (Functor_cat $B $C) $A $D $E
    (@comp_prod_fapp1_fapp0 Cat_cat $Xg $Yg $Zg $pg $qg $g)
    (@comp_prod_fapp1_fapp0 Cat_cat $Xf $Yf $Zf $pf $qf $f)
  ≡ @comp_fapp0 (Functor_cat $B0 $C0) $A0 $D0 $E0
    (@comp_prod_fapp1_fapp0 Cat_cat $Xg0 $Yg0 $Zg0 $pg0 $qg0 $g0)
    (@comp_prod_fapp1_fapp0 Cat_cat $Xf0 $Yf0 $Zf0 $pf0 $qf0 $f0)
  ↪ [ $B ≡ $B0; $C ≡ $C0; $A ≡ $A0; $D ≡ $D0; $E ≡ $E0;
      (@comp_prod_fapp1_fapp0 Cat_cat $Xg $Yg $Zg $pg $qg $g)
        ≡ (@comp_prod_fapp1_fapp0 Cat_cat $Xg0 $Yg0 $Zg0 $pg0 $qg0 $g0);
      (@comp_prod_fapp1_fapp0 Cat_cat $Xf $Yf $Zf $pf $qf $f)
        ≡ (@comp_prod_fapp1_fapp0 Cat_cat $Xf0 $Yf0 $Zf0 $pf0 $qf0 $f0) ];

// Same Cat horizontal-action shape. Every pair and endpoint is compared.
unif_rule @comp_prod_fapp1_fapp0 Cat_cat $B $C $D $fg $fg' $theta
  ≡ @comp_prod_fapp1_fapp0 Cat_cat $B0 $C0 $D0 $hk $hk' $psi
  ↪ [ $B ≡ $B0; $C ≡ $C0; $D ≡ $D0;
      $fg ≡ $hk; $fg' ≡ $hk'; $theta ≡ $psi ];

// Associativity where the inner composite retains its represented owner.
unif_rule @comp_fapp0 Cat_cat $B $L $R $G
    (@hom_postcomp_fapp0 Cat_cat Cat_cat (@id Cat_cat Cat_cat) $B $C $L $F $A)
  ≡ @comp_fapp0 Cat_cat $B $C $R (@comp_fapp0 Cat_cat $C $L $R $G $F) $A
  ↪ [ tt ≡ tt ];

// Companion view: (G∘F)∗X compares with G∘(F∗X), retaining every operand.
unif_rule @hom_postcomp_fapp0 Cat_cat Cat_cat (@id Cat_cat Cat_cat) $B $A $C
    (@comp_fapp0 Cat_cat $A $D $C $G $F) $X
  ≡ @comp_fapp0 Cat_cat $B $D $C $G
    (@hom_postcomp_fapp0 Cat_cat Cat_cat (@id Cat_cat Cat_cat) $B $A $D $F $X)
  ↪ [ tt ≡ tt ];

// Observation of a whole family mate in the original whiskering formula.
symbol one_cat_adjunction_family_transpose_agrees [B R L : Cat]
  (R1 : τ (IsNCat (cat_succ cat_zero) R))
  (L1 : τ (IsNCat (cat_succ cat_zero) L))
  [F : τ (Functor R L)] [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G))
  (A : τ (Functor B R)) (D : τ (Functor B L))
  (h : τ (@Transf B L (@comp_cat_fapp0 B R L F A) D))
  : τ (@= (@Transf B R A (@comp_cat_fapp0 B L R G D))
      (@fapp0 (Hom_cat (Functor_cat B L) (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D) (Hom_cat (Functor_cat B R) A
        (@fapp0 _ _ (@comp_cat_cov_func B L R G) D)) (@one_cat_adjunction_family_transpose_func B R L R1 L1 F G J A D)
        h)
      (@comp_fapp0 (Functor_cat B R) A
        (@comp_cat_fapp0 B L R G (@comp_cat_fapp0 B R L F A))
        (@comp_cat_fapp0 B L R G D)
        (@fapp0 _ _ (@comp_cat_cov_fapp1_func B L R G (@comp_cat_fapp0 B R L F A) D) h)
        (@fapp0 _ _ (@comp_cat_con_fapp1_func B R R A (@id_func R) (@comp_cat_fapp0 R L R G F))
          (@unit_adj_transf R L F G J))))
≔ @eq_ap (Functor (Hom_cat (Functor_cat B L) (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D) (Hom_cat (Functor_cat B R) A
  (@fapp0 _ _ (@comp_cat_cov_func B L R G) D))) (Obj (Hom_cat (Functor_cat B R) A (@fapp0 _ _ (@comp_cat_cov_func B L R
  G) D)))
    (λ M : τ (Functor (Hom_cat (Functor_cat B L) (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D) (Hom_cat (Functor_cat B
      R) A (@fapp0 _ _ (@comp_cat_cov_func B L R G) D))), @fapp0 (Hom_cat (Functor_cat B L) (@fapp0 _ _
      (@comp_cat_cov_func B R L F) A) D) (Hom_cat (Functor_cat B R) A (@fapp0 _ _ (@comp_cat_cov_func B L R G) D)) M h)
    (@one_cat_adjunction_family_transpose_func B R L R1 L1 F G J A D)
    (@adjunction_transpose_semantic_func (Functor_cat B R) (Functor_cat B L)
      (@comp_cat_cov_func B R L F) (@comp_cat_cov_func B L R G)
      (@one_cat_postcomp_adjunction B R L R1 L1 F G J) A D)
    (@adjunction_transpose_semantic_path (Functor_cat B R) (Functor_cat B L)
      (@comp_cat_cov_func B R L F) (@comp_cat_cov_func B L R G)
      (@one_cat_postcomp_adjunction B R L R1 L1 F G J) A D);

// Observation of a whole family mate in the original whiskering formula.
symbol one_cat_adjunction_family_untranspose_agrees [B R L : Cat]
  (R1 : τ (IsNCat (cat_succ cat_zero) R))
  (L1 : τ (IsNCat (cat_succ cat_zero) L))
  [F : τ (Functor R L)] [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G))
  (A : τ (Functor B R)) (D : τ (Functor B L))
  (h : τ (@Transf B R A (@comp_cat_fapp0 B L R G D)))
  : τ (@= (@Transf B L (@comp_cat_fapp0 B R L F A) D)
      (@fapp0 (Hom_cat (Functor_cat B R) A (@fapp0 _ _ (@comp_cat_cov_func B L R G) D)) (Hom_cat (Functor_cat B L)
        (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D) (@one_cat_adjunction_family_untranspose_func B R L R1 L1 F G J A
        D) h)
      (@comp_fapp0 (Functor_cat B L) (@comp_cat_fapp0 B R L F A)
        (@comp_cat_fapp0 B R L F (@comp_cat_fapp0 B L R G D)) D
        (@fapp0 _ _ (@comp_cat_con_fapp1_func B L L D (@comp_cat_fapp0 L R L F G) (@id_func L))
          (@counit_adj_transf R L F G J))
        (@fapp0 _ _ (@comp_cat_cov_fapp1_func B R L F A (@comp_cat_fapp0 B L R G D)) h)))
≔ @eq_ap (Functor (Hom_cat (Functor_cat B R) A (@fapp0 _ _ (@comp_cat_cov_func B L R G) D)) (Hom_cat (Functor_cat B L)
  (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D)) (Obj (Hom_cat (Functor_cat B L) (@fapp0 _ _ (@comp_cat_cov_func B R L
  F) A) D))
    (λ M : τ (Functor (Hom_cat (Functor_cat B R) A (@fapp0 _ _ (@comp_cat_cov_func B L R G) D)) (Hom_cat (Functor_cat B
      L) (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D)), @fapp0 (Hom_cat (Functor_cat B R) A (@fapp0 _ _
      (@comp_cat_cov_func B L R G) D)) (Hom_cat (Functor_cat B L) (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D) M h)
    (@one_cat_adjunction_family_untranspose_func B R L R1 L1 F G J A D)
    (@adjunction_untranspose_semantic_func (Functor_cat B R) (Functor_cat B L)
      (@comp_cat_cov_func B R L F) (@comp_cat_cov_func B L R G)
      (@one_cat_postcomp_adjunction B R L R1 L1 F G J) A D)
    (@adjunction_untranspose_semantic_path (Functor_cat B R) (Functor_cat B L)
      (@comp_cat_cov_func B R L F) (@comp_cat_cov_func B L R G)
      (@one_cat_postcomp_adjunction B R L R1 L1 F G J) A D);

// Whole reconstruction for the raw formula, derived through the same inverse.
symbol one_cat_adjunction_family_transpose_reconstruction [B R L : Cat]
  (R1 : τ (IsNCat (cat_succ cat_zero) R))
  (L1 : τ (IsNCat (cat_succ cat_zero) L))
  [F : τ (Functor R L)] [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G))
  (A : τ (Functor B R)) (D : τ (Functor B L))
  (h : τ (@Transf B L (@comp_cat_fapp0 B R L F A) D))
  : τ (@= (@Transf B L (@comp_cat_fapp0 B R L F A) D) (@fapp0 (Hom_cat (Functor_cat B R) A (@fapp0 _ _
    (@comp_cat_cov_func B L R G) D)) (Hom_cat (Functor_cat B L) (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D)
    (@one_cat_adjunction_family_untranspose_func B R L R1 L1 F G J A D) (@comp_fapp0 (Functor_cat B R) A
        (@comp_cat_fapp0 B L R G (@comp_cat_fapp0 B R L F A))
        (@comp_cat_fapp0 B L R G D)
        (@fapp0 _ _ (@comp_cat_cov_fapp1_func B L R G (@comp_cat_fapp0 B R L F A) D) h)
        (@fapp0 _ _ (@comp_cat_con_fapp1_func B R R A (@id_func R) (@comp_cat_fapp0 R L R G F))
          (@unit_adj_transf R L F G J)))) h)
≔ @eq_sym (Obj (Hom_cat (Functor_cat B L) (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D)) h (@fapp0 (Hom_cat
  (Functor_cat B R) A (@fapp0 _ _ (@comp_cat_cov_func B L R G) D)) (Hom_cat (Functor_cat B L) (@fapp0 _ _
  (@comp_cat_cov_func B R L F) A) D) (@one_cat_adjunction_family_untranspose_func B R L R1 L1 F G J A D) (@comp_fapp0
  (Functor_cat B R) A
        (@comp_cat_fapp0 B L R G (@comp_cat_fapp0 B R L F A))
        (@comp_cat_fapp0 B L R G D)
        (@fapp0 _ _ (@comp_cat_cov_fapp1_func B L R G (@comp_cat_fapp0 B R L F A) D) h)
        (@fapp0 _ _ (@comp_cat_con_fapp1_func B R R A (@id_func R) (@comp_cat_fapp0 R L R G F))
          (@unit_adj_transf R L F G J))))
    (@eq_ap (Obj (Hom_cat (Functor_cat B R) A (@fapp0 _ _ (@comp_cat_cov_func B L R G) D))) (Obj (Hom_cat (Functor_cat B
      L) (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D))
      (λ k : τ (Obj (Hom_cat (Functor_cat B R) A (@fapp0 _ _ (@comp_cat_cov_func B L R G) D))), @fapp0 (Hom_cat
        (Functor_cat B R) A (@fapp0 _ _ (@comp_cat_cov_func B L R G) D)) (Hom_cat (Functor_cat B L) (@fapp0 _ _
        (@comp_cat_cov_func B R L F) A) D) (@one_cat_adjunction_family_untranspose_func B R L R1 L1 F G J A D) k)
      (@fapp0 (Hom_cat (Functor_cat B L) (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D) (Hom_cat (Functor_cat B R) A
        (@fapp0 _ _ (@comp_cat_cov_func B L R G) D)) (@one_cat_adjunction_family_transpose_func B R L R1 L1 F G J A D)
        h) (@comp_fapp0 (Functor_cat B R) A
        (@comp_cat_fapp0 B L R G (@comp_cat_fapp0 B R L F A))
        (@comp_cat_fapp0 B L R G D)
        (@fapp0 _ _ (@comp_cat_cov_fapp1_func B L R G (@comp_cat_fapp0 B R L F A) D) h)
        (@fapp0 _ _ (@comp_cat_con_fapp1_func B R R A (@id_func R) (@comp_cat_fapp0 R L R G F))
          (@unit_adj_transf R L F G J)))
      (@one_cat_adjunction_family_transpose_agrees B R L R1 L1 F G J A D h));

// Whole reconstruction for the raw formula, derived through the same inverse.
symbol one_cat_adjunction_family_untranspose_reconstruction [B R L : Cat]
  (R1 : τ (IsNCat (cat_succ cat_zero) R))
  (L1 : τ (IsNCat (cat_succ cat_zero) L))
  [F : τ (Functor R L)] [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G))
  (A : τ (Functor B R)) (D : τ (Functor B L))
  (h : τ (@Transf B R A (@comp_cat_fapp0 B L R G D)))
  : τ (@= (@Transf B R A (@comp_cat_fapp0 B L R G D)) (@fapp0 (Hom_cat (Functor_cat B L) (@fapp0 _ _ (@comp_cat_cov_func
    B R L F) A) D) (Hom_cat (Functor_cat B R) A (@fapp0 _ _ (@comp_cat_cov_func B L R G) D))
    (@one_cat_adjunction_family_transpose_func B R L R1 L1 F G J A D) (@comp_fapp0 (Functor_cat B L) (@comp_cat_fapp0 B
    R L F A)
        (@comp_cat_fapp0 B R L F (@comp_cat_fapp0 B L R G D)) D
        (@fapp0 _ _ (@comp_cat_con_fapp1_func B L L D (@comp_cat_fapp0 L R L F G) (@id_func L))
          (@counit_adj_transf R L F G J))
        (@fapp0 _ _ (@comp_cat_cov_fapp1_func B R L F A (@comp_cat_fapp0 B L R G D)) h))) h)
≔ @eq_sym (Obj (Hom_cat (Functor_cat B R) A (@fapp0 _ _ (@comp_cat_cov_func B L R G) D))) h (@fapp0 (Hom_cat
  (Functor_cat B L) (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D) (Hom_cat (Functor_cat B R) A (@fapp0 _ _
  (@comp_cat_cov_func B L R G) D)) (@one_cat_adjunction_family_transpose_func B R L R1 L1 F G J A D) (@comp_fapp0
  (Functor_cat B L) (@comp_cat_fapp0 B R L F A)
        (@comp_cat_fapp0 B R L F (@comp_cat_fapp0 B L R G D)) D
        (@fapp0 _ _ (@comp_cat_con_fapp1_func B L L D (@comp_cat_fapp0 L R L F G) (@id_func L))
          (@counit_adj_transf R L F G J))
        (@fapp0 _ _ (@comp_cat_cov_fapp1_func B R L F A (@comp_cat_fapp0 B L R G D)) h)))
    (@eq_ap (Obj (Hom_cat (Functor_cat B L) (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D)) (Obj (Hom_cat (Functor_cat B
      R) A (@fapp0 _ _ (@comp_cat_cov_func B L R G) D)))
      (λ k : τ (Obj (Hom_cat (Functor_cat B L) (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D)), @fapp0 (Hom_cat
        (Functor_cat B L) (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D) (Hom_cat (Functor_cat B R) A (@fapp0 _ _
        (@comp_cat_cov_func B L R G) D)) (@one_cat_adjunction_family_transpose_func B R L R1 L1 F G J A D) k)
      (@fapp0 (Hom_cat (Functor_cat B R) A (@fapp0 _ _ (@comp_cat_cov_func B L R G) D)) (Hom_cat (Functor_cat B L)
        (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D) (@one_cat_adjunction_family_untranspose_func B R L R1 L1 F G J A
        D) h) (@comp_fapp0 (Functor_cat B L) (@comp_cat_fapp0 B R L F A)
        (@comp_cat_fapp0 B R L F (@comp_cat_fapp0 B L R G D)) D
        (@fapp0 _ _ (@comp_cat_con_fapp1_func B L L D (@comp_cat_fapp0 L R L F G) (@id_func L))
          (@counit_adj_transf R L F G J))
        (@fapp0 _ _ (@comp_cat_cov_fapp1_func B R L F A (@comp_cat_fapp0 B L R G D)) h))
      (@one_cat_adjunction_family_untranspose_agrees B R L R1 L1 F G J A D h));
