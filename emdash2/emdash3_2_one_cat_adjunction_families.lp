/* Ordinary-target postcomposition of an existing adjunction.
   The current Adjunction classifier has no unit/counit introduction rule;
   this is an explicit structural presentation operation. It is not derived
   from the current β interface or an axiom for Coim⇒Im/exactness.
   Its component observations reuse the original unit/counit by whiskering. */
require open emdash.emdash3_2_adjunction_mates;

// Ordinary functor-category profile inherited from its ordinary target.
constant symbol one_cat_functor_category [B C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  : τ (IsNCat (cat_succ cat_zero) (Functor_cat B C));

// F⊣G induces (F∘−)⊣(G∘−), with no newly selected functors.
injective symbol one_cat_postcomp_adjunction [B R L : Cat]
  (R1 : τ (IsNCat (cat_succ cat_zero) R))
  (L1 : τ (IsNCat (cat_succ cat_zero) L))
  [F : τ (Functor R L)] [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G))
  : τ (@Adjunction (Functor_cat B R) (Functor_cat B L)
      (@comp_cat_cov_func B R L F) (@comp_cat_cov_func B L R G));

// Whole unit/counit observations through existing tele-postcomposition.
// Their components and further Hom action use that same inherited owner.
rule @unit_adj_transf _ _ _ _
      (@one_cat_postcomp_adjunction $B $R $L _ _ $F $G $J)
  ↪ @comp_cat_cov_func_func_transf $B $R $R (@id_func $R)
      (@comp_cat_fapp0 $R $L $R $G $F)
      (@unit_adj_transf $R $L $F $G $J);
rule @counit_adj_transf _ _ _ _
      (@one_cat_postcomp_adjunction $B $R $L _ _ $F $G $J)
  ↪ @comp_cat_cov_func_func_transf $B $L $L
      (@comp_cat_fapp0 $L $R $L $F $G) (@id_func $L)
      (@counit_adj_transf $R $L $F $G $J);

// Whole family mate functor from the existing Hom comparison.
// Retain native postcomposition endpoints: their raw-composition readings
// are proof-time views, not the runtime source/target of the inverse cuts.
symbol one_cat_adjunction_family_transpose_func [B R L : Cat]
  (R1 : τ (IsNCat (cat_succ cat_zero) R))
  (L1 : τ (IsNCat (cat_succ cat_zero) L))
  [F : τ (Functor R L)] [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G))
  (A : τ (Functor B R)) (D : τ (Functor B L))
  : τ (Functor
      (Hom_cat (Functor_cat B L) (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D)
      (Hom_cat (Functor_cat B R) A (@fapp0 _ _ (@comp_cat_cov_func B L R G) D)))
≔ @adjunction_transpose_func (Functor_cat B R) (Functor_cat B L)
    (@comp_cat_cov_func B R L F) (@comp_cat_cov_func B L R G)
    (@one_cat_postcomp_adjunction B R L R1 L1 F G J) A D;

// Its inverse is the projection of that same existing comparison.
symbol one_cat_adjunction_family_untranspose_func [B R L : Cat]
  (R1 : τ (IsNCat (cat_succ cat_zero) R))
  (L1 : τ (IsNCat (cat_succ cat_zero) L))
  [F : τ (Functor R L)] [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G))
  (A : τ (Functor B R)) (D : τ (Functor B L))
  : τ (Functor
      (Hom_cat (Functor_cat B R) A (@fapp0 _ _ (@comp_cat_cov_func B L R G) D))
      (Hom_cat (Functor_cat B L) (@fapp0 _ _ (@comp_cat_cov_func B R L F) A) D))
≔ @adjunction_untranspose_func (Functor_cat B R) (Functor_cat B L)
    (@comp_cat_cov_func B R L F) (@comp_cat_cov_func B L R G)
    (@one_cat_postcomp_adjunction B R L R1 L1 F G J) A D;
