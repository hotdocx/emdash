/*
  Focused reviewer for variable-dimension coherent-nerve levels.

  Ordinary dimensions 0--3 compute to the expected mapping categories.  The
  augmented shape keeps its empty level distinct, and all transfor action is
  inherited from the existing iterable Functor-category owner.
*/

require open emdash.emdash3_2_coherent_nerve_levels;

assert ⊢
  @AugmentedDirectedSimplex_cat zero
  ≡ Path_cat Empty_grpd;

assert (n : τ Nat_grpd) ⊢
  @AugmentedDirectedSimplex_cat (succ n)
  ≡ @DirectedSimplex_cat n;

assert (C : Cat) ⊢
  @CoherentNerveLevel_cat C zero
  ≡ @Functor_cat Terminal_cat C;

assert (C : Cat) ⊢
  @CoherentNerveLevel_cat C (succ zero)
  ≡ @Functor_cat WalkingArrow_cat C;

assert (C : Cat) ⊢
  @CoherentNerveLevel_cat C (succ (succ zero))
  ≡ @Functor_cat
      (@Join_cat WalkingArrow_cat Terminal_cat)
      C;

assert (C : Cat) ⊢
  @CoherentNerveLevel_cat C (succ (succ (succ zero)))
  ≡ @Functor_cat
      (@Join_cat
        (@Join_cat WalkingArrow_cat Terminal_cat)
        Terminal_cat)
      C;

assert (C : Cat) ⊢
  @AugmentedCoherentNerveLevel_cat C zero
  ≡ @Functor_cat (Path_cat Empty_grpd) C;

assert (C : Cat) (n : τ Nat_grpd)
  (F G : τ (Obj (@CoherentNerveLevel_cat C n))) ⊢
  Hom_cat (@CoherentNerveLevel_cat C n) F G
  ≡ @Transf_cat (@DirectedSimplex_cat n) C F G;

// The generic off-diagonal transfor action remains available at every level.
assert [C : Cat] [n : τ Nat_grpd]
  [F G : τ (Obj (@CoherentNerveLevel_cat C n))]
  (epsilon : τ (Obj (@Transf_cat (@DirectedSimplex_cat n) C F G)))
  (X Y : τ (Obj (@DirectedSimplex_cat n))) ⊢
  @tapp1_func
    (@DirectedSimplex_cat n) C F G X Y epsilon
  : τ (Functor
      (Hom_cat (@DirectedSimplex_cat n) X Y)
      (Hom_cat C
        (@fapp0 (@DirectedSimplex_cat n) C F X)
        (@fapp0 (@DirectedSimplex_cat n) C G Y)));

// Dimension and vertex-count conventions are not silently identified.
assertnot ⊢
  @AugmentedDirectedSimplex_cat zero
  ≡ @DirectedSimplex_cat zero;
