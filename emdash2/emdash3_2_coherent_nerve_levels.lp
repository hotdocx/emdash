/*
  Variable-dimension coherent-nerve levels.

  `CoherentNerveLevel_cat(C,n)` is the whole mapping category [n] -> C.
  The separate augmented shape uses the empty path category at vertex count
  zero and recovers `DirectedSimplex_cat(n)` at successor vertex count.  This
  provides the level classifier needed by a future nerve without claiming a
  face action or a functor on the semisimplex category.

  All mapping-category hom and higher action remain at the existing
  Functor/Transf owners.  This module adds no rewrite rule, unifier, generic
  face realization, recursive-cell comparison, degeneracy, or Kan claim.
*/

require open emdash.emdash3_2_simplex_shapes;

// Augmented vertex-count shape: empty at zero, ordinary [n] at succ n.
symbol AugmentedDirectedSimplex_cat
  (m : τ Nat_grpd)
  : Cat
≔ @nat_elim
    (λ _ : τ Nat_grpd, Obj Cat_cat)
    (Path_cat Empty_grpd)
    (λ n : τ Nat_grpd,
      λ _ : τ (Obj Cat_cat),
        @DirectedSimplex_cat n)
    m;

// Ordinary dimension-n candidate nerve level.
symbol CoherentNerveLevel_cat
  (C : Cat)
  (n : τ Nat_grpd)
  : Cat
≔ @Functor_cat (@DirectedSimplex_cat n) C;

// The same level indexed by augmented vertex count.
symbol AugmentedCoherentNerveLevel_cat
  (C : Cat)
  (m : τ Nat_grpd)
  : Cat
≔ @Functor_cat (@AugmentedDirectedSimplex_cat m) C;
