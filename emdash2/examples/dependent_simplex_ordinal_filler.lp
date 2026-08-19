/* Reviewer for the constructed canonical ordinal dimension-two filler. */

require open emdash.emdash3_2_dependent_simplex_ordinal_filler;

// The source filler is the naturality cell of one profiled whole join cross,
// conjugated only at its two selected edge endpoints.
type @ordinal_simplex2_source_canonical_filler;

// Every ordinal triangle now has a canonical filler and an unconditional
// intrinsic observation.
type λ C : Cat,
  λ H : τ (Functor (@DirectedSimplex_cat (succ (succ zero))) C),
    @ordinal_dependent_simplex2_canonical_filler C H;

type λ C : Cat,
  λ H : τ (Functor (@DirectedSimplex_cat (succ (succ zero))) C),
    @ordinal_dependent_simplex2_observe_canonical C H;

// The public code records edge 01 as its intrinsic flag.
assert [C : Cat]
  (H : τ (Functor (@DirectedSimplex_cat (succ (succ zero))) C)) ⊢
  sigma_Fst (@ordinal_dependent_simplex2_observe_canonical C H)
  ≡ @dependent_simplex_code2
      C
      (@ordinal_simplex1_source C (@ordinal_simplex2_edge01 C H))
      (@dependent_simplex1
        C
        (@ordinal_simplex1_source C (@ordinal_simplex2_edge01 C H))
        (@ordinal_simplex1_target C (@ordinal_simplex2_edge01 C H))
        (@ordinal_simplex1_arrow C (@ordinal_simplex2_edge01 C H)));

// The visible 02 and 12 faces are the already-normalized selected edges.
assert [C : Cat]
  (H : τ (Functor (@DirectedSimplex_cat (succ (succ zero))) C)) ⊢
  sigma_Fst (sigma_Snd
    (@ordinal_dependent_simplex2_observe_canonical C H))
  ≡ @dependent_simplex1
      C
      (@ordinal_simplex1_source C (@ordinal_simplex2_edge01 C H))
      (@ordinal_simplex1_target C (@ordinal_simplex2_edge02 C H))
      (@ordinal_simplex2_edge02_normalized
        C H (@ordinal_dependent_simplex2_compatibility C H));

assert [C : Cat]
  (H : τ (Functor (@DirectedSimplex_cat (succ (succ zero))) C)) ⊢
  sigma_Fst (sigma_Snd (sigma_Snd
    (@ordinal_dependent_simplex2_observe_canonical C H)))
  ≡ @ordinal_simplex2_edge12_normalized
      C H (@ordinal_dependent_simplex2_compatibility C H);

// The top component is the constructed filler, not an extra argument.
assert [C : Cat]
  (H : τ (Functor (@DirectedSimplex_cat (succ (succ zero))) C)) ⊢
  sigma_Snd (sigma_Snd (sigma_Snd
    (@ordinal_dependent_simplex2_observe_canonical C H)))
  ≡ @ordinal_dependent_simplex2_canonical_filler C H;

// The filler is literally the top projection of the mapped source simplex.
assert [C : Cat]
  (H : τ (Functor (@DirectedSimplex_cat (succ (succ zero))) C)) ⊢
  @ordinal_dependent_simplex2_canonical_filler C H
  ≡ sigma_Snd (sigma_Snd
      (@ordinal_dependent_simplex2_mapped_native C H));

// A wrong final base edge is rejected.
assertnot [C : Cat]
  (H : τ (Functor (@DirectedSimplex_cat (succ (succ zero))) C))
  (wrong : τ (Hom C
    (@ordinal_simplex1_target C (@ordinal_simplex2_edge01 C H))
    (@ordinal_simplex1_target C (@ordinal_simplex2_edge02 C H)))) ⊢
  @ordinal_dependent_simplex2_canonical_filler C H
  : τ (Obj (Fibre_cat
      (@DependentTriangle_catd
        C
        (@Rep_catd C
          (@ordinal_simplex1_source C (@ordinal_simplex2_edge01 C H)))
        (@ordinal_simplex1_target C (@ordinal_simplex2_edge01 C H))
        (@ordinal_simplex1_arrow C (@ordinal_simplex2_edge01 C H))
        (@ordinal_simplex1_target C (@ordinal_simplex2_edge02 C H))
        (@ordinal_simplex2_edge02_normalized
          C H (@ordinal_dependent_simplex2_compatibility C H)))
      wrong));

// In a Path target the generic directed filler is an equality and therefore
// has the canonical inverse supplied by eq_sym.
type λ A : Grpd,
  λ H : τ (Functor
    (@DirectedSimplex_cat (succ (succ zero))) (Path_cat A)),
    @eq_sym _ _ _
      (@ordinal_dependent_simplex2_canonical_filler (Path_cat A) H);

// The selected strict profile uses the same construction; only its already-
// justified compositor cells collapse.
type λ C : Cat,
  λ S : τ (@StrictFunctorData
    (@DirectedSimplex_cat (succ (succ zero))) C),
    @ordinal_dependent_simplex2_canonical_filler
      C (@strict_functor_carrier
        (@DirectedSimplex_cat (succ (succ zero))) C S);

// The whole native map retains a further hom action for dimension three.
type λ C : Cat,
  λ H : τ (Functor (@DirectedSimplex_cat (succ (succ zero))) C),
    @ordinal_dependent_simplex2_next_func C H;
