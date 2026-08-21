/*
  Reviewer for constructive ordinal dependent-simplex dimension four.

  The identity ordinal join supplies one shaped comparison. Two applications
  of the generic PathOut transformation lift make its component at the
  canonical source tetrahedron into the fourth-level cell. The same native
  source maps under every H, while intrinsic FaceCode action exposes all five
  tetrahedral faces without a parallel boundary record.
*/

require open emdash.emdash3_2_dependent_simplex_ordinal_dimension4;

assert ⊢ ordinal_simplex4_target_cat
  ≡ @DirectedSimplex_cat (succ (succ (succ (succ zero))));

// The recursively produced object inhabits the existing native classifier.
assert ⊢ ordinal_dependent_simplex4_source
  : τ (Obj (@DependentSimplex4_cat
      ordinal_simplex4_target_cat ordinal_simplex4_target_y0
      ordinal_simplex4_target_e01 ordinal_simplex4_target_t012
      ordinal_simplex4_target_s0123));

// Its top cell is the constructor component of the second generic lift.
assert ⊢ ordinal_simplex4_omega
  ≡ @pathout_transf_component
      ordinal_simplex4_source_level2 ordinal_simplex4_target_level2
      ordinal_simplex4_left2 ordinal_simplex4_right2
      ordinal_simplex4_epsilon2 ordinal_simplex4_source_t012
      (sigma_Fst ordinal_simplex4_source_s0123)
      (sigma_Snd ordinal_simplex4_source_s0123);

// Arbitrary-target observation uses the existing dimension-four map and is
// simultaneously an object of the mapped intrinsic code.
assert [C : Cat] (H : τ (Functor ordinal_simplex4_target_cat C)) ⊢
  @ordinal_dependent_simplex4_observation C H
  : τ (Obj (@dependent_simplex_code_decode_cat
      C (succ (succ (succ (succ zero))))
      (@ordinal_dependent_simplex4_code C H)));

// All five named cofaces use the one generic FaceCode action.
type λ C : Cat, λ H : τ (Functor ordinal_simplex4_target_cat C),
  @ordinal_dependent_simplex4_face0123 C H;

type λ C : Cat, λ H : τ (Functor ordinal_simplex4_target_cat C),
  @ordinal_dependent_simplex4_face0124 C H;

type λ C : Cat, λ H : τ (Functor ordinal_simplex4_target_cat C),
  @ordinal_dependent_simplex4_face0134 C H;

type λ C : Cat, λ H : τ (Functor ordinal_simplex4_target_cat C),
  @ordinal_dependent_simplex4_face0234 C H;

type λ C : Cat, λ H : τ (Functor ordinal_simplex4_target_cat C),
  @ordinal_dependent_simplex4_face1234 C H;

// Native source/target/base projections and the final readable frame remain
// available alongside the code-selected whole faces.
type λ C : Cat, λ H : τ (Functor ordinal_simplex4_target_cat C),
  @ordinal_dependent_simplex4_s0123 C H;

type λ C : Cat, λ H : τ (Functor ordinal_simplex4_target_cat C),
  @ordinal_dependent_simplex4_s0124 C H;

type λ C : Cat, λ H : τ (Functor ordinal_simplex4_target_cat C),
  @ordinal_dependent_simplex4_theta0134 C H;

type λ C : Cat, λ H : τ (Functor ordinal_simplex4_target_cat C),
  @ordinal_dependent_simplex4_readable_cell C H;

type λ C : Cat, λ H : τ (Functor ordinal_simplex4_target_cat C),
  @ordinal_dependent_simplex4_top_component C H;

// Selected strict and exact Path targets reuse the same observation.
type λ C : Cat,
  λ S : τ (@StrictFunctorData ordinal_simplex4_target_cat C),
    @ordinal_dependent_simplex4_observation
      C (@strict_functor_carrier ordinal_simplex4_target_cat C S);

type λ A : Grpd,
  λ H : τ (Functor ordinal_simplex4_target_cat (Path_cat A)),
    @ordinal_dependent_simplex4_top_component (Path_cat A) H;

// The recursive construction remains iterable one dimension higher.
type λ u : τ (Obj ordinal_simplex4_source_level3),
  λ v : τ (Obj ordinal_simplex4_source_level3),
    @ordinal_simplex4_top_next_action u v;

// A wrong recursive source tetrahedron cannot replace the mapped source.
assertnot [C : Cat]
  (H : τ (Functor ordinal_simplex4_target_cat C))
  (wrong : τ (Obj (@DependentSimplex3_cat
    C (@ordinal_dependent_simplex4_x0 C H)
    (@ordinal_dependent_simplex4_e01 C H)
    (@ordinal_dependent_simplex4_t012 C H)))) ⊢
  @ordinal_dependent_simplex4_omega C H
  : τ (Hom
      (@DependentSimplex3_cat
        C (@ordinal_dependent_simplex4_x0 C H)
        (@ordinal_dependent_simplex4_e01 C H)
        (@ordinal_dependent_simplex4_t012 C H))
      wrong (@ordinal_dependent_simplex4_s0124 C H));

// The mapped fourth-level cell does not collapse to arbitrary replacement.
assertnot [C : Cat]
  (H : τ (Functor ordinal_simplex4_target_cat C))
  (replacement : τ (Hom
    (@DependentSimplex3_cat
      C (@ordinal_dependent_simplex4_x0 C H)
      (@ordinal_dependent_simplex4_e01 C H)
      (@ordinal_dependent_simplex4_t012 C H))
    (@ordinal_dependent_simplex4_s0123 C H)
    (@ordinal_dependent_simplex4_s0124 C H))) ⊢
  @ordinal_dependent_simplex4_omega C H ≡ replacement;
