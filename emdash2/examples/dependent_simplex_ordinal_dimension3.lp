/*
  Reviewer for the constructive ordinal dependent tetrahedron.

  One canonical source is mapped under arbitrary H.  Its four faces and top
  component are projections from the same native `DependentSimplex3_cat`
  object, and the originating whole laxity action remains iterable.
*/

require open emdash.emdash3_2_dependent_simplex_ordinal_dimension3;
require open emdash.emdash3_2_gray_profiles;

// The source is a genuine native tetrahedron, not an opaque filler package.
type ordinal_dependent_simplex3_source;
type ordinal_simplex3_theta;
type ordinal_simplex3_top_cell_reframed;

// Arbitrary target functors use the existing whole native map.
type λ C : Cat,
  λ H : τ (Functor ordinal_simplex3_target_cat C),
    @ordinal_dependent_simplex3_map C H;

type λ C : Cat,
  λ H : τ (Functor ordinal_simplex3_target_cat C),
    @ordinal_dependent_simplex3_observation C H;

// All four canonical faces and the top dependent component are unconditional.
type λ C : Cat,
  λ H : τ (Functor ordinal_simplex3_target_cat C),
    @ordinal_dependent_simplex3_face012 C H;

type λ C : Cat,
  λ H : τ (Functor ordinal_simplex3_target_cat C),
    @ordinal_dependent_simplex3_face013 C H;

type λ C : Cat,
  λ H : τ (Functor ordinal_simplex3_target_cat C),
    @ordinal_dependent_simplex3_face023 C H;

type λ C : Cat,
  λ H : τ (Functor ordinal_simplex3_target_cat C),
    @ordinal_dependent_simplex3_face123 C H;

type λ C : Cat,
  λ H : τ (Functor ordinal_simplex3_target_cat C),
    @ordinal_dependent_simplex3_top_component C H;

// The native theta base is the represented 023 face, while the public 023
// face is obtained by the promoted whole target-line functor.
type λ C : Cat,
  λ H : τ (Functor ordinal_simplex3_target_cat C),
    @ordinal_dependent_simplex3_theta_base C H;

// A wrong final base face cannot be substituted for the theta-owned base.
assertnot [C : Cat]
  (H : τ (Functor ordinal_simplex3_target_cat C))
  (wrong : τ (Hom
    (@DependentSimplex1_cat C (@ordinal_dependent_simplex3_y0 C H))
    (@ordinal_dependent_simplex3_e02 C H)
    (@ordinal_dependent_simplex3_e03 C H))) ⊢
  @ordinal_dependent_simplex3_top_component C H
  : τ (Obj (Fibre_cat
      (@homd_
        (@DependentSimplex1_cat C (@ordinal_dependent_simplex3_y0 C H))
        (@Rep_catd
          (@DependentSimplex1_cat C (@ordinal_dependent_simplex3_y0 C H))
          (@ordinal_dependent_simplex3_e01 C H))
        (@Rep_catd
          (@DependentSimplex1_cat C (@ordinal_dependent_simplex3_y0 C H))
          (@ordinal_dependent_simplex3_e01 C H))
        (@id_funcd
          (@DependentSimplex1_cat C (@ordinal_dependent_simplex3_y0 C H))
          (@Rep_catd
            (@DependentSimplex1_cat C (@ordinal_dependent_simplex3_y0 C H))
            (@ordinal_dependent_simplex3_e01 C H)))
        (@ordinal_dependent_simplex3_e02 C H)
        (@ordinal_dependent_simplex3_q012 C H)
        (@ordinal_dependent_simplex3_e03 C H)
        (@ordinal_dependent_simplex3_q013 C H))
      wrong));

// Historical strict endpoint conversion does not collapse the extracted
// laxity witness itself to identity.
assertnot ⊢
  ordinal_simplex3_top_cell
  ≡ @id
      (Hom_cat ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_e01 ordinal_simplex3_e03)
      ordinal_simplex3_top_source;

// A selected strict profile uses the same observation without a second
// simplex implementation.
type λ C : Cat,
  λ S : τ (@StrictFunctorData ordinal_simplex3_target_cat C),
    @ordinal_dependent_simplex3_observation
      C (@strict_functor_carrier ordinal_simplex3_target_cat C S);

// The same native tetrahedron specializes without extra data to a Path
// target.  Its final component deliberately remains under the recursive
// `homd_`/PathOut owner here; `dependent_simplex_profiles.lp` separately
// checks that the generic recursive tetrahedron component is an equality,
// with `eq_sym` inverse, whenever its target fibre is visibly a Path category.
type λ A : Grpd,
  λ H : τ (Functor ordinal_simplex3_target_cat (Path_cat A)),
    @ordinal_dependent_simplex3_top_component (Path_cat A) H;

// The action from which the tetrahedron was projected remains whole one
// dimension higher.
type λ u : τ (Obj (Hom_cat ordinal_simplex3_source_pathout_cat
      ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj)),
  λ v : τ (Obj (Hom_cat ordinal_simplex3_source_pathout_cat
      ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj)),
    @ordinal_simplex3_top_next_action u v;
