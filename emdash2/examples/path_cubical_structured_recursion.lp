/* Reviewer example: Nat-recursive structured cubes and new-left filling. */

require open emdash.emdash3_2_path_cubical_structured_recursion;

// The internal boundary/filler specification computes by Nat recursion.
assert [A : Grpd] ⊢
  @path_cube_spec A zero
  ≡ @path_cube_spec_base A;

assert [A : Grpd]
  (n : τ Nat_grpd) ⊢
  @path_cube_spec A (succ n)
  ≡ @path_cube_spec_step (@path_cube_spec A n);

// One structured new-left open box exists at every successor dimension.
assert [A : Grpd]
  (n : τ Nat_grpd)
  (box : τ (@StructuredOpenBoxNewLeft_grpd (@path_cube_spec A n))) ⊢
  @path_structured_open_box_new_left_fill
    (@path_cube_spec A n) box
  : τ (@StructuredPathCubeRec_grpd A (succ n));

// Filling is an algebraic section in the structured presentation.
assert [A : Grpd]
  (n : τ Nat_grpd)
  (box : τ (@StructuredOpenBoxNewLeft_grpd (@path_cube_spec A n))) ⊢
  @path_structured_open_box_new_left_section
    (@path_cube_spec A n) box
  : τ (@=
      (@StructuredOpenBoxNewLeft_grpd (@path_cube_spec A n))
      (@path_structured_open_box_new_left_restrict
        (@path_cube_spec A n)
        (@path_structured_open_box_new_left_fill
          (@path_cube_spec A n) box))
      box);

// Nat-recursive realization reaches the existing native path-cubical tower.
assert [A : Grpd]
  (n : τ Nat_grpd) ⊢
  @path_structured_path_cube_realize_function A n
  : τ (@Function_grpd
      (@StructuredPathCubeRec_grpd A n)
      (@PathCube_grpd A n));

assert [A : Grpd]
  (n : τ Nat_grpd)
  (box : τ (@StructuredOpenBoxNewLeft_grpd (@path_cube_spec A n))) ⊢
  @path_structured_open_box_new_left_native_fill A n box
  : τ (@PathCube_grpd A (succ n));

// The same interface reaches the dimension-three native acceptance level.
assert [A : Grpd]
  (box : τ (@StructuredOpenBoxNewLeft_grpd
    (@path_cube_spec A (succ (succ zero))))) ⊢
  @path_structured_open_box_new_left_native_fill
    A (succ (succ zero)) box
  : τ (@PathCube_grpd A (succ (succ (succ zero))));

// The result is intentionally one-way: no arbitrary native-cube restriction
// is claimed without inverse realization/groupoidality.
assertnot [A : Grpd]
  (n : τ Nat_grpd)
  (cube : τ (@PathCube_grpd A (succ n))) ⊢
  @path_structured_open_box_new_left_restrict
    (@path_cube_spec A n) cube
  : τ (@StructuredOpenBoxNewLeft_grpd (@path_cube_spec A n));

type @PathCubeSpecU;
type @StructuredPathCubeRec_grpd;
type @path_structured_open_box_new_left_native_fill;
