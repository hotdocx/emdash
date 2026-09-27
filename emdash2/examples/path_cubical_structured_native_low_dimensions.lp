/* Reviewer example: low-dimensional structured/native cube comparison. */

require open emdash.emdash3_2_path_cubical_structured_native_low_dimensions;

// The generic successor decoder specializes internally through dimension two.
assert [A : Grpd]
  (x : τ A) ⊢
  @path_structured_native_decode0 A x
  : τ (@StructuredPathCubeRec_grpd A zero);

assert [A : Grpd]
  (X : τ (@PathCube_grpd A (succ zero))) ⊢
  @path_structured_native_decode1 A X
  : τ (@StructuredPathCubeRec_grpd A (succ zero));

assert [A : Grpd]
  (S : τ (@PathCube_grpd A (succ (succ zero)))) ⊢
  @path_structured_native_decode2 A S
  : τ (@StructuredPathCubeRec_grpd A (succ (succ zero)));

// Pointwise readback is constructed at levels zero and one.  A level-two
// readback is an explicit input to the conditional dimension-three decoder.
assert (A : Grpd) ⊢
  @path_cube_readback0 A
  : τ (@PathCubeReadback_grpd A zero);

assert (A : Grpd) ⊢
  @path_cube_readback1 A
  : τ (@PathCubeReadback_grpd A (succ zero));

assert [A : Grpd]
  (read2 : τ (@PathCubeReadback_grpd A (succ (succ zero))))
  (Z : τ (@PathCube_grpd A (succ (succ (succ zero))))) ⊢
  @path_structured_native_decode3_with_readback A read2 Z
  : τ (@StructuredPathCubeRec_grpd A (succ (succ (succ zero))));

// Dimension zero computes in the native direction and has a structured
// propositional round trip.
assert [A : Grpd]
  (x : τ A) ⊢
  (@path_structured_path_cube_realize_function A zero)
    (@path_structured_native_decode0 A x)
  ≡ x;

assert [A : Grpd]
  (z : τ (@StructuredPathCubeRec_grpd A zero)) ⊢
  @path_structured_native_decode0_realize_path A z
  : τ (@=
      (@StructuredPathCubeRec_grpd A zero)
      (@path_structured_native_decode0
        A ((@path_structured_path_cube_realize_function A zero) z))
      z);

// Every native path edge is recovered after decoding and realization.
assert [A : Grpd]
  (X : τ (@PathCube_grpd A (succ zero))) ⊢
  @path_structured_native_decode1_realize_all_path A X
  : τ (@=
      (@PathCube_grpd A (succ zero))
      ((@path_structured_path_cube_realize_function A (succ zero))
        (@path_structured_native_decode1 A X))
      X);

// No dimension-two readback, pointwise re-inclusion law, or whole native-Hom
// functor is asserted here.  A typed attempted derivation reaches the missing
// constructor-visible cubical identity comparison before higher action and
// pasting can be assembled.
type @structured_step_decode;
type @PathCubeReadback_grpd;
type @path_structured_native_decode2;
type @path_structured_native_decode3_with_readback;
