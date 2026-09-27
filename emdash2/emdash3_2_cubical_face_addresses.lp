/*
  Emdash v3.2: recursive addresses of immediate cubical faces.

  Dimension zero has no address. Every successor adds a new left/right pair
  and lifts every older address. The structural decoder lands in the existing
  public `{L,R,*}` coface codes:

    new-L       |-> L(id),
    new-R       |-> R(id),
    older(face) |-> *(address_code(face)).

  The native indexed code is an internal recursive address language, not a
  flat `Fin(2n)` index or external source generator.
*/

require open emdash.emdash3_2_semicubical_frames;

inductive RawCubeImmediateFaceAddress : nat → TYPE ≔
| raw_cube_face_new_left
    (n : nat)
    : RawCubeImmediateFaceAddress (succ n)
| raw_cube_face_new_right
    (n : nat)
    : RawCubeImmediateFaceAddress (succ n)
| raw_cube_face_older
    (n : nat)
    (face : RawCubeImmediateFaceAddress (succ n))
    : RawCubeImmediateFaceAddress (succ (succ n));

injective symbol CubeImmediateFaceAddress
  (n : τ Nat_grpd)
  : Grpd;

rule τ (@CubeImmediateFaceAddress $n)
  ↪ RawCubeImmediateFaceAddress $n;

// Public structural decoder from one immediate-face address to its coface.
injective symbol cube_face_address_code
  [n : τ Nat_grpd]
  (face : τ (@CubeImmediateFaceAddress (succ n)))
  : τ (@CubeFaceCode n (succ n));

rule @cube_face_address_code $n (@raw_cube_face_new_left $n)
  ↪ @cube_new_left_face_code $n
with @cube_face_address_code $n (@raw_cube_face_new_right $n)
  ↪ @cube_new_right_face_code $n
with @cube_face_address_code (succ $n) (@raw_cube_face_older $n $face)
  ↪ @cube_face_keep
      $n (succ $n)
      (@cube_face_address_code $n $face);

// Dimension-two readable addresses: outer source/target, then inherited sides.
symbol cube2_face_address_u
  : τ (@CubeImmediateFaceAddress (succ (succ zero)))
≔ @raw_cube_face_new_left (succ zero);

symbol cube2_face_address_v
  : τ (@CubeImmediateFaceAddress (succ (succ zero)))
≔ @raw_cube_face_new_right (succ zero);

symbol cube2_face_address_a
  : τ (@CubeImmediateFaceAddress (succ (succ zero)))
≔ @raw_cube_face_older zero (@raw_cube_face_new_left zero);

symbol cube2_face_address_b
  : τ (@CubeImmediateFaceAddress (succ (succ zero)))
≔ @raw_cube_face_older zero (@raw_cube_face_new_right zero);
