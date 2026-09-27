/* Reviewer example: recursive immediate cubical face addresses. */

require open emdash.emdash3_2_cubical_face_addresses;

// Dimension one has exactly the two new addresses.
assert ⊢
  @cube_face_address_code zero (@raw_cube_face_new_left zero)
  ≡ @cube_new_left_face_code zero;

assert ⊢
  @cube_face_address_code zero (@raw_cube_face_new_right zero)
  ≡ @cube_new_right_face_code zero;

// Dimension two recovers u,v and the two star-lifted older sides a,b.
assert ⊢
  @cube_face_address_code (succ zero) cube2_face_address_u
  ≡ @cube_new_left_face_code (succ zero);

assert ⊢
  @cube_face_address_code (succ zero) cube2_face_address_v
  ≡ @cube_new_right_face_code (succ zero);

assert ⊢
  @cube_face_address_code (succ zero) cube2_face_address_a
  ≡ @cube_face_keep zero (succ zero) (@cube_new_left_face_code zero);

assert ⊢
  @cube_face_address_code (succ zero) cube2_face_address_b
  ≡ @cube_face_keep zero (succ zero) (@cube_new_right_face_code zero);

// Older lifting continues uniformly at dimension three.
assert (face : τ (@CubeImmediateFaceAddress (succ (succ zero)))) ⊢
  @cube_face_address_code
    (succ (succ zero))
    (@raw_cube_face_older (succ zero) face)
  ≡ @cube_face_keep
      (succ zero) (succ (succ zero))
      (@cube_face_address_code (succ zero) face);

type @CubeImmediateFaceAddress;
type @cube_face_address_code;
