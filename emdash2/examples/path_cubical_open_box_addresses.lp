/* Reviewer example: recursive addresses recover the four completed boxes. */

require open emdash.emdash3_2_path_cubical_open_box_addresses;

assert ⊢ @cube2_open_kind_at_address cube2_face_address_u
  ≡ cube2_missing_u_kind;

assert ⊢ @cube2_open_kind_at_address cube2_face_address_v
  ≡ cube2_missing_v_kind;

assert ⊢ @cube2_open_kind_at_address cube2_face_address_a
  ≡ cube2_missing_a_kind;

assert ⊢ @cube2_open_kind_at_address cube2_face_address_b
  ≡ cube2_missing_b_kind;

assert [A : Grpd] ⊢
  @PathOpenSquareAtAddress_grpd A cube2_face_address_b
  ≡ @PathOpenSquareMissingB_grpd A;

assert [A : Grpd]
  (box : τ (@PathOpenSquareMissingB_grpd A)) ⊢
  @path_open_box2_fill A cube2_face_address_b box
  ≡ @path_hfill2_missing_b A box;

assert [A : Grpd]
  (box : τ (@PathOpenSquareMissingA_grpd A)) ⊢
  @path_open_box2_section A cube2_face_address_a box
  ≡ @path_open_square_missing_a_section A box;

assert ⊢
  @cube2_open_sieve_at_address cube2_face_address_u
  ≡ @cube2_open_sieve cube2_missing_u_kind;

type @cube2_open_kind_at_address;
type @PathOpenSquareAtAddress_grpd;
type @path_open_box2_fill;
