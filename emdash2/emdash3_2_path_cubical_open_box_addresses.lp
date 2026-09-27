/*
  Emdash v3.2: dimension-two recovery through recursive face addresses.

  The four inhabitants of CubeImmediateFaceAddress(2) select the completed
  missing-u/v/a/b carriers, fillers, restrictions, sections, and ordinary
  sieves. This is a dependent facade over existing operations; it does not
  recreate the dimension-two boxes.
*/

require open emdash.emdash3_2_cubical_face_addresses;
require open emdash.emdash3_2_path_cubical_hcomp2;

// Address-to-kind comparison for the four dimension-two immediate faces.
injective symbol cube2_open_kind_at_address
  (face : τ (@CubeImmediateFaceAddress (succ (succ zero))))
  : τ Cube2OpenBoxKind;

rule @cube2_open_kind_at_address (@raw_cube_face_new_left (succ zero))
  ↪ cube2_missing_u_kind
with @cube2_open_kind_at_address (@raw_cube_face_new_right (succ zero))
  ↪ cube2_missing_v_kind
with @cube2_open_kind_at_address
      (@raw_cube_face_older zero (@raw_cube_face_new_left zero))
  ↪ cube2_missing_a_kind
with @cube2_open_kind_at_address
      (@raw_cube_face_older zero (@raw_cube_face_new_right zero))
  ↪ cube2_missing_b_kind;

// Existing explicit carrier selected by an address.
injective symbol PathOpenSquareAtAddress_grpd
  (A : Grpd)
  (face : τ (@CubeImmediateFaceAddress (succ (succ zero))))
  : Grpd;

rule @PathOpenSquareAtAddress_grpd $A (@raw_cube_face_new_left (succ zero))
  ↪ @PathOpenSquareMissingU_grpd $A
with @PathOpenSquareAtAddress_grpd $A (@raw_cube_face_new_right (succ zero))
  ↪ @PathOpenSquareMissingV_grpd $A
with @PathOpenSquareAtAddress_grpd
      $A (@raw_cube_face_older zero (@raw_cube_face_new_left zero))
  ↪ @PathOpenSquareMissingA_grpd $A
with @PathOpenSquareAtAddress_grpd
      $A (@raw_cube_face_older zero (@raw_cube_face_new_right zero))
  ↪ @PathOpenSquareMissingB_grpd $A;

// Existing filler selected dependently by the address.
injective symbol path_open_box2_fill
  [A : Grpd]
  (face : τ (@CubeImmediateFaceAddress (succ (succ zero))))
  (box : τ (@PathOpenSquareAtAddress_grpd A face))
  : τ (@PathCube_grpd A (succ (succ zero)));

rule @path_open_box2_fill _ (@raw_cube_face_new_left (succ zero)) $box
  ↪ @path_hfill2_missing_u _ $box
with @path_open_box2_fill _ (@raw_cube_face_new_right (succ zero)) $box
  ↪ @path_hfill2_missing_v _ $box
with @path_open_box2_fill
      _ (@raw_cube_face_older zero (@raw_cube_face_new_left zero)) $box
  ↪ @path_hfill2_missing_a _ $box
with @path_open_box2_fill
      _ (@raw_cube_face_older zero (@raw_cube_face_new_right zero)) $box
  ↪ @path_hfill2_missing_b _ $box;

// Existing restriction selected dependently by the address.
injective symbol path_open_box2_restrict
  [A : Grpd]
  (face : τ (@CubeImmediateFaceAddress (succ (succ zero))))
  (S : τ (@PathCube_grpd A (succ (succ zero))))
  : τ (@PathOpenSquareAtAddress_grpd A face);

rule @path_open_box2_restrict _ (@raw_cube_face_new_left (succ zero)) $S
  ↪ @path_square_restrict_missing_u _ $S
with @path_open_box2_restrict _ (@raw_cube_face_new_right (succ zero)) $S
  ↪ @path_square_restrict_missing_v _ $S
with @path_open_box2_restrict
      _ (@raw_cube_face_older zero (@raw_cube_face_new_left zero)) $S
  ↪ @path_square_restrict_missing_a _ $S
with @path_open_box2_restrict
      _ (@raw_cube_face_older zero (@raw_cube_face_new_right zero)) $S
  ↪ @path_square_restrict_missing_b _ $S;

// Existing restriction-section path selected by the address.
injective symbol path_open_box2_section
  [A : Grpd]
  (face : τ (@CubeImmediateFaceAddress (succ (succ zero))))
  (box : τ (@PathOpenSquareAtAddress_grpd A face))
  : τ (@=
      (@PathOpenSquareAtAddress_grpd A face)
      (@path_open_box2_restrict A face (@path_open_box2_fill A face box))
      box);

rule @path_open_box2_section _ (@raw_cube_face_new_left (succ zero)) $box
  ↪ @path_open_square_missing_u_section _ $box
with @path_open_box2_section _ (@raw_cube_face_new_right (succ zero)) $box
  ↪ @path_open_square_missing_v_section _ $box
with @path_open_box2_section
      _ (@raw_cube_face_older zero (@raw_cube_face_new_left zero)) $box
  ↪ @path_open_square_missing_a_section _ $box
with @path_open_box2_section
      _ (@raw_cube_face_older zero (@raw_cube_face_new_right zero)) $box
  ↪ @path_open_square_missing_b_section _ $box;

// Existing ordinary sieve selected by the same address.
symbol cube2_open_sieve_at_address
  (face : τ (@CubeImmediateFaceAddress (succ (succ zero))))
  : τ (@Sieve SemiCubePlus_cat (succ (succ zero)))
≔ @cube2_open_sieve (@cube2_open_kind_at_address face);
