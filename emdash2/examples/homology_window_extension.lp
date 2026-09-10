/* The generic extension retains the previously checked two-window result. */
require open emdash.examples.homology_adjacent_window_tails;
require open emdash.emdash3_2_homology_window_extension;
symbol via_extension ≔ @homology_whole_window_extend C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1
  row2 F G J z0 z1 C1 T T0 KP QP three lower_tail;
symbol via_empty ≔ @homology_whole_window_tail C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G
  J z0 z1 C1 T T0 KP QP;
symbol lower_via_empty ≔ @homology_whole_window_tail C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 A3 B3 D3 row0 row1 row2
  row3 G J L z1 z2 C1 T T0 KP QP;
assert ⊢ via_extension ≡ joined;
assert ⊢ via_empty ≡ upper_tail;
assert ⊢ lower_via_empty ≡ lower_tail;
