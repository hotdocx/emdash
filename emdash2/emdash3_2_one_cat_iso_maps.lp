/* Ordinary-target action on original isomorphism evidence. */
require open emdash.emdash3_2_one_cat_omega_maps;

symbol one_cat_iso_evidence_fmap [C D : Cat]
  (D1 : τ (IsNCat (cat_succ cat_zero) D)) (F : τ (Functor C D))
  [x y : τ (Obj C)] (i : τ (@IsoEvidence C x y))
  : τ (@IsoEvidence D (@fapp0 C D F x) (@fapp0 C D F y))
≔ Struct_sigma
    (@fapp1_fapp0 C D F x y (@iso_evidence_to C x y i))
    (Struct_sigma
      (@fapp1_fapp0 C D F y x (@iso_evidence_from C x y i))
      (Struct_sigma
        (@one_cat_omega_equiv_fmap_left_law C D D1 F x y
          (@iso_evidence_to C x y i) (@iso_evidence_omega_along C x y i))
        (@one_cat_omega_equiv_fmap_right_law C D D1 F x y
          (@iso_evidence_to C x y i) (@iso_evidence_omega_along C x y i))));
