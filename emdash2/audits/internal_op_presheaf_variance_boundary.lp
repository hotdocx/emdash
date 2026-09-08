/* NON-LIBRARY variance boundary: follow Edge/HomPresheaf at corrected bases.
   The imported old kernel remains unrepaired. Do not register this as a
   positive library target or mistake its negative for an impossibility
   theorem about all potential Homd target architectures. */
require open emdash.audits.internal_op_co2_families_prototype;

// Independent dimension reversals commute; select Op outside Co2.
rule Co2_cat (Op_cat $C) ↪ Op_cat (Co2_cat $C);

symbol corrected_edge_catd_func [Z : Cat]
  : τ (Functor (Op_cat (Co2_cat Z)) (Catd_cat (Co2_cat Z)))
≔ @comp_cat_fapp0
    (Op_cat (Co2_cat Z)) (Co2_cat (Catd_cat Z)) (Catd_cat (Co2_cat Z))
    (op_co2_catd_func Z)
    (@Co2_func (Op_cat Z) (Catd_cat Z) (@Rep_catd_func Z));

symbol corrected_hom_presheaf_catd_func [Z : Cat]
  : τ (Functor (Co2_cat Z) (Catd_cat (Op_cat (Co2_cat Z))))
≔ @comp_cat_fapp0
    (Co2_cat Z) (Op_cat (Catd_cat (Co2_cat Z)))
    (Catd_cat (Op_cat (Co2_cat Z)))
    (@Presheaf_catd_func (Op_cat (Co2_cat Z)))
    (@Op_func (Op_cat (Co2_cat Z)) (Catd_cat (Co2_cat Z))
      (@corrected_edge_catd_func Z));

assert [Z : Cat] (x y : τ (Obj Z)) ⊢
  @fapp0 (Co2_cat Z) Cat_cat
    (@fapp0 (Op_cat (Co2_cat Z)) (Catd_cat (Co2_cat Z))
      (@corrected_edge_catd_func Z) x) y
  ≡ Op_cat (Hom_cat Z x y);

assert [Z : Cat] (x y : τ (Obj Z)) ⊢
  @fapp0 (Op_cat (Co2_cat Z)) Cat_cat
    (@fapp0 (Co2_cat Z) (Catd_cat (Op_cat (Co2_cat Z)))
      (@corrected_hom_presheaf_catd_func Z) x) y
  ≡ Functor_cat (Op_cat (Hom_cat Z x y)) Cat_cat;

// The active Homd_target_section_catd body expects E over Z. Correcting
// only the presheaf half no longer supplies that mixed-family input type.
assertnot [Z : Cat] (E : τ (Catd Z)) (x : τ (Obj Z)) ⊢
  @Functor_catd (Op_cat (Co2_cat Z)) E
    (@fapp0 (Co2_cat Z) (Catd_cat (Op_cat (Co2_cat Z)))
      (@corrected_hom_presheaf_catd_func Z) x)
  : τ (Catd (Op_cat (Co2_cat Z)));

// With an explicitly correctly based family, that same constructor works.
// No automatic E ↦ E2 with unchanged fibres/actions is postulated.
assert [Z : Cat] (E2 : τ (Catd (Co2_cat Z))) (x : τ (Obj Z)) ⊢
  @Functor_catd (Op_cat (Co2_cat Z)) E2
    (@fapp0 (Co2_cat Z) (Catd_cat (Op_cat (Co2_cat Z)))
      (@corrected_hom_presheaf_catd_func Z) x)
  : τ (Catd (Op_cat (Co2_cat Z)));
