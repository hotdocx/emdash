/* Ordinary native slice equality and postcomposition without arrow eta rules. */
require open emdash.emdash3_2_one_cat_slice_paths;
require open emdash.emdash3_2_slice_sigma_arrow_paths;

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) (U : τ (Obj C))
  ⊢ @one_cat_slice_category C C1 U : τ (IsNCat (cat_succ cat_zero) (@Slice_cat C U));
assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) (U : τ (Obj C))
  (q r : τ (Obj (@Slice_cat C U))) (h g : τ (Hom (@Slice_cat C U) q r))
  (p : τ (@= (Hom C (@slice_object_domain C U q) (@slice_object_domain C U r))
    (@slice_arrow_underlying C U q r h) (@slice_arrow_underlying C U q r g)))
  ⊢ @one_cat_slice_arrow_path C C1 U q r h g p : τ (@= (Hom (@Slice_cat C U) q r) h g);
assert [C : Cat] [X Y : τ (Obj C)] (f : τ (Hom C X Y))
  (q r : τ (Obj (@Slice_cat C X))) (h : τ (Hom (@Slice_cat C X) q r))
  ⊢ @slice_sigma_underlying_path C X Y f q r h
    : τ (@= (Hom C (@slice_object_domain C X q) (@slice_object_domain C X r))
      (@slice_arrow_underlying C Y (@slice_sigma_obj C X Y f q) (@slice_sigma_obj C X Y f r)
        (@fapp1_fapp0 (@Slice_cat C X) (@Slice_cat C Y) (@slice_sigma_func C X Y f) q r h))
      (@slice_arrow_underlying C X q r h));
assertnot [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) (U : τ (Obj C))
  ⊢ @one_cat_slice_category C C1 U : τ (IsNCat cat_zero (@Slice_cat C U));
assertnot [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) (U : τ (Obj C))
  (q r : τ (Obj (@Slice_cat C U))) (h g : τ (Hom (@Slice_cat C U) q r))
  ⊢ @eq_refl (Hom (@Slice_cat C U) q r) h : τ (@= (Hom (@Slice_cat C U) q r) h g);
