/*
  Reviewer for selected computational binary products.

  The Boolean diagram computes at both objects.  A selected product retains
  one whole weighted-limit comparison, from which the universal cone and both
  projections are derived internally.  No componentwise naturality or claim
  that every category has products is added.
*/

require open emdash.emdash3_2_finite_limits;

// The path-discrete Boolean diagram selects the two requested objects.
assert [C : Cat]
  (x y : τ (Obj C)) ⊢
  @fapp0
    (Path_cat Bool_grpd)
    C
    (@binary_product_diagram C x y)
    false
  ≡ x;

assert [C : Cat]
  (x y : τ (Obj C)) ⊢
  @fapp0
    (Path_cat Bool_grpd)
    C
    (@binary_product_diagram C x y)
    true
  ≡ y;

// Both retained fields compute through the transparent Sigma constructor.
assert [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (Obj C))
  (universal : τ (@IsBinaryProduct_comp C x y p)) ⊢
  @binary_product_object
    C x y (@binary_product_intro C x y p universal)
  ≡ p;

assert [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (Obj C))
  (universal : τ (@IsBinaryProduct_comp C x y p)) ⊢
  @binary_product_universal
    C x y (@binary_product_intro C x y p universal)
  ≡ universal;

// The comparison-derived cone retains its whole internally natural type.
assert [C : Cat]
  [x y p : τ (Obj C)]
  (universal : τ (@IsBinaryProduct_comp C x y p)) ⊢
  @binary_product_cone C x y p universal
  : τ (ProfMap
      (@Unit_prof Terminal_cat)
      (@Prof_imply_cov
        Terminal_cat
        Terminal_cat
        (Path_cat Bool_grpd)
        (@Hom_prof_along
          Terminal_cat
          (Path_cat Bool_grpd)
          C
          (@Obj_func C p)
          (@binary_product_diagram C x y))
        (@Terminal_prof Terminal_cat (Path_cat Bool_grpd))));

// Closed endpoint projections have exactly the expected hom types.
assert [C : Cat]
  [x y p : τ (Obj C)]
  (universal : τ (@IsBinaryProduct_comp C x y p)) ⊢
  @binary_product_projection0 C x y p universal
  : τ (Hom C p x);

assert [C : Cat]
  [x y p : τ (Obj C)]
  (universal : τ (@IsBinaryProduct_comp C x y p)) ⊢
  @binary_product_projection1 C x y p universal
  : τ (Hom C p y);

// Selected presentations route to those same comparison-derived projections.
assert [C : Cat]
  [x y : τ (Obj C)]
  (P : τ (@BinaryProductPresentation C x y)) ⊢
  @selected_binary_product_projection0 C x y P
  : τ (Hom C (@binary_product_object C x y P) x);

assert [C : Cat]
  [x y : τ (Obj C)]
  (P : τ (@BinaryProductPresentation C x y)) ⊢
  @selected_binary_product_projection1 C x y P
  : τ (Hom C (@binary_product_object C x y P) y);
