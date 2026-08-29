/*
  Reviewer milestone: selected coherent dependent products in slices.

  For each u:X→Y, the selected whole covariant slice family supplies
  Πᵤ:C/X→C/Y and the existing adjunction u*⊣Πᵤ. The actual generic
  unit/counit tapp1 observations project to stable Došen operations, and both
  full post-opposite rectangles compute without duplicating generic composite
  point or identity-action rules.
*/

require open emdash.emdash3_2_slice_dependent_products;

// The selected whole family has exact conventional-slice fibres.
assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  (X : τ (Obj C)) ⊢
  @fapp0 C Cat_cat (@SliceDependentProduct_catd C PB DP) X
  ≡ @Slice_cat C X;

// Its internal action at u is the selected whole Πᵤ functor.
assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  (X Y : τ (Obj C))
  (u : τ (Hom C X Y)) ⊢
  @fapp1_fapp0 C Cat_cat
    (@SliceDependentProduct_catd C PB DP) X Y u
  ≡ @slice_dependent_product_func C PB DP X Y u;

assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  (X Y : τ (Obj C))
  (u : τ (Hom C X Y))
  (b : τ (Obj (@Slice_cat C X))) ⊢
  @fapp0
    (@Slice_cat C X) (@Slice_cat C Y)
    (@slice_dependent_product_func C PB DP X Y u)
    b
  ≡ @slice_dependent_product_obj C PB DP X Y u b;

// Full base-arrow action remains available beyond the capped Πᵤ functor.
assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  (X Y : τ (Obj C)) ⊢
  @fapp1_func C Cat_cat (@SliceDependentProduct_catd C PB DP) X Y
  : τ (Functor
      (Hom_cat C X Y)
      (Functor_cat (@Slice_cat C X) (@Slice_cat C Y)));

// Exact second adjunction u* ⊣ Πᵤ.
assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  (X Y : τ (Obj C))
  (u : τ (Hom C X Y)) ⊢
  @slice_dependent_product_adjunction C PB DP X Y u
  : τ (@Adjunction
      (@Slice_cat C Y)
      (@Slice_cat C X)
      (@slice_base_change_func C PB X Y u)
      (@slice_dependent_product_func C PB DP X Y u));

// The public unit/counit are the generic actual whole transformations.
assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  (X Y : τ (Obj C))
  (u : τ (Hom C X Y)) ⊢
  @slice_dependent_product_unit_transf C PB DP X Y u
  ≡ @unit_adj_transf
      (@Slice_cat C Y) (@Slice_cat C X)
      (@slice_base_change_func C PB X Y u)
      (@slice_dependent_product_func C PB DP X Y u)
      (@slice_dependent_product_adjunction C PB DP X Y u);

assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  (X Y : τ (Obj C))
  (u : τ (Hom C X Y)) ⊢
  @slice_dependent_product_counit_transf C PB DP X Y u
  ≡ @counit_adj_transf
      (@Slice_cat C Y) (@Slice_cat C X)
      (@slice_base_change_func C PB X Y u)
      (@slice_dependent_product_func C PB DP X Y u)
      (@slice_dependent_product_adjunction C PB DP X Y u);

// Their actual tapp1 observations compute to the stable Došen heads.
assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  (X Y : τ (Obj C))
  (u : τ (Hom C X Y))
  (a a' : τ (Obj (@Slice_cat C Y)))
  (k : τ (Hom (@Slice_cat C Y) a a')) ⊢
  @tapp1_fapp0
    (@Slice_cat C Y) (@Slice_cat C Y)
    _ _ a a'
    (@unit_adj_transf
      (@Slice_cat C Y) (@Slice_cat C X)
      (@slice_base_change_func C PB X Y u)
      (@slice_dependent_product_func C PB DP X Y u)
      (@slice_dependent_product_adjunction C PB DP X Y u))
    k
  ≡ @slice_dependent_product_gamma C PB DP X Y u a a' k;

assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  (X Y : τ (Obj C))
  (u : τ (Hom C X Y))
  (b' b : τ (Obj (@Slice_cat C X)))
  (h : τ (Hom (@Slice_cat C X) b' b)) ⊢
  @tapp1_fapp0
    (@Slice_cat C X) (@Slice_cat C X)
    _ _ b' b
    (@counit_adj_transf
      (@Slice_cat C Y) (@Slice_cat C X)
      (@slice_base_change_func C PB X Y u)
      (@slice_dependent_product_func C PB DP X Y u)
      (@slice_dependent_product_adjunction C PB DP X Y u))
    h
  ≡ @slice_dependent_product_phi C PB DP X Y u b' b h;

// Full F-side rectangle: φΠᵃ(h) ∘ u*(γΠᶜ(k)) → h ∘ u*(k).
assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  (X Y : τ (Obj C))
  (u : τ (Hom C X Y))
  (a a' : τ (Obj (@Slice_cat C Y)))
  (b : τ (Obj (@Slice_cat C X)))
  (k : τ (Hom (@Slice_cat C Y) a a'))
  (h : τ (Hom (@Slice_cat C X)
    (@slice_base_change_obj C PB X Y u a') b)) ⊢
  @comp_fapp0
    (@Slice_cat C X)
    (@slice_base_change_obj C PB X Y u a)
    (@slice_base_change_obj C PB X Y u
      (@slice_dependent_product_obj C PB DP X Y u
        (@slice_base_change_obj C PB X Y u a')))
    b
    (@slice_dependent_product_phi C PB DP X Y u
      (@slice_base_change_obj C PB X Y u a') b h)
    (@fapp1_fapp0
      (@Slice_cat C Y) (@Slice_cat C X)
      (@slice_base_change_func C PB X Y u)
      a
      (@slice_dependent_product_obj C PB DP X Y u
        (@slice_base_change_obj C PB X Y u a'))
      (@slice_dependent_product_gamma C PB DP X Y u a a' k))
  ≡ @comp_fapp0
      (@Slice_cat C X)
      (@slice_base_change_obj C PB X Y u a)
      (@slice_base_change_obj C PB X Y u a')
      b h
      (@fapp1_fapp0
        (@Slice_cat C Y) (@Slice_cat C X)
        (@slice_base_change_func C PB X Y u) a a' k);

// Full G-side rectangle: Πᵤ(φΠᵃ(h)) ∘ γΠᶜ(k) → Πᵤ(h) ∘ k.
assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  (X Y : τ (Obj C))
  (u : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C Y)))
  (b' b : τ (Obj (@Slice_cat C X)))
  (k : τ (Hom (@Slice_cat C Y)
    a (@slice_dependent_product_obj C PB DP X Y u b')))
  (h : τ (Hom (@Slice_cat C X) b' b)) ⊢
  @comp_fapp0
    (@Slice_cat C Y)
    a
    (@slice_dependent_product_obj C PB DP X Y u
      (@slice_base_change_obj C PB X Y u
        (@slice_dependent_product_obj C PB DP X Y u b')))
    (@slice_dependent_product_obj C PB DP X Y u b)
    (@fapp1_fapp0
      (@Slice_cat C X) (@Slice_cat C Y)
      (@slice_dependent_product_func C PB DP X Y u)
      (@slice_base_change_obj C PB X Y u
        (@slice_dependent_product_obj C PB DP X Y u b'))
      b
      (@slice_dependent_product_phi C PB DP X Y u b' b h))
    (@slice_dependent_product_gamma C PB DP X Y u
      a (@slice_dependent_product_obj C PB DP X Y u b') k)
  ≡ @comp_fapp0
      (@Slice_cat C Y)
      a
      (@slice_dependent_product_obj C PB DP X Y u b')
      (@slice_dependent_product_obj C PB DP X Y u b)
      (@fapp1_fapp0
        (@Slice_cat C X) (@Slice_cat C Y)
        (@slice_dependent_product_func C PB DP X Y u) b' b h)
      k;

// Identity boundaries recover components and both component triangles.
assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  (X Y : τ (Obj C))
  (u : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C Y))) ⊢
  @slice_dependent_product_gamma C PB DP X Y u a a
    (@id (@Slice_cat C Y) a)
  ≡ @slice_dependent_product_unit C PB DP X Y u a;

assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  (X Y : τ (Obj C))
  (u : τ (Hom C X Y))
  (b : τ (Obj (@Slice_cat C X))) ⊢
  @slice_dependent_product_phi C PB DP X Y u b b
    (@id (@Slice_cat C X) b)
  ≡ @slice_dependent_product_counit C PB DP X Y u b;

assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  (X Y : τ (Obj C))
  (u : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C Y))) ⊢
  @comp_fapp0
    (@Slice_cat C X)
    (@slice_base_change_obj C PB X Y u a)
    (@slice_base_change_obj C PB X Y u
      (@slice_dependent_product_obj C PB DP X Y u
        (@slice_base_change_obj C PB X Y u a)))
    (@slice_base_change_obj C PB X Y u a)
    (@slice_dependent_product_phi C PB DP X Y u
      (@slice_base_change_obj C PB X Y u a)
      (@slice_base_change_obj C PB X Y u a)
      (@id (@Slice_cat C X) (@slice_base_change_obj C PB X Y u a)))
    (@fapp1_fapp0
      (@Slice_cat C Y) (@Slice_cat C X)
      (@slice_base_change_func C PB X Y u)
      a
      (@slice_dependent_product_obj C PB DP X Y u
        (@slice_base_change_obj C PB X Y u a))
      (@slice_dependent_product_gamma C PB DP X Y u a a
        (@id (@Slice_cat C Y) a)))
  ≡ @id (@Slice_cat C X) (@slice_base_change_obj C PB X Y u a);

assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  (X Y : τ (Obj C))
  (u : τ (Hom C X Y))
  (b : τ (Obj (@Slice_cat C X))) ⊢
  @comp_fapp0
    (@Slice_cat C Y)
    (@slice_dependent_product_obj C PB DP X Y u b)
    (@slice_dependent_product_obj C PB DP X Y u
      (@slice_base_change_obj C PB X Y u
        (@slice_dependent_product_obj C PB DP X Y u b)))
    (@slice_dependent_product_obj C PB DP X Y u b)
    (@fapp1_fapp0
      (@Slice_cat C X) (@Slice_cat C Y)
      (@slice_dependent_product_func C PB DP X Y u)
      (@slice_base_change_obj C PB X Y u
        (@slice_dependent_product_obj C PB DP X Y u b))
      b
      (@slice_dependent_product_phi C PB DP X Y u b b
        (@id (@Slice_cat C X) b)))
    (@slice_dependent_product_gamma C PB DP X Y u
      (@slice_dependent_product_obj C PB DP X Y u b)
      (@slice_dependent_product_obj C PB DP X Y u b)
      (@id (@Slice_cat C Y)
        (@slice_dependent_product_obj C PB DP X Y u b)))
  ≡ @id (@Slice_cat C Y)
      (@slice_dependent_product_obj C PB DP X Y u b);

// Transparent semantic mate functors retain higher Hom action.
assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  (X Y : τ (Obj C))
  (u : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C Y)))
  (b : τ (Obj (@Slice_cat C X))) ⊢
  @slice_dependent_product_transpose_func C PB DP X Y u a b
  : τ (Functor
      (Hom_cat (@Slice_cat C X)
        (@slice_base_change_obj C PB X Y u a) b)
      (Hom_cat (@Slice_cat C Y) a
        (@slice_dependent_product_obj C PB DP X Y u b)));

assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  (X Y : τ (Obj C))
  (u : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C Y)))
  (b : τ (Obj (@Slice_cat C X))) ⊢
  @slice_dependent_product_untranspose_func C PB DP X Y u a b
  : τ (Functor
      (Hom_cat (@Slice_cat C Y) a
        (@slice_dependent_product_obj C PB DP X Y u b))
      (Hom_cat (@Slice_cat C X)
        (@slice_base_change_obj C PB X Y u a) b));

assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  (X Y : τ (Obj C))
  (u : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C Y)))
  (b : τ (Obj (@Slice_cat C X)))
  (h h' : τ (Hom (@Slice_cat C X)
    (@slice_base_change_obj C PB X Y u a) b)) ⊢
  @fapp1_func
    (Hom_cat (@Slice_cat C X)
      (@slice_base_change_obj C PB X Y u a) b)
    (Hom_cat (@Slice_cat C Y) a
      (@slice_dependent_product_obj C PB DP X Y u b))
    (@slice_dependent_product_transpose_func C PB DP X Y u a b)
    h h'
  : τ (Functor
      (Hom_cat
        (Hom_cat (@Slice_cat C X)
          (@slice_base_change_obj C PB X Y u a) b)
        h h')
      (Hom_cat
        (Hom_cat (@Slice_cat C Y) a
          (@slice_dependent_product_obj C PB DP X Y u b))
        (@slice_dependent_product_transpose C PB DP X Y u a b h)
        (@slice_dependent_product_transpose C PB DP X Y u a b h')));

// The generic adjunction owner supplies the whole varying-endpoint Hom comparison.
assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  (X Y : τ (Obj C))
  (u : τ (Hom C X Y)) ⊢
  @Adjunction_hom_prof_comparison
    (@Slice_cat C Y) (@Slice_cat C X)
    (@slice_base_change_func C PB X Y u)
    (@slice_dependent_product_func C PB DP X Y u)
    (@slice_dependent_product_adjunction C PB DP X Y u)
  : τ (ProfComparison
      (@Hom_prof_along
        (@Slice_cat C Y) (@Slice_cat C X) (@Slice_cat C X)
        (@slice_base_change_func C PB X Y u)
        (@id_func (@Slice_cat C X)))
      (@Hom_prof_along
        (@Slice_cat C Y) (@Slice_cat C X) (@Slice_cat C Y)
        (@id_func (@Slice_cat C Y))
        (@slice_dependent_product_func C PB DP X Y u)));

assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  (X Y : τ (Obj C))
  (u : τ (Hom C X Y)) ⊢
  @slice_dependent_product_hom_prof_comparison C PB DP X Y u
  ≡ @Adjunction_hom_prof_comparison
      (@Slice_cat C Y) (@Slice_cat C X)
      (@slice_base_change_func C PB X Y u)
      (@slice_dependent_product_func C PB DP X Y u)
      (@slice_dependent_product_adjunction C PB DP X Y u);

// Equal fibres do not collapse the selected dependent product to Sigma or u*.
assertnot [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  (X Y : τ (Obj C))
  (u : τ (Hom C X Y)) ⊢
  @slice_dependent_product_func C PB DP X Y u
  ≡ @slice_sigma_func C X Y u;

assertnot [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  (X : τ (Obj C))
  (u : τ (Hom C X X)) ⊢
  @slice_dependent_product_func C PB DP X X u
  ≡ @slice_base_change_func C PB X X u;

// The thin total capability retains both selected structures without new laws.
assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB)) ⊢
  @slice_dependent_products_pullbacks C
    (@slice_dependent_products_intro C PB DP)
  ≡ PB;

assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB)) ⊢
  @slice_dependent_products_structure C
    (@slice_dependent_products_intro C PB DP)
  ≡ DP;
