/*
  Reviewer milestone: chosen pullbacks as internal slice base change.

  The covariant slice family supplies Σ_f and a selected whole contravariant
  family supplies f*. Their existing adjunction owns the whole cone/lift
  equivalence. Ordinary projections and the commuting square are observations
  of the selected base-change object and counit, not independent axioms.
*/

require open emdash.emdash3_2_pullbacks;

// The two whole families have exact slice fibres and opposite variance.
assert [C : Cat]
  (X : τ (Obj C)) ⊢
  @fapp0 C Cat_cat (@SliceSigma_catd C) X
  ≡ @Slice_cat C X;

assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (X : τ (Obj C)) ⊢
  @fapp0 (Op_cat C) Cat_cat (@SliceBaseChange_catd C PB) X
  ≡ @Slice_cat C X;

assert [C : Cat]
  (X Y : τ (Obj C))
  (f : τ (Hom C X Y)) ⊢
  @slice_sigma_func C X Y f
  : τ (Functor (@Slice_cat C X) (@Slice_cat C Y));

assert [C : Cat]
  (X Y : τ (Obj C))
  (f : τ (Hom C X Y)) ⊢
  @slice_sigma_func C X Y f
  ≡ @Op_func
      (@Into_restr_cat C X)
      (@Into_restr_cat C Y)
      (@into_restr_postcompose_func C X Y f);

assert [C : Cat]
  (W X Y : τ (Obj C))
  (f : τ (Hom C X Y))
  (a : τ (Hom C W X)) ⊢
  @slice_sigma_obj C X Y f (Struct_sigma W a)
  ≡ @Struct_sigma
      (Obj (Op_cat C))
      (λ Z : τ (Obj (Op_cat C)),
        Obj (@Fibre_cat (Op_cat C) (@yoneda_psh C Y) Z))
      W
      (@hom_postcomp_fapp0 C C (@id_func C) W X Y f a);

// Whole postcomposition and the stable arbitrary-object point share the
// selected runtime endpoint.
assert [C : Cat]
  (X Y : τ (Obj C))
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X))) ⊢
  @fapp0
    (@Slice_cat C X)
    (@Slice_cat C Y)
    (@slice_sigma_func C X Y f)
    a
  ≡ @slice_sigma_obj C X Y f a;

// No equality transport is needed to observe the preserved domain or the
// postcomposed structure arrow of an arbitrary slice object.
assert [C : Cat]
  (X Y : τ (Obj C))
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X))) ⊢
  @slice_object_domain C Y (@slice_sigma_obj C X Y f a)
  ≡ @slice_object_domain C X a;

assert [C : Cat]
  (X Y : τ (Obj C))
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X))) ⊢
  @slice_object_arrow C Y (@slice_sigma_obj C X Y f a)
  ≡ @hom_postcomp_fapp0
      C C (@id Cat_cat C)
      (@slice_object_domain C X a)
      X Y f
      (@slice_object_arrow C X a);

assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (X Y : τ (Obj C))
  (f : τ (Hom C X Y)) ⊢
  @slice_base_change_func C PB X Y f
  : τ (Functor (@Slice_cat C Y) (@Slice_cat C X));

// Full base-arrow action remains available beyond the capped f* functor.
assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (X Y : τ (Obj C)) ⊢
  @fapp1_func
    (Op_cat C) Cat_cat
    (@SliceBaseChange_catd C PB)
    Y X
  : τ (Functor
      (Hom_cat (Op_cat C) Y X)
      (Functor_cat (@Slice_cat C Y) (@Slice_cat C X)));

// The selected per-arrow structure instantiates the existing adjunction.
assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (X Y : τ (Obj C))
  (f : τ (Hom C X Y)) ⊢
  @slice_base_change_adjunction C PB X Y f
  : τ (@Adjunction
      (@Slice_cat C X)
      (@Slice_cat C Y)
      (@slice_sigma_func C X Y f)
      (@slice_base_change_func C PB X Y f));

assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (X Y : τ (Obj C))
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X))) ⊢
  @slice_base_change_unit C PB X Y f a
  : τ (Hom
      (@Slice_cat C X)
      a
      (@slice_base_change_obj C PB X Y f
        (@slice_sigma_obj C X Y f a)));

assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (X Y : τ (Obj C))
  (f : τ (Hom C X Y))
  (g : τ (Obj (@Slice_cat C Y))) ⊢
  @slice_base_change_counit C PB X Y f g
  : τ (Hom
      (@Slice_cat C Y)
      (@slice_sigma_obj C X Y f
        (@slice_base_change_obj C PB X Y f g))
      g);

// Stable whole mate functors retain higher action.
assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (X Y : τ (Obj C))
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  (g : τ (Obj (@Slice_cat C Y))) ⊢
  @slice_base_change_transpose_func C PB X Y f a g
  : τ (Functor
      (Hom_cat (@Slice_cat C Y) (@slice_sigma_obj C X Y f a) g)
      (Hom_cat (@Slice_cat C X) a
        (@slice_base_change_obj C PB X Y f g)));

// Proof-time semantic usability is explicit and non-opaque.
assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (X Y : τ (Obj C))
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  (g : τ (Obj (@Slice_cat C Y)))
  (h : τ (Hom (@Slice_cat C Y)
    (@slice_sigma_obj C X Y f a) g)) ⊢
  @slice_base_change_transpose_semantic_path C PB X Y f a g h
  : τ (@=
      (Hom (@Slice_cat C X) a
        (@slice_base_change_obj C PB X Y f g))
      (@slice_base_change_transpose C PB X Y f a g h)
      (@slice_base_change_transpose_semantic C PB X Y f a g h));

assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (X Y : τ (Obj C))
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  (g : τ (Obj (@Slice_cat C Y)))
  (h : τ (Hom (@Slice_cat C Y)
    (@slice_sigma_obj C X Y f a) g)) ⊢
  @eq_refl
    (Hom (@Slice_cat C X) a
      (@slice_base_change_obj C PB X Y f g))
    (@slice_base_change_transpose_semantic C PB X Y f a g h)
  : τ (@=
      (Hom (@Slice_cat C X) a
        (@slice_base_change_obj C PB X Y f g))
      (@slice_base_change_transpose_semantic C PB X Y f a g h)
      (@slice_base_change_transpose C PB X Y f a g h));

assertnot [C : Cat]
  (PB : τ (@PullbackStructure C))
  (X Y : τ (Obj C))
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  (g : τ (Obj (@Slice_cat C Y)))
  (h : τ (Hom (@Slice_cat C Y)
    (@slice_sigma_obj C X Y f a) g)) ⊢
  @slice_base_change_transpose C PB X Y f a g h
  ≡ @slice_base_change_transpose_semantic C PB X Y f a g h;

assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (X Y : τ (Obj C))
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  (g : τ (Obj (@Slice_cat C Y)))
  (k : τ (Hom (@Slice_cat C X) a
    (@slice_base_change_obj C PB X Y f g))) ⊢
  @slice_base_change_untranspose_semantic_path C PB X Y f a g k
  : τ (@=
      (Hom (@Slice_cat C Y)
        (@slice_sigma_obj C X Y f a) g)
      (@slice_base_change_untranspose C PB X Y f a g k)
      (@slice_base_change_untranspose_semantic C PB X Y f a g k));

assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (X Y : τ (Obj C))
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  (g : τ (Obj (@Slice_cat C Y)))
  (k : τ (Hom (@Slice_cat C X) a
    (@slice_base_change_obj C PB X Y f g))) ⊢
  @eq_refl
    (Hom (@Slice_cat C Y)
      (@slice_sigma_obj C X Y f a) g)
    (@slice_base_change_untranspose_semantic C PB X Y f a g k)
  : τ (@=
      (Hom (@Slice_cat C Y)
        (@slice_sigma_obj C X Y f a) g)
      (@slice_base_change_untranspose_semantic C PB X Y f a g k)
      (@slice_base_change_untranspose C PB X Y f a g k));

assertnot [C : Cat]
  (PB : τ (@PullbackStructure C))
  (X Y : τ (Obj C))
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  (g : τ (Obj (@Slice_cat C Y)))
  (k : τ (Hom (@Slice_cat C X) a
    (@slice_base_change_obj C PB X Y f g))) ⊢
  @slice_base_change_untranspose C PB X Y f a g k
  ≡ @slice_base_change_untranspose_semantic C PB X Y f a g k;

// Both whole mate cuts compute.
assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (X Y : τ (Obj C))
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  (g : τ (Obj (@Slice_cat C Y)))
  (h : τ (Hom (@Slice_cat C Y)
    (@slice_sigma_obj C X Y f a) g)) ⊢
  @slice_base_change_untranspose C PB X Y f a g
    (@slice_base_change_transpose C PB X Y f a g h)
  ≡ h;

assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (X Y : τ (Obj C))
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  (g : τ (Obj (@Slice_cat C Y)))
  (k : τ (Hom (@Slice_cat C X) a
    (@slice_base_change_obj C PB X Y f g))) ⊢
  @slice_base_change_transpose C PB X Y f a g
    (@slice_base_change_untranspose C PB X Y f a g k)
  ≡ k;

// Pullback object, projections, and directed square come from f*(g) and ε_g.
assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (X Y : τ (Obj C))
  (f : τ (Hom C X Y))
  (g : τ (Obj (@Slice_cat C Y))) ⊢
  @pullback_fst C PB X Y f g
  : τ (Hom C (@pullback_domain C PB X Y f g) X);

assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (X Y : τ (Obj C))
  (f : τ (Hom C X Y))
  (g : τ (Obj (@Slice_cat C Y))) ⊢
  @pullback_snd C PB X Y f g
  : τ (Hom C
      (@pullback_domain C PB X Y f g)
      (@slice_object_domain C Y g));

assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (X Y : τ (Obj C))
  (f : τ (Hom C X Y))
  (g : τ (Obj (@Slice_cat C Y))) ⊢
  @pullback_square_readable_cell C PB X Y f g
  : τ (Hom
      (Hom_cat C (@pullback_domain C PB X Y f g) Y)
      (@pullback_square_readable_source C PB X Y f g)
      (@pullback_square_readable_target C PB X Y f g));

// Cone recovery and uniqueness are the computational universal property.
assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (X Y : τ (Obj C))
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  (g : τ (Obj (@Slice_cat C Y))) ⊢
  @pullback_lift_func C PB X Y f a g
  : τ (Functor
      (@pullback_cone_cat C X Y f a g)
      (Hom_cat (@Slice_cat C X) a
        (@pullback_slice_obj C PB X Y f g)));

assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (X Y : τ (Obj C))
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  (g : τ (Obj (@Slice_cat C Y)))
  (h : τ (Obj (@pullback_cone_cat C X Y f a g))) ⊢
  @fapp0
    (@pullback_cone_cat C X Y f a g)
    (Hom_cat (@Slice_cat C X) a
      (@pullback_slice_obj C PB X Y f g))
    (@pullback_lift_func C PB X Y f a g)
    h
  ≡ @pullback_lift_slice C PB X Y f a g h;

assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (X Y : τ (Obj C))
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  (g : τ (Obj (@Slice_cat C Y)))
  (h : τ (Obj (@pullback_cone_cat C X Y f a g))) ⊢
  @pullback_cone_of_lift C PB X Y f a g
    (@pullback_lift_slice C PB X Y f a g h)
  ≡ h;

assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (X Y : τ (Obj C))
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  (g : τ (Obj (@Slice_cat C Y)))
  (k : τ (Hom (@Slice_cat C X)
    a (@pullback_slice_obj C PB X Y f g))) ⊢
  @pullback_lift_slice C PB X Y f a g
    (@pullback_cone_of_lift C PB X Y f a g k)
  ≡ k;

// The first ambient projection remains the honest directed slice triangle.
assert [C : Cat]
  (PB : τ (@PullbackStructure C))
  (X Y : τ (Obj C))
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  (g : τ (Obj (@Slice_cat C Y)))
  (h : τ (Obj (@pullback_cone_cat C X Y f a g))) ⊢
  @pullback_lift_fst_cell C PB X Y f a g h
  : τ (Hom
      (Hom_cat C (@slice_object_domain C X a) X)
      (@comp_fapp0 C
        (@slice_object_domain C X a)
        (@pullback_domain C PB X Y f g)
        X
        (@pullback_fst C PB X Y f g)
        (@pullback_lift C PB X Y f a g h))
      (@slice_object_arrow C X a));

// Raw ambient composites do not silently impose strictness.
assertnot [C : Cat]
  (PB : τ (@PullbackStructure C))
  (X Y : τ (Obj C))
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  (g : τ (Obj (@Slice_cat C Y)))
  (h : τ (Obj (@pullback_cone_cat C X Y f a g))) ⊢
  @comp_fapp0 C
    (@slice_object_domain C X a)
    (@pullback_domain C PB X Y f g) X
    (@pullback_fst C PB X Y f g)
    (@pullback_lift C PB X Y f a g h)
  ≡ @slice_object_arrow C X a;

assertnot [C : Cat]
  (PB : τ (@PullbackStructure C))
  (X Y : τ (Obj C))
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  (g : τ (Obj (@Slice_cat C Y)))
  (h : τ (Obj (@pullback_cone_cat C X Y f a g))) ⊢
  @comp_fapp0 C
    (@slice_object_domain C X a)
    (@pullback_domain C PB X Y f g)
    (@slice_object_domain C Y g)
    (@pullback_snd C PB X Y f g)
    (@pullback_lift C PB X Y f a g h)
  ≡ @slice_arrow_underlying
      C Y (@slice_sigma_obj C X Y f a) g h;

// Selected base change does not collapse to covariant postcomposition.
assertnot [C : Cat]
  (PB : τ (@PullbackStructure C))
  (X : τ (Obj C))
  (f : τ (Hom C X X)) ⊢
  @slice_base_change_func C PB X X f
  ≡ @slice_sigma_func C X X f;

assertnot [C : Cat]
  (PB : τ (@PullbackStructure C))
  (E : τ (Catd (Op_cat C))) ⊢
  @SliceBaseChange_catd C PB ≡ E;

// Generic Sigma-backed slice arrows expose projections without arbitrary eta.
assertnot [C : Cat]
  (U : τ (Obj C))
  (q r : τ (Obj (@Slice_cat C U)))
  (h : τ (Hom (@Slice_cat C U) q r)) ⊢
  @slice_arrow_intro
    C U q r
    (@slice_arrow_underlying C U q r h)
    (@slice_arrow_cell C U q r h)
  ≡ h;
