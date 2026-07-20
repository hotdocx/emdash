/*
  Reviewer milestone: discrete categories derive homwise path adequacy.

  The package stores set-truncated objects and native equality-valued
  groupoidality for the core inclusion. The one-way native hom-action
  extension derives `hom_to_path`; both round trips remain propositional.
*/

require open emdash.emdash3_2_eq1_hom_action;

assert [C : Cat]
  (obj_set : τ (IsSetGrpd (Obj C)))
  (core_equiv : τ (@IsGroupoidalCat C)) ⊢
  @is_discrete_cat_core_equiv C
    (@discrete_cat_intro C obj_set core_equiv)
  ≡ core_equiv;

assert [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (@= (Obj C) x y)) ⊢
  @fapp0
    (Path_cat (@= (Obj C) x y))
    (Hom_cat C x y)
    (@core_incl_hom_func C x y)
    p
  ≡ @path_to_hom C x y p;

assert [C : Cat]
  (d : τ (IsDiscreteCat C))
  (x y : τ (Obj C)) ⊢
  @discrete_core_homwise C d x y
  : τ (@OmegaEquivAlong
      Cat_cat
      (Path_cat (@= (Obj C) x y))
      (Hom_cat C x y)
      (@core_incl_hom_func C x y));

assert [C : Cat]
  (d : τ (IsDiscreteCat C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @hom_to_path C d x y f
  : τ (@= (Obj C) x y);

assert [C : Cat]
  (d : τ (IsDiscreteCat C))
  [x y : τ (Obj C)]
  (p : τ (@= (Obj C) x y)) ⊢
  @hom_to_path_path_to_hom C d x y p
  : τ (@=
      (@= (Obj C) x y)
      (@hom_to_path C d x y (@path_to_hom C x y p))
      p);

assert [C : Cat]
  (d : τ (IsDiscreteCat C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @path_to_hom_hom_to_path_path C d x y f
  : τ (@=
      (Hom C x y)
      (@path_to_hom C x y (@hom_to_path C d x y f))
      f);

assert [C : Cat]
  (d : τ (IsDiscreteCat C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @path_to_hom_hom_to_path C d x y f
  : τ (Hom
      (Hom_cat C x y)
      (@path_to_hom C x y (@hom_to_path C d x y f))
      f);

// The coherent round trips are not installed as broad runtime cancellations.
assertnot [C : Cat]
  (d : τ (IsDiscreteCat C))
  [x y : τ (Obj C)]
  (p : τ (@= (Obj C) x y)) ⊢
  @hom_to_path C d x y (@path_to_hom C x y p)
  ≡ p;

assertnot [C : Cat]
  (d : τ (IsDiscreteCat C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @path_to_hom C x y (@hom_to_path C d x y f)
  ≡ f;
