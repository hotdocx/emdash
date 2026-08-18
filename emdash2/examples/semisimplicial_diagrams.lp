/*
  Focused reviewer for standard semisimplices and groupoid-valued diagrams.

  Yoneda owns standard-simplex restriction. Path_cat_func owns realization of
  levels, faces, diagram maps, and all higher action. The public Psh facade
  remains distinct from the raw whole-action category.
*/

require open emdash.emdash3_2_semisimplicial_diagrams;

assert ⊢
  SemiSimplicialGrpd_cat
  ≡ @Functor_cat (Op_cat SemiDeltaPlus_cat) Grpd_cat;

assert ⊢
  SemiSimplicialCat_cat
  ≡ @Psh_cat SemiDeltaPlus_cat;

assert ⊢
  SemiSimplicialCatRaw_cat
  ≡ @Functor_cat (Op_cat SemiDeltaPlus_cat) Cat_cat;

// The rigid presheaf facade is not a runtime alias for the raw owner.
assertnot ⊢
  SemiSimplicialCat_cat
  ≡ SemiSimplicialCatRaw_cat;

// Yoneda evaluates a standard simplex to its represented face-code Hom.
assert (p n : τ Nat_grpd) ⊢
  Fibre_cat (@StandardSimplex n) p
  ≡ Hom_cat SemiDeltaPlus_cat p n;

assert (n : τ Nat_grpd) ⊢
  @StandardSimplex n
  ≡ @yoneda_psh SemiDeltaPlus_cat n;

// Realization computes levelwise to a path category.
assert
  (X : τ (Obj SemiSimplicialGrpd_cat))
  (n : τ Nat_grpd) ⊢
  Fibre_cat (@semisimplicial_grpd_realize X) n
  ≡ Path_cat (@semisimplicial_grpd_level X n);

// Face action is the existing iterable path action of the groupoid function.
assert
  (X : τ (Obj SemiSimplicialGrpd_cat))
  [p n : τ Nat_grpd]
  (f : τ (@FaceCode p n)) ⊢
  @semisimplicial_grpd_realized_face_func X p n f
  ≡ @path_map_func
      (@semisimplicial_grpd_level X n)
      (@semisimplicial_grpd_level X p)
      (@semisimplicial_grpd_face_map X p n f);

// Diagram maps are the generic postcomposition action, viewed in Psh_cat.
assert
  (X Y : τ (Obj SemiSimplicialGrpd_cat))
  (eta : τ (Hom SemiSimplicialGrpd_cat X Y)) ⊢
  @semisimplicial_grpd_realize_map X Y eta
  : τ (Hom
      SemiSimplicialCat_cat
      (@semisimplicial_grpd_realize X)
      (@semisimplicial_grpd_realize Y));

// One further action stays at the raw generic whole-functor owner.
assert
  (X Y : τ (Obj SemiSimplicialGrpd_cat)) ⊢
  @fapp1_func
    SemiSimplicialGrpd_cat
    SemiSimplicialCatRaw_cat
    semisimplicial_grpd_realize_raw_func
    X Y
  : τ (Functor
      (Hom_cat SemiSimplicialGrpd_cat X Y)
      (Hom_cat
        SemiSimplicialCatRaw_cat
        (@semisimplicial_grpd_realize X)
        (@semisimplicial_grpd_realize Y)));

// Representability is not asserted for an arbitrary realized diagram.
assertnot
  (X : τ (Obj SemiSimplicialGrpd_cat))
  (n : τ Nat_grpd) ⊢
  @StandardSimplex n
  ≡ @semisimplicial_grpd_realize X;
