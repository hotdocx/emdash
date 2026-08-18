/*
  Standard semisimplices and groupoid-valued semisimplicial diagrams.

  StandardSimplex(n) is the existing Yoneda representable of the internal
  augmented semi-simplex category. Groupoid-valued diagrams are ordinary
  functors from its opposite into Grpd_cat. Whole Cat realization is generic
  postcomposition with Path_cat_func.

  The whole realization functor deliberately retains the raw
  Functor_cat(Delta_+^op,Cat) target. The public Psh_cat facade is a distinct
  runtime category head; existing object and Hom projections accept the
  realized objects and maps without pretending those category heads are
  definitionally equal. No new action, naturality rule, or unifier is added.
*/

require open emdash.emdash3_2_semisimplicial_index;
require open emdash.emdash3_2_presheaves;

// Standard representable semisimplex Delta[n] = Hom(-,n).
symbol StandardSimplex
  (n : τ (Obj SemiDeltaPlus_cat))
  : τ (@Psh SemiDeltaPlus_cat)
≔ @yoneda_psh SemiDeltaPlus_cat n;

// Groupoid-valued semisimplicial diagrams.
symbol SemiSimplicialGrpd_cat
  : Cat
≔ @Functor_cat (Op_cat SemiDeltaPlus_cat) Grpd_cat;

// Public Cat-valued presheaf facade.
symbol SemiSimplicialCat_cat
  : Cat
≔ @Psh_cat SemiDeltaPlus_cat;

// Raw whole-action owner underlying the public Cat-valued facade.
symbol SemiSimplicialCatRaw_cat
  : Cat
≔ @Functor_cat (Op_cat SemiDeltaPlus_cat) Cat_cat;

// Whole generic realization by postcomposition with Path_cat_func.
symbol semisimplicial_grpd_realize_raw_func
  : τ (Functor
      SemiSimplicialGrpd_cat
      SemiSimplicialCatRaw_cat)
≔ @comp_cat_cov_func
    (Op_cat SemiDeltaPlus_cat)
    Grpd_cat
    Cat_cat
    Path_cat_func;

// Public realized presheaf object.
symbol semisimplicial_grpd_realize
  (X : τ (Obj SemiSimplicialGrpd_cat))
  : τ (@Psh SemiDeltaPlus_cat)
≔ @fapp0
    SemiSimplicialGrpd_cat
    SemiSimplicialCatRaw_cat
    semisimplicial_grpd_realize_raw_func
    X;

// Level n of a groupoid-valued diagram.
symbol semisimplicial_grpd_level
  [X : τ (Obj SemiSimplicialGrpd_cat)]
  (n : τ Nat_grpd)
  : Grpd
≔ @fapp0
    (Op_cat SemiDeltaPlus_cat)
    Grpd_cat
    X n;

// Contravariant action of a face code on levels.
symbol semisimplicial_grpd_face_map
  [X : τ (Obj SemiSimplicialGrpd_cat)]
  [p n : τ Nat_grpd]
  (f : τ (@FaceCode p n))
  : τ (@Function_grpd
      (@semisimplicial_grpd_level X n)
      (@semisimplicial_grpd_level X p))
≔ @fapp1_fapp0
    (Op_cat SemiDeltaPlus_cat)
    Grpd_cat
    X n p f;

// The realized face action is the iterable Path action of that function.
symbol semisimplicial_grpd_realized_face_func
  [X : τ (Obj SemiSimplicialGrpd_cat)]
  [p n : τ Nat_grpd]
  (f : τ (@FaceCode p n))
  : τ (Functor
      (Path_cat (@semisimplicial_grpd_level X n))
      (Path_cat (@semisimplicial_grpd_level X p)))
≔ @fapp1_fapp0
    (Op_cat SemiDeltaPlus_cat)
    Cat_cat
    (@semisimplicial_grpd_realize X)
    n p f;

// Generic map action, viewed through the public presheaf Hom facade.
symbol semisimplicial_grpd_realize_map
  [X Y : τ (Obj SemiSimplicialGrpd_cat)]
  (eta : τ (Hom SemiSimplicialGrpd_cat X Y))
  : τ (Hom
      SemiSimplicialCat_cat
      (@semisimplicial_grpd_realize X)
      (@semisimplicial_grpd_realize Y))
≔ @fapp1_fapp0
    SemiSimplicialGrpd_cat
    SemiSimplicialCatRaw_cat
    semisimplicial_grpd_realize_raw_func
    X Y eta;
