/*
  Reviewer for the generic whole PathOut lift of an ordinary transformation.

  The source of the total component is aligned through the same stable
  post/precomposition and whole-transport chain used by the ordinal
  tetrahedron. Its fibre arrow remains the extracted pre/right laxity cell,
  reframed only by equality-induced source and target action. The resulting
  transformation retains its ordinary next hom action.
*/

require open emdash.emdash3_2_pathout_transformation_lift;

// Both endpoint comparisons are first-class paths, not runtime folds.
type λ A : Cat, λ B : Cat,
  λ F : τ (Functor A B), λ G : τ (Functor A B),
  λ epsilon : τ (Transf F G),
  λ x : τ (Obj A), λ y : τ (Obj A),
  λ p : τ (Hom A x y),
    @pathout_sigma_top_source_path A B F G epsilon x y p;

type λ A : Cat, λ B : Cat,
  λ F : τ (Functor A B), λ G : τ (Functor A B),
  λ epsilon : τ (Transf F G),
  λ x : τ (Obj A), λ y : τ (Obj A),
  λ p : τ (Hom A x y),
    @pathout_transf_formal_target_path A B F G epsilon x y p;

// The total component is constructed from the extracted laxity cell.
type λ A : Cat, λ B : Cat,
  λ F : τ (Functor A B), λ G : τ (Functor A B),
  λ epsilon : τ (Transf F G),
  λ x : τ (Obj A), λ y : τ (Obj A),
  λ p : τ (Hom A x y),
    @pathout_transf_fibre_cell A B F G epsilon x y p;

type λ A : Cat, λ B : Cat,
  λ F : τ (Functor A B), λ G : τ (Functor A B),
  λ epsilon : τ (Transf F G),
  λ x : τ (Obj A), λ y : τ (Obj A),
  λ p : τ (Hom A x y),
    @pathout_transf_component A B F G epsilon x y p;

// Constructor-visible component computation.
assert [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj A))
  (p : τ (Hom A x y)) ⊢
  @tapp0_fapp0
    (@PathOut_cat A x)
    (@PathOut_cat B (@fapp0 A B F x))
    (@pathout_map_func A B F x)
    (@pathout_transf_target_func A B F G epsilon x)
    (Struct_sigma y p)
    (@pathout_transf_lift A B F G epsilon x)
  ≡ @pathout_transf_component A B F G epsilon x y p;

// The whole transformation remains iterable one dimension higher.
type λ A : Cat, λ B : Cat,
  λ F : τ (Functor A B), λ G : τ (Functor A B),
  λ epsilon : τ (Transf F G), λ x : τ (Obj A),
  λ u : τ (Obj (@PathOut_cat A x)),
  λ v : τ (Obj (@PathOut_cat A x)),
    @tapp1_func
      (@PathOut_cat A x)
      (@PathOut_cat B (@fapp0 A B F x))
      (@pathout_map_func A B F x)
      (@pathout_transf_target_func A B F G epsilon x)
      u v
      (@pathout_transf_lift A B F G epsilon x);

// A component indexed by p cannot inhabit the q-indexed endpoint hom.
assertnot [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj A))
  (p q : τ (Hom A x y)) ⊢
  @pathout_transf_component A B F G epsilon x y p
  : τ (Hom
      (@PathOut_cat B (@fapp0 A B F x))
      (@fapp0
        (@PathOut_cat A x)
        (@PathOut_cat B (@fapp0 A B F x))
        (@pathout_map_func A B F x)
        (Struct_sigma y q))
      (@fapp0
        (@PathOut_cat A x)
        (@PathOut_cat B (@fapp0 A B F x))
        (@pathout_transf_target_func A B F G epsilon x)
        (Struct_sigma y q)));

// The derived fibre cell does not collapse to an arbitrary replacement.
assertnot [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj A))
  (p : τ (Hom A x y))
  (replacement : τ (Hom
    (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
    (@pathout_sigma_source A B F G epsilon x y p)
    (@tapp1_fapp0 A B F G x y epsilon p))) ⊢
  @pathout_transf_fibre_cell A B F G epsilon x y p
  ≡ replacement;
