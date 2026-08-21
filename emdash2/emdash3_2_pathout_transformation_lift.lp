/*
  Generic whole PathOut lift of an ordinary transformation epsilon : F => G.

  At a fixed source x, the target functor sends (y,p) to (G[y],epsilon[p]).
  Its total component has base epsilon[y] and fibre the existing pre/right
  laxity cell.  The source and target are reframed only through typed
  equality-induced hom action, so the construction preserves rather than
  collapses laxity.  One constructor-visible component beta is owned here;
  generic tapp1 action remains available for the next dependent-simplex
  successor.  No endpoint rewrite or proof-time unifier is introduced.
*/

require open emdash.emdash3_2_pathout_transformation_reframing;
require open emdash.emdash3_2_dependent_simplex_native_dimensions;

// (y,p) |-> (G[y],epsilon[p]) in PathOut_B(F[x]).
symbol pathout_transf_target_func
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x : τ (Obj A))
  : τ (Functor
      (@PathOut_cat A x)
      (@PathOut_cat B (@fapp0 A B F x)))
≔ @comp_cat_fapp0
    (@PathOut_cat A x)
    (@Sigma_cat A (@hom_ B A G (@fapp0 A B F x)))
    (@PathOut_cat B (@fapp0 A B F x))
    (@sigma_pullback_total_func
      A B G (@Rep_catd B (@fapp0 A B F x)))
    (@sigma_map_func
      A
      (@Rep_catd A x)
      (@hom_ B A G (@fapp0 A B F x))
      (@tapp1_at_transf A B F G x epsilon));

symbol pathout_transf_formal_source
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj A))
  (p : τ (Hom A x y))
  : τ (Obj (Hom_cat B
      (@fapp0 A B F x)
      (@fapp0 A B G y)))
≔ @fapp0
    (Hom_cat A y y)
    (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
    (@pathout_top_lhs_func A B F G epsilon x y p)
    (@id A y);

symbol pathout_transf_top_rhs_func
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj A))
  (p : τ (Hom A x y))
  : τ (Functor
      (Hom_cat A y y)
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y)))
≔ @functord_transport_rhs_func
    (Op_cat A)
    (@hom_con A y A (@id_func A))
    (@hom_con B (@fapp0 A B G y) A F)
    (@tapp1_con_at_transf A B F G epsilon y)
    y x p;

symbol pathout_transf_formal_target
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj A))
  (p : τ (Hom A x y))
  : τ (Obj (Hom_cat B
      (@fapp0 A B F x)
      (@fapp0 A B G y)))
≔ @fapp0
    (Hom_cat A y y)
    (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
    (@pathout_transf_top_rhs_func A B F G epsilon x y p)
    (@id A y);

// Whole pre/right strict naturality, evaluated only after the functor path is
// formed, compares the formal target with the direct off-diagonal action.
symbol pathout_transf_formal_target_path
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj A))
  (p : τ (Hom A x y))
  : τ (@=
      (Obj (Hom_cat B
        (@fapp0 A B F x)
        (@fapp0 A B G y)))
      (@pathout_transf_formal_target
        A B F G epsilon x y p)
      (@tapp1_fapp0 A B F G x y epsilon p))
≔ @eq_ap
    (Hom Cat_cat
      (Hom_cat A y y)
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y)))
    (Obj (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y)))
    (λ H : τ (Functor
        (Hom_cat A y y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))),
      @fapp0
        (Hom_cat A y y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
        H
        (@id A y))
    (@pathout_top_lhs_func A B F G epsilon x y p)
    (@pathout_transf_top_rhs_func A B F G epsilon x y p)
    (@functord_transport_strict_naturality
      (Op_cat A)
      (@hom_con A y A (@id_func A))
      (@hom_con B (@fapp0 A B G y) A F)
      (@tapp1_con_at_transf A B F G epsilon y)
      y x p);

// Reframe the source of the extracted cell along the generic represented
// source path. The cell itself remains tapp1_pre_laxity_cell.
symbol pathout_transf_source_reframe_func
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj A))
  (p : τ (Hom A x y))
  : τ (Functor
      (Hom_cat
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
        (@pathout_transf_formal_source
          A B F G epsilon x y p)
        (@pathout_transf_formal_target
          A B F G epsilon x y p))
      (Hom_cat
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
        (@pathout_sigma_source A B F G epsilon x y p)
        (@pathout_transf_formal_target
          A B F G epsilon x y p)))
≔ @hom_precomp_along_func
    (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
    (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
    (@id_func (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y)))
    (@pathout_transf_formal_target
      A B F G epsilon x y p)
    (@pathout_sigma_source A B F G epsilon x y p)
    (@pathout_transf_formal_source
      A B F G epsilon x y p)
    (@path_to_hom
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
      (@pathout_sigma_source A B F G epsilon x y p)
      (@pathout_transf_formal_source
        A B F G epsilon x y p)
      (@pathout_sigma_top_source_path A B F G epsilon x y p));

symbol pathout_transf_source_reframed_cell
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj A))
  (p : τ (Hom A x y))
  : τ (Hom
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
      (@pathout_sigma_source A B F G epsilon x y p)
      (@pathout_transf_formal_target
        A B F G epsilon x y p))
≔ @fapp0
    (Hom_cat
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
      (@pathout_transf_formal_source
        A B F G epsilon x y p)
      (@pathout_transf_formal_target
        A B F G epsilon x y p))
    (Hom_cat
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
      (@pathout_sigma_source A B F G epsilon x y p)
      (@pathout_transf_formal_target
        A B F G epsilon x y p))
    (@pathout_transf_source_reframe_func
      A B F G epsilon x y p)
    (@tapp1_pre_laxity_cell
      A B F G epsilon x y y p (@id A y));

// Reframe the target by ordinary represented postcomposition.
symbol pathout_transf_target_reframe_func
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj A))
  (p : τ (Hom A x y))
  : τ (Functor
      (Hom_cat
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
        (@pathout_sigma_source A B F G epsilon x y p)
        (@pathout_transf_formal_target
          A B F G epsilon x y p))
      (Hom_cat
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
        (@pathout_sigma_source A B F G epsilon x y p)
        (@tapp1_fapp0 A B F G x y epsilon p)))
≔ @hom_postcomp_func
    (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
    (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
    (@id_func (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y)))
    (@pathout_sigma_source A B F G epsilon x y p)
    (@pathout_transf_formal_target
      A B F G epsilon x y p)
    (@tapp1_fapp0 A B F G x y epsilon p)
    (@path_to_hom
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
      (@pathout_transf_formal_target
        A B F G epsilon x y p)
      (@tapp1_fapp0 A B F G x y epsilon p)
      (@pathout_transf_formal_target_path
        A B F G epsilon x y p));

symbol pathout_transf_fibre_cell
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj A))
  (p : τ (Hom A x y))
  : τ (Hom
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
      (@pathout_sigma_source A B F G epsilon x y p)
      (@tapp1_fapp0 A B F G x y epsilon p))
≔ @fapp0
    (Hom_cat
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
      (@pathout_sigma_source A B F G epsilon x y p)
      (@pathout_transf_formal_target
        A B F G epsilon x y p))
    (Hom_cat
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
      (@pathout_sigma_source A B F G epsilon x y p)
      (@tapp1_fapp0 A B F G x y epsilon p))
    (@pathout_transf_target_reframe_func
      A B F G epsilon x y p)
    (@pathout_transf_source_reframed_cell
      A B F G epsilon x y p);

symbol pathout_transf_component
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj A))
  (p : τ (Hom A x y))
  : τ (Hom
      (@PathOut_cat B (@fapp0 A B F x))
      (@fapp0
        (@PathOut_cat A x)
        (@PathOut_cat B (@fapp0 A B F x))
        (@pathout_map_func A B F x)
        (Struct_sigma y p))
      (@fapp0
        (@PathOut_cat A x)
        (@PathOut_cat B (@fapp0 A B F x))
        (@pathout_transf_target_func A B F G epsilon x)
        (Struct_sigma y p)))
≔ @sigma_arrow
    B
    (@Rep_catd B (@fapp0 A B F x))
    (@fapp0 A B F y)
    (@fapp0 A B G y)
    (@fapp1_fapp0 A B F x y p)
    (@tapp1_fapp0 A B F G x y epsilon p)
    (@tapp0_fapp0 A B F G y epsilon)
    (@pathout_transf_fibre_cell
      A B F G epsilon x y p);

// Whole successor owner. Its generic tapp1 action is retained.
injective symbol pathout_transf_lift
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (x : τ (Obj A))
  : τ (Transf
      (@pathout_map_func A B F x)
      (@pathout_transf_target_func A B F G epsilon x));

rule @tapp0_fapp0
      _ _ _ _
      (Struct_sigma $y $p)
      (@pathout_transf_lift $A $B $F $G $epsilon $x)
  ↪ @pathout_transf_component
      $A $B $F $G $epsilon $x $y $p;
