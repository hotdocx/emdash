/*
  Selected computational binary products.

  A pair x,y : C is the path-discrete Boolean diagram.  A candidate p is a
  binary product when `Obj_func(p)` represents its terminal-weighted cones via
  the existing whole `IsWeightedLimit_cov_comp` comparison.  Applying that
  comparison to the representable identity derives one internally natural
  universal cone; its two projections are evaluations at false and true.

  This transparent, rule-free module does not assert that arbitrary
  categories have products, add a componentwise cone/naturality calculus, or
  introduce a categorical pullback constructor.  A pullback may be selected
  later as a binary product in a conventional slice category.
*/

require open emdash.emdash3_2;

// Path-discrete two-object diagram selecting x at false and y at true.
symbol binary_product_diagram
  [C : Cat]
  (x y : τ (Obj C))
  : τ (Functor (Path_cat Bool_grpd) C)
≔ @fapp0
    (Path_cat (@Function_grpd Bool_grpd (Obj C)))
    (Functor_cat (Path_cat Bool_grpd) C)
    (@path_lift_func Bool_grpd C)
    (λ side : τ Bool_grpd,
      @bool_elim
        (λ _ : τ Bool_grpd, Obj C)
        x y side);

// Whole computational weighted-limit property of p as the product of x,y.
symbol IsBinaryProduct_comp
  [C : Cat]
  (x y p : τ (Obj C))
  : Grpd
≔ @IsWeightedLimit_cov_comp
    C
    (Path_cat Bool_grpd)
    Terminal_cat
    (@binary_product_diagram C x y)
    (@Terminal_prof Terminal_cat (Path_cat Bool_grpd))
    (@Obj_func C p);

// A selected binary product object and its whole universal comparison.
symbol BinaryProductPresentation
  [C : Cat]
  (x y : τ (Obj C))
  : Grpd
≔ `Σ_ p : τ (Obj C), @IsBinaryProduct_comp C x y p;

// Constructor retaining the selected object and universal comparison once.
symbol binary_product_intro
  [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (Obj C))
  (universal : τ (@IsBinaryProduct_comp C x y p))
  : τ (@BinaryProductPresentation C x y)
≔ @Struct_sigma
    (Obj C)
    (λ p0 : τ (Obj C), @IsBinaryProduct_comp C x y p0)
    p universal;

// Selected product object.
symbol binary_product_object
  [C : Cat]
  [x y : τ (Obj C)]
  (P : τ (@BinaryProductPresentation C x y))
  : τ (Obj C)
≔ sigma_Fst P;

// Retained whole universal comparison at the canonical dependent endpoint.
symbol binary_product_universal
  [C : Cat]
  [x y : τ (Obj C)]
  (P : τ (@BinaryProductPresentation C x y))
  : τ (@IsBinaryProduct_comp C x y (sigma_Fst P))
≔ sigma_Snd P;

// Universal binary cone, derived by applying the comparison to id_p.
symbol binary_product_cone
  [C : Cat]
  [x y p : τ (Obj C)]
  (universal : τ (@IsBinaryProduct_comp C x y p))
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
        (@Terminal_prof Terminal_cat (Path_cat Bool_grpd))))
≔ @weighted_limit_cov_pull
    C
    (Path_cat Bool_grpd)
    Terminal_cat
    (@binary_product_diagram C x y)
    (@Terminal_prof Terminal_cat (Path_cat Bool_grpd))
    (@Obj_func C p)
    universal
    Terminal_cat
    (@Obj_func C p)
    (@Unit_prof Terminal_cat)
    (@Prof_func_hom Terminal_cat C (@Obj_func C p));

// Uncurried whole cone from the terminal weight to the representable hom.
symbol binary_product_cone_eval
  [C : Cat]
  [x y p : τ (Obj C)]
  (universal : τ (@IsBinaryProduct_comp C x y p))
  : τ (ProfMap
      (@Prof_tensor
        Terminal_cat
        Terminal_cat
        (Path_cat Bool_grpd)
        (@Unit_prof Terminal_cat)
        (@Terminal_prof Terminal_cat (Path_cat Bool_grpd)))
      (@Hom_prof_along
        Terminal_cat
        (Path_cat Bool_grpd)
        C
        (@Obj_func C p)
        (@binary_product_diagram C x y)))
≔ @Prof_eval_cov_map
    Terminal_cat
    Terminal_cat
    (Path_cat Bool_grpd)
    (@Unit_prof Terminal_cat)
    (@Terminal_prof Terminal_cat (Path_cat Bool_grpd))
    (@Hom_prof_along
      Terminal_cat
      (Path_cat Bool_grpd)
      C
      (@Obj_func C p)
      (@binary_product_diagram C x y))
    (@binary_product_cone C x y p universal);

// Canonical point of the tensor source at one Boolean endpoint.
symbol binary_product_tensor_point
  (side : τ Bool_grpd)
  : τ (@Prof_hom
      Terminal_cat
      Terminal_cat
      (Path_cat Bool_grpd)
      (@id_func Terminal_cat)
      (@Prof_tensor
        Terminal_cat
        Terminal_cat
        (Path_cat Bool_grpd)
        (@Unit_prof Terminal_cat)
        (@Terminal_prof Terminal_cat (Path_cat Bool_grpd)))
      (@Obj_func (Path_cat Bool_grpd) side))
≔ @Prof_tensor_hom_hom
    Terminal_cat
    Terminal_cat
    Terminal_cat
    (Path_cat Bool_grpd)
    (@Unit_prof Terminal_cat)
    (@Terminal_prof Terminal_cat (Path_cat Bool_grpd))
    (@id_func Terminal_cat)
    (@Obj_func (Path_cat Bool_grpd) side)
    (@id_func Terminal_cat)
    (@Prof_id_hom Terminal_cat)
    (@Prof_terminal_hom
      Terminal_cat
      Terminal_cat
      (Path_cat Bool_grpd)
      (@id_func Terminal_cat)
      (@Obj_func (Path_cat Bool_grpd) side));

// Internally natural shaped hom from p to the selected diagram endpoint.
symbol binary_product_projection_cell
  [C : Cat]
  [x y p : τ (Obj C)]
  (universal : τ (@IsBinaryProduct_comp C x y p))
  (side : τ Bool_grpd)
  : τ (@Prof_hom
      Terminal_cat
      Terminal_cat
      (Path_cat Bool_grpd)
      (@id_func Terminal_cat)
      (@Hom_prof_along
        Terminal_cat
        (Path_cat Bool_grpd)
        C
        (@Obj_func C p)
        (@binary_product_diagram C x y))
      (@Obj_func (Path_cat Bool_grpd) side))
≔ @Prof_cell_apply
    Terminal_cat
    Terminal_cat
    (Path_cat Bool_grpd)
    Terminal_cat
    (Path_cat Bool_grpd)
    (@Prof_tensor
      Terminal_cat
      Terminal_cat
      (Path_cat Bool_grpd)
      (@Unit_prof Terminal_cat)
      (@Terminal_prof Terminal_cat (Path_cat Bool_grpd)))
    (@Hom_prof_along
      Terminal_cat
      (Path_cat Bool_grpd)
      C
      (@Obj_func C p)
      (@binary_product_diagram C x y))
    (@id_func Terminal_cat)
    (@id_func (Path_cat Bool_grpd))
    (@id_func Terminal_cat)
    (@Obj_func (Path_cat Bool_grpd) side)
    (@binary_product_cone_eval C x y p universal)
    (@binary_product_tensor_point side);

// Projection p -> diagram(side), evaluated from the internally natural cell.
symbol binary_product_projection
  [C : Cat]
  [x y p : τ (Obj C)]
  (universal : τ (@IsBinaryProduct_comp C x y p))
  (side : τ Bool_grpd)
  : τ (Hom C p
      (@fapp0
        (Path_cat Bool_grpd)
        C
        (@binary_product_diagram C x y)
        side))
≔ @fapp0
    Terminal_cat
    (Hom_cat C p
      (@fapp0
        (Path_cat Bool_grpd)
        C
        (@binary_product_diagram C x y)
        side))
    (@tapp0_fapp0
      (Product_cat (Op_cat Terminal_cat) Terminal_cat)
      Cat_cat
      (@Unit_prof Terminal_cat)
      (@Prof_reindex
        Terminal_cat
        Terminal_cat
        (Path_cat Bool_grpd)
        Terminal_cat
        (@Hom_prof_along
          Terminal_cat
          (Path_cat Bool_grpd)
          C
          (@Obj_func C p)
          (@binary_product_diagram C x y))
        (@id_func Terminal_cat)
        (@Obj_func (Path_cat Bool_grpd) side))
      (Struct_sigma Terminal_obj Terminal_obj)
      (@binary_product_projection_cell C x y p universal side))
    Terminal_obj;

// The two closed endpoint projections.
symbol binary_product_projection0
  [C : Cat]
  [x y p : τ (Obj C)]
  (universal : τ (@IsBinaryProduct_comp C x y p))
  : τ (Hom C p x)
≔ @binary_product_projection C x y p universal false;

symbol binary_product_projection1
  [C : Cat]
  [x y p : τ (Obj C)]
  (universal : τ (@IsBinaryProduct_comp C x y p))
  : τ (Hom C p y)
≔ @binary_product_projection C x y p universal true;

// Projections specialized to a selected product presentation.
symbol selected_binary_product_projection0
  [C : Cat]
  [x y : τ (Obj C)]
  (P : τ (@BinaryProductPresentation C x y))
  : τ (Hom C (sigma_Fst P) x)
≔ @binary_product_projection0 C x y (sigma_Fst P) (sigma_Snd P);

symbol selected_binary_product_projection1
  [C : Cat]
  [x y : τ (Obj C)]
  (P : τ (@BinaryProductPresentation C x y))
  : τ (Hom C (sigma_Fst P) y)
≔ @binary_product_projection1 C x y (sigma_Fst P) (sigma_Snd P);
