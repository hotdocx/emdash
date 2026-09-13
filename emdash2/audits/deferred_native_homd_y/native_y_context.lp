/* Candidate native local-y context; original families and runtime heads. */
require open emdash.emdash3_2;

symbol native_fibre_total_func [Z : Cat] (D : τ (Catd Z)) (y : τ (Obj Z))
  : τ (Functor (Fibre_cat D y) (@Sigma_cat Z D))
≔ @comp_cat_fapp0 (Fibre_cat D y)
    (Product_cat (Fibre_cat D y) (Fibre_cat D y)) (@Sigma_cat Z D)
    (@sigma_pullback_total_func (Fibre_cat D y) Z
      (@Const_func (Fibre_cat D y) Z y) D)
    (Struct_sigma (@id_func (Fibre_cat D y)) (@id_func (Fibre_cat D y)));

// A pointwise opposite of this represented pullback is constant.
symbol native_y_op_family_identity [Z : Cat] (D : τ (Catd Z))
  (x y : τ (Obj Z))
  : τ (Functord
      (@Const_catd (CoAbove2_cat (Fibre_cat D y)) (Op_cat (Hom_cat Z x y)))
      (@Pullback_catd (CoAbove2_cat (Fibre_cat D y))
        (CoAbove2_cat (@Sigma_cat Z D))
        (@Op_catd (@Sigma_cat Z D) (@native_index_hom_catd Z D x))
        (@CoAbove2_func (Fibre_cat D y) (@Sigma_cat Z D)
          (@native_fibre_total_func Z D y))))
≔ @id_funcd (CoAbove2_cat (Fibre_cat D y))
    (@Const_catd (CoAbove2_cat (Fibre_cat D y)) (Op_cat (Hom_cat Z x y)));

// Direct base-change totalization; no Sigma map or displayed laxity is used.
symbol native_y_inner_func [Z : Cat] (D : τ (Catd Z)) (x y : τ (Obj Z))
  : τ (Functor
      (Product_cat (CoAbove2_cat (Fibre_cat D y)) (Op_cat (Hom_cat Z x y)))
      (@native_index_inner_cat Z D x))
≔ @sigma_pullback_total_func
    (CoAbove2_cat (Fibre_cat D y)) (CoAbove2_cat (@Sigma_cat Z D))
    (@CoAbove2_func (Fibre_cat D y) (@Sigma_cat Z D)
      (@native_fibre_total_func Z D y))
    (@Op_catd (@Sigma_cat Z D) (@native_index_hom_catd Z D x));

// Product-coordinate introduction derived from homwise-dual involution.
symbol native_R_product_intro (A B : Cat)
  : τ (Functor (Product_cat (CoAbove2_cat A) (CoAbove2_cat B))
      (CoAbove2_cat (Product_cat A B)))
≔ @CoAbove2_func
    (CoAbove2_cat (Product_cat (CoAbove2_cat A) (CoAbove2_cat B)))
    (Product_cat A B)
    (Struct_sigma
      (@CoAbove2_func (Product_cat (CoAbove2_cat A) (CoAbove2_cat B))
        (CoAbove2_cat A) (@Product_projL_func (CoAbove2_cat A) (CoAbove2_cat B)))
      (@CoAbove2_func (Product_cat (CoAbove2_cat A) (CoAbove2_cat B))
        (CoAbove2_cat B) (@Product_projR_func (CoAbove2_cat A) (CoAbove2_cat B))));

// Whole inclusion of both local arguments into the shared native index.
symbol native_y_index_func [Z : Cat] (D : τ (Catd Z)) (x y : τ (Obj Z))
  : τ (Functor (Product_cat (Fibre_cat D y) (Transpose_cat (Hom_cat Z x y)))
      (@native_index_cat Z D x))
≔ @comp_cat_fapp0
    (Product_cat (Fibre_cat D y) (Transpose_cat (Hom_cat Z x y)))
    (CoAbove2_cat (Product_cat (CoAbove2_cat (Fibre_cat D y)) (Op_cat (Hom_cat Z x y))))
    (@native_index_cat Z D x)
    (@CoAbove2_func
      (Product_cat (CoAbove2_cat (Fibre_cat D y)) (Op_cat (Hom_cat Z x y)))
      (@native_index_inner_cat Z D x) (@native_y_inner_func Z D x y))
    (@native_R_product_intro (CoAbove2_cat (Fibre_cat D y)) (Op_cat (Hom_cat Z x y)));

// Evaluate the original whole index value on both local arguments.
symbol native_y_evaluation [Z : Cat] (D : τ (Catd Z)) (x y : τ (Obj Z))
  : τ (Functor (Product_cat (Product_cat (Functor_cat (@native_index_cat Z D x) Cat_cat) (Fibre_cat D y)) (Transpose_cat (Hom_cat Z x y))) Cat_cat)
≔ (@comp_cat_fapp0 (Product_cat (Product_cat (Functor_cat (@native_index_cat Z D x) Cat_cat) (Fibre_cat D y)) (Transpose_cat (Hom_cat Z x y))) (Product_cat (Functor_cat (@native_index_cat Z D x) Cat_cat) (@native_index_cat Z D x)) Cat_cat
  (@Eval_func (@native_index_cat Z D x) Cat_cat)
  (Struct_sigma (@comp_cat_fapp0 (Product_cat (Product_cat (Functor_cat (@native_index_cat Z D x) Cat_cat) (Fibre_cat D y)) (Transpose_cat (Hom_cat Z x y))) (Product_cat (Functor_cat (@native_index_cat Z D x) Cat_cat) (Fibre_cat D y)) (Functor_cat (@native_index_cat Z D x) Cat_cat)
  (@Product_projL_func (Functor_cat (@native_index_cat Z D x) Cat_cat) (Fibre_cat D y))
  (@Product_projL_func (Product_cat (Functor_cat (@native_index_cat Z D x) Cat_cat) (Fibre_cat D y)) (Transpose_cat (Hom_cat Z x y)))) (@comp_cat_fapp0 (Product_cat (Product_cat (Functor_cat (@native_index_cat Z D x) Cat_cat) (Fibre_cat D y)) (Transpose_cat (Hom_cat Z x y))) (Product_cat (Fibre_cat D y) (Transpose_cat (Hom_cat Z x y))) (@native_index_cat Z D x)
  (@native_y_index_func Z D x y)
  (Struct_sigma (@comp_cat_fapp0 (Product_cat (Product_cat (Functor_cat (@native_index_cat Z D x) Cat_cat) (Fibre_cat D y)) (Transpose_cat (Hom_cat Z x y))) (Product_cat (Functor_cat (@native_index_cat Z D x) Cat_cat) (Fibre_cat D y)) (Fibre_cat D y)
  (@Product_projR_func (Functor_cat (@native_index_cat Z D x) Cat_cat) (Fibre_cat D y))
  (@Product_projL_func (Product_cat (Functor_cat (@native_index_cat Z D x) Cat_cat) (Fibre_cat D y)) (Transpose_cat (Hom_cat Z x y)))) (@Product_projR_func (Product_cat (Functor_cat (@native_index_cat Z D x) Cat_cat) (Fibre_cat D y)) (Transpose_cat (Hom_cat Z x y)))))));

symbol native_y_restriction_step [Z : Cat] (D : τ (Catd Z)) (x y : τ (Obj Z))
  : τ (Functor (Product_cat (Functor_cat (@native_index_cat Z D x) Cat_cat) (Fibre_cat D y)) (Functor_cat (Transpose_cat (Hom_cat Z x y)) Cat_cat))
≔ (@comp_cat_fapp0 (Product_cat (Functor_cat (@native_index_cat Z D x) Cat_cat) (Fibre_cat D y)) (Functor_cat (Transpose_cat (Hom_cat Z x y)) (Product_cat (Product_cat (Functor_cat (@native_index_cat Z D x) Cat_cat) (Fibre_cat D y)) (Transpose_cat (Hom_cat Z x y)))) (Functor_cat (Transpose_cat (Hom_cat Z x y)) Cat_cat)
  (@comp_cat_cov_func (Transpose_cat (Hom_cat Z x y)) (Product_cat (Product_cat (Functor_cat (@native_index_cat Z D x) Cat_cat) (Fibre_cat D y)) (Transpose_cat (Hom_cat Z x y))) Cat_cat (@native_y_evaluation Z D x y))
  (@Product_pair_tele_func (Product_cat (Functor_cat (@native_index_cat Z D x) Cat_cat) (Fibre_cat D y)) (Transpose_cat (Hom_cat Z x y))));

symbol native_y_restriction_func [Z : Cat] (D : τ (Catd Z)) (x y : τ (Obj Z))
  : τ (Functor (Functor_cat (@native_index_cat Z D x) Cat_cat) (Functor_cat (Fibre_cat D y) (Functor_cat (Transpose_cat (Hom_cat Z x y)) Cat_cat)))
≔ (@comp_cat_fapp0 (Functor_cat (@native_index_cat Z D x) Cat_cat) (Functor_cat (Fibre_cat D y) (Product_cat (Functor_cat (@native_index_cat Z D x) Cat_cat) (Fibre_cat D y))) (Functor_cat (Fibre_cat D y) (Functor_cat (Transpose_cat (Hom_cat Z x y)) Cat_cat))
  (@comp_cat_cov_func (Fibre_cat D y) (Product_cat (Functor_cat (@native_index_cat Z D x) Cat_cat) (Fibre_cat D y)) (Functor_cat (Transpose_cat (Hom_cat Z x y)) Cat_cat) (@native_y_restriction_step Z D x y))
  (@Product_pair_tele_func (Functor_cat (@native_index_cat Z D x) Cat_cat) (Fibre_cat D y)));
