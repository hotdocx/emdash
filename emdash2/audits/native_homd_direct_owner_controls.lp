/* NON-LIBRARY reviewer of the copied direct native Homd candidate.
   The original primitive and stable source owners remain theory; this file
   introduces only a derived local-inclusion observation and assertions. */
require open emdash.emdash3_2;

symbol test_native_local_arrow_func [Z : Cat] (D : τ (Catd Z))
  (x y : τ (Obj Z)) (v : τ (Obj (Fibre_cat D y)))
  : τ (Functor (Transpose_cat (Hom_cat Z x y)) (@native_index_cat Z D x))
≔ @CoAbove2_func
    (Op_cat (Hom_cat Z x y)) (@native_index_inner_cat Z D x)
    (@sigma_intro_tapp0_func (CoAbove2_cat (@Sigma_cat Z D))
      (@Op_catd (@Sigma_cat Z D) (@native_index_hom_catd Z D x))
      (Struct_sigma y v));

assert [Z : Cat] [D E : τ (Catd Z)] (FF : τ (Functord D E)) ⊢
  @homd_int Z D E FF
  : τ (Functord (@Op_catd Z E) (@Homd_target_catd Z D));
assert [Z : Cat] [D E : τ (Catd Z)] (FF : τ (Functord D E))
  (x : τ (Obj Z)) ⊢
  @tapp0_fapp0 (CoAbove2_cat Z) Cat_cat
    (@Op_catd Z E) (@Homd_target_catd Z D)
    x (@homd_int Z D E FF)
  ≡ @homd_src_func Z D E FF x;
assert [Z : Cat] [D E : τ (Catd Z)] (FF : τ (Functord D E))
  (x : τ (Obj Z)) (u : τ (Obj (Fibre_cat E x))) ⊢
  @fapp0 (Op_cat (Fibre_cat E x))
    (CoAbove2_cat (Functor_cat (@native_index_cat Z D x) Cat_cat))
    (@homd_src_func Z D E FF x) u
  ≡ @homd_src_sec Z D E FF x u;

// The whole restriction recovers the original fixed-endpoint native Hom.
assert [Z : Cat] [D E : τ (Catd Z)] (FF : τ (Functord D E))
  (x y : τ (Obj Z)) (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat D y))) ⊢
  @comp_cat_fapp0 (Transpose_cat (Hom_cat Z x y))
    (@native_index_cat Z D x) Cat_cat
    (@homd_src_sec Z D E FF x u) (@test_native_local_arrow_func Z D x y v)
  ≡ @homd_ Z D E FF x u y v;

// The stable local y-functor retains its original covariant D[y] input.
assert [Z : Cat] [D E : τ (Catd Z)] (FF : τ (Functord D E))
  (x y : τ (Obj Z)) (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat D y))) ⊢
  @fapp0 (Fibre_cat D y)
    (Functor_cat (Transpose_cat (Hom_cat Z x y)) Cat_cat)
    (@homd_tgt_func Z D E FF x u y) v
  ≡ @homd_ Z D E FF x u y v;

// Both point-reduction paths: observe the folded restriction or first
// reduce the inclusion to the existing nested Sigma constructor.
assert [Z : Cat] [D E : τ (Catd Z)] (FF : τ (Functord D E))
  (x y : τ (Obj Z)) (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat D y))) (a : τ (Hom Z x y)) ⊢
  @fapp0 (Transpose_cat (Hom_cat Z x y)) Cat_cat
    (@comp_cat_fapp0 (Transpose_cat (Hom_cat Z x y))
      (@native_index_cat Z D x) Cat_cat
      (@homd_src_sec Z D E FF x u) (@test_native_local_arrow_func Z D x y v)) a
  ≡ @fapp0 (Transpose_cat (Hom_cat Z x y)) Cat_cat (@homd_ Z D E FF x u y v) a;
assert [Z : Cat] [D E : τ (Catd Z)] (FF : τ (Functord D E))
  (x y : τ (Obj Z)) (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat D y))) (a : τ (Hom Z x y)) ⊢
  @fapp0 (@native_index_cat Z D x) Cat_cat
    (@homd_src_sec Z D E FF x u) (Struct_sigma (Struct_sigma y v) a)
  ≡ @fapp0 (Transpose_cat (Hom_cat Z x y)) Cat_cat (@homd_ Z D E FF x u y v) a;

// Full first-hom action of the restricted functor should retain homd_.
assert [Z : Cat] [D E : τ (Catd Z)] (FF : τ (Functord D E))
  (x y : τ (Obj Z)) (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat D y))) (a b : τ (Hom Z x y)) ⊢
  @fapp1_func (Transpose_cat (Hom_cat Z x y)) Cat_cat
    (@comp_cat_fapp0 (Transpose_cat (Hom_cat Z x y))
      (@native_index_cat Z D x) Cat_cat
      (@homd_src_sec Z D E FF x u) (@test_native_local_arrow_func Z D x y v)) a b
  ≡ @fapp1_func (Transpose_cat (Hom_cat Z x y)) Cat_cat (@homd_ Z D E FF x u y v) a b;

// The whole target is shifted; dropping that shift is a different type.
assertnot [Z : Cat] (D : τ (Catd Z)) ⊢
  @Homd_target_catd Z D : τ (Catd (CoOnly2_cat Z));
assertnot [Z : Cat] [D E : τ (Catd Z)] (FF : τ (Functord D E))
  (x : τ (Obj Z)) ⊢
  @homd_src_func Z D E FF x
  : τ (Functor (Op_cat (Fibre_cat E x))
      (Functor_cat (@native_index_cat Z D x) Cat_cat));

// Homwise duality recovers the ordinary source-contravariant presentation.
assert [Z : Cat] [D E : τ (Catd Z)] (FF : τ (Functord D E))
  (x : τ (Obj Z)) ⊢
  @CoAbove2_func (Op_cat (Fibre_cat E x))
    (CoAbove2_cat (Functor_cat (@native_index_cat Z D x) Cat_cat))
    (@homd_src_func Z D E FF x)
  : τ (Functor (Transpose_cat (Fibre_cat E x))
      (Functor_cat (@native_index_cat Z D x) Cat_cat));

// A genuine base 2-cell is observed through the recovered Homd functor.
assert [Z : Cat] [D E : τ (Catd Z)] (FF : τ (Functord D E))
  (x y : τ (Obj Z)) (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat D y))) (a b : τ (Hom Z x y))
  (alpha : τ (Hom (Hom_cat Z x y) b a)) ⊢
  @fapp1_fapp0 (Transpose_cat (Hom_cat Z x y)) Cat_cat
    (@comp_cat_fapp0 (Transpose_cat (Hom_cat Z x y))
      (@native_index_cat Z D x) Cat_cat
      (@homd_src_sec Z D E FF x u) (@test_native_local_arrow_func Z D x y v)) a b alpha
  ≡ @fapp1_fapp0 (Transpose_cat (Hom_cat Z x y)) Cat_cat
      (@homd_ Z D E FF x u y v) a b alpha;

// Existing internal displayed-Hom action still composes with Op_funcd.
assert [K : Cat] [E D : τ (Catd K)] (FF GG : τ (Functord E D)) ⊢
  @tdapp1_int_func_transfd K E D FF GG
  : τ (Functor (Transfd_cat FF GG)
      (Transfd_cat (homd_int (@id_funcd K E))
        (comp_catd_fapp0 (homd_int GG) (Op_funcd FF))));

// Its first source-component fold only needs the correctly inferred base.
assert [K : Cat] [E D : τ (Catd K)] (FF : τ (Functord E D))
  (x : τ (Obj K)) (u : τ (Obj (Fibre_cat E x))) ⊢
  @tapp0_fapp0 _ _ _ _ u
    (@tdapp0_fapp0 (CoAbove2_cat K) _ _ _ _ x
      (@fdapp1_int_transfd K E D FF))
  ≡ @fdapp1_int_section_arrow K E D FF x u;
