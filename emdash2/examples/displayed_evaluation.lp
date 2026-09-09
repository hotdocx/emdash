/* Structural displayed evaluation: whole action, point computation,
   transported-identity projection orders, and noncollapse controls.
   The general op/Sigma variance repair is deliberately not claimed here. */
require open emdash.emdash3_2;

// The actual source family of Eval_funcd, named only for these reviewers.
symbol eval_order_domain [K : Cat] (I : Cat) (E : τ (Catd K)) : τ (Catd K)
≔ @comp_cat_fapp0 K (Product_cat Cat_cat Cat_cat) Cat_cat
    (@uncurry_func Cat_cat Cat_cat Cat_cat Product_cat_func)
    (Struct_sigma (@Functor_catd K (@Const_catd (Op_cat K) I) E)
      (@Const_catd K I));

symbol eval_order_transport [K : Cat] (R : τ (Catd K))
  [x y : τ (Obj K)] (p : τ (Hom K x y)) (u : τ (Obj (Fibre_cat R x)))
  : τ (Obj (Fibre_cat R y))
≔ @fapp0 (Fibre_cat R x) (Fibre_cat R y) (@catd_transport_func K R x y p) u;

symbol eval_order_leading [K I : Cat] [R E : τ (Catd K)]
  (FF : τ (Functord R (@eval_order_domain K I E))) : τ (Functord R E)
≔ @comp_catd_fapp0 K R (@eval_order_domain K I E) E (@Eval_funcd K I E) FF;

// Canonical carrier of one extracted cell, retaining its actual endpoint owners.
symbol eval_order_cell_cat [K : Cat] [R E : τ (Catd K)]
  (FF : τ (Functord R E)) [x y : τ (Obj K)]
  (p : τ (Hom K x y)) (u : τ (Obj (Fibre_cat R x))) : Cat
≔ Hom_cat (Fibre_cat E y)
    (@fapp0 _ _ (@functord_transport_lhs_func K R E FF x y p) u)
    (@fapp0 _ _ (@functord_transport_rhs_func K R E FF x y p) u);

assert [K : Cat] (R E D : τ (Catd K))
  (FF : τ (Functord R E)) (GG : τ (Functord R D))
  [x y : τ (Obj K)] (p : τ (Hom K x y)) (u : τ (Obj (Fibre_cat R x))) ⊢
  @fdapp1_int_cell K R _ (@Product_pair_funcd K R E D FF GG) x y p u
  ≡ @Product_pair (@eval_order_cell_cat K R E FF x y p u)
      (@eval_order_cell_cat K R D GG x y p u)
      (@fdapp1_int_cell K R E FF x y p u)
      (@fdapp1_int_cell K R D GG x y p u);

// Explicitly take the whole-pair-first route, bypassing the transported-id
// recognizer on the parent action, and compare with its extracted cell.
assert [K : Cat] (R E D : τ (Catd K))
  (FF : τ (Functord R E)) (GG : τ (Functord R D))
  [x y : τ (Obj K)] (p : τ (Hom K x y)) (u : τ (Obj (Fibre_cat R x))) ⊢
  @fapp0
    (Hom_cat (Fibre_cat R y) (@eval_order_transport K R x y p u) (@eval_order_transport K R x y p u))
    (Product_cat (@eval_order_cell_cat K R E FF x y p u) (@eval_order_cell_cat K R D GG x y p u))
    (@Product_pair
      (Functor_cat
        (Hom_cat (Fibre_cat R y) (@eval_order_transport K R x y p u) (@eval_order_transport K R x y p u))
        (@eval_order_cell_cat K R E FF x y p u))
      (Functor_cat
        (Hom_cat (Fibre_cat R y) (@eval_order_transport K R x y p u) (@eval_order_transport K R x y p u))
        (@eval_order_cell_cat K R D GG x y p u))
      (@fdapp1_int_hom_func K R E FF x y p u (@eval_order_transport K R x y p u))
      (@fdapp1_int_hom_func K R D GG x y p u (@eval_order_transport K R x y p u)))
    (@id (Fibre_cat R y) (@eval_order_transport K R x y p u))
  ≡ @fdapp1_int_cell K R _ (@Product_pair_funcd K R E D FF GG) x y p u;

assert [K : Cat] (R E D : τ (Catd K))
  (FF : τ (Functord R E)) (GG : τ (Functord R D))
  [x y : τ (Obj K)] (p : τ (Hom K x y)) (u : τ (Obj (Fibre_cat R x))) ⊢
  @fdapp1_int_cell K _ _ (@Op_funcd K _ _ (@Product_pair_funcd K R E D FF GG)) x y p u
  ≡ @Product_pair
      (@eval_order_cell_cat K (@Op_catd K R) (@Op_catd K E) (@Op_funcd K R E FF) x y p u)
      (@eval_order_cell_cat K (@Op_catd K R) (@Op_catd K D) (@Op_funcd K R D GG) x y p u)
      (@fdapp1_int_cell K (@Op_catd K R) (@Op_catd K E) (@Op_funcd K R E FF) x y p u)
      (@fdapp1_int_cell K (@Op_catd K R) (@Op_catd K D) (@Op_funcd K R D GG) x y p u);

assert [K I : Cat] (E : τ (Catd K)) [x y : τ (Obj K)]
  (p : τ (Hom K x y)) (U : τ (Functor I (Fibre_cat E x))) (i : τ (Obj I)) ⊢
  @fdapp1_int_cell K _ _ (@Op_funcd K _ _ (@Eval_funcd K I E))
    x y p (Struct_sigma U i)
  ≡ @id (Op_cat (Fibre_cat E y))
      (@fapp0 (Fibre_cat E x) (Fibre_cat E y)
        (@catd_transport_func K E x y p) (@fapp0 I (Fibre_cat E x) U i));

assert [K I : Cat] (R E : τ (Catd K))
  (FF : τ (Functord R (@eval_order_domain K I E)))
  [x y : τ (Obj K)] (p : τ (Hom K x y)) (u : τ (Obj (Fibre_cat R x))) ⊢
  @fdapp1_int_cell K _ _ (@Op_funcd K R E (@eval_order_leading K I R E FF)) x y p u
  ≡ @fdapp1_int_hom_fapp0 K (@Op_catd K (@eval_order_domain K I E)) (@Op_catd K E)
      (@Op_funcd K (@eval_order_domain K I E) E (@Eval_funcd K I E)) x y p
      (@fapp0 (Fibre_cat R x) (Fibre_cat (@eval_order_domain K I E) x)
        (@Fibre_func K R (@eval_order_domain K I E) FF x) u)
      (@fapp0 (Fibre_cat R y) (Fibre_cat (@eval_order_domain K I E) y)
        (@Fibre_func K R (@eval_order_domain K I E) FF y)
        (@eval_order_transport K R x y p u))
      (@fdapp1_int_cell K (@Op_catd K R) (@Op_catd K (@eval_order_domain K I E))
        (@Op_funcd K R (@eval_order_domain K I E) FF) x y p u);

/* Explicit transported-identity route of structural evaluation. */

assert [K I : Cat] (E : τ (Catd K)) [x y : τ (Obj K)]
  (p : τ (Hom K x y)) (U : τ (Functor I (Fibre_cat E x)))
  (i : τ (Obj I)) ⊢
  @fdapp1_int_cell K _ E (@Eval_funcd K I E) x y p (Struct_sigma U i)
  ≡ @id (Fibre_cat E y)
      (@fapp0 (Fibre_cat E x) (Fibre_cat E y)
        (@catd_transport_func K E x y p) (@fapp0 I (Fibre_cat E x) U i));

assert [K I : Cat] (R E : τ (Catd K))
  (FF : τ (Functord R (@eval_order_domain K I E)))
  [x y : τ (Obj K)] (p : τ (Hom K x y)) (u : τ (Obj (Fibre_cat R x))) ⊢
  @fdapp1_int_cell K R E (@eval_order_leading K I R E FF) x y p u
  ≡ @fdapp1_int_hom_fapp0 K (@eval_order_domain K I E) E (@Eval_funcd K I E)
      x y p
      (@fapp0 (Fibre_cat R x) (Fibre_cat (@eval_order_domain K I E) x)
        (@Fibre_func K R (@eval_order_domain K I E) FF x) u)
      (@fapp0 (Fibre_cat R y) (Fibre_cat (@eval_order_domain K I E) y)
        (@Fibre_func K R (@eval_order_domain K I E) FF y)
        (@eval_order_transport K R x y p u))
      (@fdapp1_int_cell K R (@eval_order_domain K I E) FF x y p u);

/* Generic weakening reduces to this original constant-section cell. */

assert [K I : Cat] (i : τ (Obj I)) [x y : τ (Obj K)]
  (p : τ (Hom K x y)) ⊢
  @fdapp1_int_cell K (@Const_catd K Terminal_cat) (@Const_catd K I)
    (@Const_func K I i) x y p Terminal_obj
  ≡ @id I i;

// Positive typing makes the following negative a genuine non-collapse test.
assert [K I : Cat] (s : τ (Functor K I)) (x : τ (Obj K)) (p : τ (Hom K x x)) ⊢
  @fdapp1_int_cell K (@Const_catd K Terminal_cat) (@Const_catd K I)
    s x x p Terminal_obj
  : τ (Hom I (@fapp0 K I s x) (@fapp0 K I s x));

assertnot [K I : Cat] (s : τ (Functor K I)) (x : τ (Obj K)) (p : τ (Hom K x x)) ⊢
  @fdapp1_int_cell K (@Const_catd K Terminal_cat) (@Const_catd K I)
    s x x p Terminal_obj
  ≡ @id I (@fapp0 K I s x);

// Generic mapped-arrow composition retains its existing accumulation direction.
assert [A B : Cat] (F : τ (Functor A B)) [x y z : τ (Obj A)]
  (f : τ (Hom A x y)) (g : τ (Hom A y z)) ⊢
  @comp_fapp0 B _ _ _ (@fapp1_fapp0 A B F y z g) (@fapp1_fapp0 A B F x y f)
  ≡ @fapp1_fapp0 A B F x z (@comp_fapp0 A x y z g f);

// The concrete leading-Eval composite agrees with the two-stage total action.
assert [K I : Cat] (R E : τ (Catd K))
  (FF : τ (Functord R (@eval_order_domain K I E)))
  [x y : τ (Obj K)] (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat R x))) (v : τ (Obj (Fibre_cat R y)))
  (alpha : τ (Hom (Fibre_cat R y) (@eval_order_transport K R x y p u) v)) ⊢
  @fapp1_fapp0 (@Sigma_cat K R) (@Sigma_cat K E)
    (@comp_cat_fapp0 (@Sigma_cat K R) (@Sigma_cat K (@eval_order_domain K I E)) (@Sigma_cat K E)
      (@sigma_map_func K (@eval_order_domain K I E) E (@Eval_funcd K I E))
      (@sigma_map_func K R (@eval_order_domain K I E) FF))
    (Struct_sigma x u) (Struct_sigma y v) (@sigma_arrow K R x y u v p alpha)
  ≡ @fapp1_fapp0 (@Sigma_cat K R) (@Sigma_cat K E)
      (@sigma_map_func K R E (@eval_order_leading K I R E FF))
      (Struct_sigma x u) (Struct_sigma y v) (@sigma_arrow K R x y u v p alpha);

// Operator hom-action still returns a whole functor, with a next Hom action.
type λ K : Cat, λ I : Cat, λ R : τ (Catd K), λ E : τ (Catd K),
  λ FF : τ (Functord R (@eval_order_domain K I E)),
  λ x : τ (Obj K), λ y : τ (Obj K), λ p : τ (Hom K x y),
  λ u : τ (Obj (Fibre_cat R x)), λ v : τ (Obj (Fibre_cat R y)),
  λ alpha : τ (Hom (Fibre_cat R y) (@eval_order_transport K R x y p u) v),
  λ beta : τ (Hom (Fibre_cat R y) (@eval_order_transport K R x y p u) v),
  @fapp1_func _ _ (@fdapp1_int_hom_func K R E (@eval_order_leading K I R E FF) x y p u v)
    alpha beta;

/* Typed controls for the remaining raw identity/terminal overlap families. */

// Build the pair of whole Hom actions first; do not call the parent's
// fdapp1 point head, whose transported-identity rule is the competing route.
symbol eval_order_pair_whole_value
  [K : Cat] [R E D : τ (Catd K)]
  (FF : τ (Functord R E)) (GG : τ (Functord R D))
  [x y : τ (Obj K)] (p : τ (Hom K x y)) (u : τ (Obj (Fibre_cat R x)))
  : τ (Obj (Product_cat (@eval_order_cell_cat K R E FF x y p u)
      (@eval_order_cell_cat K R D GG x y p u)))
≔ @fapp0
    (Hom_cat (Fibre_cat R y) (@eval_order_transport K R x y p u)
      (@eval_order_transport K R x y p u))
    (Product_cat (@eval_order_cell_cat K R E FF x y p u)
      (@eval_order_cell_cat K R D GG x y p u))
    (@Product_pair
      (Functor_cat
        (Hom_cat (Fibre_cat R y) (@eval_order_transport K R x y p u)
          (@eval_order_transport K R x y p u))
        (@eval_order_cell_cat K R E FF x y p u))
      (Functor_cat
        (Hom_cat (Fibre_cat R y) (@eval_order_transport K R x y p u)
          (@eval_order_transport K R x y p u))
        (@eval_order_cell_cat K R D GG x y p u))
      (@fdapp1_int_hom_func K R E FF x y p u (@eval_order_transport K R x y p u))
      (@fdapp1_int_hom_func K R D GG x y p u (@eval_order_transport K R x y p u)))
    (@id (Fibre_cat R y) (@eval_order_transport K R x y p u));

// Op pairing: both explicitly selected projection orders coincide.
assert [K : Cat] (R E D : τ (Catd K))
  (FF : τ (Functord R E)) (GG : τ (Functord R D))
  [x y : τ (Obj K)] (p : τ (Hom K x y)) (u : τ (Obj (Fibre_cat R x))) ⊢
  @eval_order_pair_whole_value K (@Op_catd K R) (@Op_catd K E) (@Op_catd K D)
    (@Op_funcd K R E FF) (@Op_funcd K R D GG) x y p u
  ≡ @fdapp1_int_cell K _ _
      (@Op_funcd K _ _ (@Product_pair_funcd K R E D FF GG)) x y p u;

// Same overlap after the source family is literally terminal. Arbitrary
// section cells remain in the pair; they are not collapsed to identities.
assert [K : Cat] (E D : τ (Catd K))
  (s : τ (Obj (@Pi_cat K E))) (r : τ (Obj (@Pi_cat K D)))
  [x y : τ (Obj K)] (p : τ (Hom K x y)) ⊢
  @eval_order_pair_whole_value K (@Const_catd K Terminal_cat)
    (@Op_catd K E) (@Op_catd K D)
    (@Op_funcd K (@Const_catd K Terminal_cat) E s)
    (@Op_funcd K (@Const_catd K Terminal_cat) D r) x y p Terminal_obj
  ≡ @fdapp1_int_cell K _ _
      (@Op_funcd K _ _ (@Product_pair_funcd K (@Const_catd K Terminal_cat) E D s r))
      x y p Terminal_obj;

// Identity displayed operator, generic transported-identity and terminal cases.
assert [K : Cat] (R : τ (Catd K)) [x y : τ (Obj K)]
  (p : τ (Hom K x y)) (u : τ (Obj (Fibre_cat R x))) ⊢
  @fdapp1_int_cell K R R (@id_funcd K R) x y p u
  ≡ @id (Fibre_cat R y) (@eval_order_transport K R x y p u);

assert [K : Cat] [x y : τ (Obj K)] (p : τ (Hom K x y)) ⊢
  @fdapp1_int_cell K (@Const_catd K Terminal_cat) (@Const_catd K Terminal_cat)
    (@id_funcd K (@Const_catd K Terminal_cat)) x y p Terminal_obj
  ≡ Terminal_obj;

// Constant weakening agrees with its generic cell-first route.
assert [K I : Cat] (R : τ (Catd K)) (i : τ (Obj I))
  [x y : τ (Obj K)] (p : τ (Hom K x y)) (u : τ (Obj (Fibre_cat R x))) ⊢
  @fdapp1_int_cell K R (@Const_catd K I)
    (@section_weaken_funcd K R (@Const_catd K I) (@Const_func K I i)) x y p u
  ≡ @id I i;

assert [K I : Cat] (i : τ (Obj I))
  [x y : τ (Obj K)] (p : τ (Hom K x y)) ⊢
  @fdapp1_int_cell K (@Const_catd K Terminal_cat) (@Const_catd K I)
    (@section_weaken_funcd K (@Const_catd K Terminal_cat)
      (@Const_catd K I) (@Const_func K I i)) x y p Terminal_obj
  ≡ @id I i;

assert [K I : Cat] (R : τ (Catd K)) (i : τ (Obj I))
  [x y : τ (Obj K)] (p : τ (Hom K x y)) (u : τ (Obj (Fibre_cat R x))) ⊢
  @fdapp1_int_cell K _ _ (@Op_funcd K R (@Const_catd K I)
    (@section_weaken_funcd K R (@Const_catd K I) (@Const_func K I i))) x y p u
  ≡ @id (Op_cat I) i;

assert [K I : Cat] (i : τ (Obj I))
  [x y : τ (Obj K)] (p : τ (Hom K x y)) ⊢
  @fdapp1_int_cell K _ _ (@Op_funcd K (@Const_catd K Terminal_cat) (@Const_catd K I)
    (@section_weaken_funcd K (@Const_catd K Terminal_cat)
      (@Const_catd K I) (@Const_func K I i))) x y p Terminal_obj
  ≡ @id (Op_cat I) i;

// Expand the Op-Eval whole action at the actual transported pair. The raw
// warning leaves its second pair unrelated to the first and its identity.
assert [K I : Cat] (E : τ (Catd K)) [x y : τ (Obj K)]
  (p : τ (Hom K x y)) (U : τ (Functor I (Fibre_cat E x))) (i : τ (Obj I)) ⊢
  @fapp1_fapp0
    (Op_cat (Product_cat (Functor_cat I (Fibre_cat E y)) I)) (Op_cat (Fibre_cat E y))
    (@Op_func (Product_cat (Functor_cat I (Fibre_cat E y)) I)
      (Fibre_cat E y) (@Eval_func I (Fibre_cat E y)))
    (@eval_order_transport K (@eval_order_domain K I E) x y p (Struct_sigma U i))
    (@eval_order_transport K (@eval_order_domain K I E) x y p (Struct_sigma U i))
    (@id (Op_cat (Product_cat (Functor_cat I (Fibre_cat E y)) I))
      (@eval_order_transport K (@eval_order_domain K I E) x y p (Struct_sigma U i)))
  ≡ @fdapp1_int_cell K _ _ (@Op_funcd K _ _ (@Eval_funcd K I E))
      x y p (Struct_sigma U i);

// Both levels of identity action, on an arbitrary (not necessarily identity) alpha.
assert [K : Cat] (R : τ (Catd K)) [x y : τ (Obj K)] (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat R x))) (v : τ (Obj (Fibre_cat R y))) ⊢
  @fdapp1_int_hom_func K R R (@id_funcd K R) x y p u v
  ≡ @id_func (Hom_cat (Fibre_cat R y) (@eval_order_transport K R x y p u) v);

assert [K : Cat] (R : τ (Catd K)) [x y : τ (Obj K)] (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat R x))) (v : τ (Obj (Fibre_cat R y)))
  (alpha : τ (Hom (Fibre_cat R y) (@eval_order_transport K R x y p u) v)) ⊢
  @fdapp1_int_hom_fapp0 K R R (@id_funcd K R) x y p u v alpha ≡ alpha;

// A constant argument supplies the constant whole Hom functor at id_i.
assert [K I : Cat] (R : τ (Catd K)) (i : τ (Obj I))
  [x y : τ (Obj K)] (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat R x))) (v : τ (Obj (Fibre_cat R y))) ⊢
  @fdapp1_int_hom_func K R (@Const_catd K I)
    (@section_weaken_funcd K R (@Const_catd K I) (@Const_func K I i)) x y p u v
  ≡ @Const_func (Hom_cat (Fibre_cat R y) (@eval_order_transport K R x y p u) v)
      (Hom_cat I i i) (@id I i);

assert [K I : Cat] (R : τ (Catd K)) (i : τ (Obj I))
  [x y : τ (Obj K)] (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat R x))) (v : τ (Obj (Fibre_cat R y))) ⊢
  @fdapp1_int_hom_func K _ _ (@Op_funcd K R (@Const_catd K I)
    (@section_weaken_funcd K R (@Const_catd K I) (@Const_func K I i))) x y p u v
  ≡ @Const_func (Hom_cat (Op_cat (Fibre_cat R y)) (@eval_order_transport K R x y p u) v)
      (Hom_cat (Op_cat I) i i) (@id (Op_cat I) i);

// Eval itself retains the whole mixed action, not just its component at id_i.
assert [K I : Cat] (E : τ (Catd K)) [x y : τ (Obj K)] (p : τ (Hom K x y))
  (U : τ (Functor I (Fibre_cat E x))) (V : τ (Functor I (Fibre_cat E y)))
  (i j : τ (Obj I)) ⊢
  @fdapp1_int_hom_func K _ E (@Eval_funcd K I E) x y p (Struct_sigma U i) (Struct_sigma V j)
  ≡ @Eval_fapp1_func I (Fibre_cat E y)
      (@comp_cat_fapp0 I (Fibre_cat E x) (Fibre_cat E y)
        (@catd_transport_func K E x y p) U) V i j;

assert [K I : Cat] (E : τ (Catd K)) [x y : τ (Obj K)] (p : τ (Hom K x y))
  (U : τ (Functor I (Fibre_cat E x))) (V : τ (Functor I (Fibre_cat E y)))
  (i j : τ (Obj I))
  (eta : τ (Transf (@comp_cat_fapp0 I (Fibre_cat E x) (Fibre_cat E y)
      (@catd_transport_func K E x y p) U) V)) (q : τ (Hom I i j)) ⊢
  @fdapp1_int_hom_fapp0 K _ E (@Eval_funcd K I E) x y p
    (Struct_sigma U i) (Struct_sigma V j) (Struct_sigma eta q)
  ≡ @tapp1_fapp0 I (Fibre_cat E y)
      (@comp_cat_fapp0 I (Fibre_cat E x) (Fibre_cat E y)
        (@catd_transport_func K E x y p) U) V i j eta q;

assert [K I : Cat] (E : τ (Catd K)) [x y : τ (Obj K)] (p : τ (Hom K x y))
  (U : τ (Functor I (Fibre_cat E x))) (V : τ (Functor I (Fibre_cat E y)))
  (i j : τ (Obj I)) ⊢
  @fdapp1_int_hom_func K _ _ (@Op_funcd K _ _ (@Eval_funcd K I E))
    x y p (Struct_sigma U i) (Struct_sigma V j)
  ≡ @Eval_fapp1_func I (Fibre_cat E y) V
      (@Hom_fapp0 Cat_cat I I (Fibre_cat E x) (Fibre_cat E y)
        (@id Cat_cat I) (@catd_transport_func K E x y p) U) j i;

// The two new structural whole joins are restricted to constant sections.
assert [K I : Cat] (i : τ (Obj I)) ⊢
  @section_weaken_funcd K (@Const_catd K Terminal_cat) (@Const_catd K I) (@Const_func K I i)
  ≡ @Const_func K I i;

assert [K I : Cat] (i : τ (Obj I)) ⊢
  @Op_funcd K (@Const_catd K Terminal_cat) (@Const_catd K I) (@Const_func K I i)
  ≡ @Const_func K (Op_cat I) i;

// Whole-first versus terminal-source unit-first, not merely the point at tt.
assert [K I : Cat] (i : τ (Obj I))
  [x y : τ (Obj K)] (p : τ (Hom K x y)) ⊢
  @fdapp1_int_hom_func K (@Const_catd K Terminal_cat) (@Const_catd K I)
    (@section_weaken_funcd K (@Const_catd K Terminal_cat) (@Const_catd K I)
      (@Const_func K I i)) x y p Terminal_obj Terminal_obj
  ≡ @Const_func Terminal_cat (Hom_cat I i i) (@id I i);

assert [K I : Cat] (i : τ (Obj I))
  [x y : τ (Obj K)] (p : τ (Hom K x y)) ⊢
  @fdapp1_int_hom_func K _ _ (@Op_funcd K (@Const_catd K Terminal_cat) (@Const_catd K I)
    (@section_weaken_funcd K (@Const_catd K Terminal_cat) (@Const_catd K I)
      (@Const_func K I i))) x y p Terminal_obj Terminal_obj
  ≡ @Const_func Terminal_cat (Hom_cat (Op_cat I) i i) (@id (Op_cat I) i);

// Neutral terminal-fibre objects/arrows also exercise the capped projection;
// their type alone does not make their syntax literally Terminal_obj.
assert [K I : Cat] (i : τ (Obj I)) [x y : τ (Obj K)] (p : τ (Hom K x y))
  (u v : τ (Obj Terminal_cat)) (alpha : τ (Hom Terminal_cat u v)) ⊢
  @fdapp1_int_hom_fapp0 K (@Const_catd K Terminal_cat) (@Const_catd K I)
    (@Const_func K I i) x y p u v alpha
  ≡ @id I i;
