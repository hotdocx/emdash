/*
  Enhanced triangular chosen binary products.

  A witness is indexed by a selected whole product functor

    P : C × C ⊢ C.

  Its two projections are whole transfors P => pi_1 and P => pi_2. Došen's
  K_1^a and K_2^a operations are stable projections of their full
  off-diagonal actions. Pairing is one whole transfor between contravariant
  represented Cat-valued families, so every point component is a whole
  functor and another base/hom action remains available.

  Ordinary ambient composition owns the triangular runtime orientation:

    h o K_i^a(f)      -> K_i^a(h o f)
    K_1^a(h) o <f,g> -> h o f
    K_2^a(h) o <f,g> -> h o g
    <f,g> o h         -> <f o h,g o h>
    <pi_1,pi_2>       -> id.

  The two selected §6.4 reductions are oriented toward one K^a operation.
  The extra whole P action is not expanded at runtime. Its local projection
  comparisons are proof-time usability rules, from which an explicit
  propositional product-map agreement is derived below.

  This module does not construct Došen's free syntax or decision algorithm,
  assert products for every category, replace the existing per-pair
  weighted-limit BinaryProductPresentation, or add a terminal object.
*/

require open emdash.emdash3_2;

// Selected chosen-binary-product structure indexed by its whole product functor.
injective symbol BinaryProducts
  [C : Cat]
  (P : τ (Functor (Product_cat C C) C))
  : Grpd;

// Whole first projection kappa_1 : P => pi_1.
symbol binary_products_proj1_transf
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (B : τ (@BinaryProducts C P))
  : τ (Transf P (@Product_projL_func C C));

// Whole second projection kappa_2 : P => pi_2.
symbol binary_products_proj2_transf
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (B : τ (@BinaryProducts C P))
  : τ (Transf P (@Product_projR_func C C));

// Stable first projection at P(A0,A1).
symbol binary_products_proj1_fapp0
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (B : τ (@BinaryProducts C P))
  (A0 A1 : τ (Obj C))
  : τ (Hom C
      (@fapp0 (Product_cat C C) C P (@Product_pair C C A0 A1))
      A0);

// Stable second projection at P(A0,A1).
symbol binary_products_proj2_fapp0
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (B : τ (@BinaryProducts C P))
  (A0 A1 : τ (Obj C))
  : τ (Hom C
      (@fapp0 (Product_cat C C) C P (@Product_pair C C A0 A1))
      A1);

// Pointwise product Hom(-,A0) × Hom(-,A1) over Op(C).
symbol binary_products_pair_source_family
  [C : Cat]
  (A0 A1 : τ (Obj C))
  : τ (Functor (Op_cat C) Cat_cat)
≔ @comp_cat_fapp0
    (Op_cat C)
    (Product_cat Cat_cat Cat_cat)
    Cat_cat
    (@uncurry_func Cat_cat Cat_cat Cat_cat Product_cat_func)
    (Struct_sigma
      (@hom_con C A0 C (@id_func C))
      (@hom_con C A1 C (@id_func C)));

// Represented target Hom(-,P(A0,A1)) over Op(C).
symbol binary_products_pair_target_family
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (A0 A1 : τ (Obj C))
  : τ (Functor (Op_cat C) Cat_cat)
≔ @hom_con
    C
    (@fapp0
      (Product_cat C C) C P
      (@Product_pair C C A0 A1))
    C
    (@id_func C);

// Whole internally natural pairing operation.
symbol binary_products_pair_transf
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (B : τ (@BinaryProducts C P))
  (A0 A1 : τ (Obj C))
  : τ (Transf
      (@binary_products_pair_source_family C A0 A1)
      (@binary_products_pair_target_family C P A0 A1));

// Stable whole pairing functor at source X.
injective symbol binary_products_pair_func
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (B : τ (@BinaryProducts C P))
  (X A0 A1 : τ (Obj C))
  : τ (Functor
      (Product_cat (Hom_cat C X A0) (Hom_cat C X A1))
      (Hom_cat C X
        (@fapp0
          (Product_cat C C) C P
          (@Product_pair C C A0 A1))));

// Stable point pairing <f,g> : X -> P(A0,A1).
symbol binary_products_pair_fapp0
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (B : τ (@BinaryProducts C P))
  [X A0 A1 : τ (Obj C)]
  (f : τ (Hom C X A0))
  (g : τ (Hom C X A1))
  : τ (Hom C X
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A0 A1)));

// Stable K_1^a_A(f) : P(B0,A) -> B1.
symbol binary_products_K1a_fapp0
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (B : τ (@BinaryProducts C P))
  [A B0 B1 : τ (Obj C)]
  (f : τ (Hom C B0 B1))
  : τ (Hom C
      (@fapp0 (Product_cat C C) C P (@Product_pair C C B0 A))
      B1);

// Stable K_2^a_A(f) : P(A,B0) -> B1.
symbol binary_products_K2a_fapp0
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (B : τ (@BinaryProducts C P))
  [A B0 B1 : τ (Obj C)]
  (f : τ (Hom C B0 B1))
  : τ (Hom C
      (@fapp0 (Product_cat C C) C P (@Product_pair C C A B0))
      B1);

// Canonical post-Product_pair projection ladder for the first off-diagonal action.
rule @tapp1_fapp0
      _ _ _ _
      (Struct_sigma $B0 $A0)
      (Struct_sigma $B1 $A1)
      (@binary_products_proj1_transf $C $P $BP)
      (Struct_sigma $f $g)
  ↪ @binary_products_K1a_fapp0
      $C $P $BP $A0 $B0 $B1 $f;

// Canonical post-Product_pair projection ladder for the second off-diagonal action.
rule @tapp1_fapp0
      _ _ _ _
      (Struct_sigma $A0 $B0)
      (Struct_sigma $A1 $B1)
      (@binary_products_proj2_transf $C $P $BP)
      (Struct_sigma $f $g)
  ↪ @binary_products_K2a_fapp0
      $C $P $BP $A0 $B0 $B1 $g;

// Canonical point projections of the two whole projection transfors.
rule @tapp0_fapp0
      _ _ _ _
      (Struct_sigma $A0 $A1)
      (@binary_products_proj1_transf $C $P $BP)
  ↪ @binary_products_proj1_fapp0
      $C $P $BP $A0 $A1;

rule @tapp0_fapp0
      _ _ _ _
      (Struct_sigma $A0 $A1)
      (@binary_products_proj2_transf $C $P $BP)
  ↪ @binary_products_proj2_fapp0
      $C $P $BP $A0 $A1;

// Component projection of the whole pairing transfor.
rule @tapp0_fapp0
      _ Cat_cat _ _ $X
      (@binary_products_pair_transf $C $P $BP $A0 $A1)
  ↪ @binary_products_pair_func
      $C $P $BP $X $A0 $A1;

// Object projection of the stable whole pairing functor.
rule @fapp0
      _ _
      (@binary_products_pair_func $C $P $BP $X $A0 $A1)
      (Struct_sigma $f $g)
  ↪ @binary_products_pair_fapp0
      $C $P $BP $X $A0 $A1 $f $g;

// Došen naturality: h o K_1^a(f) -> K_1^a(h o f).
rule @comp_fapp0
      $C _ $B1 $B2
      $h
      (@binary_products_K1a_fapp0
        $C $P $BP $A $B0 $B1 $f)
  ↪ @binary_products_K1a_fapp0
      $C $P $BP $A $B0 $B2
      (@comp_fapp0 $C $B0 $B1 $B2 $h $f);

// Došen naturality: h o K_2^a(f) -> K_2^a(h o f).
rule @comp_fapp0
      $C _ $B1 $B2
      $h
      (@binary_products_K2a_fapp0
        $C $P $BP $A $B0 $B1 $f)
  ↪ @binary_products_K2a_fapp0
      $C $P $BP $A $B0 $B2
      (@comp_fapp0 $C $B0 $B1 $B2 $h $f);

// Došen distribution: <f,g> o h -> <f o h,g o h>.
rule @comp_fapp0
      $C $X0 $X1 _
      (@binary_products_pair_fapp0
        $C $P $BP $X1 $A0 $A1 $f $g)
      $h
  ↪ @binary_products_pair_fapp0
      $C $P $BP $X0 $A0 $A1
      (@comp_fapp0 $C $X0 $X1 $A0 $f $h)
      (@comp_fapp0 $C $X0 $X1 $A1 $g $h);

// K_i^a(id) is the corresponding point projection.
rule @binary_products_K1a_fapp0
      $C $P $BP $A $B $B (@id $C $B)
  ↪ @binary_products_proj1_fapp0
      $C $P $BP $B $A;

rule @binary_products_K2a_fapp0
      $C $P $BP $A $B $B (@id $C $B)
  ↪ @binary_products_proj2_fapp0
      $C $P $BP $A $B;

// Product beta: K_1^a(h) o <f,g> -> h o f.
rule @comp_fapp0
      _ _ _ _
      (@binary_products_K1a_fapp0
        $C $P $BP $B $A $D $h)
      (@binary_products_pair_fapp0
        $C $P $BP $X $A $B $f $g)
  ↪ @comp_fapp0 $C $X $A $D $h $f;

// Product beta: K_2^a(h) o <f,g> -> h o g.
rule @comp_fapp0
      _ _ _ _
      (@binary_products_K2a_fapp0
        $C $P $BP $A $B $D $h)
      (@binary_products_pair_fapp0
        $C $P $BP $X $A $B $f $g)
  ↪ @comp_fapp0 $C $X $B $D $h $g;

// Post-K_i(id) projection-order joins for the two beta laws.
rule @comp_fapp0
      _ _ _ _
      (@binary_products_proj1_fapp0
        $C $P $BP $A $B)
      (@binary_products_pair_fapp0
        $C $P $BP $X $A $B $f $g)
  ↪ $f;

rule @comp_fapp0
      _ _ _ _
      (@binary_products_proj2_fapp0
        $C $P $BP $A $B)
      (@binary_products_pair_fapp0
        $C $P $BP $X $A $B $f $g)
  ↪ $g;

// Product eta: <pi_1,pi_2> -> id.
rule @binary_products_pair_fapp0
      $C $P $BP _ $A $B
      (@binary_products_proj1_fapp0 $C $P $BP $A $B)
      (@binary_products_proj2_fapp0 $C $P $BP $A $B)
  ↪ @id
      $C
      (@fapp0
        (Product_cat $C $C) $C $P
        (@Product_pair $C $C $A $B));

// §6.4 normalization: <K_1^a(f),K_1^a(g)> -> K_1^a(<f,g>).
rule @binary_products_pair_fapp0
      $C $P $BP _ $D0 $D1
      (@binary_products_K1a_fapp0
        $C $P $BP $A $B $D0 $f)
      (@binary_products_K1a_fapp0
        $C $P $BP $A $B $D1 $g)
  ↪ @binary_products_K1a_fapp0
      $C $P $BP
      $A $B
      (@fapp0
        (Product_cat $C $C) $C $P
        (@Product_pair $C $C $D0 $D1))
      (@binary_products_pair_fapp0
        $C $P $BP $B $D0 $D1 $f $g);

// §6.4 normalization: <K_2^a(f),K_2^a(g)> -> K_2^a(<f,g>).
rule @binary_products_pair_fapp0
      $C $P $BP _ $D0 $D1
      (@binary_products_K2a_fapp0
        $C $P $BP $A $B $D0 $f)
      (@binary_products_K2a_fapp0
        $C $P $BP $A $B $D1 $g)
  ↪ @binary_products_K2a_fapp0
      $C $P $BP
      $A $B
      (@fapp0
        (Product_cat $C $C) $C $P
        (@Product_pair $C $C $D0 $D1))
      (@binary_products_pair_fapp0
        $C $P $BP $B $D0 $D1 $f $g);

// --------------------------------------------------------------------------
// Derived product map and proof-time agreement with the extra whole P action
// --------------------------------------------------------------------------

// Došen-derived point action (f,g) |-> <K_1^a(f),K_2^a(g)>.
symbol binary_products_map_fapp0
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (B : τ (@BinaryProducts C P))
  [A0 A1 B0 B1 : τ (Obj C)]
  (f : τ (Hom C A0 A1))
  (g : τ (Hom C B0 B1))
  : τ (Hom C
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A0 B0))
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A1 B1)))
≔ @binary_products_pair_fapp0
    C P B
    (@fapp0
      (Product_cat C C) C P
      (@Product_pair C C A0 B0))
    A1 B1
    (@binary_products_K1a_fapp0 C P B B0 A0 A1 f)
    (@binary_products_K2a_fapp0 C P B A0 B0 B1 g);

// Readable semantic point action of the selected whole product functor P.
symbol binary_products_semantic_map_fapp0
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (_ : τ (@BinaryProducts C P))
  [A0 A1 B0 B1 : τ (Obj C)]
  (f : τ (Hom C A0 A1))
  (g : τ (Hom C B0 B1))
  : τ (Hom C
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A0 B0))
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A1 B1)))
≔ @fapp1_fapp0
    (Product_cat C C) C P
    (@Product_pair C C A0 B0)
    (@Product_pair C C A1 B1)
    (@Product_pair
      (Hom_cat C A0 A1)
      (Hom_cat C B0 B1)
      f g);

/*
  Proof-time coherence of the extra whole P action with the triangular
  projections. These are usability comparisons, not runtime reductions:
  generic P action and the stable K^a heads retain distinct normal forms.

  `Struct_sigma` is the canonical post-Product_pair shape. No defined alias
  occurs on either unification-rule side.
*/
unif_rule
  @comp_fapp0
    _ _ _ _
    (@binary_products_proj1_fapp0
      $C $P $BP $A1 $B1)
    (@fapp1_fapp0
      _ _ $P
      (Struct_sigma $A0 $B0)
      (Struct_sigma $A1 $B1)
      (Struct_sigma $f $g))
  ≡ @binary_products_K1a_fapp0
      $C $P $BP $B0 $A0 $A1 $f
  ↪ [ tt ≡ tt ];

unif_rule
  @comp_fapp0
    _ _ _ _
    (@binary_products_proj2_fapp0
      $C $P $BP $A1 $B1)
    (@fapp1_fapp0
      _ _ $P
      (Struct_sigma $A0 $B0)
      (Struct_sigma $A1 $B1)
      (Struct_sigma $f $g))
  ≡ @binary_products_K2a_fapp0
      $C $P $BP $A0 $B0 $B1 $g
  ↪ [ tt ≡ tt ];

// Typed equality view of product eta.
symbol binary_products_pair_eta_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (B : τ (@BinaryProducts C P))
  (A0 A1 : τ (Obj C))
  : τ (@=
      (Hom C
        (@fapp0
          (Product_cat C C) C P
          (@Product_pair C C A0 A1))
        (@fapp0
          (Product_cat C C) C P
          (@Product_pair C C A0 A1)))
      (@binary_products_pair_fapp0
        C P B
        (@fapp0
          (Product_cat C C) C P
          (@Product_pair C C A0 A1))
        A0 A1
        (@binary_products_proj1_fapp0 C P B A0 A1)
        (@binary_products_proj2_fapp0 C P B A0 A1))
      (@id C
        (@fapp0
          (Product_cat C C) C P
          (@Product_pair C C A0 A1))))
≔ @eq_refl
    (Hom C
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A0 A1))
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A0 A1)))
    (@binary_products_pair_fapp0
      C P B
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A0 A1))
      A0 A1
      (@binary_products_proj1_fapp0 C P B A0 A1)
      (@binary_products_proj2_fapp0 C P B A0 A1));

// Typed equality view of pairing distribution.
symbol binary_products_pair_distribution_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (B : τ (@BinaryProducts C P))
  [X0 X1 A0 A1 : τ (Obj C)]
  (h : τ (Hom C X0 X1))
  (f : τ (Hom C X1 A0))
  (g : τ (Hom C X1 A1))
  : τ (@=
      (Hom C X0
        (@fapp0
          (Product_cat C C) C P
          (@Product_pair C C A0 A1)))
      (@comp_fapp0
        C X0 X1
        (@fapp0
          (Product_cat C C) C P
          (@Product_pair C C A0 A1))
        (@binary_products_pair_fapp0 C P B X1 A0 A1 f g)
        h)
      (@binary_products_pair_fapp0
        C P B X0 A0 A1
        (@comp_fapp0 C X0 X1 A0 f h)
        (@comp_fapp0 C X0 X1 A1 g h)))
≔ @eq_refl
    (Hom C X0
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A0 A1)))
    (@comp_fapp0
      C X0 X1
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A0 A1))
      (@binary_products_pair_fapp0 C P B X1 A0 A1 f g)
      h);

// Typed proof-time first-projection comparison.
symbol binary_products_proj1_action_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (B : τ (@BinaryProducts C P))
  [A0 A1 B0 B1 : τ (Obj C)]
  (f : τ (Hom C A0 A1))
  (g : τ (Hom C B0 B1))
  : τ (@=
      (Hom C
        (@fapp0
          (Product_cat C C) C P
          (@Product_pair C C A0 B0))
        A1)
      (@comp_fapp0
        C
        (@fapp0
          (Product_cat C C) C P
          (@Product_pair C C A0 B0))
        (@fapp0
          (Product_cat C C) C P
          (@Product_pair C C A1 B1))
        A1
        (@binary_products_proj1_fapp0 C P B A1 B1)
        (@binary_products_semantic_map_fapp0
          C P B A0 A1 B0 B1 f g))
      (@binary_products_K1a_fapp0 C P B B0 A0 A1 f))
≔ @eq_refl
    (Hom C
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A0 B0))
      A1)
    (@binary_products_K1a_fapp0 C P B B0 A0 A1 f);

// Typed proof-time second-projection comparison.
symbol binary_products_proj2_action_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (B : τ (@BinaryProducts C P))
  [A0 A1 B0 B1 : τ (Obj C)]
  (f : τ (Hom C A0 A1))
  (g : τ (Hom C B0 B1))
  : τ (@=
      (Hom C
        (@fapp0
          (Product_cat C C) C P
          (@Product_pair C C A0 B0))
        B1)
      (@comp_fapp0
        C
        (@fapp0
          (Product_cat C C) C P
          (@Product_pair C C A0 B0))
        (@fapp0
          (Product_cat C C) C P
          (@Product_pair C C A1 B1))
        B1
        (@binary_products_proj2_fapp0 C P B A1 B1)
        (@binary_products_semantic_map_fapp0
          C P B A0 A1 B0 B1 f g))
      (@binary_products_K2a_fapp0 C P B A0 B0 B1 g))
≔ @eq_refl
    (Hom C
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A0 B0))
      B1)
    (@binary_products_K2a_fapp0 C P B A0 B0 B1 g);

// Equality action by postcomposing a fixed arrow on the right.
symbol binary_products_comp_post_path
  [C : Cat]
  [X Y Z : τ (Obj C)]
  (h : τ (Hom C X Y))
  [k l : τ (Hom C Y Z)]
  (p : τ (@= (Hom C Y Z) k l))
  : τ (@=
      (Hom C X Z)
      (@comp_fapp0 C X Y Z k h)
      (@comp_fapp0 C X Y Z l h))
≔ @eq_ap
    (Hom C Y Z)
    (Hom C X Z)
    (λ q : τ (Hom C Y Z), @comp_fapp0 C X Y Z q h)
    k l p;

// Equality action in the first pairing input.
symbol binary_products_pair_left_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (B : τ (@BinaryProducts C P))
  [X A0 A1 : τ (Obj C)]
  [f f' : τ (Hom C X A0)]
  (p : τ (@= (Hom C X A0) f f'))
  (g : τ (Hom C X A1))
  : τ (@=
      (Hom C X
        (@fapp0
          (Product_cat C C) C P
          (@Product_pair C C A0 A1)))
      (@binary_products_pair_fapp0 C P B X A0 A1 f g)
      (@binary_products_pair_fapp0 C P B X A0 A1 f' g))
≔ @eq_ap
    (Hom C X A0)
    (Hom C X
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A0 A1)))
    (λ q : τ (Hom C X A0),
      @binary_products_pair_fapp0 C P B X A0 A1 q g)
    f f' p;

// Equality action in the second pairing input.
symbol binary_products_pair_right_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (B : τ (@BinaryProducts C P))
  [X A0 A1 : τ (Obj C)]
  (f : τ (Hom C X A0))
  [g g' : τ (Hom C X A1)]
  (p : τ (@= (Hom C X A1) g g'))
  : τ (@=
      (Hom C X
        (@fapp0
          (Product_cat C C) C P
          (@Product_pair C C A0 A1)))
      (@binary_products_pair_fapp0 C P B X A0 A1 f g)
      (@binary_products_pair_fapp0 C P B X A0 A1 f g'))
≔ @eq_ap
    (Hom C X A1)
    (Hom C X
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A0 A1)))
    (λ q : τ (Hom C X A1),
      @binary_products_pair_fapp0 C P B X A0 A1 f q)
    g g' p;

// Common ancestor <pi_1,pi_2> o P[(f,g)].
symbol binary_products_map_common_fapp0
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (B : τ (@BinaryProducts C P))
  [A0 A1 B0 B1 : τ (Obj C)]
  (f : τ (Hom C A0 A1))
  (g : τ (Hom C B0 B1))
  : τ (Hom C
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A0 B0))
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A1 B1)))
≔ @comp_fapp0
    C
    (@fapp0
      (Product_cat C C) C P
      (@Product_pair C C A0 B0))
    (@fapp0
      (Product_cat C C) C P
      (@Product_pair C C A1 B1))
    (@fapp0
      (Product_cat C C) C P
      (@Product_pair C C A1 B1))
    (@binary_products_pair_fapp0
      C P B
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A1 B1))
      A1 B1
      (@binary_products_proj1_fapp0 C P B A1 B1)
      (@binary_products_proj2_fapp0 C P B A1 B1))
    (@binary_products_semantic_map_fapp0
      C P B A0 A1 B0 B1 f g);

// Semantic P action reaches the common ancestor by left identity and eta.
symbol binary_products_semantic_to_common_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (B : τ (@BinaryProducts C P))
  [A0 A1 B0 B1 : τ (Obj C)]
  (f : τ (Hom C A0 A1))
  (g : τ (Hom C B0 B1))
  : τ (@=
      (Hom C
        (@fapp0
          (Product_cat C C) C P
          (@Product_pair C C A0 B0))
        (@fapp0
          (Product_cat C C) C P
          (@Product_pair C C A1 B1)))
      (@binary_products_semantic_map_fapp0
        C P B A0 A1 B0 B1 f g)
      (@binary_products_map_common_fapp0
        C P B A0 A1 B0 B1 f g))
≔ @eq_trans
    (Hom C
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A0 B0))
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A1 B1)))
    (@binary_products_semantic_map_fapp0
      C P B A0 A1 B0 B1 f g)
    (@comp_fapp0
      C
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A0 B0))
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A1 B1))
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A1 B1))
      (@id C
        (@fapp0
          (Product_cat C C) C P
          (@Product_pair C C A1 B1)))
      (@binary_products_semantic_map_fapp0
        C P B A0 A1 B0 B1 f g))
    (@binary_products_map_common_fapp0
      C P B A0 A1 B0 B1 f g)
    (@eq_refl
      (Hom C
        (@fapp0
          (Product_cat C C) C P
          (@Product_pair C C A0 B0))
        (@fapp0
          (Product_cat C C) C P
          (@Product_pair C C A1 B1)))
      (@binary_products_semantic_map_fapp0
        C P B A0 A1 B0 B1 f g))
    (@binary_products_comp_post_path
      C
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A0 B0))
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A1 B1))
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A1 B1))
      (@binary_products_semantic_map_fapp0
        C P B A0 A1 B0 B1 f g)
      (@id C
        (@fapp0
          (Product_cat C C) C P
          (@Product_pair C C A1 B1)))
      (@binary_products_pair_fapp0
        C P B
        (@fapp0
          (Product_cat C C) C P
          (@Product_pair C C A1 B1))
        A1 B1
        (@binary_products_proj1_fapp0 C P B A1 B1)
        (@binary_products_proj2_fapp0 C P B A1 B1))
      (@eq_sym
        (Hom C
          (@fapp0
            (Product_cat C C) C P
            (@Product_pair C C A1 B1))
          (@fapp0
            (Product_cat C C) C P
            (@Product_pair C C A1 B1)))
        (@binary_products_pair_fapp0
          C P B
          (@fapp0
            (Product_cat C C) C P
            (@Product_pair C C A1 B1))
          A1 B1
          (@binary_products_proj1_fapp0 C P B A1 B1)
          (@binary_products_proj2_fapp0 C P B A1 B1))
        (@id C
          (@fapp0
            (Product_cat C C) C P
            (@Product_pair C C A1 B1)))
        (@binary_products_pair_eta_path C P B A1 B1)));

// First projection cut after semantic P action, used only in the map proof.
symbol binary_products_map_proj1_cut
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (B : τ (@BinaryProducts C P))
  [A0 A1 B0 B1 : τ (Obj C)]
  (f : τ (Hom C A0 A1))
  (g : τ (Hom C B0 B1))
  : τ (Hom C
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A0 B0))
      A1)
≔ @comp_fapp0
    C
    (@fapp0
      (Product_cat C C) C P
      (@Product_pair C C A0 B0))
    (@fapp0
      (Product_cat C C) C P
      (@Product_pair C C A1 B1))
    A1
    (@binary_products_proj1_fapp0 C P B A1 B1)
    (@binary_products_semantic_map_fapp0
      C P B A0 A1 B0 B1 f g);

// Second projection cut after semantic P action, used only in the map proof.
symbol binary_products_map_proj2_cut
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (B : τ (@BinaryProducts C P))
  [A0 A1 B0 B1 : τ (Obj C)]
  (f : τ (Hom C A0 A1))
  (g : τ (Hom C B0 B1))
  : τ (Hom C
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A0 B0))
      B1)
≔ @comp_fapp0
    C
    (@fapp0
      (Product_cat C C) C P
      (@Product_pair C C A0 B0))
    (@fapp0
      (Product_cat C C) C P
      (@Product_pair C C A1 B1))
    B1
    (@binary_products_proj2_fapp0 C P B A1 B1)
    (@binary_products_semantic_map_fapp0
      C P B A0 A1 B0 B1 f g);

// Distribution branch before either proof-time projection comparison.
symbol binary_products_map_distributed_fapp0
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (B : τ (@BinaryProducts C P))
  [A0 A1 B0 B1 : τ (Obj C)]
  (f : τ (Hom C A0 A1))
  (g : τ (Hom C B0 B1))
  : τ (Hom C
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A0 B0))
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A1 B1)))
≔ @binary_products_pair_fapp0
    C P B
    (@fapp0
      (Product_cat C C) C P
      (@Product_pair C C A0 B0))
    A1 B1
    (@binary_products_map_proj1_cut
      C P B A0 A1 B0 B1 f g)
    (@binary_products_map_proj2_cut
      C P B A0 A1 B0 B1 f g);

// Distribution branch after joining its first projection.
symbol binary_products_map_left_joined_fapp0
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (B : τ (@BinaryProducts C P))
  [A0 A1 B0 B1 : τ (Obj C)]
  (f : τ (Hom C A0 A1))
  (g : τ (Hom C B0 B1))
  : τ (Hom C
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A0 B0))
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A1 B1)))
≔ @binary_products_pair_fapp0
    C P B
    (@fapp0
      (Product_cat C C) C P
      (@Product_pair C C A0 B0))
    A1 B1
    (@binary_products_K1a_fapp0 C P B B0 A0 A1 f)
    (@binary_products_map_proj2_cut
      C P B A0 A1 B0 B1 f g);

// The common ancestor reaches the triangular product map constructively.
symbol binary_products_common_to_map_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (B : τ (@BinaryProducts C P))
  [A0 A1 B0 B1 : τ (Obj C)]
  (f : τ (Hom C A0 A1))
  (g : τ (Hom C B0 B1))
  : τ (@=
      (Hom C
        (@fapp0
          (Product_cat C C) C P
          (@Product_pair C C A0 B0))
        (@fapp0
          (Product_cat C C) C P
          (@Product_pair C C A1 B1)))
      (@binary_products_map_common_fapp0
        C P B A0 A1 B0 B1 f g)
      (@binary_products_map_fapp0
        C P B A0 A1 B0 B1 f g))
≔ @eq_trans
    (Hom C
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A0 B0))
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A1 B1)))
    (@binary_products_map_common_fapp0
      C P B A0 A1 B0 B1 f g)
    (@binary_products_map_distributed_fapp0
      C P B A0 A1 B0 B1 f g)
    (@binary_products_map_fapp0
      C P B A0 A1 B0 B1 f g)
    (@binary_products_pair_distribution_path
      C P B
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A0 B0))
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A1 B1))
      A1 B1
      (@binary_products_semantic_map_fapp0
        C P B A0 A1 B0 B1 f g)
      (@binary_products_proj1_fapp0 C P B A1 B1)
      (@binary_products_proj2_fapp0 C P B A1 B1))
    (@eq_trans
      (Hom C
        (@fapp0
          (Product_cat C C) C P
          (@Product_pair C C A0 B0))
        (@fapp0
          (Product_cat C C) C P
          (@Product_pair C C A1 B1)))
      (@binary_products_map_distributed_fapp0
        C P B A0 A1 B0 B1 f g)
      (@binary_products_map_left_joined_fapp0
        C P B A0 A1 B0 B1 f g)
      (@binary_products_map_fapp0
        C P B A0 A1 B0 B1 f g)
      (@binary_products_pair_left_path
        C P B
        (@fapp0
          (Product_cat C C) C P
          (@Product_pair C C A0 B0))
        A1 B1
        (@binary_products_map_proj1_cut
          C P B A0 A1 B0 B1 f g)
        (@binary_products_K1a_fapp0 C P B B0 A0 A1 f)
        (@binary_products_proj1_action_path
          C P B A0 A1 B0 B1 f g)
        (@binary_products_map_proj2_cut
          C P B A0 A1 B0 B1 f g))
      (@binary_products_pair_right_path
        C P B
        (@fapp0
          (Product_cat C C) C P
          (@Product_pair C C A0 B0))
        A1 B1
        (@binary_products_K1a_fapp0 C P B B0 A0 A1 f)
        (@binary_products_map_proj2_cut
          C P B A0 A1 B0 B1 f g)
        (@binary_products_K2a_fapp0 C P B A0 B0 B1 g)
        (@binary_products_proj2_action_path
          C P B A0 A1 B0 B1 f g)));

// Final non-opaque agreement: P[(f,g)] = <K_1^a(f),K_2^a(g)>.
symbol binary_products_map_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (B : τ (@BinaryProducts C P))
  [A0 A1 B0 B1 : τ (Obj C)]
  (f : τ (Hom C A0 A1))
  (g : τ (Hom C B0 B1))
  : τ (@=
      (Hom C
        (@fapp0
          (Product_cat C C) C P
          (@Product_pair C C A0 B0))
        (@fapp0
          (Product_cat C C) C P
          (@Product_pair C C A1 B1)))
      (@binary_products_semantic_map_fapp0
        C P B A0 A1 B0 B1 f g)
      (@binary_products_map_fapp0
        C P B A0 A1 B0 B1 f g))
≔ @eq_trans
    (Hom C
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A0 B0))
      (@fapp0
        (Product_cat C C) C P
        (@Product_pair C C A1 B1)))
    (@binary_products_semantic_map_fapp0
      C P B A0 A1 B0 B1 f g)
    (@binary_products_map_common_fapp0
      C P B A0 A1 B0 B1 f g)
    (@binary_products_map_fapp0
      C P B A0 A1 B0 B1 f g)
    (@binary_products_semantic_to_common_path
      C P B A0 A1 B0 B1 f g)
    (@binary_products_common_to_map_path
      C P B A0 A1 B0 B1 f g);

// --------------------------------------------------------------------------
// Ordinary hom-level universal-property consumer
// --------------------------------------------------------------------------

// Reconstruct h from its two projection cuts.
symbol binary_products_pair_reconstruct_fapp0
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (B : τ (@BinaryProducts C P))
  [X A0 A1 : τ (Obj C)]
  (h : τ (Hom C X
    (@fapp0 (Product_cat C C) C P (@Product_pair C C A0 A1))))
  : τ (Hom C X
      (@fapp0 (Product_cat C C) C P (@Product_pair C C A0 A1)))
≔ @binary_products_pair_fapp0
    C P B X A0 A1
    (@comp_fapp0
      C X
      (@fapp0 (Product_cat C C) C P (@Product_pair C C A0 A1))
      A0
      (@binary_products_proj1_fapp0 C P B A0 A1)
      h)
    (@comp_fapp0
      C X
      (@fapp0 (Product_cat C C) C P (@Product_pair C C A0 A1))
      A1
      (@binary_products_proj2_fapp0 C P B A0 A1)
      h);

// Common ancestor <pi_1,pi_2> o h for uniqueness.
symbol binary_products_pair_unique_common_fapp0
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (B : τ (@BinaryProducts C P))
  [X A0 A1 : τ (Obj C)]
  (h : τ (Hom C X
    (@fapp0 (Product_cat C C) C P (@Product_pair C C A0 A1))))
  : τ (Hom C X
      (@fapp0 (Product_cat C C) C P (@Product_pair C C A0 A1)))
≔ @comp_fapp0
    C X
    (@fapp0 (Product_cat C C) C P (@Product_pair C C A0 A1))
    (@fapp0 (Product_cat C C) C P (@Product_pair C C A0 A1))
    (@binary_products_pair_fapp0
      C P B
      (@fapp0 (Product_cat C C) C P (@Product_pair C C A0 A1))
      A0 A1
      (@binary_products_proj1_fapp0 C P B A0 A1)
      (@binary_products_proj2_fapp0 C P B A0 A1))
    h;

// Universal uniqueness: h = <pi_1 o h,pi_2 o h>.
symbol binary_products_pair_unique_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (B : τ (@BinaryProducts C P))
  [X A0 A1 : τ (Obj C)]
  (h : τ (Hom C X
    (@fapp0 (Product_cat C C) C P (@Product_pair C C A0 A1))))
  : τ (@=
      (Hom C X
        (@fapp0 (Product_cat C C) C P (@Product_pair C C A0 A1)))
      h
      (@binary_products_pair_reconstruct_fapp0 C P B X A0 A1 h))
≔ @eq_trans
    (Hom C X
      (@fapp0 (Product_cat C C) C P (@Product_pair C C A0 A1)))
    h
    (@binary_products_pair_unique_common_fapp0 C P B X A0 A1 h)
    (@binary_products_pair_reconstruct_fapp0 C P B X A0 A1 h)
    (@eq_trans
      (Hom C X
        (@fapp0 (Product_cat C C) C P (@Product_pair C C A0 A1)))
      h
      (@comp_fapp0
        C X
        (@fapp0 (Product_cat C C) C P (@Product_pair C C A0 A1))
        (@fapp0 (Product_cat C C) C P (@Product_pair C C A0 A1))
        (@id C
          (@fapp0 (Product_cat C C) C P (@Product_pair C C A0 A1)))
        h)
      (@binary_products_pair_unique_common_fapp0 C P B X A0 A1 h)
      (@eq_refl
        (Hom C X
          (@fapp0 (Product_cat C C) C P (@Product_pair C C A0 A1)))
        h)
      (@binary_products_comp_post_path
        C X
        (@fapp0 (Product_cat C C) C P (@Product_pair C C A0 A1))
        (@fapp0 (Product_cat C C) C P (@Product_pair C C A0 A1))
        h
        (@id C
          (@fapp0 (Product_cat C C) C P (@Product_pair C C A0 A1)))
        (@binary_products_pair_fapp0
          C P B
          (@fapp0 (Product_cat C C) C P (@Product_pair C C A0 A1))
          A0 A1
          (@binary_products_proj1_fapp0 C P B A0 A1)
          (@binary_products_proj2_fapp0 C P B A0 A1))
        (@eq_sym
          (Hom C
            (@fapp0 (Product_cat C C) C P (@Product_pair C C A0 A1))
            (@fapp0 (Product_cat C C) C P (@Product_pair C C A0 A1)))
          (@binary_products_pair_fapp0
            C P B
            (@fapp0 (Product_cat C C) C P (@Product_pair C C A0 A1))
            A0 A1
            (@binary_products_proj1_fapp0 C P B A0 A1)
            (@binary_products_proj2_fapp0 C P B A0 A1))
          (@id C
            (@fapp0 (Product_cat C C) C P (@Product_pair C C A0 A1)))
          (@binary_products_pair_eta_path C P B A0 A1))))
    (@binary_products_pair_distribution_path
      C P B
      X
      (@fapp0 (Product_cat C C) C P (@Product_pair C C A0 A1))
      A0 A1
      h
      (@binary_products_proj1_fapp0 C P B A0 A1)
      (@binary_products_proj2_fapp0 C P B A0 A1));
