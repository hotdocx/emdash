/* Ordinary contravariant owners selectively ported from 20c6dd2e.
   Whole/component/identity computation, proof-time Op bridges, and retained
   higher action; no opaque action-profile migration is imported. */
require open emdash.emdash3_2;

// Inferred identity categories may normalize before the outer con cut.

assert [A B C : Cat]
  (H : τ (Functor A (Product_cat B C))) ⊢
  @tapp1_con_int_fapp0_transf A (Product_cat B C) H H
    (@id (Product_cat (Functor_cat A B) (Functor_cat A C)) H)
  ≡ @fapp1_con_int_transf A (Product_cat B C) H;

assert [A B C : Cat]
  (H : τ (Functor A (Product_cat B C))) (Y : τ (Obj A)) ⊢
  @tapp1_con_at_transf A (Product_cat B C) H H
    (@id (Product_cat (Functor_cat A B) (Functor_cat A C)) H) Y
  ≡ @fapp1_con_at_transf A (Product_cat B C) H Y;

// The arbitrary fixed-target mirror is the opposite specialization of the
// existing internal action and projects to the same off-diagonal hom functor.
assert [A B : Cat] [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (Y : τ (Obj A)) ⊢
  @eq_refl
    (Obj (@Transf_cat
      (Op_cat A)
      Cat_cat
      (@hom_con A Y A (@id_func A))
      (@hom_con B (@fapp0 A B G Y) A F)))
    (@tapp1_con_at_transf A B F G epsilon Y)
  : τ (@=
      (Obj (@Transf_cat
        (Op_cat A)
        Cat_cat
        (@hom_con A Y A (@id_func A))
        (@hom_con B (@fapp0 A B G Y) A F)))
      (@tapp0_fapp0
        (Op_cat (Op_cat A))
        (@Catd_cat (Op_cat A))
        (@hom_int
          (Op_cat A)
          (Op_cat A)
          (@id_func (Op_cat A)))
        (@comp_cat_fapp0
          (Op_cat (Op_cat A))
          (Op_cat (Op_cat B))
          (@Catd_cat (Op_cat A))
          (@hom_int
            (Op_cat B)
            (Op_cat A)
            (@Op_func A B F))
          (@Op_func
            (Op_cat A)
            (Op_cat B)
            (@Op_func A B G)))
        Y
        (@tapp1_con_int_fapp0_transf A B F G epsilon))
      (@tapp1_con_at_transf A B F G epsilon Y));

// The direct opposite presentation compares proof-time in both orientations.
assert [A B : Cat] [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (Y : τ (Obj A)) ⊢
  @eq_refl
    (Obj (@Transf_cat
      (Op_cat A)
      Cat_cat
      (@hom_con A Y A (@id_func A))
      (@hom_con B (@fapp0 A B G Y) A F)))
    (@tapp1_con_at_transf A B F G epsilon Y)
  : τ (@=
      (Obj (@Transf_cat
        (Op_cat A)
        Cat_cat
        (@hom_con A Y A (@id_func A))
        (@hom_con B (@fapp0 A B G Y) A F)))
      (@tapp1_at_transf
        (Op_cat A)
        (Op_cat B)
        (@Op_func A B G)
        (@Op_func A B F)
        Y
        (@Op_transf A B F G epsilon))
      (@tapp1_con_at_transf A B F G epsilon Y));

assert [A B : Cat] [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (Y : τ (Obj A)) ⊢
  @eq_refl
    (Obj (@Transf_cat
      (Op_cat A)
      Cat_cat
      (@hom_con A Y A (@id_func A))
      (@hom_con B (@fapp0 A B G Y) A F)))
    (@tapp1_con_at_transf A B F G epsilon Y)
  : τ (@=
      (Obj (@Transf_cat
        (Op_cat A)
        Cat_cat
        (@hom_con A Y A (@id_func A))
        (@hom_con B (@fapp0 A B G Y) A F)))
      (@tapp1_con_at_transf A B F G epsilon Y)
      (@tapp1_at_transf
        (Op_cat A)
        (Op_cat B)
        (@Op_func A B G)
        (@Op_func A B F)
        Y
        (@Op_transf A B F G epsilon)));

assert [A B : Cat] [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (X Y : τ (Obj A)) ⊢
  @tapp0_fapp0
    (Op_cat A)
    Cat_cat
    (@hom_con A Y A (@id_func A))
    (@hom_con B (@fapp0 A B G Y) A F)
    X
    (@tapp1_con_at_transf A B F G epsilon Y)
  ≡ @tapp1_func A B F G X Y epsilon;

// The identity-specialized internal and fixed-target owners compute in the
// same stable contravariant ladder.
assert [A B : Cat] (F : τ (Functor A B)) ⊢
  @tapp1_con_int_fapp0_transf
    A B F F (@id (Functor_cat A B) F)
  ≡ @fapp1_con_int_transf A B F;

assert [A B : Cat] (F : τ (Functor A B)) (Y : τ (Obj A)) ⊢
  @tapp0_fapp0
    (Op_cat (Op_cat A))
    (@Catd_cat (Op_cat A))
    (@hom_int
      (Op_cat A)
      (Op_cat A)
      (@id_func (Op_cat A)))
    (@comp_cat_fapp0
      (Op_cat (Op_cat A))
      (Op_cat (Op_cat B))
      (@Catd_cat (Op_cat A))
      (@hom_int
        (Op_cat B)
        (Op_cat A)
        (@Op_func A B F))
      (@Op_func
        (Op_cat A)
        (Op_cat B)
        (@Op_func A B F)))
    Y
    (@fapp1_con_int_transf A B F)
  ≡ @fapp1_con_at_transf A B F Y;

// The direct opposite identity-specialized action compares proof-time.
assert [A B : Cat] (F : τ (Functor A B)) (Y : τ (Obj A)) ⊢
  @eq_refl
    (Obj (@Transf_cat
      (Op_cat A)
      Cat_cat
      (@hom_con A Y A (@id_func A))
      (@hom_con B (@fapp0 A B F Y) A F)))
    (@fapp1_con_at_transf A B F Y)
  : τ (@=
      (Obj (@Transf_cat
        (Op_cat A)
        Cat_cat
        (@hom_con A Y A (@id_func A))
        (@hom_con B (@fapp0 A B F Y) A F)))
      (@fapp1_at_transf
        (Op_cat A)
        (Op_cat B)
        (@Op_func A B F)
        Y)
      (@fapp1_con_at_transf A B F Y));

// Identity specialization reuses the target-internalized functor action.
assert [A B : Cat] (F : τ (Functor A B)) (Y : τ (Obj A)) ⊢
  @eq_refl
    (Obj (@Transf_cat
      (Op_cat A)
      Cat_cat
      (@hom_con A Y A (@id_func A))
      (@hom_con B (@fapp0 A B F Y) A F)))
    (@tapp1_con_at_transf
      A B F F
      (@id (Functor_cat A B) F)
      Y)
  : τ (@=
      (Obj (@Transf_cat
        (Op_cat A)
        Cat_cat
        (@hom_con A Y A (@id_func A))
        (@hom_con B (@fapp0 A B F Y) A F)))
      (@tapp1_con_at_transf
        A B F F
        (@id (Functor_cat A B) F)
        Y)
      (@fapp1_con_at_transf A B F Y));

assert [A B : Cat] (F : τ (Functor A B)) (X Y : τ (Obj A)) ⊢
  @tapp0_fapp0
    (Op_cat A)
    Cat_cat
    (@hom_con A Y A (@id_func A))
    (@hom_con B (@fapp0 A B F Y) A F)
    X
    (@fapp1_con_at_transf A B F Y)
  ≡ @fapp1_func A B F X Y;

// The whole displayed extraction consumes the fixed-target mirror and
// computes to the established fdapp1_int_cell pre/right witness.
assert [A B : Cat] [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  [W X Y : τ (Obj A)]
  (h : τ (Hom A W X))
  (q : τ (Hom A X Y)) ⊢
  @tapp0_fapp0
    (Hom_cat A X Y)
    (Hom_cat B (@fapp0 A B F W) (@fapp0 A B G Y))
    (@functord_transport_lhs_func
      (Op_cat A)
      (@hom_con A Y A (@id_func A))
      (@hom_con B (@fapp0 A B G Y) A F)
      (@tapp1_con_at_transf A B F G epsilon Y)
      X W h)
    (@functord_transport_rhs_func
      (Op_cat A)
      (@hom_con A Y A (@id_func A))
      (@hom_con B (@fapp0 A B G Y) A F)
      (@tapp1_con_at_transf A B F G epsilon Y)
      X W h)
    q
    (@functord_laxity_transf
      (Op_cat A)
      (@hom_con A Y A (@id_func A))
      (@hom_con B (@fapp0 A B G Y) A F)
      (@tapp1_con_at_transf A B F G epsilon Y)
      X W h)
  ≡ @fdapp1_int_cell
      (Op_cat A)
      (@hom_con A Y A (@id_func A))
      (@hom_con B (@fapp0 A B G Y) A F)
      (@tapp1_con_at_transf A B F G epsilon Y)
      X W h q;

assert
  [A B : Cat] [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G)) ⊢
  @eq_refl (Transf
      (@hom_int (Op_cat A) (Op_cat A) (@id_func (Op_cat A)))
      (@comp_cat_fapp0 A B (@Catd_cat (Op_cat A))
        (@hom_int (Op_cat B) (Op_cat A) (@Op_func A B F)) G)) (@tapp1_con_int_fapp0_transf A B F G epsilon)
  : τ (@= (Transf
      (@hom_int (Op_cat A) (Op_cat A) (@id_func (Op_cat A)))
      (@comp_cat_fapp0 A B (@Catd_cat (Op_cat A))
        (@hom_int (Op_cat B) (Op_cat A) (@Op_func A B F)) G))
      (@tapp1_int_fapp0_transf (Op_cat A) (Op_cat B)
        (@Op_func A B G) (@Op_func A B F) (@Op_transf A B F G epsilon))
      (@tapp1_con_int_fapp0_transf A B F G epsilon));

assert
  [A B : Cat] [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G)) ⊢
  @eq_refl (Transf
      (@hom_int (Op_cat A) (Op_cat A) (@id_func (Op_cat A)))
      (@comp_cat_fapp0 A B (@Catd_cat (Op_cat A))
        (@hom_int (Op_cat B) (Op_cat A) (@Op_func A B F)) G)) (@tapp1_con_int_fapp0_transf A B F G epsilon)
  : τ (@= (Transf
      (@hom_int (Op_cat A) (Op_cat A) (@id_func (Op_cat A)))
      (@comp_cat_fapp0 A B (@Catd_cat (Op_cat A))
        (@hom_int (Op_cat B) (Op_cat A) (@Op_func A B F)) G))
      (@tapp1_con_int_fapp0_transf A B F G epsilon)
      (@tapp1_int_fapp0_transf (Op_cat A) (Op_cat B)
        (@Op_func A B G) (@Op_func A B F) (@Op_transf A B F G epsilon)));

// The semantic bridge is proof-time, not a global runtime orientation.
assertnot
  [A B : Cat] [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G)) ⊢
  @tapp1_int_fapp0_transf (Op_cat A) (Op_cat B)
        (@Op_func A B G) (@Op_func A B F) (@Op_transf A B F G epsilon)
  ≡ @tapp1_con_int_fapp0_transf A B F G epsilon;

assert
  [A B : Cat] (F : τ (Functor A B)) ⊢
  @eq_refl (Transf
      (@hom_int (Op_cat A) (Op_cat A) (@id_func (Op_cat A)))
      (@comp_cat_fapp0 A B (@Catd_cat (Op_cat A))
        (@hom_int (Op_cat B) (Op_cat A) (@Op_func A B F)) F)) (@fapp1_con_int_transf A B F)
  : τ (@= (Transf
      (@hom_int (Op_cat A) (Op_cat A) (@id_func (Op_cat A)))
      (@comp_cat_fapp0 A B (@Catd_cat (Op_cat A))
        (@hom_int (Op_cat B) (Op_cat A) (@Op_func A B F)) F))
      (@fapp1_int_transf (Op_cat A) (Op_cat B) (@Op_func A B F))
      (@fapp1_con_int_transf A B F));

assert
  [A B : Cat] (F : τ (Functor A B)) ⊢
  @eq_refl (Transf
      (@hom_int (Op_cat A) (Op_cat A) (@id_func (Op_cat A)))
      (@comp_cat_fapp0 A B (@Catd_cat (Op_cat A))
        (@hom_int (Op_cat B) (Op_cat A) (@Op_func A B F)) F)) (@fapp1_con_int_transf A B F)
  : τ (@= (Transf
      (@hom_int (Op_cat A) (Op_cat A) (@id_func (Op_cat A)))
      (@comp_cat_fapp0 A B (@Catd_cat (Op_cat A))
        (@hom_int (Op_cat B) (Op_cat A) (@Op_func A B F)) F))
      (@fapp1_con_int_transf A B F)
      (@fapp1_int_transf (Op_cat A) (Op_cat B) (@Op_func A B F)));

// The comparison does not identify arbitrary distinct transfors.
assertnot [A B : Cat] [F G : τ (Functor A B)]
  (epsilon other : τ (Transf F G)) (Y : τ (Obj A)) ⊢
  @eq_refl
    (Transf (@hom_con A Y A (@id_func A))
      (@hom_con B (@fapp0 A B G Y) A F))
    (@tapp1_con_at_transf A B F G epsilon Y)
  : τ (@=
      (Transf (@hom_con A Y A (@id_func A))
        (@hom_con B (@fapp0 A B G Y) A F))
      (@tapp1_con_at_transf A B F G epsilon Y)
      (@tapp1_at_transf (Op_cat A) (Op_cat B)
        (@Op_func A B G) (@Op_func A B F) Y
        (@Op_transf A B F G other)));

// One further whole hom action remains after the fixed-target component.
assert [A B : Cat] [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G)) (X Y : τ (Obj A))
  (f g : τ (Hom A X Y)) ⊢
  @fapp1_func (Hom_cat A X Y)
    (Hom_cat B (@fapp0 A B F X) (@fapp0 A B G Y))
    (@tapp0_fapp0 (Op_cat A) Cat_cat
      (@hom_con A Y A (@id_func A))
      (@hom_con B (@fapp0 A B G Y) A F) X
      (@tapp1_con_at_transf A B F G epsilon Y)) f g
  ≡ @fapp1_func (Hom_cat A X Y)
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B G Y))
      (@tapp1_func A B F G X Y epsilon) f g;
