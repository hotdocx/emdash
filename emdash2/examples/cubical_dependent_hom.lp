/*
  Reviewer example: a rule-free two-sided dependent hom and its directed
  square specialization.

  The general construction transports two endpoints into one cross fibre.
  For E = hom_int(id_C), its objects are 2-cells

    b o u ==> v o a.

  The classifier remains whole in both side arrows.  No primitive square,
  point beta, rewrite, or proof-time unifier is used.
*/

require open emdash.emdash3_2_cubical_dependent_hom;

// The source side remains a whole covariant action in b.
assert [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  (x1 : τ (Obj K1))
  (x2 y2 : τ (Obj K2))
  (u : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E x1) x2))) ⊢
  @homdc_source_func K1 K2 E x1 x2 y2 u
  : τ (Functor
      (Hom_cat K2 x2 y2)
      (Fibre_cat
        (@fapp0 (Op_cat K1) (Catd_cat K2) E x1)
        y2));

// The target side remains a whole action in a, formed by the outer hom
// action of E followed by fibre and object evaluation.
assert [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  (x1 y1 : τ (Obj K1))
  (y2 : τ (Obj K2))
  (v : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E y1) y2))) ⊢
  @homdc_target_func K1 K2 E x1 y1 y2 v
  : τ (Functor
      (Hom_cat K1 x1 y1)
      (Fibre_cat
        (@fapp0 (Op_cat K1) (Catd_cat K2) E x1)
        y2));

// The selected curried variance is covariant in a and contravariant in b.
assert [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  (x1 y1 : τ (Obj K1))
  (x2 y2 : τ (Obj K2))
  (u : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E x1) x2)))
  (v : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E y1) y2))) ⊢
  @homdc_ K1 K2 E x1 y1 x2 y2 u v
  : τ (Functor
      (Hom_cat K1 x1 y1)
      (Catd_cat (Op_cat (Hom_cat K2 x2 y2))));

// Generic fibre computation in the common cross corner.
assert [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  (x1 y1 : τ (Obj K1))
  (x2 y2 : τ (Obj K2))
  (u : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E x1) x2)))
  (v : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E y1) y2)))
  (a : τ (Hom K1 x1 y1))
  (b : τ (Hom K2 x2 y2)) ⊢
  @eq_refl
    Cat_grpd
    (@homdc_fibre K1 K2 E x1 y1 x2 y2 u v a b)
  : τ (@=
      Cat_grpd
      (@homdc_fibre K1 K2 E x1 y1 x2 y2 u v a b)
      (@Hom_cat
        (Fibre_cat
          (@fapp0 (Op_cat K1) (Catd_cat K2) E x1)
          y2)
        (@fapp0
          (Hom_cat K2 x2 y2)
          (Fibre_cat
            (@fapp0 (Op_cat K1) (Catd_cat K2) E x1)
            y2)
          (@homdc_source_func K1 K2 E x1 x2 y2 u)
          b)
        (@fapp0
          (Hom_cat K1 x1 y1)
          (Fibre_cat
            (@fapp0 (Op_cat K1) (Catd_cat K2) E x1)
            y2)
          (@homdc_target_func K1 K2 E x1 y1 y2 v)
          a)));

// In the identity represented family, the fibre is the standard directed
// lax-square 2-cell category Hom_{Hom_C(x1,y2)}(b o u,v o a).
assert [C : Cat]
  (x1 y1 x2 y2 : τ (Obj C))
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2)) ⊢
  @eq_refl
    Cat_grpd
    (@homdc_square_fibre C x1 y1 x2 y2 u v a b)
  : τ (@=
      Cat_grpd
      (@homdc_square_fibre C x1 y1 x2 y2 u v a b)
      (@Hom_cat
        (@Hom_cat C x1 y2)
        (@comp_fapp0 C x1 x2 y2 b u)
        (@comp_fapp0 C x1 y1 y2 v a)));

// The outer and inner hom actions remain available after the point
// observation; no capped square constructor has erased either coordinate.
assert [C : Cat]
  (x1 y1 x2 y2 : τ (Obj C))
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (a a' : τ (Hom C x1 y1)) ⊢
  @fapp1_func
    (Hom_cat C x1 y1)
    (Catd_cat (Op_cat (Hom_cat C x2 y2)))
    (@homdc_square_func C x1 y1 x2 y2 u v)
    a a'
  : τ (Functor
      (Hom_cat (Hom_cat C x1 y1) a a')
      (Hom_cat
        (Catd_cat (Op_cat (Hom_cat C x2 y2)))
        (@fapp0
          (Hom_cat C x1 y1)
          (Catd_cat (Op_cat (Hom_cat C x2 y2)))
          (@homdc_square_func C x1 y1 x2 y2 u v)
          a)
        (@fapp0
          (Hom_cat C x1 y1)
          (Catd_cat (Op_cat (Hom_cat C x2 y2)))
          (@homdc_square_func C x1 y1 x2 y2 u v)
          a')));

assert [C : Cat]
  (x1 y1 x2 y2 : τ (Obj C))
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (a : τ (Hom C x1 y1))
  (b b' : τ (Hom C x2 y2)) ⊢
  @fapp1_func
    (Op_cat (Hom_cat C x2 y2))
    Cat_cat
    (@fapp0
      (Hom_cat C x1 y1)
      (Catd_cat (Op_cat (Hom_cat C x2 y2)))
      (@homdc_square_func C x1 y1 x2 y2 u v)
      a)
    b b'
  : τ (Functor
      (Hom_cat (Op_cat (Hom_cat C x2 y2)) b b')
      (Hom_cat
        Cat_cat
        (@homdc_square_fibre C x1 y1 x2 y2 u v a b)
        (@homdc_square_fibre C x1 y1 x2 y2 u v a b')));

// A direct unit-profunctor dependent hom uses a different boundary: for
// u_tw : y1 -> x2 it gives b o u_tw o a ==> v_tw.  The standard square
// family does not collapse to that twisted presentation.
assertnot [C : Cat]
  (x1 y1 x2 y2 : τ (Obj C))
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (u_tw : τ (Hom C y1 x2))
  (v_tw : τ (Hom C x1 y2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2)) ⊢
  @homdc_square_fibre C x1 y1 x2 y2 u v a b
  ≡ @Hom_cat
      (@Hom_cat C x1 y2)
      (@comp_fapp0
        C x1 x2 y2 b
        (@comp_fapp0 C x1 y1 x2 u_tw a))
      v_tw;
