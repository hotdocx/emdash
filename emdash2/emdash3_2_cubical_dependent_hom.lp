/*
  Emdash v3.2: the fixed-endpoint cubical dependent hom.

  A mixed-variance Cat-valued family

    E : K1^op -> Catd(K2)

  sends a forward second-coordinate arrow b : x2 -> y2 and a forward
  first-coordinate arrow a : x1 -> y1 to two objects of the common cross
  fibre E[x1][y2]:

    source_E(u,b) = E[x1][b](u),
    target_E(v,a) = E[a^op][y2](v).

  The selected lax square orientation is the hom from source to target.  Its
  whole curried classifier is covariant in a and contravariant in b:

    homdc_(E,x1,u,y1,v)
      : Hom_K1(x1,y1) -> Catd(Hom_K2(x2,y2)^op).

  This module is transparent and rule-free.  Both endpoint actions are
  assembled from the existing whole functor/transfor evaluators, and the
  final family is represented by hom_con_int.  It therefore retains the
  ordinary hom actions in both side-arrow coordinates without postulating a
  square, coherence cell, rewrite, or unifier.
*/

require open emdash.emdash3_2;

// Whole covariant second-coordinate action on the source endpoint.
//
//   homdc_source_func(E,x1,u)[b] = E[x1][b](u).
symbol homdc_source_func
  [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  (x1 : τ (Obj K1))
  (x2 y2 : τ (Obj K2))
  (u : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E x1) x2)))
  : τ (Functor
      (Hom_cat K2 x2 y2)
      (Fibre_cat
        (@fapp0 (Op_cat K1) (Catd_cat K2) E x1)
        y2))
≔ @fib_cov_tapp0_func
    K2
    (@fapp0 (Op_cat K1) (Catd_cat K2) E x1)
    x2 y2 u;

// Whole contravariant first-coordinate action on the target endpoint.
// The source Hom in Op(K1) is judgmentally Hom_K1(x1,y1); component
// evaluation at y2 and object evaluation at v retain the complete action in
// a instead of postulating the capped formula E[a^op][y2](v).
symbol homdc_target_func
  [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  (x1 y1 : τ (Obj K1))
  (y2 : τ (Obj K2))
  (v : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E y1) y2)))
  : τ (Functor
      (Hom_cat K1 x1 y1)
      (Fibre_cat
        (@fapp0 (Op_cat K1) (Catd_cat K2) E x1)
        y2))
≔ @comp_cat_fapp0
    (Hom_cat K1 x1 y1)
    (Functor_cat
      (Fibre_cat
        (@fapp0 (Op_cat K1) (Catd_cat K2) E y1)
        y2)
      (Fibre_cat
        (@fapp0 (Op_cat K1) (Catd_cat K2) E x1)
        y2))
    (Fibre_cat
      (@fapp0 (Op_cat K1) (Catd_cat K2) E x1)
      y2)
    (@fapp0_func
      (Fibre_cat
        (@fapp0 (Op_cat K1) (Catd_cat K2) E y1)
        y2)
      (Fibre_cat
        (@fapp0 (Op_cat K1) (Catd_cat K2) E x1)
        y2)
      v)
    (@comp_cat_fapp0
      (Hom_cat K1 x1 y1)
      (@Functord_cat
        K2
        (@fapp0 (Op_cat K1) (Catd_cat K2) E y1)
        (@fapp0 (Op_cat K1) (Catd_cat K2) E x1))
      (Functor_cat
        (Fibre_cat
          (@fapp0 (Op_cat K1) (Catd_cat K2) E y1)
          y2)
        (Fibre_cat
          (@fapp0 (Op_cat K1) (Catd_cat K2) E x1)
          y2))
      (@tapp0_func
        K2 Cat_cat
        (@fapp0 (Op_cat K1) (Catd_cat K2) E y1)
        (@fapp0 (Op_cat K1) (Catd_cat K2) E x1)
        y2)
      (@fapp1_func
        (Op_cat K1)
        (Catd_cat K2)
        E y1 x1));

// Curried fixed-endpoint cubical dependent hom.
//
//   homdc_(E,x1,u,y1,v)[a][b]
//     = Hom_{E[x1][y2]}(E[x1][b](u),E[a^op][y2](v)).
symbol homdc_
  [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  (x1 y1 : τ (Obj K1))
  (x2 y2 : τ (Obj K2))
  (u : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E x1) x2)))
  (v : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E y1) y2)))
  : τ (Functor
      (Hom_cat K1 x1 y1)
      (Catd_cat (Op_cat (Hom_cat K2 x2 y2))))
≔ @comp_cat_fapp0
    (Hom_cat K1 x1 y1)
    (Fibre_cat
      (@fapp0 (Op_cat K1) (Catd_cat K2) E x1)
      y2)
    (Catd_cat (Op_cat (Hom_cat K2 x2 y2)))
    (@hom_con_int
      (Fibre_cat
        (@fapp0 (Op_cat K1) (Catd_cat K2) E x1)
        y2)
      (Hom_cat K2 x2 y2)
      (@homdc_source_func K1 K2 E x1 x2 y2 u))
    (@homdc_target_func K1 K2 E x1 y1 y2 v);

// Readable selected fibre of the curried classifier.
symbol homdc_fibre
  [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  (x1 y1 : τ (Obj K1))
  (x2 y2 : τ (Obj K2))
  (u : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E x1) x2)))
  (v : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E y1) y2)))
  (a : τ (Hom K1 x1 y1))
  (b : τ (Hom K2 x2 y2))
  : Cat
≔ @Fibre_cat
    (Op_cat (Hom_cat K2 x2 y2))
    (@fapp0
      (Hom_cat K1 x1 y1)
      (Catd_cat (Op_cat (Hom_cat K2 x2 y2)))
      (@homdc_ K1 K2 E x1 y1 x2 y2 u v)
      a)
    b;

// Identity represented-family specialization: the ordinary directed square
// frame with vertical edges u,v and horizontal edges a,b.
symbol homdc_square_func
  [C : Cat]
  (x1 y1 x2 y2 : τ (Obj C))
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  : τ (Functor
      (Hom_cat C x1 y1)
      (Catd_cat (Op_cat (Hom_cat C x2 y2))))
≔ @homdc_
    C C
    (@hom_int C C (@id_func C))
    x1 y1 x2 y2 u v;

// Readable filler-category observation for a directed square.
// Its objects are 2-cells b o u ==> v o a in C.
symbol homdc_square_fibre
  [C : Cat]
  [x1 y1 x2 y2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  : Cat
≔ @homdc_fibre
    C C
    (@hom_int C C (@id_func C))
    x1 y1 x2 y2 u v a b;
