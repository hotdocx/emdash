/*
  Finite free vectors, column matrices, and presentation agreements.

  A vector is the existing right-associated FiniteFamily of ring elements.
  A rows-by-columns matrix is a FiniteFamily of column vectors and therefore
  acts R^columns -> R^rows by a finite linear combination.  Presentation
  agreement retains explicit coefficients and an equation; it is not a
  quotient-module equality or an Abelian-category construction.
*/

require open emdash.emdash3_2_commutative_algebra_finite;

// Finite free vectors reuse the canonical finite-family representation.
symbol CommRingVector
  (R : τ CommRing)
  (n : τ Nat_grpd)
  : Grpd
≔ @FiniteFamily (@comm_ring_carrier R) n;

// The zero vector, recursively aligned with its length.
symbol comm_ring_vector_zero
  (R : τ CommRing)
  (n : τ Nat_grpd)
  : τ (@CommRingVector R n)
≔ @nat_elim
    (λ n0 : τ Nat_grpd, @CommRingVector R n0)
    (@finite_family_nil (@comm_ring_carrier R))
    (λ n0 : τ Nat_grpd,
      λ tail : τ (@CommRingVector R n0),
        @finite_family_cons
          (@comm_ring_carrier R) n0 (@comm_ring_zero R) tail)
    n;

// Componentwise vector addition.
symbol comm_ring_vector_add
  (R : τ CommRing)
  (n : τ Nat_grpd)
  (u v : τ (@CommRingVector R n))
  : τ (@CommRingVector R n)
≔ (@nat_elim
    (λ n0 : τ Nat_grpd,
      @Function_grpd
        (@CommRingVector R n0)
        (@Function_grpd
          (@CommRingVector R n0)
          (@CommRingVector R n0)))
    (λ _ : τ (@CommRingVector R zero),
      λ _ : τ (@CommRingVector R zero),
        @finite_family_nil (@comm_ring_carrier R))
    (λ n0 : τ Nat_grpd,
      λ rec : τ (@Function_grpd
        (@CommRingVector R n0)
        (@Function_grpd
          (@CommRingVector R n0)
          (@CommRingVector R n0))),
      λ us : τ (@CommRingVector R (succ n0)),
      λ vs : τ (@CommRingVector R (succ n0)),
        @finite_family_cons
          (@comm_ring_carrier R) n0
          (@comm_ring_add R
            (@finite_family_head (@comm_ring_carrier R) n0 us)
            (@finite_family_head (@comm_ring_carrier R) n0 vs))
          (rec
            (@finite_family_tail (@comm_ring_carrier R) n0 us)
            (@finite_family_tail (@comm_ring_carrier R) n0 vs)))
    n) u v;

// Componentwise additive inverse.
symbol comm_ring_vector_neg
  (R : τ CommRing)
  (n : τ Nat_grpd)
  (u : τ (@CommRingVector R n))
  : τ (@CommRingVector R n)
≔ @finite_family_map
    (@comm_ring_carrier R)
    (@comm_ring_carrier R)
    (λ x : τ (@comm_ring_carrier R), @comm_ring_neg R x)
    n u;

symbol comm_ring_vector_sub
  (R : τ CommRing)
  (n : τ Nat_grpd)
  (u v : τ (@CommRingVector R n))
  : τ (@CommRingVector R n)
≔ @comm_ring_vector_add R n u (@comm_ring_vector_neg R n v);

// Componentwise scalar multiplication.
symbol comm_ring_vector_scale
  (R : τ CommRing)
  (n : τ Nat_grpd)
  (a : τ (@comm_ring_carrier R))
  (u : τ (@CommRingVector R n))
  : τ (@CommRingVector R n)
≔ @finite_family_map
    (@comm_ring_carrier R)
    (@comm_ring_carrier R)
    (λ x : τ (@comm_ring_carrier R), @comm_ring_mul R a x)
    n u;

// Column-oriented rows-by-columns matrices.
symbol CommRingMatrix
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  : Grpd
≔ @FiniteFamily (@CommRingVector R rows) columns;

// Matrix action is the finite linear combination of columns.
symbol comm_ring_matrix_apply
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows columns))
  (x : τ (@CommRingVector R columns))
  : τ (@CommRingVector R rows)
≔ (@nat_elim
    (λ columns0 : τ Nat_grpd,
      @Function_grpd
        (@CommRingMatrix R rows columns0)
        (@Function_grpd
          (@CommRingVector R columns0)
          (@CommRingVector R rows)))
    (λ _ : τ (@CommRingMatrix R rows zero),
      λ _ : τ (@CommRingVector R zero),
        @comm_ring_vector_zero R rows)
    (λ columns0 : τ Nat_grpd,
      λ rec : τ (@Function_grpd
        (@CommRingMatrix R rows columns0)
        (@Function_grpd
          (@CommRingVector R columns0)
          (@CommRingVector R rows))),
      λ columnsA : τ (@CommRingMatrix R rows (succ columns0)),
      λ coefficients : τ (@CommRingVector R (succ columns0)),
        @comm_ring_vector_add R rows
          (@comm_ring_vector_scale R rows
            (@finite_family_head
              (@comm_ring_carrier R) columns0 coefficients)
            (@finite_family_head
              (@CommRingVector R rows) columns0 columnsA))
          (rec
            (@finite_family_tail
              (@CommRingVector R rows) columns0 columnsA)
            (@finite_family_tail
              (@comm_ring_carrier R) columns0 coefficients)))
    columns) A x;

// Zero matrix: a finite family of zero columns.
symbol comm_ring_matrix_zero
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  : τ (@CommRingMatrix R rows columns)
≔ (@nat_elim
    (λ columns0 : τ Nat_grpd, @CommRingMatrix R rows columns0)
    (@finite_family_nil (@CommRingVector R rows))
    (λ columns0 : τ Nat_grpd,
      λ tail : τ (@CommRingMatrix R rows columns0),
        @finite_family_cons
          (@CommRingVector R rows) columns0
          (@comm_ring_vector_zero R rows)
          tail)
    columns);

// Matrix composition maps the left action over the columns of the right.
symbol comm_ring_matrix_comp
  (R : τ CommRing)
  (rows middle columns : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows middle))
  (B : τ (@CommRingMatrix R middle columns))
  : τ (@CommRingMatrix R rows columns)
≔ @finite_family_map
    (@CommRingVector R middle)
    (@CommRingVector R rows)
    (λ column : τ (@CommRingVector R middle),
      @comm_ring_matrix_apply R rows middle A column)
    columns B;

// Explicit relation coefficients witnessing agreement modulo a presentation.
symbol CommRingPresentationAgreement
  (R : τ CommRing)
  (generators relations : τ Nat_grpd)
  (A : τ (@CommRingMatrix R generators relations))
  (v w : τ (@CommRingVector R generators))
  : Grpd
≔ `Σ_ coefficients : τ (@CommRingVector R relations),
    @= (@CommRingVector R generators)
      (@comm_ring_matrix_apply R generators relations A coefficients)
      (@comm_ring_vector_sub R generators v w);

symbol comm_ring_presentation_agreement_intro
  [R : τ CommRing]
  [generators relations : τ Nat_grpd]
  [A : τ (@CommRingMatrix R generators relations)]
  [v w : τ (@CommRingVector R generators)]
  (coefficients : τ (@CommRingVector R relations))
  (law : τ (@= (@CommRingVector R generators)
      (@comm_ring_matrix_apply R generators relations A coefficients)
      (@comm_ring_vector_sub R generators v w)))
  : τ (@CommRingPresentationAgreement
      R generators relations A v w)
≔ @Struct_sigma
    (@CommRingVector R relations)
    (λ c : τ (@CommRingVector R relations),
      @= (@CommRingVector R generators)
        (@comm_ring_matrix_apply R generators relations A c)
        (@comm_ring_vector_sub R generators v w))
    coefficients law;

// A syzygy is a selected coefficient vector sent to zero.
symbol CommRingMatrixSyzygy
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows columns))
  (s : τ (@CommRingVector R columns))
  : Grpd
≔ @= (@CommRingVector R rows)
    (@comm_ring_matrix_apply R rows columns A s)
    (@comm_ring_vector_zero R rows);

// Adjacent presentation differentials compose to the zero matrix.
symbol CommRingMatrixCompositeZero
  (R : τ CommRing)
  (rows middle columns : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows middle))
  (B : τ (@CommRingMatrix R middle columns))
  : Grpd
≔ @= (@CommRingMatrix R rows columns)
    (@comm_ring_matrix_comp R rows middle columns A B)
    (@comm_ring_matrix_zero R rows columns);
