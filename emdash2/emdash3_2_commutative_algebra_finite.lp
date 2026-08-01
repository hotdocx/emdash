/*
  Finite commutative-ring sums and unimodular cover presentations.

  This rule-free one-way module defines the selected finite sum and dot
  product, proves preservation by structured ring maps, and packages chosen
  coefficients witnessing that a finite family generates the unit ideal.
  The resulting Zariski-cover presentation is algebraic input data only: this
  module declares no Spec, basic-open, localization family, coverage, topology,
  power, radical, fraction, polynomial, or quotient interface.
*/

require open emdash.emdash3_2_finite_families;
require open emdash.emdash3_2_commutative_algebra_category;

// Ring-valued finite sum, with zero as the empty sum.
symbol comm_ring_finite_sum
  (R : τ CommRing)
  (n : τ Nat_grpd)
  (xs : τ (@FiniteFamily (@comm_ring_carrier R) n))
  : τ (@comm_ring_carrier R)
≔ (@nat_elim
    (λ n0 : τ Nat_grpd,
      @Function_grpd
        (@FiniteFamily (@comm_ring_carrier R) n0)
        (@comm_ring_carrier R))
    (λ _ : τ (@FiniteFamily (@comm_ring_carrier R) zero),
      @comm_ring_zero R)
    (λ n0 : τ Nat_grpd,
      λ rec : τ (@Function_grpd
        (@FiniteFamily (@comm_ring_carrier R) n0)
        (@comm_ring_carrier R)),
      λ ys : τ (@FiniteFamily (@comm_ring_carrier R) (succ n0)),
        @comm_ring_add R
          (@finite_family_head (@comm_ring_carrier R) n0 ys)
          (rec (@finite_family_tail (@comm_ring_carrier R) n0 ys)))
    n) xs;

// Finite dot product sum_i a_i*f_i, recursively sharing the same length.
symbol comm_ring_finite_dot
  (R : τ CommRing)
  (n : τ Nat_grpd)
  (coefficients generators :
    τ (@FiniteFamily (@comm_ring_carrier R) n))
  : τ (@comm_ring_carrier R)
≔ (@nat_elim
    (λ n0 : τ Nat_grpd,
      @Function_grpd
        (@FiniteFamily (@comm_ring_carrier R) n0)
        (@Function_grpd
          (@FiniteFamily (@comm_ring_carrier R) n0)
          (@comm_ring_carrier R)))
    (λ _ : τ (@FiniteFamily (@comm_ring_carrier R) zero),
      λ _ : τ (@FiniteFamily (@comm_ring_carrier R) zero),
        @comm_ring_zero R)
    (λ n0 : τ Nat_grpd,
      λ rec : τ (@Function_grpd
        (@FiniteFamily (@comm_ring_carrier R) n0)
        (@Function_grpd
          (@FiniteFamily (@comm_ring_carrier R) n0)
          (@comm_ring_carrier R))),
      λ as0 : τ (@FiniteFamily (@comm_ring_carrier R) (succ n0)),
      λ fs0 : τ (@FiniteFamily (@comm_ring_carrier R) (succ n0)),
        @comm_ring_add R
          (@comm_ring_mul R
            (@finite_family_head (@comm_ring_carrier R) n0 as0)
            (@finite_family_head (@comm_ring_carrier R) n0 fs0))
          (rec
            (@finite_family_tail (@comm_ring_carrier R) n0 as0)
            (@finite_family_tail (@comm_ring_carrier R) n0 fs0)))
    n) coefficients generators;

// Structured ring maps preserve the recursively selected finite sum.
symbol comm_ring_hom_finite_sum_path
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (n : τ Nat_grpd)
  (xs : τ (@FiniteFamily (@comm_ring_carrier R) n))
  : τ (@= (@comm_ring_carrier S)
      (@comm_ring_hom_apply R S h
        (@comm_ring_finite_sum R n xs))
      (@comm_ring_finite_sum S n
        (@finite_family_map
          (@comm_ring_carrier R)
          (@comm_ring_carrier S)
          (@comm_ring_hom_function R S h)
          n xs)))
≔ (@nat_elim
    (λ n0 : τ Nat_grpd,
      @Pi_grpd
        (@FiniteFamily (@comm_ring_carrier R) n0)
        (λ ys : τ (@FiniteFamily (@comm_ring_carrier R) n0),
          @= (@comm_ring_carrier S)
            (@comm_ring_hom_apply R S h
              (@comm_ring_finite_sum R n0 ys))
            (@comm_ring_finite_sum S n0
              (@finite_family_map
                (@comm_ring_carrier R)
                (@comm_ring_carrier S)
                (@comm_ring_hom_function R S h)
                n0 ys))))
    (λ _ : τ (@FiniteFamily (@comm_ring_carrier R) zero),
      @comm_ring_hom_zero_law R S h)
    (λ n0 : τ Nat_grpd,
      λ ih : τ (@Pi_grpd
        (@FiniteFamily (@comm_ring_carrier R) n0)
        (λ ys : τ (@FiniteFamily (@comm_ring_carrier R) n0),
          @= (@comm_ring_carrier S)
            (@comm_ring_hom_apply R S h
              (@comm_ring_finite_sum R n0 ys))
            (@comm_ring_finite_sum S n0
              (@finite_family_map
                (@comm_ring_carrier R)
                (@comm_ring_carrier S)
                (@comm_ring_hom_function R S h)
                n0 ys)))),
      λ ys : τ (@FiniteFamily (@comm_ring_carrier R) (succ n0)),
        @eq_trans
          (@comm_ring_carrier S)
          (@comm_ring_hom_apply R S h
            (@comm_ring_add R
              (@finite_family_head (@comm_ring_carrier R) n0 ys)
              (@comm_ring_finite_sum R n0
                (@finite_family_tail (@comm_ring_carrier R) n0 ys))))
          (@comm_ring_add S
            (@comm_ring_hom_apply R S h
              (@finite_family_head (@comm_ring_carrier R) n0 ys))
            (@comm_ring_hom_apply R S h
              (@comm_ring_finite_sum R n0
                (@finite_family_tail (@comm_ring_carrier R) n0 ys))))
          (@comm_ring_add S
            (@comm_ring_hom_apply R S h
              (@finite_family_head (@comm_ring_carrier R) n0 ys))
            (@comm_ring_finite_sum S n0
              (@finite_family_map
                (@comm_ring_carrier R)
                (@comm_ring_carrier S)
                (@comm_ring_hom_function R S h)
                n0
                (@finite_family_tail (@comm_ring_carrier R) n0 ys))))
          ((@comm_ring_hom_add_law R S h)
            (@finite_family_head (@comm_ring_carrier R) n0 ys)
            (@comm_ring_finite_sum R n0
              (@finite_family_tail (@comm_ring_carrier R) n0 ys)))
          (@eq_ap
            (@comm_ring_carrier S)
            (@comm_ring_carrier S)
            (λ z : τ (@comm_ring_carrier S),
              @comm_ring_add S
                (@comm_ring_hom_apply R S h
                  (@finite_family_head (@comm_ring_carrier R) n0 ys))
                z)
            (@comm_ring_hom_apply R S h
              (@comm_ring_finite_sum R n0
                (@finite_family_tail (@comm_ring_carrier R) n0 ys)))
            (@comm_ring_finite_sum S n0
              (@finite_family_map
                (@comm_ring_carrier R)
                (@comm_ring_carrier S)
                (@comm_ring_hom_function R S h)
                n0
                (@finite_family_tail (@comm_ring_carrier R) n0 ys)))
            (ih (@finite_family_tail (@comm_ring_carrier R) n0 ys))))
    n) xs;

// Structured ring maps preserve the finite dot product.
symbol comm_ring_hom_finite_dot_path
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (n : τ Nat_grpd)
  (coefficients generators :
    τ (@FiniteFamily (@comm_ring_carrier R) n))
  : τ (@= (@comm_ring_carrier S)
      (@comm_ring_hom_apply R S h
        (@comm_ring_finite_dot R n coefficients generators))
      (@comm_ring_finite_dot S n
        (@finite_family_map
          (@comm_ring_carrier R)
          (@comm_ring_carrier S)
          (@comm_ring_hom_function R S h)
          n coefficients)
        (@finite_family_map
          (@comm_ring_carrier R)
          (@comm_ring_carrier S)
          (@comm_ring_hom_function R S h)
          n generators)))
≔ (@nat_elim
    (λ n0 : τ Nat_grpd,
      @Pi_grpd
        (@FiniteFamily (@comm_ring_carrier R) n0)
        (λ as0 : τ (@FiniteFamily (@comm_ring_carrier R) n0),
          @Pi_grpd
            (@FiniteFamily (@comm_ring_carrier R) n0)
            (λ fs0 : τ (@FiniteFamily (@comm_ring_carrier R) n0),
              @= (@comm_ring_carrier S)
                (@comm_ring_hom_apply R S h
                  (@comm_ring_finite_dot R n0 as0 fs0))
                (@comm_ring_finite_dot S n0
                  (@finite_family_map
                    (@comm_ring_carrier R)
                    (@comm_ring_carrier S)
                    (@comm_ring_hom_function R S h)
                    n0 as0)
                  (@finite_family_map
                    (@comm_ring_carrier R)
                    (@comm_ring_carrier S)
                    (@comm_ring_hom_function R S h)
                    n0 fs0)))))
    (λ _ : τ (@FiniteFamily (@comm_ring_carrier R) zero),
      λ _ : τ (@FiniteFamily (@comm_ring_carrier R) zero),
        @comm_ring_hom_zero_law R S h)
    (λ n0 : τ Nat_grpd,
      λ ih : τ (@Pi_grpd
        (@FiniteFamily (@comm_ring_carrier R) n0)
        (λ as0 : τ (@FiniteFamily (@comm_ring_carrier R) n0),
          @Pi_grpd
            (@FiniteFamily (@comm_ring_carrier R) n0)
            (λ fs0 : τ (@FiniteFamily (@comm_ring_carrier R) n0),
              @= (@comm_ring_carrier S)
                (@comm_ring_hom_apply R S h
                  (@comm_ring_finite_dot R n0 as0 fs0))
                (@comm_ring_finite_dot S n0
                  (@finite_family_map
                    (@comm_ring_carrier R)
                    (@comm_ring_carrier S)
                    (@comm_ring_hom_function R S h)
                    n0 as0)
                  (@finite_family_map
                    (@comm_ring_carrier R)
                    (@comm_ring_carrier S)
                    (@comm_ring_hom_function R S h)
                    n0 fs0))))),
      λ as0 : τ (@FiniteFamily (@comm_ring_carrier R) (succ n0)),
      λ fs0 : τ (@FiniteFamily (@comm_ring_carrier R) (succ n0)),
        @eq_trans
          (@comm_ring_carrier S)
          (@comm_ring_hom_apply R S h
            (@comm_ring_add R
              (@comm_ring_mul R
                (@finite_family_head (@comm_ring_carrier R) n0 as0)
                (@finite_family_head (@comm_ring_carrier R) n0 fs0))
              (@comm_ring_finite_dot R n0
                (@finite_family_tail (@comm_ring_carrier R) n0 as0)
                (@finite_family_tail (@comm_ring_carrier R) n0 fs0))))
          (@comm_ring_add S
            (@comm_ring_hom_apply R S h
              (@comm_ring_mul R
                (@finite_family_head (@comm_ring_carrier R) n0 as0)
                (@finite_family_head (@comm_ring_carrier R) n0 fs0)))
            (@comm_ring_hom_apply R S h
              (@comm_ring_finite_dot R n0
                (@finite_family_tail (@comm_ring_carrier R) n0 as0)
                (@finite_family_tail (@comm_ring_carrier R) n0 fs0))))
          (@comm_ring_add S
            (@comm_ring_mul S
              (@comm_ring_hom_apply R S h
                (@finite_family_head (@comm_ring_carrier R) n0 as0))
              (@comm_ring_hom_apply R S h
                (@finite_family_head (@comm_ring_carrier R) n0 fs0)))
            (@comm_ring_finite_dot S n0
              (@finite_family_map
                (@comm_ring_carrier R)
                (@comm_ring_carrier S)
                (@comm_ring_hom_function R S h)
                n0
                (@finite_family_tail (@comm_ring_carrier R) n0 as0))
              (@finite_family_map
                (@comm_ring_carrier R)
                (@comm_ring_carrier S)
                (@comm_ring_hom_function R S h)
                n0
                (@finite_family_tail (@comm_ring_carrier R) n0 fs0))))
          ((@comm_ring_hom_add_law R S h)
            (@comm_ring_mul R
              (@finite_family_head (@comm_ring_carrier R) n0 as0)
              (@finite_family_head (@comm_ring_carrier R) n0 fs0))
            (@comm_ring_finite_dot R n0
              (@finite_family_tail (@comm_ring_carrier R) n0 as0)
              (@finite_family_tail (@comm_ring_carrier R) n0 fs0)))
          (@eq_trans
            (@comm_ring_carrier S)
            (@comm_ring_add S
              (@comm_ring_hom_apply R S h
                (@comm_ring_mul R
                  (@finite_family_head (@comm_ring_carrier R) n0 as0)
                  (@finite_family_head (@comm_ring_carrier R) n0 fs0)))
              (@comm_ring_hom_apply R S h
                (@comm_ring_finite_dot R n0
                  (@finite_family_tail (@comm_ring_carrier R) n0 as0)
                  (@finite_family_tail (@comm_ring_carrier R) n0 fs0))))
            (@comm_ring_add S
              (@comm_ring_mul S
                (@comm_ring_hom_apply R S h
                  (@finite_family_head (@comm_ring_carrier R) n0 as0))
                (@comm_ring_hom_apply R S h
                  (@finite_family_head (@comm_ring_carrier R) n0 fs0)))
              (@comm_ring_hom_apply R S h
                (@comm_ring_finite_dot R n0
                  (@finite_family_tail (@comm_ring_carrier R) n0 as0)
                  (@finite_family_tail (@comm_ring_carrier R) n0 fs0))))
            (@comm_ring_add S
              (@comm_ring_mul S
                (@comm_ring_hom_apply R S h
                  (@finite_family_head (@comm_ring_carrier R) n0 as0))
                (@comm_ring_hom_apply R S h
                  (@finite_family_head (@comm_ring_carrier R) n0 fs0)))
              (@comm_ring_finite_dot S n0
                (@finite_family_map
                  (@comm_ring_carrier R)
                  (@comm_ring_carrier S)
                  (@comm_ring_hom_function R S h)
                  n0
                  (@finite_family_tail (@comm_ring_carrier R) n0 as0))
                (@finite_family_map
                  (@comm_ring_carrier R)
                  (@comm_ring_carrier S)
                  (@comm_ring_hom_function R S h)
                  n0
                  (@finite_family_tail (@comm_ring_carrier R) n0 fs0))))
            (@eq_ap
              (@comm_ring_carrier S)
              (@comm_ring_carrier S)
              (λ z : τ (@comm_ring_carrier S),
                @comm_ring_add S z
                  (@comm_ring_hom_apply R S h
                    (@comm_ring_finite_dot R n0
                      (@finite_family_tail (@comm_ring_carrier R) n0 as0)
                      (@finite_family_tail (@comm_ring_carrier R) n0 fs0))))
              (@comm_ring_hom_apply R S h
                (@comm_ring_mul R
                  (@finite_family_head (@comm_ring_carrier R) n0 as0)
                  (@finite_family_head (@comm_ring_carrier R) n0 fs0)))
              (@comm_ring_mul S
                (@comm_ring_hom_apply R S h
                  (@finite_family_head (@comm_ring_carrier R) n0 as0))
                (@comm_ring_hom_apply R S h
                  (@finite_family_head (@comm_ring_carrier R) n0 fs0)))
              ((@comm_ring_hom_mul_law R S h)
                (@finite_family_head (@comm_ring_carrier R) n0 as0)
                (@finite_family_head (@comm_ring_carrier R) n0 fs0)))
            (@eq_ap
              (@comm_ring_carrier S)
              (@comm_ring_carrier S)
              (λ z : τ (@comm_ring_carrier S),
                @comm_ring_add S
                  (@comm_ring_mul S
                    (@comm_ring_hom_apply R S h
                      (@finite_family_head (@comm_ring_carrier R) n0 as0))
                    (@comm_ring_hom_apply R S h
                      (@finite_family_head (@comm_ring_carrier R) n0 fs0)))
                  z)
              (@comm_ring_hom_apply R S h
                (@comm_ring_finite_dot R n0
                  (@finite_family_tail (@comm_ring_carrier R) n0 as0)
                  (@finite_family_tail (@comm_ring_carrier R) n0 fs0)))
              (@comm_ring_finite_dot S n0
                (@finite_family_map
                  (@comm_ring_carrier R)
                  (@comm_ring_carrier S)
                  (@comm_ring_hom_function R S h)
                  n0
                  (@finite_family_tail (@comm_ring_carrier R) n0 as0))
                (@finite_family_map
                  (@comm_ring_carrier R)
                  (@comm_ring_carrier S)
                  (@comm_ring_hom_function R S h)
                  n0
                  (@finite_family_tail (@comm_ring_carrier R) n0 fs0)))
              (ih
                (@finite_family_tail (@comm_ring_carrier R) n0 as0)
                (@finite_family_tail (@comm_ring_carrier R) n0 fs0)))))
    n) coefficients generators;

// Chosen coefficient data exhibiting that the generators span the unit ideal.
symbol CommRingUnimodularPresentation
  [R : τ CommRing]
  (n : τ Nat_grpd)
  (generators : τ (@FiniteFamily (@comm_ring_carrier R) n))
  : Grpd
≔ `Σ_ coefficients :
      τ (@FiniteFamily (@comm_ring_carrier R) n),
    @= (@comm_ring_carrier R)
      (@comm_ring_finite_dot R n coefficients generators)
      (@comm_ring_one R);

symbol comm_ring_unimodular_intro
  [R : τ CommRing]
  [n : τ Nat_grpd]
  [generators : τ (@FiniteFamily (@comm_ring_carrier R) n)]
  (coefficients : τ (@FiniteFamily (@comm_ring_carrier R) n))
  (law : τ (@= (@comm_ring_carrier R)
      (@comm_ring_finite_dot R n coefficients generators)
      (@comm_ring_one R)))
  : τ (@CommRingUnimodularPresentation R n generators)
≔ @Struct_sigma
    (@FiniteFamily (@comm_ring_carrier R) n)
    (λ as0 : τ (@FiniteFamily (@comm_ring_carrier R) n),
      @= (@comm_ring_carrier R)
        (@comm_ring_finite_dot R n as0 generators)
        (@comm_ring_one R))
    coefficients
    law;

symbol comm_ring_unimodular_coefficients
  [R : τ CommRing]
  [n : τ Nat_grpd]
  [generators : τ (@FiniteFamily (@comm_ring_carrier R) n)]
  (u : τ (@CommRingUnimodularPresentation R n generators))
  : τ (@FiniteFamily (@comm_ring_carrier R) n)
≔ sigma_Fst u;

symbol comm_ring_unimodular_law
  [R : τ CommRing]
  [n : τ Nat_grpd]
  [generators : τ (@FiniteFamily (@comm_ring_carrier R) n)]
  (u : τ (@CommRingUnimodularPresentation R n generators))
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_finite_dot R n
        (@comm_ring_unimodular_coefficients R n generators u)
        generators)
      (@comm_ring_one R))
≔ sigma_Snd u;

// The retained coefficient presentation is set-valued, but not claimed a prop.
symbol comm_ring_unimodular_is_set
  [R : τ CommRing]
  (n : τ Nat_grpd)
  (generators : τ (@FiniteFamily (@comm_ring_carrier R) n))
  : τ (IsSetGrpd (@CommRingUnimodularPresentation R n generators))
≔ @is_trunc_sigma
    trunc_zero
    (@FiniteFamily (@comm_ring_carrier R) n)
    (λ coefficients : τ (@FiniteFamily (@comm_ring_carrier R) n),
      @= (@comm_ring_carrier R)
        (@comm_ring_finite_dot R n coefficients generators)
        (@comm_ring_one R))
    (@finite_family_is_set
      (@comm_ring_carrier R)
      (@comm_ring_carrier_is_set R)
      n)
    (λ coefficients : τ (@FiniteFamily (@comm_ring_carrier R) n),
      @prop_is_trunc_succ
        trunc_minus_one
        (@= (@comm_ring_carrier R)
          (@comm_ring_finite_dot R n coefficients generators)
          (@comm_ring_one R))
        ((@comm_ring_carrier_is_set R)
          (@comm_ring_finite_dot R n coefficients generators)
          (@comm_ring_one R)));

// Unimodular presentations are stable under arbitrary structured base change.
symbol comm_ring_unimodular_map
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  [n : τ Nat_grpd]
  [generators : τ (@FiniteFamily (@comm_ring_carrier R) n)]
  (u : τ (@CommRingUnimodularPresentation R n generators))
  : τ (@CommRingUnimodularPresentation
      S n
      (@finite_family_map
        (@comm_ring_carrier R)
        (@comm_ring_carrier S)
        (@comm_ring_hom_function R S h)
        n generators))
≔ @comm_ring_unimodular_intro
    S n
    (@finite_family_map
      (@comm_ring_carrier R)
      (@comm_ring_carrier S)
      (@comm_ring_hom_function R S h)
      n generators)
    (@finite_family_map
      (@comm_ring_carrier R)
      (@comm_ring_carrier S)
      (@comm_ring_hom_function R S h)
      n
      (@comm_ring_unimodular_coefficients R n generators u))
    (@eq_trans
      (@comm_ring_carrier S)
      (@comm_ring_finite_dot S n
        (@finite_family_map
          (@comm_ring_carrier R)
          (@comm_ring_carrier S)
          (@comm_ring_hom_function R S h)
          n
          (@comm_ring_unimodular_coefficients R n generators u))
        (@finite_family_map
          (@comm_ring_carrier R)
          (@comm_ring_carrier S)
          (@comm_ring_hom_function R S h)
          n generators))
      (@comm_ring_hom_apply R S h
        (@comm_ring_finite_dot R n
          (@comm_ring_unimodular_coefficients R n generators u)
          generators))
      (@comm_ring_one S)
      (@eq_sym
        (@comm_ring_carrier S)
        (@comm_ring_hom_apply R S h
          (@comm_ring_finite_dot R n
            (@comm_ring_unimodular_coefficients R n generators u)
            generators))
        (@comm_ring_finite_dot S n
          (@finite_family_map
            (@comm_ring_carrier R)
            (@comm_ring_carrier S)
            (@comm_ring_hom_function R S h)
            n
            (@comm_ring_unimodular_coefficients R n generators u))
          (@finite_family_map
            (@comm_ring_carrier R)
            (@comm_ring_carrier S)
            (@comm_ring_hom_function R S h)
            n generators))
        (@comm_ring_hom_finite_dot_path
          R S h n
          (@comm_ring_unimodular_coefficients R n generators u)
          generators))
      (@eq_trans
        (@comm_ring_carrier S)
        (@comm_ring_hom_apply R S h
          (@comm_ring_finite_dot R n
            (@comm_ring_unimodular_coefficients R n generators u)
            generators))
        (@comm_ring_hom_apply R S h (@comm_ring_one R))
        (@comm_ring_one S)
        (@eq_ap
          (@comm_ring_carrier R)
          (@comm_ring_carrier S)
          (@comm_ring_hom_function R S h)
          (@comm_ring_finite_dot R n
            (@comm_ring_unimodular_coefficients R n generators u)
            generators)
          (@comm_ring_one R)
          (@comm_ring_unimodular_law R n generators u))
        (@comm_ring_hom_one_law R S h)));

// Algebraic input presentation for a future finite basic-open Zariski cover.
symbol CommRingZariskiCoverPresentation
  (R : τ CommRing)
  : Grpd
≔ `Σ_ n : τ Nat_grpd,
   `Σ_ generators :
      τ (@FiniteFamily (@comm_ring_carrier R) n),
      @CommRingUnimodularPresentation R n generators;

symbol comm_ring_zariski_cover_is_set
  (R : τ CommRing)
  : τ (IsSetGrpd (@CommRingZariskiCoverPresentation R))
≔ @is_trunc_sigma
    trunc_zero
    Nat_grpd
    (λ n : τ Nat_grpd,
      `Σ_ generators :
        τ (@FiniteFamily (@comm_ring_carrier R) n),
        @CommRingUnimodularPresentation R n generators)
    nat_is_set
    (λ n : τ Nat_grpd,
      @is_trunc_sigma
        trunc_zero
        (@FiniteFamily (@comm_ring_carrier R) n)
        (λ generators : τ (@FiniteFamily (@comm_ring_carrier R) n),
          @CommRingUnimodularPresentation R n generators)
        (@finite_family_is_set
          (@comm_ring_carrier R)
          (@comm_ring_carrier_is_set R)
          n)
        (λ generators : τ (@FiniteFamily (@comm_ring_carrier R) n),
          @comm_ring_unimodular_is_set R n generators));

symbol comm_ring_zariski_cover_intro
  [R : τ CommRing]
  (n : τ Nat_grpd)
  (generators : τ (@FiniteFamily (@comm_ring_carrier R) n))
  (unimodular : τ (@CommRingUnimodularPresentation R n generators))
  : τ (@CommRingZariskiCoverPresentation R)
≔ @Struct_sigma
    Nat_grpd
    (λ n0 : τ Nat_grpd,
      `Σ_ generators0 :
        τ (@FiniteFamily (@comm_ring_carrier R) n0),
        @CommRingUnimodularPresentation R n0 generators0)
    n
    (@Struct_sigma
      (@FiniteFamily (@comm_ring_carrier R) n)
      (λ generators0 : τ (@FiniteFamily (@comm_ring_carrier R) n),
        @CommRingUnimodularPresentation R n generators0)
      generators
      unimodular);

symbol comm_ring_zariski_cover_length
  [R : τ CommRing]
  (cover : τ (@CommRingZariskiCoverPresentation R))
  : τ Nat_grpd
≔ sigma_Fst cover;

symbol comm_ring_zariski_cover_generators
  [R : τ CommRing]
  (cover : τ (@CommRingZariskiCoverPresentation R))
  : τ (@FiniteFamily
      (@comm_ring_carrier R)
      (@comm_ring_zariski_cover_length R cover))
≔ sigma_Fst (sigma_Snd cover);

symbol comm_ring_zariski_cover_unimodular
  [R : τ CommRing]
  (cover : τ (@CommRingZariskiCoverPresentation R))
  : τ (@CommRingUnimodularPresentation
      R
      (@comm_ring_zariski_cover_length R cover)
      (@comm_ring_zariski_cover_generators R cover))
≔ sigma_Snd (sigma_Snd cover);

// Base change acts on generators and retained coefficients pointwise.
symbol comm_ring_zariski_cover_map
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (cover : τ (@CommRingZariskiCoverPresentation R))
  : τ (@CommRingZariskiCoverPresentation S)
≔ @comm_ring_zariski_cover_intro
    S
    (@comm_ring_zariski_cover_length R cover)
    (@finite_family_map
      (@comm_ring_carrier R)
      (@comm_ring_carrier S)
      (@comm_ring_hom_function R S h)
      (@comm_ring_zariski_cover_length R cover)
      (@comm_ring_zariski_cover_generators R cover))
    (@comm_ring_unimodular_map
      R S h
      (@comm_ring_zariski_cover_length R cover)
      (@comm_ring_zariski_cover_generators R cover)
      (@comm_ring_zariski_cover_unimodular R cover));

// The singleton family [1] is the canonical nonempty Zariski presentation.
symbol comm_ring_unit_unimodular
  (R : τ CommRing)
  : τ (@CommRingUnimodularPresentation
      R
      (succ zero)
      (@finite_family_singleton
        (@comm_ring_carrier R)
        (@comm_ring_one R)))
≔ @comm_ring_unimodular_intro
    R
    (succ zero)
    (@finite_family_singleton
      (@comm_ring_carrier R)
      (@comm_ring_one R))
    (@finite_family_singleton
      (@comm_ring_carrier R)
      (@comm_ring_one R))
    (@eq_trans
      (@comm_ring_carrier R)
      (@comm_ring_add R
        (@comm_ring_mul R (@comm_ring_one R) (@comm_ring_one R))
        (@comm_ring_zero R))
      (@comm_ring_add R (@comm_ring_one R) (@comm_ring_zero R))
      (@comm_ring_one R)
      (@eq_ap
        (@comm_ring_carrier R)
        (@comm_ring_carrier R)
        (λ z : τ (@comm_ring_carrier R),
          @comm_ring_add R z (@comm_ring_zero R))
        (@comm_ring_mul R (@comm_ring_one R) (@comm_ring_one R))
        (@comm_ring_one R)
        ((@comm_ring_mul_one_law R) (@comm_ring_one R)))
      ((@comm_ring_add_zero_law R) (@comm_ring_one R)));

symbol comm_ring_unit_zariski_cover
  (R : τ CommRing)
  : τ (@CommRingZariskiCoverPresentation R)
≔ @comm_ring_zariski_cover_intro
    R
    (succ zero)
    (@finite_family_singleton
      (@comm_ring_carrier R)
      (@comm_ring_one R))
    (@comm_ring_unit_unimodular R);

// Binary helper matching the familiar a*f+b*g=1 cover presentation.
symbol comm_ring_binary_unimodular
  [R : τ CommRing]
  (f g a b : τ (@comm_ring_carrier R))
  (law : τ (@= (@comm_ring_carrier R)
      (@comm_ring_add R
        (@comm_ring_mul R a f)
        (@comm_ring_mul R b g))
      (@comm_ring_one R)))
  : τ (@CommRingUnimodularPresentation
      R
      (succ (succ zero))
      (@finite_family_pair (@comm_ring_carrier R) f g))
≔ @comm_ring_unimodular_intro
    R
    (succ (succ zero))
    (@finite_family_pair (@comm_ring_carrier R) f g)
    (@finite_family_pair (@comm_ring_carrier R) a b)
    (@eq_trans
      (@comm_ring_carrier R)
      (@comm_ring_add R
        (@comm_ring_mul R a f)
        (@comm_ring_add R
          (@comm_ring_mul R b g)
          (@comm_ring_zero R)))
      (@comm_ring_add R
        (@comm_ring_mul R a f)
        (@comm_ring_mul R b g))
      (@comm_ring_one R)
      (@eq_ap
        (@comm_ring_carrier R)
        (@comm_ring_carrier R)
        (λ z : τ (@comm_ring_carrier R),
          @comm_ring_add R (@comm_ring_mul R a f) z)
        (@comm_ring_add R
          (@comm_ring_mul R b g)
          (@comm_ring_zero R))
        (@comm_ring_mul R b g)
        ((@comm_ring_add_zero_law R) (@comm_ring_mul R b g)))
      law);

symbol comm_ring_binary_zariski_cover
  [R : τ CommRing]
  (f g a b : τ (@comm_ring_carrier R))
  (law : τ (@= (@comm_ring_carrier R)
      (@comm_ring_add R
        (@comm_ring_mul R a f)
        (@comm_ring_mul R b g))
      (@comm_ring_one R)))
  : τ (@CommRingZariskiCoverPresentation R)
≔ @comm_ring_zariski_cover_intro
    R
    (succ (succ zero))
    (@finite_family_pair (@comm_ring_carrier R) f g)
    (@comm_ring_binary_unimodular R f g a b law);
