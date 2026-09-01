/*
  Set-valued path induction for 0-truncation.

  Equality in a set is a proposition and therefore, in particular, a set.
  The existing restricted `trunc_ind_ambient` can consequently promote a path
  law from point constructors to arbitrary 0-truncated points. This module
  packages exactly the unary, curried-binary, and curried-ternary instances
  consumed by Freyd preadditivity; it adds no eliminator or runtime rule.
*/

require open emdash.emdash3_2_truncation_reflector;

// Path data on every point constructor of a 0-truncation.
symbol TruncZeroSetPointPaths
  [A S : Grpd]
  (h k : τ (@Function_grpd (@Trunc_grpd trunc_zero A) S))
  : Grpd
≔ @Pi_grpd A
    (λ a : τ A,
      @= S
        (h (@trunc_intro trunc_zero A a))
        (k (@trunc_intro trunc_zero A a)));

// Unary set-valued path induction through the existing restricted eliminator.
symbol trunc_zero_set_path_ind
  [A S : Grpd]
  (S_set : τ (IsSetGrpd S))
  [h k : τ (@Function_grpd (@Trunc_grpd trunc_zero A) S)]
  (p : τ (@TruncZeroSetPointPaths A S h k))
  (z : τ (@Trunc_grpd trunc_zero A))
  : τ (@= S (h z) (k z))
≔ @trunc_ind_ambient
    trunc_zero A
    (λ z : τ (@Trunc_grpd trunc_zero A),
      @= S (h z) (k z))
    (λ z : τ (@Trunc_grpd trunc_zero A),
      @is_trunc_path_same_level
        trunc_zero S S_set (h z) (k z))
    p z;

// Point-constructor data for curried binary maps out of 0-truncations.
symbol TruncZeroSetBinaryPointPaths
  [A B S : Grpd]
  (h k : τ (@Function_grpd
      (@Trunc_grpd trunc_zero A)
      (@Function_grpd (@Trunc_grpd trunc_zero B) S)))
  : Grpd
≔ @Pi_grpd A
    (λ a : τ A,
      @Pi_grpd B
        (λ b : τ B,
          @= S
            (h (@trunc_intro trunc_zero A a)
              (@trunc_intro trunc_zero B b))
            (k (@trunc_intro trunc_zero A a)
              (@trunc_intro trunc_zero B b))));

// Binary set-valued path induction by two unary restricted eliminations.
symbol trunc_zero_set_binary_path_ind
  [A B S : Grpd]
  (S_set : τ (IsSetGrpd S))
  [h k : τ (@Function_grpd
      (@Trunc_grpd trunc_zero A)
      (@Function_grpd (@Trunc_grpd trunc_zero B) S))]
  (p : τ (@TruncZeroSetBinaryPointPaths A B S h k))
  (z : τ (@Trunc_grpd trunc_zero A))
  (w : τ (@Trunc_grpd trunc_zero B))
  : τ (@= S (h z w) (k z w))
≔ @trunc_zero_set_path_ind
    A S S_set
    (λ z : τ (@Trunc_grpd trunc_zero A), h z w)
    (λ z : τ (@Trunc_grpd trunc_zero A), k z w)
    (λ a : τ A,
      @trunc_zero_set_path_ind
        B S S_set
        (h (@trunc_intro trunc_zero A a))
        (k (@trunc_intro trunc_zero A a))
        (p a)
        w)
    z;

// Point-constructor data for curried ternary maps out of 0-truncations.
symbol TruncZeroSetTernaryPointPaths
  [A B C S : Grpd]
  (h k : τ (@Function_grpd
      (@Trunc_grpd trunc_zero A)
      (@Function_grpd
        (@Trunc_grpd trunc_zero B)
        (@Function_grpd (@Trunc_grpd trunc_zero C) S))))
  : Grpd
≔ @Pi_grpd A
    (λ a : τ A,
      @Pi_grpd B
        (λ b : τ B,
          @Pi_grpd C
            (λ c : τ C,
              @= S
                (h (@trunc_intro trunc_zero A a)
                  (@trunc_intro trunc_zero B b)
                  (@trunc_intro trunc_zero C c))
                (k (@trunc_intro trunc_zero A a)
                  (@trunc_intro trunc_zero B b)
                  (@trunc_intro trunc_zero C c)))));

// Ternary set-valued path induction by unary then binary elimination.
symbol trunc_zero_set_ternary_path_ind
  [A B C S : Grpd]
  (S_set : τ (IsSetGrpd S))
  [h k : τ (@Function_grpd
      (@Trunc_grpd trunc_zero A)
      (@Function_grpd
        (@Trunc_grpd trunc_zero B)
        (@Function_grpd (@Trunc_grpd trunc_zero C) S)))]
  (p : τ (@TruncZeroSetTernaryPointPaths A B C S h k))
  (x : τ (@Trunc_grpd trunc_zero A))
  (y : τ (@Trunc_grpd trunc_zero B))
  (z : τ (@Trunc_grpd trunc_zero C))
  : τ (@= S (h x y z) (k x y z))
≔ @trunc_zero_set_path_ind
    A S S_set
    (λ x : τ (@Trunc_grpd trunc_zero A), h x y z)
    (λ x : τ (@Trunc_grpd trunc_zero A), k x y z)
    (λ a : τ A,
      @trunc_zero_set_binary_path_ind
        B C S S_set
        (h (@trunc_intro trunc_zero A a))
        (k (@trunc_intro trunc_zero A a))
        (p a)
        y z)
    x;
