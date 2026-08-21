/*
  Intrinsic all-dimensional ordinal dependent-simplex source recursion.

  A nonzero intrinsic flag code is folded into one join-lift stage containing
  a target code, two whole maps, and a transformation. The one-flag clause is
  the generic identity-join comparison; every later flag applies
  pathout_transf_lift. Given the old source s, the successor code steps at
  F[s] and the successor object is (G[s],epsilon[s]). The zero-code clause
  evaluates the primitive join cross at the reflexive outgoing path.

  Nat recursion therefore constructs canonical sources at variable dimension;
  arbitrary-target observation and nonempty faces reuse the existing mapped
  decoder and FaceCode action. This curated indexed recursion adds no second
  simplex semantics, endpoint normalization, broad eta, or proof-time unifier.
*/

require open emdash.emdash3_2_dependent_simplex_ordinal_dimension4;

// A nonzero old flag code determines a target code of the same dimension and
// two whole maps related by one transformation.
symbol OrdinalJoinLiftStage
  (A : Cat)
  (n : τ Nat_grpd)
  (K : Cat)
  : Grpd
≔ `Σ_ B : τ (Obj Cat_cat),
   `Σ_ d : τ (@RawDependentSimplexCode
      (@ordinal_join_target_cat A) n B),
   `Σ_ F : τ (Functor K B),
   `Σ_ G : τ (Functor K B),
     @Transf K B F G;

symbol ordinal_join_lift_stage
  [A : Cat]
  [n : τ Nat_grpd]
  [K B : Cat]
  (d : τ (@RawDependentSimplexCode
      (@ordinal_join_target_cat A) n B))
  (F G : τ (Functor K B))
  (epsilon : τ (Transf F G))
  : τ (@OrdinalJoinLiftStage A n K)
≔ @Struct_sigma
    (Obj Cat_cat)
    (λ B0 : τ (Obj Cat_cat),
      @Σ_ (@RawDependentSimplexCode
          (@ordinal_join_target_cat A) n B0)
        (λ _ : τ (@RawDependentSimplexCode
            (@ordinal_join_target_cat A) n B0),
          @Σ_ (Functor K B0)
            (λ F0 : τ (Functor K B0),
              @Σ_ (Functor K B0)
                (λ G0 : τ (Functor K B0), @Transf K B0 F0 G0))))
    B
    (@Struct_sigma
      (@RawDependentSimplexCode (@ordinal_join_target_cat A) n B)
      (λ _ : τ (@RawDependentSimplexCode
          (@ordinal_join_target_cat A) n B),
        @Σ_ (Functor K B)
          (λ F0 : τ (Functor K B),
            @Σ_ (Functor K B)
              (λ G0 : τ (Functor K B), @Transf K B F0 G0)))
      d
      (@Struct_sigma
        (Functor K B)
        (λ F0 : τ (Functor K B),
          @Σ_ (Functor K B)
            (λ G0 : τ (Functor K B), @Transf K B F0 G0))
        F
        (@Struct_sigma
          (Functor K B)
          (λ G0 : τ (Functor K B), @Transf K B F G0)
          G epsilon)));

symbol ordinal_join_lift_stage_target_cat
  [A : Cat]
  [n : τ Nat_grpd]
  [K : Cat]
  (S : τ (@OrdinalJoinLiftStage A n K))
  : Cat
≔ sigma_Fst S;

symbol ordinal_join_lift_stage_target_raw
  [A : Cat]
  [n : τ Nat_grpd]
  [K : Cat]
  (S : τ (@OrdinalJoinLiftStage A n K))
  : τ (@RawDependentSimplexCode
      (@ordinal_join_target_cat A) n
      (@ordinal_join_lift_stage_target_cat A n K S))
≔ sigma_Fst (sigma_Snd S);

symbol ordinal_join_lift_stage_left
  [A : Cat]
  [n : τ Nat_grpd]
  [K : Cat]
  (S : τ (@OrdinalJoinLiftStage A n K))
  : τ (Functor K (@ordinal_join_lift_stage_target_cat A n K S))
≔ sigma_Fst (sigma_Snd (sigma_Snd S));

symbol ordinal_join_lift_stage_right
  [A : Cat]
  [n : τ Nat_grpd]
  [K : Cat]
  (S : τ (@OrdinalJoinLiftStage A n K))
  : τ (Functor K (@ordinal_join_lift_stage_target_cat A n K S))
≔ sigma_Fst (sigma_Snd (sigma_Snd (sigma_Snd S)));

symbol ordinal_join_lift_stage_transf
  [A : Cat]
  [n : τ Nat_grpd]
  [K : Cat]
  (S : τ (@OrdinalJoinLiftStage A n K))
  : τ (Transf
      (@ordinal_join_lift_stage_left A n K S)
      (@ordinal_join_lift_stage_right A n K S))
≔ sigma_Snd (sigma_Snd (sigma_Snd (sigma_Snd S)));

symbol ordinal_join_lift_stage_component
  [A : Cat]
  [n : τ Nat_grpd]
  [K : Cat]
  (S : τ (@OrdinalJoinLiftStage A (succ n) K))
  (s : τ (Obj K))
  : τ (Hom
      (@ordinal_join_lift_stage_target_cat A (succ n) K S)
      (@fapp0
        K (@ordinal_join_lift_stage_target_cat A (succ n) K S)
        (@ordinal_join_lift_stage_left A (succ n) K S) s)
      (@fapp0
        K (@ordinal_join_lift_stage_target_cat A (succ n) K S)
        (@ordinal_join_lift_stage_right A (succ n) K S) s))
≔ @tapp0_fapp0
    K (@ordinal_join_lift_stage_target_cat A (succ n) K S)
    (@ordinal_join_lift_stage_left A (succ n) K S)
    (@ordinal_join_lift_stage_right A (succ n) K S)
    s (@ordinal_join_lift_stage_transf A (succ n) K S);

// One-flag stage: the generic shaped comparison for A * 1.
symbol ordinal_join_lift_stage_one
  (A : Cat)
  (x0 : τ (Obj A))
  : τ (@OrdinalJoinLiftStage
      A (succ zero) (@PathOut_cat A x0))
≔ @ordinal_join_lift_stage
    A (succ zero) (@PathOut_cat A x0)
    (@PathOut_cat
      (@ordinal_join_target_cat A)
      (@ordinal_join_target_base A x0))
    (@raw_dependent_simplex_step
      (@ordinal_join_target_cat A) zero (@ordinal_join_target_cat A)
      (@raw_dependent_simplex_zero (@ordinal_join_target_cat A))
      (@ordinal_join_target_base A x0))
    (@ordinal_join_observed_pathout A x0)
    (@ordinal_join_primitive_pathout A x0)
    (@ordinal_join_pathout_transf A x0);

// Structural stage successor: retain the target code and lift epsilon at x.
symbol ordinal_join_lift_stage_step
  [A : Cat]
  [n : τ Nat_grpd]
  [K : Cat]
  (S : τ (@OrdinalJoinLiftStage A (succ n) K))
  (x : τ (Obj K))
  : τ (@OrdinalJoinLiftStage
      A (succ (succ n)) (@PathOut_cat K x))
≔ @ordinal_join_lift_stage
    A (succ (succ n)) (@PathOut_cat K x)
    (@PathOut_cat
      (@ordinal_join_lift_stage_target_cat A (succ n) K S)
      (@fapp0
        K (@ordinal_join_lift_stage_target_cat A (succ n) K S)
        (@ordinal_join_lift_stage_left A (succ n) K S) x))
    (@raw_dependent_simplex_step
      (@ordinal_join_target_cat A) (succ n)
      (@ordinal_join_lift_stage_target_cat A (succ n) K S)
      (@ordinal_join_lift_stage_target_raw A (succ n) K S)
      (@fapp0
        K (@ordinal_join_lift_stage_target_cat A (succ n) K S)
        (@ordinal_join_lift_stage_left A (succ n) K S) x))
    (@pathout_map_func
      K (@ordinal_join_lift_stage_target_cat A (succ n) K S)
      (@ordinal_join_lift_stage_left A (succ n) K S) x)
    (@pathout_transf_target_func
      K (@ordinal_join_lift_stage_target_cat A (succ n) K S)
      (@ordinal_join_lift_stage_left A (succ n) K S)
      (@ordinal_join_lift_stage_right A (succ n) K S)
      (@ordinal_join_lift_stage_transf A (succ n) K S) x)
    (@pathout_transf_lift
      K (@ordinal_join_lift_stage_target_cat A (succ n) K S)
      (@ordinal_join_lift_stage_left A (succ n) K S)
      (@ordinal_join_lift_stage_right A (succ n) K S)
      (@ordinal_join_lift_stage_transf A (succ n) K S) x);

// Recursion over an existing nonzero intrinsic code.
injective symbol raw_ordinal_join_lift_stage
  [A : Cat]
  [n : τ Nat_grpd]
  [K : Cat]
  (c : τ (@RawDependentSimplexCode A (succ n) K))
  : τ (@OrdinalJoinLiftStage A (succ n) K);

rule @raw_ordinal_join_lift_stage
      _ zero _
      (@raw_dependent_simplex_step
        $A zero _ (@raw_dependent_simplex_zero _) $x0)
  ↪ @ordinal_join_lift_stage_one $A $x0
with @raw_ordinal_join_lift_stage
      _ (succ $n) _
      (@raw_dependent_simplex_step $A (succ $n) $K $c $x)
  ↪ @ordinal_join_lift_stage_step
      $A $n $K
      (@raw_ordinal_join_lift_stage $A $n $K $c)
      $x;

symbol ordinal_join_lift_stage_from_code
  [A : Cat]
  [n : τ Nat_grpd]
  (c : τ (@DependentSimplexCode A (succ n)))
  : τ (@OrdinalJoinLiftStage
      A (succ n) (@dependent_simplex_code_decode_cat A (succ n) c))
≔ @raw_ordinal_join_lift_stage
    A n (@dependent_simplex_code_decode_cat A (succ n) c)
    (@dependent_simplex_code_raw A (succ n) c);

// Reuse the existing code-plus-object observation package.
symbol ordinal_dependent_simplex_source_in_code
  [A : Cat]
  [n : τ Nat_grpd]
  (S : τ (@DependentSimplexObservation A n))
  : τ (@DependentSimplexCode A n)
≔ sigma_Fst S;

symbol ordinal_dependent_simplex_source_in_object
  [A : Cat]
  [n : τ Nat_grpd]
  (S : τ (@DependentSimplexObservation A n))
  : τ (Obj (@dependent_simplex_code_decode_cat A n
      (@ordinal_dependent_simplex_source_in_code A n S)))
≔ sigma_Snd S;

// Public target-code view of a nonzero join-lift stage.
symbol ordinal_join_lift_stage_target_code
  [A : Cat]
  [n : τ Nat_grpd]
  [K : Cat]
  (S : τ (@OrdinalJoinLiftStage A (succ n) K))
  : τ (@DependentSimplexCode (@ordinal_join_target_cat A) (succ n))
≔ @Struct_sigma
    (Obj Cat_cat)
    (λ B : τ (Obj Cat_cat),
      @RawDependentSimplexCode (@ordinal_join_target_cat A) (succ n) B)
    (@ordinal_join_lift_stage_target_cat A (succ n) K S)
    (@ordinal_join_lift_stage_target_raw A (succ n) K S);

// Zero-code successor: evaluate the primitive join cross at the reflexive
// outgoing path of the supplied old point.
symbol ordinal_join_source_zero_step
  (A : Cat)
  (x0 : τ (Obj A))
  : τ (@DependentSimplexObservation
      (@ordinal_join_target_cat A) (succ zero))
≔ @dependent_simplex_observation
    (@ordinal_join_target_cat A) (succ zero)
    (@dependent_simplex_code1
      (@ordinal_join_target_cat A)
      (@ordinal_join_target_base A x0))
    (@fapp0
      (@PathOut_cat A x0)
      (@PathOut_cat
        (@ordinal_join_target_cat A)
        (@ordinal_join_target_base A x0))
      (@ordinal_join_primitive_pathout A x0)
      (@pathout_obj A x0 x0 (@id A x0)));

// Nonzero successor: step the target code at F[s] and use epsilon[s] as the
// new outgoing arrow.
symbol ordinal_join_source_from_stage
  [A : Cat]
  [n : τ Nat_grpd]
  [K : Cat]
  (S : τ (@OrdinalJoinLiftStage A (succ n) K))
  (s : τ (Obj K))
  : τ (@DependentSimplexObservation
      (@ordinal_join_target_cat A) (succ (succ n)))
≔ @dependent_simplex_observation
    (@ordinal_join_target_cat A) (succ (succ n))
    (@dependent_simplex_code_step
      (@ordinal_join_target_cat A) (succ n)
      (@ordinal_join_lift_stage_target_code A n K S)
      (@fapp0
        K (@ordinal_join_lift_stage_target_cat A (succ n) K S)
        (@ordinal_join_lift_stage_left A (succ n) K S) s))
    (@pathout_obj
      (@ordinal_join_lift_stage_target_cat A (succ n) K S)
      (@fapp0
        K (@ordinal_join_lift_stage_target_cat A (succ n) K S)
        (@ordinal_join_lift_stage_left A (succ n) K S) s)
      (@fapp0
        K (@ordinal_join_lift_stage_target_cat A (succ n) K S)
        (@ordinal_join_lift_stage_right A (succ n) K S) s)
      (@ordinal_join_lift_stage_component A n K S s));

// Raw structural successor, with one zero-code clause and one nonzero clause.
injective symbol raw_ordinal_dependent_simplex_source_successor
  [A : Cat]
  [n : τ Nat_grpd]
  [K : Cat]
  (c : τ (@RawDependentSimplexCode A n K))
  (s : τ (Obj K))
  : τ (@DependentSimplexObservation
      (@ordinal_join_target_cat A) (succ n));

rule @raw_ordinal_dependent_simplex_source_successor
      _ zero _ (@raw_dependent_simplex_zero $A) $x0
  ↪ @ordinal_join_source_zero_step $A $x0
with @raw_ordinal_dependent_simplex_source_successor
      _ (succ $n) _
      (@raw_dependent_simplex_step $A $n $K $c $x) $s
  ↪ @ordinal_join_source_from_stage
      $A $n (@PathOut_cat $K $x)
      (@raw_ordinal_join_lift_stage
        $A $n (@PathOut_cat $K $x)
        (@raw_dependent_simplex_step $A $n $K $c $x))
      $s;

// Ordinal specialization: Delta[n+1] computes to Delta[n] * 1.
symbol OrdinalDependentSimplexSource
  (n : τ Nat_grpd)
  : Grpd
≔ @DependentSimplexObservation (@DirectedSimplex_cat n) n;

symbol ordinal_dependent_simplex_source_successor
  [n : τ Nat_grpd]
  (S : τ (@OrdinalDependentSimplexSource n))
  : τ (@OrdinalDependentSimplexSource (succ n))
≔ @raw_ordinal_dependent_simplex_source_successor
    (@DirectedSimplex_cat n) n
    (@dependent_simplex_code_decode_cat
      (@DirectedSimplex_cat n) n
      (@ordinal_dependent_simplex_source_in_code
        (@DirectedSimplex_cat n) n S))
    (@dependent_simplex_code_raw
      (@DirectedSimplex_cat n) n
      (@ordinal_dependent_simplex_source_in_code
        (@DirectedSimplex_cat n) n S))
    (@ordinal_dependent_simplex_source_in_object
      (@DirectedSimplex_cat n) n S);

symbol ordinal_dependent_simplex_source_zero
  : τ (@OrdinalDependentSimplexSource zero)
≔ @dependent_simplex_observation
    (@DirectedSimplex_cat zero) zero
    (@dependent_simplex_code_zero (@DirectedSimplex_cat zero))
    Terminal_obj;

// Genuine Nat-indexed canonical source.
symbol ordinal_dependent_simplex_source
  (n : τ Nat_grpd)
  : τ (@OrdinalDependentSimplexSource n)
≔ @nat_elim
    (λ n0 : τ Nat_grpd, @OrdinalDependentSimplexSource n0)
    ordinal_dependent_simplex_source_zero
    (λ n0 : τ Nat_grpd,
      λ previous : τ (@OrdinalDependentSimplexSource n0),
        @ordinal_dependent_simplex_source_successor n0 previous)
    n;

symbol ordinal_dependent_simplex_source_code
  (n : τ Nat_grpd)
  : τ (@DependentSimplexCode (@DirectedSimplex_cat n) n)
≔ @ordinal_dependent_simplex_source_in_code
    (@DirectedSimplex_cat n) n
    (@ordinal_dependent_simplex_source n);

symbol ordinal_dependent_simplex_source_object
  (n : τ Nat_grpd)
  : τ (Obj (@dependent_simplex_code_decode_cat
      (@DirectedSimplex_cat n) n
      (@ordinal_dependent_simplex_source_code n)))
≔ @ordinal_dependent_simplex_source_in_object
    (@DirectedSimplex_cat n) n
    (@ordinal_dependent_simplex_source n);

// Generic observation under H is already the existing mapped decoder.
symbol ordinal_dependent_simplex_observation
  [n : τ Nat_grpd]
  [C : Cat]
  (H : τ (Functor (@DirectedSimplex_cat n) C))
  : τ (Obj (@dependent_simplex_code_decode_cat
      C n
      (@dependent_simplex_code_map_target
        (@DirectedSimplex_cat n) C H n
        (@ordinal_dependent_simplex_source_code n))))
≔ @fapp0
    (@dependent_simplex_code_decode_cat
      (@DirectedSimplex_cat n) n
      (@ordinal_dependent_simplex_source_code n))
    (@dependent_simplex_code_decode_cat
      C n
      (@dependent_simplex_code_map_target
        (@DirectedSimplex_cat n) C H n
        (@ordinal_dependent_simplex_source_code n)))
    (@dependent_simplex_code_map_func
      (@DirectedSimplex_cat n) C H n
      (@ordinal_dependent_simplex_source_code n))
    (@ordinal_dependent_simplex_source_object n);

// Generic nonempty face of the canonical observation.
symbol ordinal_dependent_simplex_face
  [p n : τ Nat_grpd]
  [C : Cat]
  (H : τ (Functor (@DirectedSimplex_cat n) C))
  (alpha : τ (@DependentSimplexFaceRef p n))
  : τ (Obj (@dependent_simplex_code_decode_cat
      C p
      (@dependent_simplex_face_target
        C p n
        (@dependent_simplex_code_map_target
          (@DirectedSimplex_cat n) C H n
          (@ordinal_dependent_simplex_source_code n))
        alpha)))
≔ @fapp0
    (@dependent_simplex_code_decode_cat
      C n
      (@dependent_simplex_code_map_target
        (@DirectedSimplex_cat n) C H n
        (@ordinal_dependent_simplex_source_code n)))
    (@dependent_simplex_code_decode_cat
      C p
      (@dependent_simplex_face_target
        C p n
        (@dependent_simplex_code_map_target
          (@DirectedSimplex_cat n) C H n
          (@ordinal_dependent_simplex_source_code n))
        alpha))
    (@dependent_simplex_face_func
      C p n
      (@dependent_simplex_code_map_target
        (@DirectedSimplex_cat n) C H n
        (@ordinal_dependent_simplex_source_code n))
      alpha)
    (@ordinal_dependent_simplex_observation n C H);

// The canonical nonzero source code retains the whole join-lift stage and its
// next hom action.
symbol ordinal_dependent_simplex_lift_stage
  [n : τ Nat_grpd]
  : τ (@OrdinalJoinLiftStage
      (@DirectedSimplex_cat (succ n))
      (succ n)
      (@dependent_simplex_code_decode_cat
        (@DirectedSimplex_cat (succ n)) (succ n)
        (@ordinal_dependent_simplex_source_code (succ n))))
≔ @ordinal_join_lift_stage_from_code
    (@DirectedSimplex_cat (succ n)) n
    (@ordinal_dependent_simplex_source_code (succ n));

symbol ordinal_dependent_simplex_successor_cell
  [n : τ Nat_grpd]
  : τ (Hom
      (@ordinal_join_lift_stage_target_cat
        (@DirectedSimplex_cat (succ n)) (succ n)
        (@dependent_simplex_code_decode_cat
          (@DirectedSimplex_cat (succ n)) (succ n)
          (@ordinal_dependent_simplex_source_code (succ n)))
        (@ordinal_dependent_simplex_lift_stage n))
      (@fapp0
        (@dependent_simplex_code_decode_cat
          (@DirectedSimplex_cat (succ n)) (succ n)
          (@ordinal_dependent_simplex_source_code (succ n)))
        (@ordinal_join_lift_stage_target_cat
          (@DirectedSimplex_cat (succ n)) (succ n)
          (@dependent_simplex_code_decode_cat
            (@DirectedSimplex_cat (succ n)) (succ n)
            (@ordinal_dependent_simplex_source_code (succ n)))
          (@ordinal_dependent_simplex_lift_stage n))
        (@ordinal_join_lift_stage_left
          (@DirectedSimplex_cat (succ n)) (succ n)
          (@dependent_simplex_code_decode_cat
            (@DirectedSimplex_cat (succ n)) (succ n)
            (@ordinal_dependent_simplex_source_code (succ n)))
          (@ordinal_dependent_simplex_lift_stage n))
        (@ordinal_dependent_simplex_source_object (succ n)))
      (@fapp0
        (@dependent_simplex_code_decode_cat
          (@DirectedSimplex_cat (succ n)) (succ n)
          (@ordinal_dependent_simplex_source_code (succ n)))
        (@ordinal_join_lift_stage_target_cat
          (@DirectedSimplex_cat (succ n)) (succ n)
          (@dependent_simplex_code_decode_cat
            (@DirectedSimplex_cat (succ n)) (succ n)
            (@ordinal_dependent_simplex_source_code (succ n)))
          (@ordinal_dependent_simplex_lift_stage n))
        (@ordinal_join_lift_stage_right
          (@DirectedSimplex_cat (succ n)) (succ n)
          (@dependent_simplex_code_decode_cat
            (@DirectedSimplex_cat (succ n)) (succ n)
            (@ordinal_dependent_simplex_source_code (succ n)))
          (@ordinal_dependent_simplex_lift_stage n))
        (@ordinal_dependent_simplex_source_object (succ n))))
≔ @ordinal_join_lift_stage_component
    (@DirectedSimplex_cat (succ n)) n
    (@dependent_simplex_code_decode_cat
      (@DirectedSimplex_cat (succ n)) (succ n)
      (@ordinal_dependent_simplex_source_code (succ n)))
    (@ordinal_dependent_simplex_lift_stage n)
    (@ordinal_dependent_simplex_source_object (succ n));

symbol ordinal_dependent_simplex_lift_next_action
  [n : τ Nat_grpd]
  (u v : τ (Obj (@dependent_simplex_code_decode_cat
      (@DirectedSimplex_cat (succ n)) (succ n)
      (@ordinal_dependent_simplex_source_code (succ n)))))
  : τ (Functor
      (Hom_cat
        (@dependent_simplex_code_decode_cat
          (@DirectedSimplex_cat (succ n)) (succ n)
          (@ordinal_dependent_simplex_source_code (succ n)))
        u v)
      (Hom_cat
        (@ordinal_join_lift_stage_target_cat
          (@DirectedSimplex_cat (succ n)) (succ n)
          (@dependent_simplex_code_decode_cat
            (@DirectedSimplex_cat (succ n)) (succ n)
            (@ordinal_dependent_simplex_source_code (succ n)))
          (@ordinal_dependent_simplex_lift_stage n))
        (@fapp0
          (@dependent_simplex_code_decode_cat
            (@DirectedSimplex_cat (succ n)) (succ n)
            (@ordinal_dependent_simplex_source_code (succ n)))
          (@ordinal_join_lift_stage_target_cat
            (@DirectedSimplex_cat (succ n)) (succ n)
            (@dependent_simplex_code_decode_cat
              (@DirectedSimplex_cat (succ n)) (succ n)
              (@ordinal_dependent_simplex_source_code (succ n)))
            (@ordinal_dependent_simplex_lift_stage n))
          (@ordinal_join_lift_stage_left
            (@DirectedSimplex_cat (succ n)) (succ n)
            (@dependent_simplex_code_decode_cat
              (@DirectedSimplex_cat (succ n)) (succ n)
              (@ordinal_dependent_simplex_source_code (succ n)))
            (@ordinal_dependent_simplex_lift_stage n))
          u)
        (@fapp0
          (@dependent_simplex_code_decode_cat
            (@DirectedSimplex_cat (succ n)) (succ n)
            (@ordinal_dependent_simplex_source_code (succ n)))
          (@ordinal_join_lift_stage_target_cat
            (@DirectedSimplex_cat (succ n)) (succ n)
            (@dependent_simplex_code_decode_cat
              (@DirectedSimplex_cat (succ n)) (succ n)
              (@ordinal_dependent_simplex_source_code (succ n)))
            (@ordinal_dependent_simplex_lift_stage n))
          (@ordinal_join_lift_stage_right
            (@DirectedSimplex_cat (succ n)) (succ n)
            (@dependent_simplex_code_decode_cat
              (@DirectedSimplex_cat (succ n)) (succ n)
              (@ordinal_dependent_simplex_source_code (succ n)))
            (@ordinal_dependent_simplex_lift_stage n))
          v)))
≔ @tapp1_func
    (@dependent_simplex_code_decode_cat
      (@DirectedSimplex_cat (succ n)) (succ n)
      (@ordinal_dependent_simplex_source_code (succ n)))
    (@ordinal_join_lift_stage_target_cat
      (@DirectedSimplex_cat (succ n)) (succ n)
      (@dependent_simplex_code_decode_cat
        (@DirectedSimplex_cat (succ n)) (succ n)
        (@ordinal_dependent_simplex_source_code (succ n)))
      (@ordinal_dependent_simplex_lift_stage n))
    (@ordinal_join_lift_stage_left
      (@DirectedSimplex_cat (succ n)) (succ n)
      (@dependent_simplex_code_decode_cat
        (@DirectedSimplex_cat (succ n)) (succ n)
        (@ordinal_dependent_simplex_source_code (succ n)))
      (@ordinal_dependent_simplex_lift_stage n))
    (@ordinal_join_lift_stage_right
      (@DirectedSimplex_cat (succ n)) (succ n)
      (@dependent_simplex_code_decode_cat
        (@DirectedSimplex_cat (succ n)) (succ n)
        (@ordinal_dependent_simplex_source_code (succ n)))
      (@ordinal_dependent_simplex_lift_stage n))
    u v
    (@ordinal_join_lift_stage_transf
      (@DirectedSimplex_cat (succ n)) (succ n)
      (@dependent_simplex_code_decode_cat
        (@DirectedSimplex_cat (succ n)) (succ n)
        (@ordinal_dependent_simplex_source_code (succ n)))
      (@ordinal_dependent_simplex_lift_stage n));

// Nat recursion computes to the structural successor at every n.
symbol ordinal_dependent_simplex_source_successor_path
  (n : τ Nat_grpd)
  : τ (@=
      (@OrdinalDependentSimplexSource (succ n))
      (@ordinal_dependent_simplex_source (succ n))
      (@ordinal_dependent_simplex_source_successor
        n (@ordinal_dependent_simplex_source n)))
≔ @eq_refl
    (@OrdinalDependentSimplexSource (succ n))
    (@ordinal_dependent_simplex_source (succ n));

symbol ordinal_dependent_simplex_source_zero_object_path
  : τ (@=
      (Obj (@DirectedSimplex_cat zero))
      (@ordinal_dependent_simplex_source_object zero)
      Terminal_obj)
≔ @eq_refl
    (Obj (@DirectedSimplex_cat zero))
    (@ordinal_dependent_simplex_source_object zero);
