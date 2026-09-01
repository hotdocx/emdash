/*
  Finite free modules as a matrix category over one commutative ring.

  Objects are ranks and Homs are path categories of column-oriented matrices.
  Generic category identity/composition remain runtime owners. Rigid
  pointwise matrix heads meet them at proof time and expose visible column
  projections. This follows CommRing_cat usability and avoids reducing generic
  composition directly into the transparent Nat-recursive matrix body, whose
  strict-functoriality overlap expands pathologically. A runtime fold to the
  rigid head checks but leaves higher-action joins consumer-gated. Additive and
  Abelian structures remain separate.
*/

require open emdash.emdash3_2_commutative_algebra_bounded_free_chain_maps;

injective symbol CommRingFiniteFree_cat
  (R : τ CommRing)
  : Cat;

rule Obj (@CommRingFiniteFree_cat _)
  ↪ Nat_grpd;

rule Hom_cat (@CommRingFiniteFree_cat $R) $source $target
  ↪ Path_cat (@CommRingMatrix $R $target $source);

// Stable identity-matrix representation with recursive column observations.
injective symbol comm_ring_finite_free_id_matrix
  (R : τ CommRing)
  (n : τ Nat_grpd)
  : τ (@CommRingMatrix R n n);

rule @comm_ring_finite_free_id_matrix $R zero
  ↪ @finite_family_nil (@CommRingVector $R zero);

rule sigma_Fst
      (@comm_ring_finite_free_id_matrix $R (succ $n))
  ↪ @finite_family_cons
      (@comm_ring_carrier $R) $n
      (@comm_ring_one $R)
      (@comm_ring_vector_zero $R $n);

rule sigma_Snd
      (@comm_ring_finite_free_id_matrix $R (succ $n))
  ↪ @finite_family_map
      (@CommRingVector $R $n)
      (@CommRingVector $R (succ $n))
      (λ column : τ (@CommRingVector $R $n),
        @finite_family_cons
          (@comm_ring_carrier $R) $n
          (@comm_ring_zero $R)
          column)
      $n
      (@comm_ring_finite_free_id_matrix $R $n);

// Generic identity and the rigid matrix representation meet only at proof time.
unif_rule
  @id (@CommRingFiniteFree_cat $R) $n
  ≡ @comm_ring_finite_free_id_matrix $R $n
  ↪ [ tt ≡ tt ];

symbol comm_ring_finite_free_id_matrix_path
  (R : τ CommRing)
  (n : τ Nat_grpd)
  : τ (@= (@CommRingMatrix R n n)
      (@id (@CommRingFiniteFree_cat R) n)
      (@comm_ring_finite_free_id_matrix R n))
≔ @eq_refl (@CommRingMatrix R n n)
    (@id (@CommRingFiniteFree_cat R) n);

// Stable composition representation with constructor-visible column action.
injective symbol comm_ring_finite_free_comp_matrix
  (R : τ CommRing)
  (source middle target : τ Nat_grpd)
  (g : τ (@CommRingMatrix R target middle))
  (f : τ (@CommRingMatrix R middle source))
  : τ (@CommRingMatrix R target source);

rule @comm_ring_finite_free_comp_matrix
      $R zero _ $target _ _
  ↪ @finite_family_nil (@CommRingVector $R $target);

rule sigma_Fst
      (@comm_ring_finite_free_comp_matrix
        $R (succ $n) $middle $target $g $f)
  ↪ @comm_ring_matrix_apply $R $target $middle $g
      (@finite_family_head
        (@CommRingVector $R $middle) $n $f);

rule sigma_Snd
      (@comm_ring_finite_free_comp_matrix
        $R (succ $n) $middle $target $g $f)
  ↪ @comm_ring_finite_free_comp_matrix
      $R $n $middle $target $g
      (@finite_family_tail
        (@CommRingVector $R $middle) $n $f);

unif_rule
  @comp_fapp0
      (@CommRingFiniteFree_cat $R)
      $source $middle $target $g $f
  ≡ @comm_ring_finite_free_comp_matrix
      $R $source $middle $target $g $f
  ↪ [ tt ≡ tt ];

symbol comm_ring_finite_free_comp_matrix_path
  (R : τ CommRing)
  (source middle target : τ Nat_grpd)
  (g : τ (@CommRingMatrix R target middle))
  (f : τ (@CommRingMatrix R middle source))
  : τ (@= (@CommRingMatrix R target source)
      (@comp_fapp0
        (@CommRingFiniteFree_cat R)
        source middle target g f)
      (@comm_ring_finite_free_comp_matrix
        R source middle target g f))
≔ @eq_refl (@CommRingMatrix R target source)
    (@comp_fapp0
      (@CommRingFiniteFree_cat R)
      source middle target g f);

/*
  Constructed comparison with the transparent direct matrix evaluator.

  At zero columns both implementations are empty. At a successor they expose
  the same first matrix-action column; the induction hypothesis compares the
  tails through the constant tail family of the encoded Sigma. This is an
  ordinary path, not a unifier or an opaque equality bridge.
*/
symbol comm_ring_finite_free_comp_transparent_path
  (R : τ CommRing)
  (source middle target : τ Nat_grpd)
  (g : τ (@CommRingMatrix R target middle))
  (f : τ (@CommRingMatrix R middle source))
  : τ (@= (@CommRingMatrix R target source)
      (@comm_ring_finite_free_comp_matrix
        R source middle target g f)
      (@comm_ring_matrix_comp R target middle source g f))
≔ (@nat_elim
    (λ source0 : τ Nat_grpd,
      @Pi_grpd
        (@CommRingMatrix R middle source0)
        (λ f0 : τ (@CommRingMatrix R middle source0),
          @= (@CommRingMatrix R target source0)
            (@comm_ring_finite_free_comp_matrix
              R source0 middle target g f0)
            (@comm_ring_matrix_comp
              R target middle source0 g f0)))
    (λ _ : τ (@CommRingMatrix R middle zero),
      @eq_refl
        (@CommRingMatrix R target zero)
        (@finite_family_nil (@CommRingVector R target)))
    (λ source0 : τ Nat_grpd,
      λ ih : τ (@Pi_grpd
        (@CommRingMatrix R middle source0)
        (λ f0 : τ (@CommRingMatrix R middle source0),
          @= (@CommRingMatrix R target source0)
            (@comm_ring_finite_free_comp_matrix
              R source0 middle target g f0)
            (@comm_ring_matrix_comp
              R target middle source0 g f0))),
      λ f0 : τ (@CommRingMatrix R middle (succ source0)),
        @Struct_sigma
          (@= (@CommRingVector R target)
            (@comm_ring_matrix_apply R target middle g
              (@finite_family_head
                (@CommRingVector R middle) source0 f0))
            (@comm_ring_matrix_apply R target middle g
              (@finite_family_head
                (@CommRingVector R middle) source0 f0)))
          (λ p : τ (@= (@CommRingVector R target)
              (@comm_ring_matrix_apply R target middle g
                (@finite_family_head
                  (@CommRingVector R middle) source0 f0))
              (@comm_ring_matrix_apply R target middle g
                (@finite_family_head
                  (@CommRingVector R middle) source0 f0))),
            @PathOver
              (@CommRingVector R target)
              (λ _ : τ (@CommRingVector R target),
                @CommRingMatrix R target source0)
              (@comm_ring_matrix_apply R target middle g
                (@finite_family_head
                  (@CommRingVector R middle) source0 f0))
              (@comm_ring_matrix_apply R target middle g
                (@finite_family_head
                  (@CommRingVector R middle) source0 f0))
              p
              (@comm_ring_finite_free_comp_matrix
                R source0 middle target g
                (@finite_family_tail
                  (@CommRingVector R middle) source0 f0))
              (@comm_ring_matrix_comp
                R target middle source0 g
                (@finite_family_tail
                  (@CommRingVector R middle) source0 f0)))
          (@eq_refl
            (@CommRingVector R target)
            (@comm_ring_matrix_apply R target middle g
              (@finite_family_head
                (@CommRingVector R middle) source0 f0)))
          (@const_pathover
            (@CommRingVector R target)
            (@CommRingMatrix R target source0)
            (@comm_ring_matrix_apply R target middle g
              (@finite_family_head
                (@CommRingVector R middle) source0 f0))
            (@comm_ring_matrix_apply R target middle g
              (@finite_family_head
                (@CommRingVector R middle) source0 f0))
            (@comm_ring_finite_free_comp_matrix
              R source0 middle target g
              (@finite_family_tail
                (@CommRingVector R middle) source0 f0))
            (@comm_ring_matrix_comp
              R target middle source0 g
              (@finite_family_tail
                (@CommRingVector R middle) source0 f0))
            (@eq_refl
              (@CommRingVector R target)
              (@comm_ring_matrix_apply R target middle g
                (@finite_family_head
                  (@CommRingVector R middle) source0 f0)))
            (ih
              (@finite_family_tail
                (@CommRingVector R middle) source0 f0))))
    source) f;

// Generic finite-free composition agrees propositionally with direct matrix
// evaluation by composing the proof-time usability view with the path above.
symbol comm_ring_finite_free_comp_fapp0_transparent_path
  (R : τ CommRing)
  (source middle target : τ Nat_grpd)
  (g : τ (@CommRingMatrix R target middle))
  (f : τ (@CommRingMatrix R middle source))
  : τ (@= (@CommRingMatrix R target source)
      (@comp_fapp0
        (@CommRingFiniteFree_cat R)
        source middle target g f)
      (@comm_ring_matrix_comp R target middle source g f))
≔ @eq_trans
    (@CommRingMatrix R target source)
    (@comp_fapp0
      (@CommRingFiniteFree_cat R)
      source middle target g f)
    (@comm_ring_finite_free_comp_matrix
      R source middle target g f)
    (@comm_ring_matrix_comp R target middle source g f)
    (@comm_ring_finite_free_comp_matrix_path
      R source middle target g f)
    (@comm_ring_finite_free_comp_transparent_path
      R source middle target g f);

/*
  Transparent matrix identity laws transported from generic category units.

  The identity comparison is applied explicitly inside composition because
  unification rules are not assumed transitive. The final generic unit step is
  judgmental; the whole transparent statement remains propositional.
*/
symbol comm_ring_matrix_comp_right_identity_path
  (R : τ CommRing)
  (source target : τ Nat_grpd)
  (g : τ (@CommRingMatrix R target source))
  : τ (@= (@CommRingMatrix R target source)
      (@comm_ring_matrix_comp R target source source g
        (@comm_ring_finite_free_id_matrix R source))
      g)
≔ @eq_trans
    (@CommRingMatrix R target source)
    (@comm_ring_matrix_comp R target source source g
      (@comm_ring_finite_free_id_matrix R source))
    (@comp_fapp0
      (@CommRingFiniteFree_cat R)
      source source target g
      (@comm_ring_finite_free_id_matrix R source))
    g
    (@eq_sym
      (@CommRingMatrix R target source)
      (@comp_fapp0
        (@CommRingFiniteFree_cat R)
        source source target g
        (@comm_ring_finite_free_id_matrix R source))
      (@comm_ring_matrix_comp R target source source g
        (@comm_ring_finite_free_id_matrix R source))
      (@comm_ring_finite_free_comp_fapp0_transparent_path
        R source source target g
        (@comm_ring_finite_free_id_matrix R source)))
    (@eq_trans
      (@CommRingMatrix R target source)
      (@comp_fapp0
        (@CommRingFiniteFree_cat R)
        source source target g
        (@comm_ring_finite_free_id_matrix R source))
      (@comp_fapp0
        (@CommRingFiniteFree_cat R)
        source source target g
        (@id (@CommRingFiniteFree_cat R) source))
      g
      (@eq_ap
        (@CommRingMatrix R source source)
        (@CommRingMatrix R target source)
        (λ u : τ (@CommRingMatrix R source source),
          @comp_fapp0
            (@CommRingFiniteFree_cat R)
            source source target g u)
        (@comm_ring_finite_free_id_matrix R source)
        (@id (@CommRingFiniteFree_cat R) source)
        (@eq_sym
          (@CommRingMatrix R source source)
          (@id (@CommRingFiniteFree_cat R) source)
          (@comm_ring_finite_free_id_matrix R source)
          (@comm_ring_finite_free_id_matrix_path R source)))
      (@eq_refl (@CommRingMatrix R target source) g));

symbol comm_ring_matrix_comp_left_identity_path
  (R : τ CommRing)
  (source target : τ Nat_grpd)
  (g : τ (@CommRingMatrix R target source))
  : τ (@= (@CommRingMatrix R target source)
      (@comm_ring_matrix_comp R target target source
        (@comm_ring_finite_free_id_matrix R target) g)
      g)
≔ @eq_trans
    (@CommRingMatrix R target source)
    (@comm_ring_matrix_comp R target target source
      (@comm_ring_finite_free_id_matrix R target) g)
    (@comp_fapp0
      (@CommRingFiniteFree_cat R)
      source target target
      (@comm_ring_finite_free_id_matrix R target) g)
    g
    (@eq_sym
      (@CommRingMatrix R target source)
      (@comp_fapp0
        (@CommRingFiniteFree_cat R)
        source target target
        (@comm_ring_finite_free_id_matrix R target) g)
      (@comm_ring_matrix_comp R target target source
        (@comm_ring_finite_free_id_matrix R target) g)
      (@comm_ring_finite_free_comp_fapp0_transparent_path
        R source target target
        (@comm_ring_finite_free_id_matrix R target) g))
    (@eq_trans
      (@CommRingMatrix R target source)
      (@comp_fapp0
        (@CommRingFiniteFree_cat R)
        source target target
        (@comm_ring_finite_free_id_matrix R target) g)
      (@comp_fapp0
        (@CommRingFiniteFree_cat R)
        source target target
        (@id (@CommRingFiniteFree_cat R) target) g)
      g
      (@eq_ap
        (@CommRingMatrix R target target)
        (@CommRingMatrix R target source)
        (λ u : τ (@CommRingMatrix R target target),
          @comp_fapp0
            (@CommRingFiniteFree_cat R)
            source target target u g)
        (@comm_ring_finite_free_id_matrix R target)
        (@id (@CommRingFiniteFree_cat R) target)
        (@eq_sym
          (@CommRingMatrix R target target)
          (@id (@CommRingFiniteFree_cat R) target)
          (@comm_ring_finite_free_id_matrix R target)
          (@comm_ring_finite_free_id_matrix_path R target)))
      (@eq_refl (@CommRingMatrix R target source) g));

/*
  Transparent matrix associativity transported from generic cut association.

  Each inner and outer generic/transparent comparison is applied explicitly;
  no transitivity of unification rules or algebraic runtime normalization is
  assumed.
*/
symbol comm_ring_matrix_comp_assoc_path
  (R : τ CommRing)
  (A B C D : τ Nat_grpd)
  (h : τ (@CommRingMatrix R D C))
  (g : τ (@CommRingMatrix R C B))
  (f : τ (@CommRingMatrix R B A))
  : τ (@= (@CommRingMatrix R D A)
      (@comm_ring_matrix_comp R D C A h
        (@comm_ring_matrix_comp R C B A g f))
      (@comm_ring_matrix_comp R D B A
        (@comm_ring_matrix_comp R D C B h g) f))
≔ @eq_trans
    (@CommRingMatrix R D A)
    (@comm_ring_matrix_comp R D C A h
      (@comm_ring_matrix_comp R C B A g f))
    (@comp_fapp0
      (@CommRingFiniteFree_cat R)
      A C D h
      (@comm_ring_matrix_comp R C B A g f))
    (@comm_ring_matrix_comp R D B A
      (@comm_ring_matrix_comp R D C B h g) f)
    (@eq_sym
      (@CommRingMatrix R D A)
      (@comp_fapp0
        (@CommRingFiniteFree_cat R)
        A C D h
        (@comm_ring_matrix_comp R C B A g f))
      (@comm_ring_matrix_comp R D C A h
        (@comm_ring_matrix_comp R C B A g f))
      (@comm_ring_finite_free_comp_fapp0_transparent_path
        R A C D h
        (@comm_ring_matrix_comp R C B A g f)))
    (@eq_trans
      (@CommRingMatrix R D A)
      (@comp_fapp0
        (@CommRingFiniteFree_cat R)
        A C D h
        (@comm_ring_matrix_comp R C B A g f))
      (@comp_fapp0
        (@CommRingFiniteFree_cat R)
        A C D h
        (@comp_fapp0
          (@CommRingFiniteFree_cat R)
          A B C g f))
      (@comm_ring_matrix_comp R D B A
        (@comm_ring_matrix_comp R D C B h g) f)
      (@eq_ap
        (@CommRingMatrix R C A)
        (@CommRingMatrix R D A)
        (λ u : τ (@CommRingMatrix R C A),
          @comp_fapp0
            (@CommRingFiniteFree_cat R)
            A C D h u)
        (@comm_ring_matrix_comp R C B A g f)
        (@comp_fapp0
          (@CommRingFiniteFree_cat R)
          A B C g f)
        (@eq_sym
          (@CommRingMatrix R C A)
          (@comp_fapp0
            (@CommRingFiniteFree_cat R)
            A B C g f)
          (@comm_ring_matrix_comp R C B A g f)
          (@comm_ring_finite_free_comp_fapp0_transparent_path
            R A B C g f)))
      (@eq_trans
        (@CommRingMatrix R D A)
        (@comp_fapp0
          (@CommRingFiniteFree_cat R)
          A C D h
          (@comp_fapp0
            (@CommRingFiniteFree_cat R)
            A B C g f))
        (@comp_fapp0
          (@CommRingFiniteFree_cat R)
          A B D
          (@comp_fapp0
            (@CommRingFiniteFree_cat R)
            B C D h g)
          f)
        (@comm_ring_matrix_comp R D B A
          (@comm_ring_matrix_comp R D C B h g) f)
        (@comp_assoc
          (@CommRingFiniteFree_cat R)
          A B C D h g f)
        (@eq_trans
          (@CommRingMatrix R D A)
          (@comp_fapp0
            (@CommRingFiniteFree_cat R)
            A B D
            (@comp_fapp0
              (@CommRingFiniteFree_cat R)
              B C D h g)
            f)
          (@comp_fapp0
            (@CommRingFiniteFree_cat R)
            A B D
            (@comm_ring_matrix_comp R D C B h g)
            f)
          (@comm_ring_matrix_comp R D B A
            (@comm_ring_matrix_comp R D C B h g) f)
          (@eq_ap
            (@CommRingMatrix R D B)
            (@CommRingMatrix R D A)
            (λ u : τ (@CommRingMatrix R D B),
              @comp_fapp0
                (@CommRingFiniteFree_cat R)
                A B D u f)
            (@comp_fapp0
              (@CommRingFiniteFree_cat R)
              B C D h g)
            (@comm_ring_matrix_comp R D C B h g)
            (@comm_ring_finite_free_comp_fapp0_transparent_path
              R B C D h g))
          (@comm_ring_finite_free_comp_fapp0_transparent_path
            R A B D
            (@comm_ring_matrix_comp R D C B h g)
            f))));

/*
  Pasting two relation-preserving matrix squares.

  The proof is the standard five-step categorical calculation: associate,
  apply the second square, reassociate, apply the first square, and associate.
  It is reusable by presentation maps and later chain-map constructions.
*/
symbol comm_ring_matrix_square_comp_path
  (R : τ CommRing)
  (p_rel p_gen q_rel q_gen s_rel s_gen : τ Nat_grpd)
  (R_P : τ (@CommRingMatrix R p_gen p_rel))
  (R_Q : τ (@CommRingMatrix R q_gen q_rel))
  (R_S : τ (@CommRingMatrix R s_gen s_rel))
  (F : τ (@CommRingMatrix R q_gen p_gen))
  (W : τ (@CommRingMatrix R q_rel p_rel))
  (G : τ (@CommRingMatrix R s_gen q_gen))
  (V : τ (@CommRingMatrix R s_rel q_rel))
  (law_f : τ (@= (@CommRingMatrix R q_gen p_rel)
      (@comm_ring_matrix_comp R q_gen q_rel p_rel R_Q W)
      (@comm_ring_matrix_comp R q_gen p_gen p_rel F R_P)))
  (law_g : τ (@= (@CommRingMatrix R s_gen q_rel)
      (@comm_ring_matrix_comp R s_gen s_rel q_rel R_S V)
      (@comm_ring_matrix_comp R s_gen q_gen q_rel G R_Q)))
  : τ (@= (@CommRingMatrix R s_gen p_rel)
      (@comm_ring_matrix_comp R s_gen s_rel p_rel R_S
        (@comm_ring_matrix_comp R s_rel q_rel p_rel V W))
      (@comm_ring_matrix_comp R s_gen p_gen p_rel
        (@comm_ring_matrix_comp R s_gen q_gen p_gen G F) R_P))
≔ @eq_trans
    (@CommRingMatrix R s_gen p_rel)
    _ _ _
    (@comm_ring_matrix_comp_assoc_path R
      p_rel q_rel s_rel s_gen R_S V W)
    (@eq_trans
      (@CommRingMatrix R s_gen p_rel)
      _ _ _
      (@eq_ap
        (@CommRingMatrix R s_gen q_rel)
        (@CommRingMatrix R s_gen p_rel)
        (λ u : τ (@CommRingMatrix R s_gen q_rel),
          @comm_ring_matrix_comp R s_gen q_rel p_rel u W)
        (@comm_ring_matrix_comp R s_gen s_rel q_rel R_S V)
        (@comm_ring_matrix_comp R s_gen q_gen q_rel G R_Q)
        law_g)
      (@eq_trans
        (@CommRingMatrix R s_gen p_rel)
        _ _ _
        (@eq_sym
          (@CommRingMatrix R s_gen p_rel)
          (@comm_ring_matrix_comp R s_gen q_gen p_rel G
            (@comm_ring_matrix_comp R q_gen q_rel p_rel R_Q W))
          (@comm_ring_matrix_comp R s_gen q_rel p_rel
            (@comm_ring_matrix_comp R s_gen q_gen q_rel G R_Q) W)
          (@comm_ring_matrix_comp_assoc_path R
            p_rel q_rel q_gen s_gen G R_Q W))
        (@eq_trans
          (@CommRingMatrix R s_gen p_rel)
          _ _ _
          (@eq_ap
            (@CommRingMatrix R q_gen p_rel)
            (@CommRingMatrix R s_gen p_rel)
            (λ u : τ (@CommRingMatrix R q_gen p_rel),
              @comm_ring_matrix_comp R s_gen q_gen p_rel G u)
            (@comm_ring_matrix_comp R q_gen q_rel p_rel R_Q W)
            (@comm_ring_matrix_comp R q_gen p_gen p_rel F R_P)
            law_f)
          (@comm_ring_matrix_comp_assoc_path R
            p_rel p_gen q_gen s_gen G F R_P))));
