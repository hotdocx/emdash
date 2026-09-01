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
