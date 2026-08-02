/*
  Topology-visible invertibility support and pointwise localization factors.

  The semantic support D(s) of a section is already an ordinary sieve whose
  literal membership computes to unit evidence for the restricted section.
  This rule-free one-way module first exposes the proposition that D(s) covers
  in a supplied Grothendieck topology.  It then consumes an actual member
  f:V->U of D(s): the universal property of a chosen localization O(U)[1/s]
  selects a structured factor to O(V), together with its pointwise triangle
  over the presheaf restriction O(f).

  This is the computational front of the Cartier-style comparison
  lim_{V in D(s)} O(V) = O(U)[1/s].  The memberwise factors assemble as one
  ordinary transformation from the constant localization ring to the value
  diagram over the category of elements of D(s).  Its transformation type
  internalizes restriction naturality; the derived objectwise restriction
  equation remains construction evidence rather than a downstream proof
  field.  The module deliberately does not claim that this cone is limiting,
  that O is a sheaf, or that a generated Zariski topology, Spec, or scheme has
  been constructed.
*/

require open emdash.emdash3_2_commutative_algebra_presheaves;
require open emdash.emdash3_2_sites;

// A section is locally invertible when its semantic support sieve covers.
symbol CommRingPshInvertibilityCover
  [K : Cat]
  (T : τ (@GrothTopology K))
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  : Grpd
≔ @groth_topology_covers
    K T U (@comm_ring_psh_invertibility_sieve K O U s);

symbol comm_ring_psh_invertibility_cover_is_prop
  [K : Cat]
  (T : τ (@GrothTopology K))
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  : τ (IsPropGrpd (@CommRingPshInvertibilityCover K T O U s))
≔ @covers_is_prop
    K
    (@groth_topology_cover_predicate K T)
    U
    (@comm_ring_psh_invertibility_sieve K O U s);

// Closed topology model: every semantic invertibility support covers.
symbol chaotic_comm_ring_psh_invertibility_cover
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  : τ (@CommRingPshInvertibilityCover
      K (@chaotic_groth_topology K) O U s)
≔ tt;

/*
  Candidate factorization space from a chosen localization O(U)[1/s] to O(V)
  over the actual structured presheaf restriction O(f):O(U)->O(V).
*/
symbol CommRingPshLocalizationFactorAlong
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  [V : τ (Obj K)]
  (f : τ (Hom K V U))
  : Grpd
≔ @CommRingLocalizationFactor
    (@comm_ring_psh_value K O U)
    (@comm_ring_localization_target
      (@comm_ring_psh_value K O U) s localization)
    (@comm_ring_psh_value K O V)
    (@comm_ring_localization_map
      (@comm_ring_psh_value K O U) s localization)
    (@comm_ring_psh_restriction_hom K O V U f);

// Membership f∈D(s) supplies the universal factor selected by localization.
symbol comm_ring_psh_localization_factor_at_member
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  [V : τ (Obj K)]
  (f : τ (Hom K V U))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f)))
  : τ (@CommRingPshLocalizationFactorAlong
      K O U s localization V f)
≔ @is_contr_center
    (@CommRingPshLocalizationFactorAlong K O U s localization V f)
    (@comm_ring_localization_factorization_is_contr
      (@comm_ring_psh_value K O U)
      s
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization)
      (@comm_ring_localization_map
        (@comm_ring_psh_value K O U) s localization)
      (@comm_ring_localization_property
        (@comm_ring_psh_value K O U) s localization)
      (@comm_ring_psh_value K O V)
      (@comm_ring_psh_restriction_hom K O V U f)
      member);

symbol comm_ring_psh_localization_factor_map_at_member
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  [V : τ (Obj K)]
  (f : τ (Hom K V U))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f)))
  : τ (@CommRingHom
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization)
      (@comm_ring_psh_value K O V))
≔ @comm_ring_localization_factor_map
    (@comm_ring_psh_value K O U)
    (@comm_ring_localization_target
      (@comm_ring_psh_value K O U) s localization)
    (@comm_ring_psh_value K O V)
    (@comm_ring_localization_map
      (@comm_ring_psh_value K O U) s localization)
    (@comm_ring_psh_restriction_hom K O V U f)
    (@comm_ring_psh_localization_factor_at_member
      K O U s localization V f member);

// The universal factor triangle is exposed directly on carrier elements.
symbol comm_ring_psh_localization_factor_triangle_at
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  [V : τ (Obj K)]
  (f : τ (Hom K V U))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f)))
  (x : τ (@CommRingPshSection K O U))
  : τ (@= (@CommRingPshSection K O V)
      (@comm_ring_hom_apply
        (@comm_ring_localization_target
          (@comm_ring_psh_value K O U) s localization)
        (@comm_ring_psh_value K O V)
        (@comm_ring_psh_localization_factor_map_at_member
          K O U s localization V f member)
        (@comm_ring_hom_apply
          (@comm_ring_psh_value K O U)
          (@comm_ring_localization_target
            (@comm_ring_psh_value K O U) s localization)
          (@comm_ring_localization_map
            (@comm_ring_psh_value K O U) s localization)
          x))
      (@comm_ring_psh_restrict K O V U f x))
≔ (@comm_ring_localization_factor_agreement
      (@comm_ring_psh_value K O U)
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization)
      (@comm_ring_psh_value K O V)
      (@comm_ring_localization_map
        (@comm_ring_psh_value K O U) s localization)
      (@comm_ring_psh_restriction_hom K O V U f)
      (@comm_ring_psh_localization_factor_at_member
        K O U s localization V f member)) x;

/*
  Internal localization-factor cone.

  An object of `CommRingPshInvertibilityElements_cat(O,U,s)` is a literal
  triple `(V,f,member)` with `f:V->U` and `member:f∈D_O(s)`.  The two existing
  Sigma projections send it to V in Op(K); composing with O gives the value
  diagram `(V,f,member) |-> O(V)`.

  The selected localization factors are packaged as one ordinary
  transformation from the constant localization target to this diagram.  Its
  `Transf` classifier and the generic off-diagonal `tapp1` calculus own
  naturality internally.  The sole local computation rule exposes its
  component at a literal member; no family of external naturality squares is
  added to the public interface.
*/
symbol CommRingPshInvertibilityElements_cat
  [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U))
  : Cat
≔ @Sigma_cat
    (@Into_restr_cat K U)
    (@sieve_higher
      K U
      (@comm_ring_psh_invertibility_sieve K O U s));

// Readable constructor for the literal total object `(V,f,member)`.
symbol comm_ring_psh_invertibility_element
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  [V : τ (Obj K)]
  (f : τ (Hom K V U))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f)))
  : τ (Obj (@CommRingPshInvertibilityElements_cat K O U s))
≔ @Struct_sigma
    (Obj (@Into_restr_cat K U))
    (λ q : τ (Obj (@Into_restr_cat K U)),
      Obj
        (@Fibre_cat
          (@Into_restr_cat K U)
          (@sieve_higher
            K U
            (@comm_ring_psh_invertibility_sieve K O U s))
          q))
    (@Struct_sigma
      (Obj (Op_cat K))
      (λ W : τ (Obj (Op_cat K)),
        Obj (@Fibre_cat (Op_cat K) (@yoneda_psh K U) W))
      V
      f)
    member;

symbol comm_ring_psh_invertibility_domain_func
  [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U))
  : τ (Functor
      (@CommRingPshInvertibilityElements_cat K O U s)
      (Op_cat K))
≔ @comp_cat_fapp0
    (@CommRingPshInvertibilityElements_cat K O U s)
    (@Into_restr_cat K U)
    (Op_cat K)
    (@Sigma_proj1_func
      (Op_cat K)
      (@yoneda_psh K U))
    (@Sigma_proj1_func
      (@Into_restr_cat K U)
      (@sieve_higher
        K U
        (@comm_ring_psh_invertibility_sieve K O U s)));

symbol comm_ring_psh_invertibility_value_diagram
  [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U))
  : τ (Functor
      (@CommRingPshInvertibilityElements_cat K O U s)
      CommRing_cat)
≔ @comp_cat_fapp0
    (@CommRingPshInvertibilityElements_cat K O U s)
    (Op_cat K)
    CommRing_cat
    O
    (@comm_ring_psh_invertibility_domain_func K O U s);

injective symbol comm_ring_psh_localization_factor_cone
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  : τ (@Transf
      (@CommRingPshInvertibilityElements_cat K O U s)
      CommRing_cat
      (@Const_func
        (@CommRingPshInvertibilityElements_cat K O U s)
        CommRing_cat
        (@comm_ring_localization_target
          (@comm_ring_psh_value K O U) s localization))
      (@comm_ring_psh_invertibility_value_diagram K O U s));

// Literal cone component: the selected universal factor at `(V,f,member)`.
rule @tapp0_fapp0
      _
      CommRing_cat
      _
      _
      (Struct_sigma (Struct_sigma $V $f) $member)
      (@comm_ring_psh_localization_factor_cone
        $K $O $U $s $localization)
  ↪ @comm_ring_psh_localization_factor_map_at_member
      $K $O $U $s $localization $V $f $member;

/*
  Derived objectwise restriction-coherence audit.

  For f:V->U and g:W->V, following the selected factor at f by O(g)
  still factors the localization map over O(f o g).  Its triangle is the
  factor triangle at f mapped by O(g), followed by the presheaf composition
  path.  Contractibility then identifies it with the factor selected directly
  at f o g.  This theorem validates the literal components exposed above;
  downstream consumers use the internal transformation rather than carrying
  this equation as an external naturality field.
*/
symbol comm_ring_psh_localization_factor_after_restriction_agreement
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  [W V : τ (Obj K)]
  (f : τ (Hom K V U))
  (g : τ (Hom K W V))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f)))
  : τ (@CommRingLocalizationAgreement
      (@comm_ring_psh_value K O U)
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization)
      (@comm_ring_psh_value K O W)
      (@comm_ring_localization_map
        (@comm_ring_psh_value K O U) s localization)
      (@comm_ring_hom_comp_pointwise
        (@comm_ring_localization_target
          (@comm_ring_psh_value K O U) s localization)
        (@comm_ring_psh_value K O V)
        (@comm_ring_psh_value K O W)
        (@comm_ring_psh_restriction_hom K O W V g)
        (@comm_ring_psh_localization_factor_map_at_member
          K O U s localization V f member))
      (@comm_ring_psh_restriction_hom K O W U
        (@comp_fapp0 K W V U f g)))
≔ λ x : τ (@CommRingPshSection K O U),
    @eq_trans
      (@CommRingPshSection K O W)
      (@comm_ring_psh_restrict K O W V g
        (@comm_ring_hom_apply
          (@comm_ring_localization_target
            (@comm_ring_psh_value K O U) s localization)
          (@comm_ring_psh_value K O V)
          (@comm_ring_psh_localization_factor_map_at_member
            K O U s localization V f member)
          (@comm_ring_hom_apply
            (@comm_ring_psh_value K O U)
            (@comm_ring_localization_target
              (@comm_ring_psh_value K O U) s localization)
            (@comm_ring_localization_map
              (@comm_ring_psh_value K O U) s localization)
            x)))
      (@comm_ring_psh_restrict K O W V g
        (@comm_ring_psh_restrict K O V U f x))
      (@comm_ring_psh_restrict K O W U
        (@comp_fapp0 K W V U f g) x)
      (@eq_ap
        (@CommRingPshSection K O V)
        (@CommRingPshSection K O W)
        (λ y : τ (@CommRingPshSection K O V),
          @comm_ring_psh_restrict K O W V g y)
        (@comm_ring_hom_apply
          (@comm_ring_localization_target
            (@comm_ring_psh_value K O U) s localization)
          (@comm_ring_psh_value K O V)
          (@comm_ring_psh_localization_factor_map_at_member
            K O U s localization V f member)
          (@comm_ring_hom_apply
            (@comm_ring_psh_value K O U)
            (@comm_ring_localization_target
              (@comm_ring_psh_value K O U) s localization)
            (@comm_ring_localization_map
              (@comm_ring_psh_value K O U) s localization)
            x))
        (@comm_ring_psh_restrict K O V U f x)
        (@comm_ring_psh_localization_factor_triangle_at
          K O U s localization V f member x))
      (@eq_sym
        (@CommRingPshSection K O W)
        (@comm_ring_psh_restrict K O W U
          (@comp_fapp0 K W V U f g) x)
        (@comm_ring_psh_restrict K O W V g
          (@comm_ring_psh_restrict K O V U f x))
        (@comm_ring_psh_restrict_comp_path K O W V U f g x));

// The restriction composite packaged as a competing factor at f o g.
symbol comm_ring_psh_localization_factor_after_restriction
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  [W V : τ (Obj K)]
  (f : τ (Hom K V U))
  (g : τ (Hom K W V))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f)))
  : τ (@CommRingPshLocalizationFactorAlong
      K O U s localization W (@comp_fapp0 K W V U f g))
≔ @comm_ring_localization_factor_intro
    (@comm_ring_psh_value K O U)
    (@comm_ring_localization_target
      (@comm_ring_psh_value K O U) s localization)
    (@comm_ring_psh_value K O W)
    (@comm_ring_localization_map
      (@comm_ring_psh_value K O U) s localization)
    (@comm_ring_psh_restriction_hom K O W U
      (@comp_fapp0 K W V U f g))
    (@comm_ring_hom_comp_pointwise
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization)
      (@comm_ring_psh_value K O V)
      (@comm_ring_psh_value K O W)
      (@comm_ring_psh_restriction_hom K O W V g)
      (@comm_ring_psh_localization_factor_map_at_member
        K O U s localization V f member))
    (@comm_ring_psh_localization_factor_after_restriction_agreement
      K O U s localization W V f g member);

// Universal uniqueness identifies the direct and iterated factor packages.
symbol comm_ring_psh_localization_factor_restriction_package_path
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  [W V : τ (Obj K)]
  (f : τ (Hom K V U))
  (g : τ (Hom K W V))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f)))
  : τ (@=
      (@CommRingPshLocalizationFactorAlong
        K O U s localization W (@comp_fapp0 K W V U f g))
      (@comm_ring_psh_localization_factor_at_member
        K O U s localization W (@comp_fapp0 K W V U f g)
        (@comm_ring_psh_invertible_along_restrict
          K O W V U f g s member))
      (@comm_ring_psh_localization_factor_after_restriction
        K O U s localization W V f g member))
≔ @is_contr_path
    (@CommRingPshLocalizationFactorAlong
      K O U s localization W (@comp_fapp0 K W V U f g))
    (@comm_ring_localization_factorization_is_contr
      (@comm_ring_psh_value K O U)
      s
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization)
      (@comm_ring_localization_map
        (@comm_ring_psh_value K O U) s localization)
      (@comm_ring_localization_property
        (@comm_ring_psh_value K O U) s localization)
      (@comm_ring_psh_value K O W)
      (@comm_ring_psh_restriction_hom K O W U
        (@comp_fapp0 K W V U f g))
      (@comm_ring_psh_invertible_along_restrict
        K O W V U f g s member))
    (@comm_ring_psh_localization_factor_after_restriction
      K O U s localization W V f g member);

// Usable objectwise cone equation: direct factor = restriction after factor.
symbol comm_ring_psh_localization_factor_restriction_path
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  [W V : τ (Obj K)]
  (f : τ (Hom K V U))
  (g : τ (Hom K W V))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f)))
  : τ (@=
      (@CommRingHom
        (@comm_ring_localization_target
          (@comm_ring_psh_value K O U) s localization)
        (@comm_ring_psh_value K O W))
      (@comm_ring_psh_localization_factor_map_at_member
        K O U s localization W (@comp_fapp0 K W V U f g)
        (@comm_ring_psh_invertible_along_restrict
          K O W V U f g s member))
      (@comm_ring_hom_comp_pointwise
        (@comm_ring_localization_target
          (@comm_ring_psh_value K O U) s localization)
        (@comm_ring_psh_value K O V)
        (@comm_ring_psh_value K O W)
        (@comm_ring_psh_restriction_hom K O W V g)
        (@comm_ring_psh_localization_factor_map_at_member
          K O U s localization V f member)))
≔ @eq_ap
    (@CommRingPshLocalizationFactorAlong
      K O U s localization W (@comp_fapp0 K W V U f g))
    (@CommRingHom
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization)
      (@comm_ring_psh_value K O W))
    (λ factor : τ (@CommRingPshLocalizationFactorAlong
        K O U s localization W (@comp_fapp0 K W V U f g)),
      @comm_ring_localization_factor_map
        (@comm_ring_psh_value K O U)
        (@comm_ring_localization_target
          (@comm_ring_psh_value K O U) s localization)
        (@comm_ring_psh_value K O W)
        (@comm_ring_localization_map
          (@comm_ring_psh_value K O U) s localization)
        (@comm_ring_psh_restriction_hom K O W U
          (@comp_fapp0 K W V U f g))
        factor)
    (@comm_ring_psh_localization_factor_at_member
      K O U s localization W (@comp_fapp0 K W V U f g)
      (@comm_ring_psh_invertible_along_restrict
        K O W V U f g s member))
    (@comm_ring_psh_localization_factor_after_restriction
      K O U s localization W V f g member)
    (@comm_ring_psh_localization_factor_restriction_package_path
      K O U s localization W V f g member);
