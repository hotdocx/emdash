/*
  Selected computational glue for localization matching families.

  For a chosen localization O(U)[1/s], the preceding matching layer sends
  localization elements to coherent sections over the complete category of
  elements of D(s).  This module packages the converse as selected locality
  data.  Glue is a genuine functor from the matching category to the Path
  category of the localization carrier, so its action on matching arrows is
  internal rather than supplied by external naturality equations.

  Two retained laws expose the computational Cartier boundary:

    glue(restrict(x)) = x

  and, at every support element e,

    restrict(glue(m))[e] = m[e].

  At a literal e=(V,f,member), the second left endpoint computes to the
  selected localization factor applied to glue(m).  This is selected
  basic-open locality data, not ordinary sheaf descent over a covering sieve:
  D(s) need not cover U.  The module is rule-free and claims no whole
  categorical DefIso, sheafhood, generated topology, Spec, or scheme.
*/

require open emdash.emdash3_2_commutative_algebra_matching;

// Carrier of the selected localization target.
symbol CommRingPshLocalizationCarrier
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  : Grpd
≔ @comm_ring_carrier
    (@comm_ring_localization_target
      (@comm_ring_psh_value K O U) s localization);

// Classifier of functors from coherent matching families to localization paths.
symbol CommRingPshLocalizationGlueFunctor
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  : Grpd
≔ Obj (@Functor_cat
    (@CommRingPshLocalizationMatching_cat K O U s)
    (Path_cat (@CommRingPshLocalizationCarrier
      K O U s localization)));

// Glue is a left inverse to canonical restriction on localization elements.
symbol CommRingPshLocalizationGlueRestrictLaw
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  (glue_func : τ (@CommRingPshLocalizationGlueFunctor
      K O U s localization))
  : Grpd
≔ @Pi_grpd
    (@CommRingPshLocalizationCarrier K O U s localization)
    (λ x : τ (@CommRingPshLocalizationCarrier
        K O U s localization),
      @=
        (@CommRingPshLocalizationCarrier K O U s localization)
        (@fapp0
          (@CommRingPshLocalizationMatching_cat K O U s)
          (Path_cat (@CommRingPshLocalizationCarrier
            K O U s localization))
          glue_func
          (@comm_ring_psh_localization_matching_section
            K O U s localization x))
        x);

/*
  Componentwise right-inverse law.

  The matching object already carries its coherence internally as an object
  of Pi_cat.  This law observes the inverse at piapp0; it is not a separately
  propagated family of naturality squares.
*/
symbol CommRingPshLocalizationRestrictGlueComponentLaw
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  (glue_func : τ (@CommRingPshLocalizationGlueFunctor
      K O U s localization))
  : Grpd
≔ @Pi_grpd
    (Obj (@CommRingPshLocalizationMatching_cat K O U s))
    (λ matching : τ (Obj
        (@CommRingPshLocalizationMatching_cat K O U s)),
      @Pi_grpd
        (Obj (@CommRingPshInvertibilityElements_cat K O U s))
        (λ element : τ (Obj
            (@CommRingPshInvertibilityElements_cat K O U s)),
          @=
            (Obj (@Fibre_cat
              (@CommRingPshInvertibilityElements_cat K O U s)
              (@comm_ring_psh_localization_matching_catd K O U s)
              element))
            (@piapp0
              (@CommRingPshInvertibilityElements_cat K O U s)
              (@comm_ring_psh_localization_matching_catd K O U s)
              (@comm_ring_psh_localization_matching_section
                K O U s localization
                (@fapp0
                  (@CommRingPshLocalizationMatching_cat K O U s)
                  (Path_cat (@CommRingPshLocalizationCarrier
                    K O U s localization))
                  glue_func matching))
              element)
            (@piapp0
              (@CommRingPshInvertibilityElements_cat K O U s)
              (@comm_ring_psh_localization_matching_catd K O U s)
              matching element)));

// Selected glue functor together with its two computational inverse laws.
symbol CommRingPshLocalizationGlue
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  : Grpd
≔ @Σ_
    (@CommRingPshLocalizationGlueFunctor K O U s localization)
    (λ glue_func : τ (@CommRingPshLocalizationGlueFunctor
        K O U s localization),
      @Product_grpd
        (@CommRingPshLocalizationGlueRestrictLaw
          K O U s localization glue_func)
        (@CommRingPshLocalizationRestrictGlueComponentLaw
          K O U s localization glue_func));

symbol comm_ring_psh_localization_glue_intro
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  (glue_func : τ (@CommRingPshLocalizationGlueFunctor
      K O U s localization))
  (glue_restrict : τ (@CommRingPshLocalizationGlueRestrictLaw
      K O U s localization glue_func))
  (restrict_glue : τ
      (@CommRingPshLocalizationRestrictGlueComponentLaw
        K O U s localization glue_func))
  : τ (@CommRingPshLocalizationGlue K O U s localization)
≔ @Struct_sigma
    (@CommRingPshLocalizationGlueFunctor K O U s localization)
    (λ candidate : τ (@CommRingPshLocalizationGlueFunctor
        K O U s localization),
      @Product_grpd
        (@CommRingPshLocalizationGlueRestrictLaw
          K O U s localization candidate)
        (@CommRingPshLocalizationRestrictGlueComponentLaw
          K O U s localization candidate))
    glue_func
    (@Product_pair_grpd
      (@CommRingPshLocalizationGlueRestrictLaw
        K O U s localization glue_func)
      (@CommRingPshLocalizationRestrictGlueComponentLaw
        K O U s localization glue_func)
      glue_restrict restrict_glue);

// Selected glue functor projection.
symbol comm_ring_psh_localization_glue_func
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  (glue : τ (@CommRingPshLocalizationGlue K O U s localization))
  : τ (@CommRingPshLocalizationGlueFunctor K O U s localization)
≔ sigma_Fst glue;

// Object action of selected glue.
symbol comm_ring_psh_localization_glue
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  (glue : τ (@CommRingPshLocalizationGlue K O U s localization))
  (matching : τ (Obj
      (@CommRingPshLocalizationMatching_cat K O U s)))
  : τ (@CommRingPshLocalizationCarrier K O U s localization)
≔ @fapp0
    (@CommRingPshLocalizationMatching_cat K O U s)
    (Path_cat (@CommRingPshLocalizationCarrier
      K O U s localization))
    (@comm_ring_psh_localization_glue_func
      K O U s localization glue)
    matching;

// First inverse law, exposed at the localization carrier.
symbol comm_ring_psh_localization_glue_restrict_path
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  (glue : τ (@CommRingPshLocalizationGlue K O U s localization))
  (x : τ (@CommRingPshLocalizationCarrier K O U s localization))
  : τ (@=
      (@CommRingPshLocalizationCarrier K O U s localization)
      (@comm_ring_psh_localization_glue
        K O U s localization glue
        (@comm_ring_psh_localization_matching_section
          K O U s localization x))
      x)
≔ (sigma_Fst (sigma_Snd glue)) x;

// Second inverse law, exposed at an arbitrary internal support element.
symbol comm_ring_psh_localization_restrict_glue_component_path
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  (glue : τ (@CommRingPshLocalizationGlue K O U s localization))
  (matching : τ (Obj
      (@CommRingPshLocalizationMatching_cat K O U s)))
  (element : τ (Obj
      (@CommRingPshInvertibilityElements_cat K O U s)))
  : τ (@=
      (Obj (@Fibre_cat
        (@CommRingPshInvertibilityElements_cat K O U s)
        (@comm_ring_psh_localization_matching_catd K O U s)
        element))
      (@piapp0
        (@CommRingPshInvertibilityElements_cat K O U s)
        (@comm_ring_psh_localization_matching_catd K O U s)
        (@comm_ring_psh_localization_matching_section
          K O U s localization
          (@comm_ring_psh_localization_glue
            K O U s localization glue matching))
        element)
      (@piapp0
        (@CommRingPshInvertibilityElements_cat K O U s)
        (@comm_ring_psh_localization_matching_catd K O U s)
        matching element))
≔ (sigma_Snd (sigma_Snd glue)) matching element;

/*
  Literal Cartier computation.

  The preceding pointwise law specializes at `(V,f,member)`. The matching
  section beta already owns the left reduction to factor(glue(matching)); no
  glue-specific rewrite rule is introduced.
*/
symbol comm_ring_psh_localization_glue_at_member_path
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [V U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  (glue : τ (@CommRingPshLocalizationGlue K O U s localization))
  (matching : τ (Obj
      (@CommRingPshLocalizationMatching_cat K O U s)))
  (f : τ (Hom K V U))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f)))
  : τ (@=
      (@comm_ring_carrier (@comm_ring_psh_value K O V))
      (@comm_ring_hom_apply
        (@comm_ring_localization_target
          (@comm_ring_psh_value K O U) s localization)
        (@comm_ring_psh_value K O V)
        (@comm_ring_psh_localization_factor_map_at_member
          K O U s localization V f member)
        (@comm_ring_psh_localization_glue
          K O U s localization glue matching))
      (@piapp0
        (@CommRingPshInvertibilityElements_cat K O U s)
        (@comm_ring_psh_localization_matching_catd K O U s)
        matching
        (@comm_ring_psh_invertibility_element
          K O U s V f member)))
≔ @comm_ring_psh_localization_restrict_glue_component_path
    K O U s localization glue matching
    (@comm_ring_psh_invertibility_element K O U s V f member);
