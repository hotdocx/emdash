/*
  Maps of chain pairs as a middle arrow and two internal Hom factor points.

  The familiar two compatibilities are projections of those existing fibres.
  No square primitive, six-object diagram AST, or new computation rule.
*/
require open emdash.emdash3_2_chain_pair_data;
require open emdash.emdash3_2_hom_factor_composition;

// A middle map with its two triangular internal Hom factor points.
symbol ComputationalChainPairMap
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  : Grpd
≔ `Σ_ f : τ (Hom C B0 B1), @Product_grpd
  (@HomPostcompFactor C A1 B1 A0
    (@computational_chain_pair_dnext C S A1 B1 D1 p1)
    (@comp_fapp0 C A0 B0 B1 f
      (@computational_chain_pair_dnext C S A0 B0 D0 p0)))
  (@HomPrecompFactor C B0 D0 D1
    (@computational_chain_pair_d C S A0 B0 D0 p0)
    (@comp_fapp0 C B0 B1 D1
      (@computational_chain_pair_d C S A1 B1 D1 p1) f));

// Primary introduction: retain the actual two Hom-fibre points.
symbol computational_chain_pair_map_intro
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (f : τ (Hom C B0 B1))
  (upper : τ
      (@HomPostcompFactor C A1 B1 A0
        (@computational_chain_pair_dnext C S A1 B1 D1 p1)
        (@comp_fapp0 C A0 B0 B1 f
          (@computational_chain_pair_dnext C S A0 B0 D0 p0))))
  (lower : τ
      (@HomPrecompFactor C B0 D0 D1
        (@computational_chain_pair_d C S A0 B0 D0 p0)
        (@comp_fapp0 C B0 B1 D1
          (@computational_chain_pair_d C S A1 B1 D1 p1) f)))
  : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)
≔ @Struct_sigma (Hom C B0 B1)
    (λ f0 : τ (Hom C B0 B1), @Product_grpd
        (@HomPostcompFactor C A1 B1 A0
          (@computational_chain_pair_dnext C S A1 B1 D1 p1)
          (@comp_fapp0 C A0 B0 B1 f0
            (@computational_chain_pair_dnext C S A0 B0 D0 p0)))
        (@HomPrecompFactor C B0 D0 D1
          (@computational_chain_pair_d C S A0 B0 D0 p0)
          (@comp_fapp0 C B0 B1 D1
            (@computational_chain_pair_d C S A1 B1 D1 p1) f0)))
    f (Product_pair_grpd upper lower);

// The middle component.
symbol computational_chain_pair_map_middle
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  : τ (Hom C B0 B1)
≔ sigma_Fst F;

// The upper postcomposition factor point.
symbol computational_chain_pair_map_upper
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  : τ
    (@HomPostcompFactor C A1 B1 A0
      (@computational_chain_pair_dnext C S A1 B1 D1 p1)
      (@comp_fapp0 C A0 B0 B1
        (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F)
        (@computational_chain_pair_dnext C S A0 B0 D0 p0)))
≔ sigma_Fst (sigma_Snd F);

// The lower precomposition factor point.
symbol computational_chain_pair_map_lower
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  : τ
    (@HomPrecompFactor C B0 D0 D1
      (@computational_chain_pair_d C S A0 B0 D0 p0)
      (@comp_fapp0 C B0 B1 D1
        (@computational_chain_pair_d C S A1 B1 D1 p1)
        (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F)))
≔ sigma_Snd (sigma_Snd F);

// The upper component, projected from its factor point.
symbol computational_chain_pair_map_next
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  : τ (Hom C A0 A1)
≔ @hom_postcomp_factor_arrow C A1 B1 A0 (@computational_chain_pair_dnext C S A1 B1 D1 p1)
    (@comp_fapp0 C A0 B0 B1
        (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F)
        (@computational_chain_pair_dnext C S A0 B0 D0 p0))
      (@computational_chain_pair_map_upper C S A0 B0 D0 A1 B1 D1 p0 p1 F);

// The lower component, projected from its factor point.
symbol computational_chain_pair_map_prev
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  : τ (Hom C D0 D1)
≔ @hom_precomp_factor_arrow C B0 D0 D1 (@computational_chain_pair_d C S A0 B0 D0 p0)
    (@comp_fapp0 C B0 B1 D1
        (@computational_chain_pair_d C S A1 B1 D1 p1)
        (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F))
      (@computational_chain_pair_map_lower C S A0 B0 D0 A1 B1 D1 p0 p1 F);

// The upper compatibility is the existing factor reconstruction.
symbol computational_chain_pair_map_upper_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  : τ (@= (Hom C A0 B1)
      (@comp_fapp0 C A0 A1 B1
          (@computational_chain_pair_dnext C S A1 B1 D1 p1)
          (@computational_chain_pair_map_next C S A0 B0 D0 A1 B1 D1 p0 p1 F))
      (@comp_fapp0 C A0 B0 B1
          (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F)
          (@computational_chain_pair_dnext C S A0 B0 D0 p0)))
≔ @hom_postcomp_factor_path C A1 B1 A0 (@computational_chain_pair_dnext C S A1 B1 D1 p1)
    (@comp_fapp0 C A0 B0 B1
        (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F)
        (@computational_chain_pair_dnext C S A0 B0 D0 p0))
      (@computational_chain_pair_map_upper C S A0 B0 D0 A1 B1 D1 p0 p1 F);

// The lower compatibility is the existing factor reconstruction.
symbol computational_chain_pair_map_lower_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  : τ (@= (Hom C B0 D1)
      (@comp_fapp0 C B0 D0 D1
          (@computational_chain_pair_map_prev C S A0 B0 D0 A1 B1 D1 p0 p1 F)
          (@computational_chain_pair_d C S A0 B0 D0 p0))
      (@comp_fapp0 C B0 B1 D1
          (@computational_chain_pair_d C S A1 B1 D1 p1)
          (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F)))
≔ @hom_precomp_factor_path C B0 D0 D1 (@computational_chain_pair_d C S A0 B0 D0 p0)
    (@comp_fapp0 C B0 B1 D1
        (@computational_chain_pair_d C S A1 B1 D1 p1)
        (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F))
      (@computational_chain_pair_map_lower C S A0 B0 D0 A1 B1 D1 p0 p1 F);

// Conventional components/paths are a transparent usability constructor.
symbol computational_chain_pair_map_of_components
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (next : τ (Hom C A0 A1))
  (middle : τ (Hom C B0 B1))
  (prev : τ (Hom C D0 D1))
  (upper : τ (@= (Hom C A0 B1)
    (@comp_fapp0 C A0 A1 B1 (@computational_chain_pair_dnext C S A1 B1 D1 p1) next)
    (@comp_fapp0 C A0 B0 B1 middle (@computational_chain_pair_dnext C S A0 B0 D0 p0))))
  (lower : τ (@= (Hom C B0 D1)
    (@comp_fapp0 C B0 D0 D1 prev (@computational_chain_pair_d C S A0 B0 D0 p0))
    (@comp_fapp0 C B0 B1 D1 (@computational_chain_pair_d C S A1 B1 D1 p1) middle)))
  : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)
≔ @computational_chain_pair_map_intro C S A0 B0 D0 A1 B1 D1 p0 p1 middle
    (@hom_postcomp_factor_intro C A1 B1 A0 (@computational_chain_pair_dnext C S A1 B1 D1 p1)
      (@comp_fapp0 C A0 B0 B1 middle (@computational_chain_pair_dnext C S A0 B0 D0 p0)) next upper)
    (@hom_precomp_factor_intro C B0 D0 D1 (@computational_chain_pair_d C S A0 B0 D0 p0)
      (@comp_fapp0 C B0 B1 D1 (@computational_chain_pair_d C S A1 B1 D1 p1) middle) prev lower);
