/* Monomorphic local-extension criterion for computational exactness. */

require open emdash.emdash3_2_exactness_covers;

symbol ComputationalExactExtensionWitness
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Abl : τ (@PreAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D))
  (T : τ (Obj C))
  (cocone : τ (@CokernelCoannihilator C
    (@computational_homology_preadditive C P t Abl)
    A B
    (@computational_chain_pair_dnext C
      (@computational_homology_preadditive C P t Abl) A B D pair)
    T))
  : Grpd
≔ `Σ_ U : τ (Obj C),
   `Σ_ m : τ (Hom C T U),
   `Σ_ monic : τ (@IsMonic C T U m),
   `Σ_ d : τ (Hom C D U),
      @= (Hom C B U)
        (@comp_fapp0 C _ _ _ m
          (@cokernel_coannihilator_arrow C
            (@computational_homology_preadditive C P t Abl)
            A B
            (@computational_chain_pair_dnext C
              (@computational_homology_preadditive C P t Abl) A B D pair)
            T cocone))
        (@comp_fapp0 C _ _ _ d
          (@computational_chain_pair_d C
            (@computational_homology_preadditive C P t Abl) A B D pair));

symbol computational_exact_extension_intro
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Abl : τ (@PreAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D)]
  [T : τ (Obj C)]
  [cocone : τ (@CokernelCoannihilator C
    (@computational_homology_preadditive C P t Abl)
    A B
    (@computational_chain_pair_dnext C
      (@computational_homology_preadditive C P t Abl) A B D pair)
    T)]
  (U : τ (Obj C))
  (m : τ (Hom C T U))
  (monic : τ (@IsMonic C T U m))
  (d : τ (Hom C D U))
  (path : τ (@= (Hom C B U)
    (@comp_fapp0 C _ _ _ m
      (@cokernel_coannihilator_arrow C
        (@computational_homology_preadditive C P t Abl)
        A B
        (@computational_chain_pair_dnext C
          (@computational_homology_preadditive C P t Abl) A B D pair)
        T cocone))
    (@comp_fapp0 C _ _ _ d
      (@computational_chain_pair_d C
        (@computational_homology_preadditive C P t Abl) A B D pair))))
  : τ (@ComputationalExactExtensionWitness C P t Abl
      A B D pair T cocone)
≔ @Struct_sigma
    (Obj C)
    (λ U0 : τ (Obj C),
      `Σ_ m0 : τ (Hom C T U0),
      `Σ_ monic0 : τ (@IsMonic C T U0 m0),
      `Σ_ d0 : τ (Hom C D U0),
        @= (Hom C B U0)
          (@comp_fapp0 C _ _ _ m0
            (@cokernel_coannihilator_arrow C
              (@computational_homology_preadditive C P t Abl)
              A B
              (@computational_chain_pair_dnext C
                (@computational_homology_preadditive C P t Abl) A B D pair)
              T cocone))
          (@comp_fapp0 C _ _ _ d0
            (@computational_chain_pair_d C
              (@computational_homology_preadditive C P t Abl) A B D pair)))
    U
    (@Struct_sigma
      (Hom C T U)
      (λ m0 : τ (Hom C T U),
        `Σ_ monic0 : τ (@IsMonic C T U m0),
        `Σ_ d0 : τ (Hom C D U),
          @= (Hom C B U)
            (@comp_fapp0 C _ _ _ m0
              (@cokernel_coannihilator_arrow C
                (@computational_homology_preadditive C P t Abl)
                A B
                (@computational_chain_pair_dnext C
                  (@computational_homology_preadditive C P t Abl) A B D pair)
                T cocone))
            (@comp_fapp0 C _ _ _ d0
              (@computational_chain_pair_d C
                (@computational_homology_preadditive C P t Abl) A B D pair)))
      m
      (@Struct_sigma
        (@IsMonic C T U m)
        (λ _ : τ _,
          `Σ_ d0 : τ (Hom C D U),
            @= (Hom C B U)
              (@comp_fapp0 C _ _ _ m
                (@cokernel_coannihilator_arrow C
                  (@computational_homology_preadditive C P t Abl)
                  A B
                  (@computational_chain_pair_dnext C
                    (@computational_homology_preadditive C P t Abl)
                    A B D pair)
                  T cocone))
              (@comp_fapp0 C _ _ _ d0
                (@computational_chain_pair_d C
                  (@computational_homology_preadditive C P t Abl)
                  A B D pair)))
        monic
        (@Struct_sigma
          (Hom C D U)
          (λ d0 : τ (Hom C D U),
            @= (Hom C B U)
              (@comp_fapp0 C _ _ _ m
                (@cokernel_coannihilator_arrow C
                  (@computational_homology_preadditive C P t Abl)
                  A B
                  (@computational_chain_pair_dnext C
                    (@computational_homology_preadditive C P t Abl)
                    A B D pair)
                  T cocone))
              (@comp_fapp0 C _ _ _ d0
                (@computational_chain_pair_d C
                  (@computational_homology_preadditive C P t Abl)
                  A B D pair)))
          d path)));

symbol computational_exact_extension_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Abl : τ (@PreAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D)]
  [T : τ (Obj C)]
  [cocone : τ (@CokernelCoannihilator C
    (@computational_homology_preadditive C P t Abl)
    A B
    (@computational_chain_pair_dnext C
      (@computational_homology_preadditive C P t Abl) A B D pair)
    T)]
  (extension : τ (@ComputationalExactExtensionWitness C P t Abl
    A B D pair T cocone))
  : τ (Obj C)
≔ sigma_Fst extension;

symbol computational_exact_extension_monomorphism
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Abl : τ (@PreAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D)]
  [T : τ (Obj C)]
  [cocone : τ (@CokernelCoannihilator C
    (@computational_homology_preadditive C P t Abl)
    A B
    (@computational_chain_pair_dnext C
      (@computational_homology_preadditive C P t Abl) A B D pair)
    T)]
  (extension : τ (@ComputationalExactExtensionWitness C P t Abl
    A B D pair T cocone))
  : τ (Hom C T
      (@computational_exact_extension_object C P t Abl
        A B D pair T cocone extension))
≔ sigma_Fst (sigma_Snd extension);

symbol computational_exact_extension_is_monic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Abl : τ (@PreAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D)]
  [T : τ (Obj C)]
  [cocone : τ (@CokernelCoannihilator C
    (@computational_homology_preadditive C P t Abl)
    A B
    (@computational_chain_pair_dnext C
      (@computational_homology_preadditive C P t Abl) A B D pair)
    T)]
  (extension : τ (@ComputationalExactExtensionWitness C P t Abl
    A B D pair T cocone))
  : τ (@IsMonic C T
      (@computational_exact_extension_object C P t Abl
        A B D pair T cocone extension)
      (@computational_exact_extension_monomorphism C P t Abl
        A B D pair T cocone extension))
≔ sigma_Fst (sigma_Snd (sigma_Snd extension));

symbol computational_exact_extension_factor
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Abl : τ (@PreAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D)]
  [T : τ (Obj C)]
  [cocone : τ (@CokernelCoannihilator C
    (@computational_homology_preadditive C P t Abl)
    A B
    (@computational_chain_pair_dnext C
      (@computational_homology_preadditive C P t Abl) A B D pair)
    T)]
  (extension : τ (@ComputationalExactExtensionWitness C P t Abl
    A B D pair T cocone))
  : τ (Hom C D
      (@computational_exact_extension_object C P t Abl
        A B D pair T cocone extension))
≔ sigma_Fst (sigma_Snd (sigma_Snd (sigma_Snd extension)));

symbol computational_exact_extension_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Abl : τ (@PreAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D)]
  [T : τ (Obj C)]
  [cocone : τ (@CokernelCoannihilator C
    (@computational_homology_preadditive C P t Abl)
    A B
    (@computational_chain_pair_dnext C
      (@computational_homology_preadditive C P t Abl) A B D pair)
    T)]
  (extension : τ (@ComputationalExactExtensionWitness C P t Abl
    A B D pair T cocone))
  : τ (@= (Hom C B
      (@computational_exact_extension_object C P t Abl
        A B D pair T cocone extension))
      (@comp_fapp0 C _ _ _
        (@computational_exact_extension_monomorphism C P t Abl
          A B D pair T cocone extension)
        (@cokernel_coannihilator_arrow C
          (@computational_homology_preadditive C P t Abl)
          A B
          (@computational_chain_pair_dnext C
            (@computational_homology_preadditive C P t Abl) A B D pair)
          T cocone))
      (@comp_fapp0 C _ _ _
        (@computational_exact_extension_factor C P t Abl
          A B D pair T cocone extension)
        (@computational_chain_pair_d C
          (@computational_homology_preadditive C P t Abl) A B D pair)))
≔ sigma_Snd (sigma_Snd (sigma_Snd (sigma_Snd extension)));

symbol HasComputationalExactExtensions
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Abl : τ (@PreAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D))
  : Grpd
≔ @Pi_grpd (Obj C) (λ T : τ (Obj C),
    @Pi_grpd
      (@CokernelCoannihilator C
        (@computational_homology_preadditive C P t Abl)
        A B
        (@computational_chain_pair_dnext C
          (@computational_homology_preadditive C P t Abl) A B D pair)
        T)
      (λ cocone : τ _,
        @ComputationalExactExtensionWitness C P t Abl
          A B D pair T cocone));

// Monicity is transported along an explicit arrow path.
symbol is_monic_of_equal
  [C : Cat]
  [X Y : τ (Obj C)]
  (f g : τ (Hom C X Y))
  (path : τ (@= (Hom C X Y) f g))
  (monic : τ (@IsMonic C X Y g))
  : τ (@IsMonic C X Y f)
≔ λ T : τ (Obj C),
   λ u : τ (Hom C T X),
   λ v : τ (Hom C T X),
   λ p : τ (@= (Hom C T Y)
      (@comp_fapp0 C _ _ _ f u)
      (@comp_fapp0 C _ _ _ f v)),
     monic T u v
       (@eq_trans _ _ _ _
         (@eq_sym _ _ _
           (@eq_ap (Hom C X Y) (Hom C T Y)
             (λ h : τ (Hom C X Y), @comp_fapp0 C _ _ _ h u)
             _ _ path))
         (@eq_trans _ _ _ _ p
           (@eq_ap (Hom C X Y) (Hom C T Y)
             (λ h : τ (Hom C X Y), @comp_fapp0 C _ _ _ h v)
             _ _ path)));
