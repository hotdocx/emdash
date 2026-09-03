/* Epimorphic local-cover criterion for computational exactness. */

require open emdash.emdash3_2_short_exact_sequences;

symbol ComputationalExactCoverWitness
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Abl : τ (@PreAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D))
  (T : τ (Obj C))
  (cone : τ (@WeakKernelAnnihilator C
    (@computational_homology_preadditive C P t Abl)
    B D
    (@computational_chain_pair_d C
      (@computational_homology_preadditive C P t Abl) A B D pair)
    T))
  : Grpd
≔ `Σ_ U : τ (Obj C),
   `Σ_ e : τ (Hom C U T),
   `Σ_ epic : τ (@IsEpic C U T e),
   `Σ_ a : τ (Hom C U A),
      @= (Hom C U B)
        (@comp_fapp0 C _ _ _
          (@computational_chain_pair_dnext C
            (@computational_homology_preadditive C P t Abl) A B D pair)
          a)
        (@comp_fapp0 C _ _ _
          (@weak_kernel_annihilator_arrow C
            (@computational_homology_preadditive C P t Abl)
            B D
            (@computational_chain_pair_d C
              (@computational_homology_preadditive C P t Abl) A B D pair)
            T cone)
          e);

symbol computational_exact_cover_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Abl : τ (@PreAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D)]
  [T : τ (Obj C)]
  [cone : τ (@WeakKernelAnnihilator C
    (@computational_homology_preadditive C P t Abl)
    B D
    (@computational_chain_pair_d C
      (@computational_homology_preadditive C P t Abl) A B D pair)
    T)]
  (cover : τ (@ComputationalExactCoverWitness C P t Abl
    A B D pair T cone))
  : τ (Obj C)
≔ sigma_Fst cover;

symbol computational_exact_cover_epimorphism
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Abl : τ (@PreAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D)]
  [T : τ (Obj C)]
  [cone : τ (@WeakKernelAnnihilator C
    (@computational_homology_preadditive C P t Abl)
    B D
    (@computational_chain_pair_d C
      (@computational_homology_preadditive C P t Abl) A B D pair)
    T)]
  (cover : τ (@ComputationalExactCoverWitness C P t Abl
    A B D pair T cone))
  : τ (Hom C
      (@computational_exact_cover_object C P t Abl
        A B D pair T cone cover)
      T)
≔ sigma_Fst (sigma_Snd cover);

symbol computational_exact_cover_is_epic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Abl : τ (@PreAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D)]
  [T : τ (Obj C)]
  [cone : τ (@WeakKernelAnnihilator C
    (@computational_homology_preadditive C P t Abl)
    B D
    (@computational_chain_pair_d C
      (@computational_homology_preadditive C P t Abl) A B D pair)
    T)]
  (cover : τ (@ComputationalExactCoverWitness C P t Abl
    A B D pair T cone))
  : τ (@IsEpic C
      (@computational_exact_cover_object C P t Abl
        A B D pair T cone cover)
      T
      (@computational_exact_cover_epimorphism C P t Abl
        A B D pair T cone cover))
≔ sigma_Fst (sigma_Snd (sigma_Snd cover));

symbol computational_exact_cover_factor
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Abl : τ (@PreAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D)]
  [T : τ (Obj C)]
  [cone : τ (@WeakKernelAnnihilator C
    (@computational_homology_preadditive C P t Abl)
    B D
    (@computational_chain_pair_d C
      (@computational_homology_preadditive C P t Abl) A B D pair)
    T)]
  (cover : τ (@ComputationalExactCoverWitness C P t Abl
    A B D pair T cone))
  : τ (Hom C
      (@computational_exact_cover_object C P t Abl
        A B D pair T cone cover)
      A)
≔ sigma_Fst (sigma_Snd (sigma_Snd (sigma_Snd cover)));

symbol computational_exact_cover_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Abl : τ (@PreAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D)]
  [T : τ (Obj C)]
  [cone : τ (@WeakKernelAnnihilator C
    (@computational_homology_preadditive C P t Abl)
    B D
    (@computational_chain_pair_d C
      (@computational_homology_preadditive C P t Abl) A B D pair)
    T)]
  (cover : τ (@ComputationalExactCoverWitness C P t Abl
    A B D pair T cone))
  : τ (@= (Hom C
      (@computational_exact_cover_object C P t Abl
        A B D pair T cone cover)
      B)
      (@comp_fapp0 C _ _ _
        (@computational_chain_pair_dnext C
          (@computational_homology_preadditive C P t Abl) A B D pair)
        (@computational_exact_cover_factor C P t Abl
          A B D pair T cone cover))
      (@comp_fapp0 C _ _ _
        (@weak_kernel_annihilator_arrow C
          (@computational_homology_preadditive C P t Abl)
          B D
          (@computational_chain_pair_d C
            (@computational_homology_preadditive C P t Abl) A B D pair)
          T cone)
        (@computational_exact_cover_epimorphism C P t Abl
          A B D pair T cone cover)))
≔ sigma_Snd (sigma_Snd (sigma_Snd (sigma_Snd cover)));

symbol HasComputationalExactCovers
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
      (@WeakKernelAnnihilator C
        (@computational_homology_preadditive C P t Abl)
        B D
        (@computational_chain_pair_d C
          (@computational_homology_preadditive C P t Abl) A B D pair)
        T)
      (λ cone : τ _,
        @ComputationalExactCoverWitness C P t Abl
          A B D pair T cone));

// If e = b o a is epic, then b is epic.
symbol is_epic_of_epic_factor
  [C : Cat]
  [U A B : τ (Obj C)]
  (a : τ (Hom C U A))
  (b : τ (Hom C A B))
  (e : τ (Hom C U B))
  (factor : τ (@= (Hom C U B)
    (@comp_fapp0 C _ _ _ b a) e))
  (epic : τ (@IsEpic C U B e))
  : τ (@IsEpic C A B b)
≔ λ T : τ (Obj C),
   λ u : τ (Hom C B T),
   λ v : τ (Hom C B T),
   λ p : τ (@= (Hom C A T)
      (@comp_fapp0 C _ _ _ u b)
      (@comp_fapp0 C _ _ _ v b)),
     epic T u v
       (@eq_trans _ _ _ _
         (@eq_ap
           (Hom C U B) (Hom C U T)
           (λ h : τ (Hom C U B), @comp_fapp0 C _ _ _ u h)
           _ _ (@eq_sym _ _ _ factor))
         (@eq_trans _ _ _ _
           (@comp_assoc C _ _ _ _ u b a)
           (@eq_trans _ _ _ _
             (@eq_ap
               (Hom C A T) (Hom C U T)
               (λ h : τ (Hom C A T), @comp_fapp0 C _ _ _ h a)
               _ _ p)
             (@eq_trans _ _ _ _
               (@eq_sym _ _ _ (@comp_assoc C _ _ _ _ v b a))
               (@eq_ap
                 (Hom C U B) (Hom C U T)
                 (λ h : τ (Hom C U B), @comp_fapp0 C _ _ _ v h)
                 _ _ factor)))));

symbol identity_is_epic
  [C : Cat]
  [X : τ (Obj C)]
  : τ (@IsEpic C X X (@id C X))
≔ λ T : τ (Obj C),
   λ u : τ (Hom C X T),
   λ v : τ (Hom C X T),
   λ p : τ (@= (Hom C X T)
     (@comp_fapp0 C _ _ _ u (@id C X))
     (@comp_fapp0 C _ _ _ v (@id C X))), p;

// Epicity is transported along an explicit arrow path.
symbol is_epic_of_equal
  [C : Cat]
  [X Y : τ (Obj C)]
  (f g : τ (Hom C X Y))
  (path : τ (@= (Hom C X Y) f g))
  (epic : τ (@IsEpic C X Y g))
  : τ (@IsEpic C X Y f)
≔ λ T : τ (Obj C),
   λ u : τ (Hom C Y T),
   λ v : τ (Hom C Y T),
   λ p : τ (@= (Hom C X T)
      (@comp_fapp0 C _ _ _ u f)
      (@comp_fapp0 C _ _ _ v f)),
     epic T u v
       (@eq_trans _ _ _ _
         (@eq_sym _ _ _
           (@eq_ap (Hom C X Y) (Hom C X T)
             (λ h : τ (Hom C X Y), @comp_fapp0 C _ _ _ u h)
             _ _ path))
         (@eq_trans _ _ _ _ p
           (@eq_ap (Hom C X Y) (Hom C X T)
             (λ h : τ (Hom C X Y), @comp_fapp0 C _ _ _ v h)
             _ _ path)));
