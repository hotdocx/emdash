/*
  Whole bounded Freyd chain maps over the existing recursive complex owners.

  Every component is a raw presentation morphism; every square is the existing
  presentation-morphism agreement. The tail follows the actual two complex
  tails. No new square primitive, quotient decoder, rule, or unifier.
*/

require open emdash.emdash3_2_commutative_algebra_freyd_bounded_complexes;

// Readable alias for precisely one of the two existing homology-map laws.
symbol CommRingFreydChainMapSquare
  [R : τ CommRing]
  [S0 S1 T0 T1 : τ (@CommRingPresentation R)]
  (sd : τ (@CommRingPresentationMorphism R S1 S0))
  (td : τ (@CommRingPresentationMorphism R T1 T0))
  (f0 : τ (@CommRingPresentationMorphism R S0 T0))
  (f1 : τ (@CommRingPresentationMorphism R S1 T1))
  : Grpd
≔ @CommRingPresentationMorphismAgreement R S1 T0
    (@comm_ring_presentation_morphism_map R S1 T0
      (@comm_ring_presentation_morphism_comp R S1 T1 T0 td f1))
    (@comm_ring_presentation_morphism_map R S1 T0
      (@comm_ring_presentation_morphism_comp R S1 S0 T0 f0 sd));

// Tail over the actual two complex tails, indexed by the current component.
symbol CommRingFreydChainMapTail
  (R : τ CommRing)
  (length : τ Nat_grpd)
  (sourceBelow sourceCurrent : τ (@CommRingPresentation R))
  (sourceBoundary : τ (@CommRingPresentationMorphism R sourceCurrent sourceBelow))
  (sourceTail : τ (@CommRingFreydChainTail R
      length sourceBelow sourceCurrent sourceBoundary))
  (targetBelow targetCurrent : τ (@CommRingPresentation R))
  (targetBoundary : τ (@CommRingPresentationMorphism R targetCurrent targetBelow))
  (targetTail : τ (@CommRingFreydChainTail R
      length targetBelow targetCurrent targetBoundary))
  (currentMap : τ (@CommRingPresentationMorphism R sourceCurrent targetCurrent))
  : Grpd
≔ (@nat_elim
    (λ length0 : τ Nat_grpd,
      @Pi_grpd (@CommRingPresentation R)
        (λ sourceBelow0 : τ (@CommRingPresentation R),
          @Pi_grpd (@CommRingPresentation R)
            (λ sourceCurrent0 : τ (@CommRingPresentation R),
              @Pi_grpd
                (@CommRingPresentationMorphism R sourceCurrent0 sourceBelow0)
                (λ sourceBoundary0 : τ (@CommRingPresentationMorphism R sourceCurrent0 sourceBelow0),
                  @Pi_grpd
                    (@CommRingFreydChainTail R length0
                      sourceBelow0 sourceCurrent0 sourceBoundary0)
                    (λ _ : τ (@CommRingFreydChainTail R length0
                        sourceBelow0 sourceCurrent0 sourceBoundary0),
                      @Pi_grpd (@CommRingPresentation R)
                        (λ targetBelow0 : τ (@CommRingPresentation R),
                          @Pi_grpd (@CommRingPresentation R)
                            (λ targetCurrent0 : τ (@CommRingPresentation R),
                              @Pi_grpd
                                (@CommRingPresentationMorphism R targetCurrent0 targetBelow0)
                                (λ targetBoundary0 : τ (@CommRingPresentationMorphism R targetCurrent0 targetBelow0),
                                  @Pi_grpd
                                    (@CommRingFreydChainTail R length0
                                      targetBelow0 targetCurrent0
                                      targetBoundary0)
                                    (λ _ : τ (@CommRingFreydChainTail R length0
                                        targetBelow0 targetCurrent0
                                        targetBoundary0),
                                      @Function_grpd
                                        (@CommRingPresentationMorphism R sourceCurrent0 targetCurrent0)
                                        Grpd_grpd)))))))))
    (λ sourceBelow0 : τ (@CommRingPresentation R),
      λ sourceCurrent0 : τ (@CommRingPresentation R),
      λ sourceBoundary0 : τ (@CommRingPresentationMorphism R sourceCurrent0 sourceBelow0),
      λ _ : τ (@CommRingFreydChainTail R zero
        sourceBelow0 sourceCurrent0 sourceBoundary0),
      λ targetBelow0 : τ (@CommRingPresentation R),
      λ targetCurrent0 : τ (@CommRingPresentation R),
      λ targetBoundary0 : τ (@CommRingPresentationMorphism R targetCurrent0 targetBelow0),
      λ _ : τ (@CommRingFreydChainTail R zero
        targetBelow0 targetCurrent0 targetBoundary0),
      λ _ : τ (@CommRingPresentationMorphism R sourceCurrent0 targetCurrent0),
        Unit_grpd)
    (λ length0 : τ Nat_grpd,
      λ rec,
      λ sourceBelow0 : τ (@CommRingPresentation R),
      λ sourceCurrent0 : τ (@CommRingPresentation R),
      λ sourceBoundary0 : τ (@CommRingPresentationMorphism R sourceCurrent0 sourceBelow0),
      λ sourceTail0 : τ (@CommRingFreydChainTail R (succ length0)
        sourceBelow0 sourceCurrent0 sourceBoundary0),
      λ targetBelow0 : τ (@CommRingPresentation R),
      λ targetCurrent0 : τ (@CommRingPresentation R),
      λ targetBoundary0 : τ (@CommRingPresentationMorphism R targetCurrent0 targetBelow0),
      λ targetTail0 : τ (@CommRingFreydChainTail R (succ length0)
        targetBelow0 targetCurrent0 targetBoundary0),
      λ currentMap0 : τ (@CommRingPresentationMorphism R sourceCurrent0 targetCurrent0),
        `Σ_ nextMap : τ (@CommRingPresentationMorphism R
            (@comm_ring_freyd_chain_tail_next R length0 sourceBelow0 sourceCurrent0 sourceBoundary0 sourceTail0)
            (@comm_ring_freyd_chain_tail_next R length0 targetBelow0 targetCurrent0 targetBoundary0 targetTail0)),
          @Product_grpd
            (@CommRingFreydChainMapSquare R
              sourceCurrent0
              (@comm_ring_freyd_chain_tail_next R
                length0 sourceBelow0 sourceCurrent0
                sourceBoundary0 sourceTail0)
              targetCurrent0
              (@comm_ring_freyd_chain_tail_next R
                length0 targetBelow0 targetCurrent0
                targetBoundary0 targetTail0)
              (@comm_ring_freyd_chain_tail_differential R
                length0 sourceBelow0 sourceCurrent0
                sourceBoundary0 sourceTail0)
              (@comm_ring_freyd_chain_tail_differential R
                length0 targetBelow0 targetCurrent0
                targetBoundary0 targetTail0)
              currentMap0 nextMap)
            (rec
              sourceCurrent0
              (@comm_ring_freyd_chain_tail_next R
                length0 sourceBelow0 sourceCurrent0
                sourceBoundary0 sourceTail0)
              (@comm_ring_freyd_chain_tail_differential R
                length0 sourceBelow0 sourceCurrent0
                sourceBoundary0 sourceTail0)
              (@comm_ring_freyd_chain_tail_rest R
                length0 sourceBelow0 sourceCurrent0
                sourceBoundary0 sourceTail0)
              targetCurrent0
              (@comm_ring_freyd_chain_tail_next R
                length0 targetBelow0 targetCurrent0
                targetBoundary0 targetTail0)
              (@comm_ring_freyd_chain_tail_differential R
                length0 targetBelow0 targetCurrent0
                targetBoundary0 targetTail0)
              (@comm_ring_freyd_chain_tail_rest R
                length0 targetBelow0 targetCurrent0
                targetBoundary0 targetTail0)
              nextMap))
    length)
    sourceBelow sourceCurrent sourceBoundary sourceTail
    targetBelow targetCurrent targetBoundary targetTail
    currentMap;

// No remaining degree: the map tail is the existing unit point.
symbol comm_ring_freyd_chain_map_tail_nil
  [R : τ CommRing]
  [sourceBelow sourceCurrent : τ (@CommRingPresentation R)]
  [sourceBoundary : τ (@CommRingPresentationMorphism R sourceCurrent sourceBelow)]
  [sourceTail : τ (@CommRingFreydChainTail R
      zero sourceBelow sourceCurrent sourceBoundary)]
  [targetBelow targetCurrent : τ (@CommRingPresentation R)]
  [targetBoundary : τ (@CommRingPresentationMorphism R targetCurrent targetBelow)]
  [targetTail : τ (@CommRingFreydChainTail R
      zero targetBelow targetCurrent targetBoundary)]
  [currentMap : τ (@CommRingPresentationMorphism R sourceCurrent targetCurrent)]
  : τ (@CommRingFreydChainMapTail R zero
      sourceBelow sourceCurrent sourceBoundary sourceTail
      targetBelow targetCurrent targetBoundary targetTail
      currentMap)
≔ tt;

// Retain the next component, its agreement, and the remaining map tail.
symbol comm_ring_freyd_chain_map_tail_cons
  [R : τ CommRing]
  [length : τ Nat_grpd]
  [sourceBelow sourceCurrent : τ (@CommRingPresentation R)]
  [sourceBoundary : τ (@CommRingPresentationMorphism R sourceCurrent sourceBelow)]
  [sourceTail : τ (@CommRingFreydChainTail R
      (succ length) sourceBelow sourceCurrent sourceBoundary)]
  [targetBelow targetCurrent : τ (@CommRingPresentation R)]
  [targetBoundary : τ (@CommRingPresentationMorphism R targetCurrent targetBelow)]
  [targetTail : τ (@CommRingFreydChainTail R
      (succ length) targetBelow targetCurrent targetBoundary)]
  [currentMap : τ (@CommRingPresentationMorphism R sourceCurrent targetCurrent)]
  (nextMap : τ (@CommRingPresentationMorphism R
      (@comm_ring_freyd_chain_tail_next R length sourceBelow sourceCurrent sourceBoundary sourceTail)
      (@comm_ring_freyd_chain_tail_next R length targetBelow targetCurrent targetBoundary targetTail)))
  (law : τ (@CommRingFreydChainMapSquare R
      sourceCurrent
      (@comm_ring_freyd_chain_tail_next R
        length sourceBelow sourceCurrent sourceBoundary sourceTail)
      targetCurrent
      (@comm_ring_freyd_chain_tail_next R
        length targetBelow targetCurrent targetBoundary targetTail)
      (@comm_ring_freyd_chain_tail_differential R
        length sourceBelow sourceCurrent sourceBoundary sourceTail)
      (@comm_ring_freyd_chain_tail_differential R
        length targetBelow targetCurrent targetBoundary targetTail)
      currentMap nextMap))
  (rest : τ (@CommRingFreydChainMapTail R length
      sourceCurrent
      (@comm_ring_freyd_chain_tail_next R
        length sourceBelow sourceCurrent sourceBoundary sourceTail)
      (@comm_ring_freyd_chain_tail_differential R
        length sourceBelow sourceCurrent sourceBoundary sourceTail)
      (@comm_ring_freyd_chain_tail_rest R
        length sourceBelow sourceCurrent sourceBoundary sourceTail)
      targetCurrent
      (@comm_ring_freyd_chain_tail_next R
        length targetBelow targetCurrent targetBoundary targetTail)
      (@comm_ring_freyd_chain_tail_differential R
        length targetBelow targetCurrent targetBoundary targetTail)
      (@comm_ring_freyd_chain_tail_rest R
        length targetBelow targetCurrent targetBoundary targetTail)
      nextMap))
  : τ (@CommRingFreydChainMapTail R (succ length)
      sourceBelow sourceCurrent sourceBoundary sourceTail
      targetBelow targetCurrent targetBoundary targetTail
      currentMap)
≔ Struct_sigma nextMap (Product_pair_grpd law rest);

// Observe the retained next component.
symbol comm_ring_freyd_chain_map_tail_next_map
  [R : τ CommRing]
  [length : τ Nat_grpd]
  [sourceBelow sourceCurrent : τ (@CommRingPresentation R)]
  [sourceBoundary : τ (@CommRingPresentationMorphism R sourceCurrent sourceBelow)]
  [sourceTail : τ (@CommRingFreydChainTail R
      (succ length) sourceBelow sourceCurrent sourceBoundary)]
  [targetBelow targetCurrent : τ (@CommRingPresentation R)]
  [targetBoundary : τ (@CommRingPresentationMorphism R targetCurrent targetBelow)]
  [targetTail : τ (@CommRingFreydChainTail R
      (succ length) targetBelow targetCurrent targetBoundary)]
  [currentMap : τ (@CommRingPresentationMorphism R sourceCurrent targetCurrent)]
  (mapTail : τ (@CommRingFreydChainMapTail R (succ length)
      sourceBelow sourceCurrent sourceBoundary sourceTail
      targetBelow targetCurrent targetBoundary targetTail currentMap))
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_freyd_chain_tail_next R length sourceBelow sourceCurrent sourceBoundary sourceTail)
      (@comm_ring_freyd_chain_tail_next R length targetBelow targetCurrent targetBoundary targetTail))
≔ sigma_Fst mapTail;

// Observe its presentation-morphism agreement, at the actual differentials.
symbol comm_ring_freyd_chain_map_tail_law
  [R : τ CommRing]
  [length : τ Nat_grpd]
  [sourceBelow sourceCurrent : τ (@CommRingPresentation R)]
  [sourceBoundary : τ (@CommRingPresentationMorphism R sourceCurrent sourceBelow)]
  [sourceTail : τ (@CommRingFreydChainTail R
      (succ length) sourceBelow sourceCurrent sourceBoundary)]
  [targetBelow targetCurrent : τ (@CommRingPresentation R)]
  [targetBoundary : τ (@CommRingPresentationMorphism R targetCurrent targetBelow)]
  [targetTail : τ (@CommRingFreydChainTail R
      (succ length) targetBelow targetCurrent targetBoundary)]
  [currentMap : τ (@CommRingPresentationMorphism R sourceCurrent targetCurrent)]
  (mapTail : τ (@CommRingFreydChainMapTail R (succ length)
      sourceBelow sourceCurrent sourceBoundary sourceTail
      targetBelow targetCurrent targetBoundary targetTail currentMap))
  : τ (@CommRingFreydChainMapSquare R
      sourceCurrent
      (@comm_ring_freyd_chain_tail_next R
        length sourceBelow sourceCurrent sourceBoundary sourceTail)
      targetCurrent
      (@comm_ring_freyd_chain_tail_next R
        length targetBelow targetCurrent targetBoundary targetTail)
      (@comm_ring_freyd_chain_tail_differential R
        length sourceBelow sourceCurrent sourceBoundary sourceTail)
      (@comm_ring_freyd_chain_tail_differential R
        length targetBelow targetCurrent targetBoundary targetTail)
      currentMap
      (@comm_ring_freyd_chain_map_tail_next_map R length
        sourceBelow sourceCurrent sourceBoundary sourceTail
        targetBelow targetCurrent targetBoundary targetTail
        currentMap mapTail))
≔ sigma_Fst (sigma_Snd mapTail);

// Continue with both projected complex tails and the retained next component.
symbol comm_ring_freyd_chain_map_tail_rest
  [R : τ CommRing]
  [length : τ Nat_grpd]
  [sourceBelow sourceCurrent : τ (@CommRingPresentation R)]
  [sourceBoundary : τ (@CommRingPresentationMorphism R sourceCurrent sourceBelow)]
  [sourceTail : τ (@CommRingFreydChainTail R
      (succ length) sourceBelow sourceCurrent sourceBoundary)]
  [targetBelow targetCurrent : τ (@CommRingPresentation R)]
  [targetBoundary : τ (@CommRingPresentationMorphism R targetCurrent targetBelow)]
  [targetTail : τ (@CommRingFreydChainTail R
      (succ length) targetBelow targetCurrent targetBoundary)]
  [currentMap : τ (@CommRingPresentationMorphism R sourceCurrent targetCurrent)]
  (mapTail : τ (@CommRingFreydChainMapTail R (succ length)
      sourceBelow sourceCurrent sourceBoundary sourceTail
      targetBelow targetCurrent targetBoundary targetTail currentMap))
  : τ (@CommRingFreydChainMapTail R length
      sourceCurrent
      (@comm_ring_freyd_chain_tail_next R
        length sourceBelow sourceCurrent sourceBoundary sourceTail)
      (@comm_ring_freyd_chain_tail_differential R
        length sourceBelow sourceCurrent sourceBoundary sourceTail)
      (@comm_ring_freyd_chain_tail_rest R
        length sourceBelow sourceCurrent sourceBoundary sourceTail)
      targetCurrent
      (@comm_ring_freyd_chain_tail_next R
        length targetBelow targetCurrent targetBoundary targetTail)
      (@comm_ring_freyd_chain_tail_differential R
        length targetBelow targetCurrent targetBoundary targetTail)
      (@comm_ring_freyd_chain_tail_rest R
        length targetBelow targetCurrent targetBoundary targetTail)
      (@comm_ring_freyd_chain_map_tail_next_map R length
        sourceBelow sourceCurrent sourceBoundary sourceTail
        targetBelow targetCurrent targetBoundary targetTail
        currentMap mapTail))
≔ sigma_Snd (sigma_Snd mapTail);

// Whole map: one component in length zero; two components and a tail otherwise.
symbol CommRingFreydBoundedChainMap
  (R : τ CommRing)
  (length : τ Nat_grpd)
  (source target : τ (@CommRingFreydBoundedComplex R length))
  : Grpd
≔ (@nat_elim
    (λ length0 : τ Nat_grpd,
      @Pi_grpd (@CommRingFreydBoundedComplex R length0)
        (λ _ : τ (@CommRingFreydBoundedComplex R length0),
          @Function_grpd
            (@CommRingFreydBoundedComplex R length0)
            Grpd_grpd))
    (λ source0 : τ (@CommRingFreydBoundedComplex R zero),
      λ target0 : τ (@CommRingFreydBoundedComplex R zero),
        @CommRingPresentationMorphism R source0 target0)
    (λ tailLength : τ Nat_grpd,
      λ _,
      λ source0 : τ (@CommRingFreydBoundedComplex R (succ tailLength)),
      λ target0 : τ (@CommRingFreydBoundedComplex R (succ tailLength)),
        `Σ_ F0 : τ (@CommRingPresentationMorphism R
            (@comm_ring_freyd_bounded_complex_P0 R tailLength source0)
            (@comm_ring_freyd_bounded_complex_P0 R tailLength target0)),
          `Σ_ F1 : τ (@CommRingPresentationMorphism R
              (@comm_ring_freyd_bounded_complex_P1 R tailLength source0)
              (@comm_ring_freyd_bounded_complex_P1 R tailLength target0)),
            @Product_grpd
              (@CommRingFreydChainMapSquare R
                (@comm_ring_freyd_bounded_complex_P0 R tailLength source0)
                (@comm_ring_freyd_bounded_complex_P1 R tailLength source0)
                (@comm_ring_freyd_bounded_complex_P0 R tailLength target0)
                (@comm_ring_freyd_bounded_complex_P1 R tailLength target0)
                (@comm_ring_freyd_bounded_complex_d1 R tailLength source0)
                (@comm_ring_freyd_bounded_complex_d1 R tailLength target0)
                F0 F1)
              (@CommRingFreydChainMapTail R tailLength
                (@comm_ring_freyd_bounded_complex_P0 R tailLength source0)
                (@comm_ring_freyd_bounded_complex_P1 R tailLength source0)
                (@comm_ring_freyd_bounded_complex_d1 R tailLength source0)
                (@comm_ring_freyd_bounded_complex_tail R tailLength source0)
                (@comm_ring_freyd_bounded_complex_P0 R tailLength target0)
                (@comm_ring_freyd_bounded_complex_P1 R tailLength target0)
                (@comm_ring_freyd_bounded_complex_d1 R tailLength target0)
                (@comm_ring_freyd_bounded_complex_tail R tailLength target0)
                F1))
    length) source target;

// A map between length-zero complexes is an ordinary raw presentation morphism.
symbol comm_ring_freyd_bounded_chain_map_zero
  [R : τ CommRing]
  [source target : τ (@CommRingPresentation R)]
  (F0 : τ (@CommRingPresentationMorphism R source target))
  : τ (@CommRingFreydBoundedChainMap R zero source target)
≔ F0;

// Assemble a positive-length map without reconstructing its input complexes.
symbol comm_ring_freyd_bounded_chain_map_succ
  [R : τ CommRing]
  [tailLength : τ Nat_grpd]
  [source target : τ (@CommRingFreydBoundedComplex R (succ tailLength))]
  (F0 : τ (@CommRingPresentationMorphism R
      (@comm_ring_freyd_bounded_complex_P0 R tailLength source)
      (@comm_ring_freyd_bounded_complex_P0 R tailLength target)))
  (F1 : τ (@CommRingPresentationMorphism R
      (@comm_ring_freyd_bounded_complex_P1 R tailLength source)
      (@comm_ring_freyd_bounded_complex_P1 R tailLength target)))
  (law : τ (@CommRingFreydChainMapSquare R
      (@comm_ring_freyd_bounded_complex_P0 R tailLength source)
      (@comm_ring_freyd_bounded_complex_P1 R tailLength source)
      (@comm_ring_freyd_bounded_complex_P0 R tailLength target)
      (@comm_ring_freyd_bounded_complex_P1 R tailLength target)
      (@comm_ring_freyd_bounded_complex_d1 R tailLength source)
      (@comm_ring_freyd_bounded_complex_d1 R tailLength target)
      F0 F1))
  (tail : τ (@CommRingFreydChainMapTail R tailLength
      (@comm_ring_freyd_bounded_complex_P0 R tailLength source)
      (@comm_ring_freyd_bounded_complex_P1 R tailLength source)
      (@comm_ring_freyd_bounded_complex_d1 R tailLength source)
      (@comm_ring_freyd_bounded_complex_tail R tailLength source)
      (@comm_ring_freyd_bounded_complex_P0 R tailLength target)
      (@comm_ring_freyd_bounded_complex_P1 R tailLength target)
      (@comm_ring_freyd_bounded_complex_d1 R tailLength target)
      (@comm_ring_freyd_bounded_complex_tail R tailLength target)
      F1))
  : τ (@CommRingFreydBoundedChainMap R
      (succ tailLength) source target)
≔ Struct_sigma F0 (Struct_sigma F1 (Product_pair_grpd law tail));

// Degree-zero component.
symbol comm_ring_freyd_bounded_chain_map_F0
  [R : τ CommRing]
  [tailLength : τ Nat_grpd]
  [source target : τ (@CommRingFreydBoundedComplex R (succ tailLength))]
  (f : τ (@CommRingFreydBoundedChainMap R
      (succ tailLength) source target))
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_freyd_bounded_complex_P0 R tailLength source)
      (@comm_ring_freyd_bounded_complex_P0 R tailLength target))
≔ sigma_Fst f;

// Degree-one component.
symbol comm_ring_freyd_bounded_chain_map_F1
  [R : τ CommRing]
  [tailLength : τ Nat_grpd]
  [source target : τ (@CommRingFreydBoundedComplex R (succ tailLength))]
  (f : τ (@CommRingFreydBoundedChainMap R
      (succ tailLength) source target))
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_freyd_bounded_complex_P1 R tailLength source)
      (@comm_ring_freyd_bounded_complex_P1 R tailLength target))
≔ sigma_Fst (sigma_Snd f);

// Agreement for the first differential.
symbol comm_ring_freyd_bounded_chain_map_first_law
  [R : τ CommRing]
  [tailLength : τ Nat_grpd]
  [source target : τ (@CommRingFreydBoundedComplex R (succ tailLength))]
  (f : τ (@CommRingFreydBoundedChainMap R
      (succ tailLength) source target))
  : τ (@CommRingFreydChainMapSquare R
      (@comm_ring_freyd_bounded_complex_P0 R tailLength source)
      (@comm_ring_freyd_bounded_complex_P1 R tailLength source)
      (@comm_ring_freyd_bounded_complex_P0 R tailLength target)
      (@comm_ring_freyd_bounded_complex_P1 R tailLength target)
      (@comm_ring_freyd_bounded_complex_d1 R tailLength source)
      (@comm_ring_freyd_bounded_complex_d1 R tailLength target)
      (@comm_ring_freyd_bounded_chain_map_F0 R tailLength source target f)
      (@comm_ring_freyd_bounded_chain_map_F1 R tailLength source target f))
≔ sigma_Fst (sigma_Snd (sigma_Snd f));

// Retained map tail above degree one.
symbol comm_ring_freyd_bounded_chain_map_tail
  [R : τ CommRing]
  [tailLength : τ Nat_grpd]
  [source target : τ (@CommRingFreydBoundedComplex R (succ tailLength))]
  (f : τ (@CommRingFreydBoundedChainMap R
      (succ tailLength) source target))
  : τ (@CommRingFreydChainMapTail R tailLength
      (@comm_ring_freyd_bounded_complex_P0 R tailLength source)
      (@comm_ring_freyd_bounded_complex_P1 R tailLength source)
      (@comm_ring_freyd_bounded_complex_d1 R tailLength source)
      (@comm_ring_freyd_bounded_complex_tail R tailLength source)
      (@comm_ring_freyd_bounded_complex_P0 R tailLength target)
      (@comm_ring_freyd_bounded_complex_P1 R tailLength target)
      (@comm_ring_freyd_bounded_complex_d1 R tailLength target)
      (@comm_ring_freyd_bounded_complex_tail R tailLength target)
      (@comm_ring_freyd_bounded_chain_map_F1 R tailLength source target f))
≔ sigma_Snd (sigma_Snd (sigma_Snd f));

// The first two stored laws are exactly the existing one-degree chain-map data.
symbol comm_ring_freyd_chain_map_first_homology
  [R : τ CommRing]
  [length : τ Nat_grpd]
  [S0 S1 T0 T1 : τ (@CommRingPresentation R)]
  [sd : τ (@CommRingPresentationMorphism R S1 S0)]
  [td : τ (@CommRingPresentationMorphism R T1 T0)]
  [st : τ (@CommRingFreydChainTail R (succ length) S0 S1 sd)]
  [ttail : τ (@CommRingFreydChainTail R (succ length) T0 T1 td)]
  [f0 : τ (@CommRingPresentationMorphism R S0 T0)]
  [f1 : τ (@CommRingPresentationMorphism R S1 T1)]
  (lower : τ (@CommRingFreydChainMapSquare R S0 S1 T0 T1 sd td f0 f1))
  (tail : τ (@CommRingFreydChainMapTail R (succ length)
    S0 S1 sd st T0 T1 td ttail f1))
  : τ (@CommRingFreydHomologyChainMap R
      (@comm_ring_freyd_chain_tail_next R length S0 S1 sd st) S1 S0
      (@comm_ring_freyd_chain_tail_next R length T0 T1 td ttail) T1 T0
      (@comm_ring_freyd_chain_tail_differential R length S0 S1 sd st) sd
      (@comm_ring_freyd_chain_tail_differential R length T0 T1 td ttail) td
      (@comm_ring_freyd_chain_map_tail_next_map R length
        S0 S1 sd st T0 T1 td ttail f1 tail) f1 f0)
≔ @Product_pair_grpd _ _
    (@comm_ring_freyd_chain_map_tail_law R length
      S0 S1 sd st T0 T1 td ttail f1 tail)
    lower;
