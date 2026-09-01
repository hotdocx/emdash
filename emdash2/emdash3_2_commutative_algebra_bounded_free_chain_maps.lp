/*
  Whole chain maps between independently packaged bounded free complexes.

  The recursive tail follows both complex tails, selects one next component,
  stores the computed exact square, and recurses. Positive-length whole maps
  retain F0, F1, the first square, and the remaining map tail. Components are
  data; square proofs are derived/adopted evidence, not independent usability
  inputs. No formal category, quotient module, exactness, or homology is added.
*/

require open emdash.emdash3_2_commutative_algebra_bounded_free_complexes;

symbol CommRingFreeChainMapTail
  (R : τ CommRing)
  (length : τ Nat_grpd)
  (sourceBelow sourceCurrent : τ Nat_grpd)
  (sourceBoundary : τ (@CommRingMatrix R sourceBelow sourceCurrent))
  (sourceTail : τ (@CommRingFreeChainTail R
      length sourceBelow sourceCurrent sourceBoundary))
  (targetBelow targetCurrent : τ Nat_grpd)
  (targetBoundary : τ (@CommRingMatrix R targetBelow targetCurrent))
  (targetTail : τ (@CommRingFreeChainTail R
      length targetBelow targetCurrent targetBoundary))
  (currentMap : τ (@CommRingMatrix R targetCurrent sourceCurrent))
  : Grpd
≔ (@nat_elim
    (λ length0 : τ Nat_grpd,
      @Pi_grpd Nat_grpd
        (λ sourceBelow0 : τ Nat_grpd,
          @Pi_grpd Nat_grpd
            (λ sourceCurrent0 : τ Nat_grpd,
              @Pi_grpd
                (@CommRingMatrix R sourceBelow0 sourceCurrent0)
                (λ sourceBoundary0 : τ (@CommRingMatrix R
                    sourceBelow0 sourceCurrent0),
                  @Pi_grpd
                    (@CommRingFreeChainTail R length0
                      sourceBelow0 sourceCurrent0 sourceBoundary0)
                    (λ _ : τ (@CommRingFreeChainTail R length0
                        sourceBelow0 sourceCurrent0 sourceBoundary0),
                      @Pi_grpd Nat_grpd
                        (λ targetBelow0 : τ Nat_grpd,
                          @Pi_grpd Nat_grpd
                            (λ targetCurrent0 : τ Nat_grpd,
                              @Pi_grpd
                                (@CommRingMatrix R
                                  targetBelow0 targetCurrent0)
                                (λ targetBoundary0 : τ (@CommRingMatrix R
                                    targetBelow0 targetCurrent0),
                                  @Pi_grpd
                                    (@CommRingFreeChainTail R length0
                                      targetBelow0 targetCurrent0
                                      targetBoundary0)
                                    (λ _ : τ (@CommRingFreeChainTail R length0
                                        targetBelow0 targetCurrent0
                                        targetBoundary0),
                                      @Function_grpd
                                        (@CommRingMatrix R
                                          targetCurrent0 sourceCurrent0)
                                        Grpd_grpd)))))))))
    (λ sourceBelow0 : τ Nat_grpd,
      λ sourceCurrent0 : τ Nat_grpd,
      λ sourceBoundary0 : τ (@CommRingMatrix R
        sourceBelow0 sourceCurrent0),
      λ _ : τ (@CommRingFreeChainTail R zero
        sourceBelow0 sourceCurrent0 sourceBoundary0),
      λ targetBelow0 : τ Nat_grpd,
      λ targetCurrent0 : τ Nat_grpd,
      λ targetBoundary0 : τ (@CommRingMatrix R
        targetBelow0 targetCurrent0),
      λ _ : τ (@CommRingFreeChainTail R zero
        targetBelow0 targetCurrent0 targetBoundary0),
      λ _ : τ (@CommRingMatrix R targetCurrent0 sourceCurrent0),
        Unit_grpd)
    (λ length0 : τ Nat_grpd,
      λ rec,
      λ sourceBelow0 : τ Nat_grpd,
      λ sourceCurrent0 : τ Nat_grpd,
      λ sourceBoundary0 : τ (@CommRingMatrix R
        sourceBelow0 sourceCurrent0),
      λ sourceTail0 : τ (@CommRingFreeChainTail R (succ length0)
        sourceBelow0 sourceCurrent0 sourceBoundary0),
      λ targetBelow0 : τ Nat_grpd,
      λ targetCurrent0 : τ Nat_grpd,
      λ targetBoundary0 : τ (@CommRingMatrix R
        targetBelow0 targetCurrent0),
      λ targetTail0 : τ (@CommRingFreeChainTail R (succ length0)
        targetBelow0 targetCurrent0 targetBoundary0),
      λ currentMap0 : τ (@CommRingMatrix R
        targetCurrent0 sourceCurrent0),
        `Σ_ nextMap : τ (@CommRingMatrix R
            (@comm_ring_free_chain_tail_next_rank R
              length0 targetBelow0 targetCurrent0
              targetBoundary0 targetTail0)
            (@comm_ring_free_chain_tail_next_rank R
              length0 sourceBelow0 sourceCurrent0
              sourceBoundary0 sourceTail0)),
          @Product_grpd
            (@CommRingChainMapSquare R
              sourceCurrent0
              (@comm_ring_free_chain_tail_next_rank R
                length0 sourceBelow0 sourceCurrent0
                sourceBoundary0 sourceTail0)
              targetCurrent0
              (@comm_ring_free_chain_tail_next_rank R
                length0 targetBelow0 targetCurrent0
                targetBoundary0 targetTail0)
              (@comm_ring_free_chain_tail_differential R
                length0 sourceBelow0 sourceCurrent0
                sourceBoundary0 sourceTail0)
              (@comm_ring_free_chain_tail_differential R
                length0 targetBelow0 targetCurrent0
                targetBoundary0 targetTail0)
              currentMap0 nextMap)
            (rec
              sourceCurrent0
              (@comm_ring_free_chain_tail_next_rank R
                length0 sourceBelow0 sourceCurrent0
                sourceBoundary0 sourceTail0)
              (@comm_ring_free_chain_tail_differential R
                length0 sourceBelow0 sourceCurrent0
                sourceBoundary0 sourceTail0)
              (@comm_ring_free_chain_tail_rest R
                length0 sourceBelow0 sourceCurrent0
                sourceBoundary0 sourceTail0)
              targetCurrent0
              (@comm_ring_free_chain_tail_next_rank R
                length0 targetBelow0 targetCurrent0
                targetBoundary0 targetTail0)
              (@comm_ring_free_chain_tail_differential R
                length0 targetBelow0 targetCurrent0
                targetBoundary0 targetTail0)
              (@comm_ring_free_chain_tail_rest R
                length0 targetBelow0 targetCurrent0
                targetBoundary0 targetTail0)
              nextMap))
    length)
    sourceBelow sourceCurrent sourceBoundary sourceTail
    targetBelow targetCurrent targetBoundary targetTail
    currentMap;

symbol comm_ring_free_chain_map_tail_nil
  [R : τ CommRing]
  [sourceBelow sourceCurrent : τ Nat_grpd]
  [sourceBoundary : τ (@CommRingMatrix R sourceBelow sourceCurrent)]
  [sourceTail : τ (@CommRingFreeChainTail R
      zero sourceBelow sourceCurrent sourceBoundary)]
  [targetBelow targetCurrent : τ Nat_grpd]
  [targetBoundary : τ (@CommRingMatrix R targetBelow targetCurrent)]
  [targetTail : τ (@CommRingFreeChainTail R
      zero targetBelow targetCurrent targetBoundary)]
  [currentMap : τ (@CommRingMatrix R targetCurrent sourceCurrent)]
  : τ (@CommRingFreeChainMapTail R zero
      sourceBelow sourceCurrent sourceBoundary sourceTail
      targetBelow targetCurrent targetBoundary targetTail
      currentMap)
≔ tt;

symbol comm_ring_free_chain_map_tail_cons
  [R : τ CommRing]
  [length : τ Nat_grpd]
  [sourceBelow sourceCurrent : τ Nat_grpd]
  [sourceBoundary : τ (@CommRingMatrix R sourceBelow sourceCurrent)]
  [sourceTail : τ (@CommRingFreeChainTail R
      (succ length) sourceBelow sourceCurrent sourceBoundary)]
  [targetBelow targetCurrent : τ Nat_grpd]
  [targetBoundary : τ (@CommRingMatrix R targetBelow targetCurrent)]
  [targetTail : τ (@CommRingFreeChainTail R
      (succ length) targetBelow targetCurrent targetBoundary)]
  [currentMap : τ (@CommRingMatrix R targetCurrent sourceCurrent)]
  (nextMap : τ (@CommRingMatrix R
      (@comm_ring_free_chain_tail_next_rank R
        length targetBelow targetCurrent targetBoundary targetTail)
      (@comm_ring_free_chain_tail_next_rank R
        length sourceBelow sourceCurrent sourceBoundary sourceTail)))
  (law : τ (@CommRingChainMapSquare R
      sourceCurrent
      (@comm_ring_free_chain_tail_next_rank R
        length sourceBelow sourceCurrent sourceBoundary sourceTail)
      targetCurrent
      (@comm_ring_free_chain_tail_next_rank R
        length targetBelow targetCurrent targetBoundary targetTail)
      (@comm_ring_free_chain_tail_differential R
        length sourceBelow sourceCurrent sourceBoundary sourceTail)
      (@comm_ring_free_chain_tail_differential R
        length targetBelow targetCurrent targetBoundary targetTail)
      currentMap nextMap))
  (rest : τ (@CommRingFreeChainMapTail R length
      sourceCurrent
      (@comm_ring_free_chain_tail_next_rank R
        length sourceBelow sourceCurrent sourceBoundary sourceTail)
      (@comm_ring_free_chain_tail_differential R
        length sourceBelow sourceCurrent sourceBoundary sourceTail)
      (@comm_ring_free_chain_tail_rest R
        length sourceBelow sourceCurrent sourceBoundary sourceTail)
      targetCurrent
      (@comm_ring_free_chain_tail_next_rank R
        length targetBelow targetCurrent targetBoundary targetTail)
      (@comm_ring_free_chain_tail_differential R
        length targetBelow targetCurrent targetBoundary targetTail)
      (@comm_ring_free_chain_tail_rest R
        length targetBelow targetCurrent targetBoundary targetTail)
      nextMap))
  : τ (@CommRingFreeChainMapTail R (succ length)
      sourceBelow sourceCurrent sourceBoundary sourceTail
      targetBelow targetCurrent targetBoundary targetTail
      currentMap)
≔ Struct_sigma nextMap (Product_pair_grpd law rest);

symbol comm_ring_free_chain_map_tail_next_map
  [R : τ CommRing]
  [length : τ Nat_grpd]
  [sourceBelow sourceCurrent : τ Nat_grpd]
  [sourceBoundary : τ (@CommRingMatrix R sourceBelow sourceCurrent)]
  [sourceTail : τ (@CommRingFreeChainTail R
      (succ length) sourceBelow sourceCurrent sourceBoundary)]
  [targetBelow targetCurrent : τ Nat_grpd]
  [targetBoundary : τ (@CommRingMatrix R targetBelow targetCurrent)]
  [targetTail : τ (@CommRingFreeChainTail R
      (succ length) targetBelow targetCurrent targetBoundary)]
  [currentMap : τ (@CommRingMatrix R targetCurrent sourceCurrent)]
  (mapTail : τ (@CommRingFreeChainMapTail R (succ length)
      sourceBelow sourceCurrent sourceBoundary sourceTail
      targetBelow targetCurrent targetBoundary targetTail currentMap))
  : τ (@CommRingMatrix R
      (@comm_ring_free_chain_tail_next_rank R
        length targetBelow targetCurrent targetBoundary targetTail)
      (@comm_ring_free_chain_tail_next_rank R
        length sourceBelow sourceCurrent sourceBoundary sourceTail))
≔ sigma_Fst mapTail;

symbol comm_ring_free_chain_map_tail_law
  [R : τ CommRing]
  [length : τ Nat_grpd]
  [sourceBelow sourceCurrent : τ Nat_grpd]
  [sourceBoundary : τ (@CommRingMatrix R sourceBelow sourceCurrent)]
  [sourceTail : τ (@CommRingFreeChainTail R
      (succ length) sourceBelow sourceCurrent sourceBoundary)]
  [targetBelow targetCurrent : τ Nat_grpd]
  [targetBoundary : τ (@CommRingMatrix R targetBelow targetCurrent)]
  [targetTail : τ (@CommRingFreeChainTail R
      (succ length) targetBelow targetCurrent targetBoundary)]
  [currentMap : τ (@CommRingMatrix R targetCurrent sourceCurrent)]
  (mapTail : τ (@CommRingFreeChainMapTail R (succ length)
      sourceBelow sourceCurrent sourceBoundary sourceTail
      targetBelow targetCurrent targetBoundary targetTail currentMap))
  : τ (@CommRingChainMapSquare R
      sourceCurrent
      (@comm_ring_free_chain_tail_next_rank R
        length sourceBelow sourceCurrent sourceBoundary sourceTail)
      targetCurrent
      (@comm_ring_free_chain_tail_next_rank R
        length targetBelow targetCurrent targetBoundary targetTail)
      (@comm_ring_free_chain_tail_differential R
        length sourceBelow sourceCurrent sourceBoundary sourceTail)
      (@comm_ring_free_chain_tail_differential R
        length targetBelow targetCurrent targetBoundary targetTail)
      currentMap
      (@comm_ring_free_chain_map_tail_next_map R length
        sourceBelow sourceCurrent sourceBoundary sourceTail
        targetBelow targetCurrent targetBoundary targetTail
        currentMap mapTail))
≔ sigma_Fst (sigma_Snd mapTail);

symbol comm_ring_free_chain_map_tail_rest
  [R : τ CommRing]
  [length : τ Nat_grpd]
  [sourceBelow sourceCurrent : τ Nat_grpd]
  [sourceBoundary : τ (@CommRingMatrix R sourceBelow sourceCurrent)]
  [sourceTail : τ (@CommRingFreeChainTail R
      (succ length) sourceBelow sourceCurrent sourceBoundary)]
  [targetBelow targetCurrent : τ Nat_grpd]
  [targetBoundary : τ (@CommRingMatrix R targetBelow targetCurrent)]
  [targetTail : τ (@CommRingFreeChainTail R
      (succ length) targetBelow targetCurrent targetBoundary)]
  [currentMap : τ (@CommRingMatrix R targetCurrent sourceCurrent)]
  (mapTail : τ (@CommRingFreeChainMapTail R (succ length)
      sourceBelow sourceCurrent sourceBoundary sourceTail
      targetBelow targetCurrent targetBoundary targetTail currentMap))
  : τ (@CommRingFreeChainMapTail R length
      sourceCurrent
      (@comm_ring_free_chain_tail_next_rank R
        length sourceBelow sourceCurrent sourceBoundary sourceTail)
      (@comm_ring_free_chain_tail_differential R
        length sourceBelow sourceCurrent sourceBoundary sourceTail)
      (@comm_ring_free_chain_tail_rest R
        length sourceBelow sourceCurrent sourceBoundary sourceTail)
      targetCurrent
      (@comm_ring_free_chain_tail_next_rank R
        length targetBelow targetCurrent targetBoundary targetTail)
      (@comm_ring_free_chain_tail_differential R
        length targetBelow targetCurrent targetBoundary targetTail)
      (@comm_ring_free_chain_tail_rest R
        length targetBelow targetCurrent targetBoundary targetTail)
      (@comm_ring_free_chain_map_tail_next_map R length
        sourceBelow sourceCurrent sourceBoundary sourceTail
        targetBelow targetCurrent targetBoundary targetTail
        currentMap mapTail))
≔ sigma_Snd (sigma_Snd mapTail);

symbol CommRingBoundedFreeChainMap
  (R : τ CommRing)
  (length : τ Nat_grpd)
  (source target : τ (@CommRingBoundedFreeComplex R length))
  : Grpd
≔ (@nat_elim
    (λ length0 : τ Nat_grpd,
      @Pi_grpd (@CommRingBoundedFreeComplex R length0)
        (λ _ : τ (@CommRingBoundedFreeComplex R length0),
          @Function_grpd
            (@CommRingBoundedFreeComplex R length0)
            Grpd_grpd))
    (λ source0 : τ (@CommRingBoundedFreeComplex R zero),
      λ target0 : τ (@CommRingBoundedFreeComplex R zero),
        @CommRingMatrix R target0 source0)
    (λ tailLength : τ Nat_grpd,
      λ _,
      λ source0 : τ (@CommRingBoundedFreeComplex R (succ tailLength)),
      λ target0 : τ (@CommRingBoundedFreeComplex R (succ tailLength)),
        `Σ_ F0 : τ (@CommRingMatrix R
            (@comm_ring_bounded_free_complex_rank0 R tailLength target0)
            (@comm_ring_bounded_free_complex_rank0 R tailLength source0)),
          `Σ_ F1 : τ (@CommRingMatrix R
              (@comm_ring_bounded_free_complex_rank1 R tailLength target0)
              (@comm_ring_bounded_free_complex_rank1 R tailLength source0)),
            @Product_grpd
              (@CommRingChainMapSquare R
                (@comm_ring_bounded_free_complex_rank0 R tailLength source0)
                (@comm_ring_bounded_free_complex_rank1 R tailLength source0)
                (@comm_ring_bounded_free_complex_rank0 R tailLength target0)
                (@comm_ring_bounded_free_complex_rank1 R tailLength target0)
                (@comm_ring_bounded_free_complex_d1 R tailLength source0)
                (@comm_ring_bounded_free_complex_d1 R tailLength target0)
                F0 F1)
              (@CommRingFreeChainMapTail R tailLength
                (@comm_ring_bounded_free_complex_rank0 R tailLength source0)
                (@comm_ring_bounded_free_complex_rank1 R tailLength source0)
                (@comm_ring_bounded_free_complex_d1 R tailLength source0)
                (@comm_ring_bounded_free_complex_tail R tailLength source0)
                (@comm_ring_bounded_free_complex_rank0 R tailLength target0)
                (@comm_ring_bounded_free_complex_rank1 R tailLength target0)
                (@comm_ring_bounded_free_complex_d1 R tailLength target0)
                (@comm_ring_bounded_free_complex_tail R tailLength target0)
                F1))
    length) source target;

symbol comm_ring_bounded_free_chain_map_zero
  [R : τ CommRing]
  [source target : τ Nat_grpd]
  (F0 : τ (@CommRingMatrix R target source))
  : τ (@CommRingBoundedFreeChainMap R zero source target)
≔ F0;

symbol comm_ring_bounded_free_chain_map_succ
  [R : τ CommRing]
  [tailLength : τ Nat_grpd]
  [source target : τ (@CommRingBoundedFreeComplex R (succ tailLength))]
  (F0 : τ (@CommRingMatrix R
      (@comm_ring_bounded_free_complex_rank0 R tailLength target)
      (@comm_ring_bounded_free_complex_rank0 R tailLength source)))
  (F1 : τ (@CommRingMatrix R
      (@comm_ring_bounded_free_complex_rank1 R tailLength target)
      (@comm_ring_bounded_free_complex_rank1 R tailLength source)))
  (law : τ (@CommRingChainMapSquare R
      (@comm_ring_bounded_free_complex_rank0 R tailLength source)
      (@comm_ring_bounded_free_complex_rank1 R tailLength source)
      (@comm_ring_bounded_free_complex_rank0 R tailLength target)
      (@comm_ring_bounded_free_complex_rank1 R tailLength target)
      (@comm_ring_bounded_free_complex_d1 R tailLength source)
      (@comm_ring_bounded_free_complex_d1 R tailLength target)
      F0 F1))
  (tail : τ (@CommRingFreeChainMapTail R tailLength
      (@comm_ring_bounded_free_complex_rank0 R tailLength source)
      (@comm_ring_bounded_free_complex_rank1 R tailLength source)
      (@comm_ring_bounded_free_complex_d1 R tailLength source)
      (@comm_ring_bounded_free_complex_tail R tailLength source)
      (@comm_ring_bounded_free_complex_rank0 R tailLength target)
      (@comm_ring_bounded_free_complex_rank1 R tailLength target)
      (@comm_ring_bounded_free_complex_d1 R tailLength target)
      (@comm_ring_bounded_free_complex_tail R tailLength target)
      F1))
  : τ (@CommRingBoundedFreeChainMap R
      (succ tailLength) source target)
≔ Struct_sigma F0 (Struct_sigma F1 (Product_pair_grpd law tail));

symbol comm_ring_bounded_free_chain_map_F0
  [R : τ CommRing]
  [tailLength : τ Nat_grpd]
  [source target : τ (@CommRingBoundedFreeComplex R (succ tailLength))]
  (f : τ (@CommRingBoundedFreeChainMap R
      (succ tailLength) source target))
  : τ (@CommRingMatrix R
      (@comm_ring_bounded_free_complex_rank0 R tailLength target)
      (@comm_ring_bounded_free_complex_rank0 R tailLength source))
≔ sigma_Fst f;

symbol comm_ring_bounded_free_chain_map_F1
  [R : τ CommRing]
  [tailLength : τ Nat_grpd]
  [source target : τ (@CommRingBoundedFreeComplex R (succ tailLength))]
  (f : τ (@CommRingBoundedFreeChainMap R
      (succ tailLength) source target))
  : τ (@CommRingMatrix R
      (@comm_ring_bounded_free_complex_rank1 R tailLength target)
      (@comm_ring_bounded_free_complex_rank1 R tailLength source))
≔ sigma_Fst (sigma_Snd f);

symbol comm_ring_bounded_free_chain_map_first_law
  [R : τ CommRing]
  [tailLength : τ Nat_grpd]
  [source target : τ (@CommRingBoundedFreeComplex R (succ tailLength))]
  (f : τ (@CommRingBoundedFreeChainMap R
      (succ tailLength) source target))
  : τ (@CommRingChainMapSquare R
      (@comm_ring_bounded_free_complex_rank0 R tailLength source)
      (@comm_ring_bounded_free_complex_rank1 R tailLength source)
      (@comm_ring_bounded_free_complex_rank0 R tailLength target)
      (@comm_ring_bounded_free_complex_rank1 R tailLength target)
      (@comm_ring_bounded_free_complex_d1 R tailLength source)
      (@comm_ring_bounded_free_complex_d1 R tailLength target)
      (@comm_ring_bounded_free_chain_map_F0 R tailLength source target f)
      (@comm_ring_bounded_free_chain_map_F1 R tailLength source target f))
≔ sigma_Fst (sigma_Snd (sigma_Snd f));

symbol comm_ring_bounded_free_chain_map_tail
  [R : τ CommRing]
  [tailLength : τ Nat_grpd]
  [source target : τ (@CommRingBoundedFreeComplex R (succ tailLength))]
  (f : τ (@CommRingBoundedFreeChainMap R
      (succ tailLength) source target))
  : τ (@CommRingFreeChainMapTail R tailLength
      (@comm_ring_bounded_free_complex_rank0 R tailLength source)
      (@comm_ring_bounded_free_complex_rank1 R tailLength source)
      (@comm_ring_bounded_free_complex_d1 R tailLength source)
      (@comm_ring_bounded_free_complex_tail R tailLength source)
      (@comm_ring_bounded_free_complex_rank0 R tailLength target)
      (@comm_ring_bounded_free_complex_rank1 R tailLength target)
      (@comm_ring_bounded_free_complex_d1 R tailLength target)
      (@comm_ring_bounded_free_complex_tail R tailLength target)
      (@comm_ring_bounded_free_chain_map_F1 R tailLength source target f))
≔ sigma_Snd (sigma_Snd (sigma_Snd f));
