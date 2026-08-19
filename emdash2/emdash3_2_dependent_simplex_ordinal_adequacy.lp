/*
  Strongest low-dimensional ordinal/dependent comparison supported by current
  join and dependent-hom owners.

  Dimension zero is whole. Dimension one observes an ordinal walking-arrow map
  as an intrinsic code plus edge object. Dimension two computes all three edge
  restrictions and their shared vertices; one explicit dependent triangle
  filler is the remaining input required to assemble the native observation.
  Dimensions three and four
  recurse through that same missing compatibility and filler boundary; this
  module adds no join uniqueness, functor extensionality, rule, or unifier.
*/

require open emdash.emdash3_2_dependent_simplex_faces;

// Object-level total of an intrinsic code and one decoded simplex. This is a
// Grpd-valued observation package, not the rejected mixed-variance category.
symbol DependentSimplexObservation
  (C : Cat)
  (n : τ Nat_grpd)
  : Grpd
≔ `Σ_ code : τ (@DependentSimplexCode C n),
    Obj (@dependent_simplex_code_decode_cat C n code);

symbol dependent_simplex_observation
  [C : Cat]
  [n : τ Nat_grpd]
  (code : τ (@DependentSimplexCode C n))
  (simplex : τ (Obj (@dependent_simplex_code_decode_cat C n code)))
  : τ (@DependentSimplexObservation C n)
≔ Struct_sigma code simplex;

// Dimension-zero ordinal observation and constant encoding are whole.
symbol ordinal_simplex0_observe_func
  (C : Cat)
  : τ (Functor (Functor_cat Terminal_cat C) C)
≔ @fapp0_func Terminal_cat C Terminal_obj;

symbol ordinal_simplex0_encode_func
  (C : Cat)
  : τ (Functor C (Functor_cat Terminal_cat C))
≔ @Const_func_func Terminal_cat C;

// Read a map of the walking arrow at its two endpoints and generator.
symbol ordinal_simplex1_source
  [C : Cat]
  (H : τ (Functor WalkingArrow_cat C))
  : τ (Obj C)
≔ @fapp0 WalkingArrow_cat C H walking_arrow_src;

symbol ordinal_simplex1_target
  [C : Cat]
  (H : τ (Functor WalkingArrow_cat C))
  : τ (Obj C)
≔ @fapp0 WalkingArrow_cat C H walking_arrow_tgt;

symbol ordinal_simplex1_arrow
  [C : Cat]
  (H : τ (Functor WalkingArrow_cat C))
  : τ (Hom C
      (@ordinal_simplex1_source C H)
      (@ordinal_simplex1_target C H))
≔ @fapp1_fapp0
    WalkingArrow_cat C H
    walking_arrow_src walking_arrow_tgt
    walking_arrow_generator;

symbol ordinal_dependent_simplex1_observe
  [C : Cat]
  (H : τ (Functor WalkingArrow_cat C))
  : τ (@DependentSimplexObservation C (succ zero))
≔ @dependent_simplex_observation
    C (succ zero)
    (@dependent_simplex_code1 C (@ordinal_simplex1_source C H))
    (@dependent_simplex1
      C
      (@ordinal_simplex1_source C H)
      (@ordinal_simplex1_target C H)
      (@ordinal_simplex1_arrow C H));

// The three ordinal edges of a triangle are whole restrictions.
symbol ordinal_simplex2_edge01
  [C : Cat]
  (H : τ (Functor (@DirectedSimplex_cat (succ (succ zero))) C))
  : τ (Functor WalkingArrow_cat C)
≔ @comp_cat_fapp0
    WalkingArrow_cat
    (@DirectedSimplex_cat (succ (succ zero)))
    C H simplex_edge_zero_one_func;

symbol ordinal_simplex2_edge02
  [C : Cat]
  (H : τ (Functor (@DirectedSimplex_cat (succ (succ zero))) C))
  : τ (Functor WalkingArrow_cat C)
≔ @comp_cat_fapp0
    WalkingArrow_cat
    (@DirectedSimplex_cat (succ (succ zero)))
    C H simplex_edge_zero_two_func;

symbol ordinal_simplex2_edge12
  [C : Cat]
  (H : τ (Functor (@DirectedSimplex_cat (succ (succ zero))) C))
  : τ (Functor WalkingArrow_cat C)
≔ @comp_cat_fapp0
    WalkingArrow_cat
    (@DirectedSimplex_cat (succ (succ zero)))
    C H simplex_edge_one_two_func;

// The three selected ordinal edges do not currently share their vertices by
// definitional equality. Record exactly the endpoint comparisons required by
// the native triangle instead of postulating join-map composition.
symbol OrdinalDependentSimplex2Compatibility
  [C : Cat]
  (H : τ (Functor (@DirectedSimplex_cat (succ (succ zero))) C))
  : Grpd
≔ `Σ_ source02 : τ (@=
      (Obj C)
      (@ordinal_simplex1_source C (@ordinal_simplex2_edge02 C H))
      (@ordinal_simplex1_source C (@ordinal_simplex2_edge01 C H))),
   `Σ_ source12 : τ (@=
      (Obj C)
      (@ordinal_simplex1_source C (@ordinal_simplex2_edge12 C H))
      (@ordinal_simplex1_target C (@ordinal_simplex2_edge01 C H))),
     @=
      (Obj C)
      (@ordinal_simplex1_target C (@ordinal_simplex2_edge12 C H))
      (@ordinal_simplex1_target C (@ordinal_simplex2_edge02 C H));

symbol ordinal_simplex2_source02_path
  [C : Cat]
  [H : τ (Functor (@DirectedSimplex_cat (succ (succ zero))) C)]
  (compat : τ (@OrdinalDependentSimplex2Compatibility C H))
  : τ (@=
      (Obj C)
      (@ordinal_simplex1_source C (@ordinal_simplex2_edge02 C H))
      (@ordinal_simplex1_source C (@ordinal_simplex2_edge01 C H)))
≔ sigma_Fst compat;

symbol ordinal_simplex2_source12_path
  [C : Cat]
  [H : τ (Functor (@DirectedSimplex_cat (succ (succ zero))) C)]
  (compat : τ (@OrdinalDependentSimplex2Compatibility C H))
  : τ (@=
      (Obj C)
      (@ordinal_simplex1_source C (@ordinal_simplex2_edge12 C H))
      (@ordinal_simplex1_target C (@ordinal_simplex2_edge01 C H)))
≔ sigma_Fst (sigma_Snd compat);

symbol ordinal_simplex2_target12_path
  [C : Cat]
  [H : τ (Functor (@DirectedSimplex_cat (succ (succ zero))) C)]
  (compat : τ (@OrdinalDependentSimplex2Compatibility C H))
  : τ (@=
      (Obj C)
      (@ordinal_simplex1_target C (@ordinal_simplex2_edge12 C H))
      (@ordinal_simplex1_target C (@ordinal_simplex2_edge02 C H)))
≔ sigma_Snd (sigma_Snd compat);

// The join-eliminator point betas make all three selected shared vertices
// judgmentally compatible, even though the corresponding whole face functors
// remain distinct.
symbol ordinal_dependent_simplex2_compatibility
  [C : Cat]
  (H : τ (Functor (@DirectedSimplex_cat (succ (succ zero))) C))
  : τ (@OrdinalDependentSimplex2Compatibility C H)
≔ Struct_sigma
    (@eq_refl
      (Obj C)
      (@ordinal_simplex1_source C (@ordinal_simplex2_edge01 C H)))
    (Struct_sigma
      (@eq_refl
        (Obj C)
        (@ordinal_simplex1_target C (@ordinal_simplex2_edge01 C H)))
      (@eq_refl
        (Obj C)
        (@ordinal_simplex1_target C (@ordinal_simplex2_edge02 C H))));

// Normalize edge 02 to the common vertex-0 endpoint.
symbol ordinal_simplex2_edge02_normalized
  [C : Cat]
  [H : τ (Functor (@DirectedSimplex_cat (succ (succ zero))) C)]
  (compat : τ (@OrdinalDependentSimplex2Compatibility C H))
  : τ (Hom C
      (@ordinal_simplex1_source C (@ordinal_simplex2_edge01 C H))
      (@ordinal_simplex1_target C (@ordinal_simplex2_edge02 C H)))
≔ @comp_fapp0
    C
    (@ordinal_simplex1_source C (@ordinal_simplex2_edge01 C H))
    (@ordinal_simplex1_source C (@ordinal_simplex2_edge02 C H))
    (@ordinal_simplex1_target C (@ordinal_simplex2_edge02 C H))
    (@ordinal_simplex1_arrow C (@ordinal_simplex2_edge02 C H))
    (@path_to_hom
      C
      (@ordinal_simplex1_source C (@ordinal_simplex2_edge01 C H))
      (@ordinal_simplex1_source C (@ordinal_simplex2_edge02 C H))
      (@eq_sym
        (Obj C)
        (@ordinal_simplex1_source C (@ordinal_simplex2_edge02 C H))
        (@ordinal_simplex1_source C (@ordinal_simplex2_edge01 C H))
        (@ordinal_simplex2_source02_path C H compat)));

// Normalize edge 12 at both endpoints.
symbol ordinal_simplex2_edge12_normalized
  [C : Cat]
  [H : τ (Functor (@DirectedSimplex_cat (succ (succ zero))) C)]
  (compat : τ (@OrdinalDependentSimplex2Compatibility C H))
  : τ (Hom C
      (@ordinal_simplex1_target C (@ordinal_simplex2_edge01 C H))
      (@ordinal_simplex1_target C (@ordinal_simplex2_edge02 C H)))
≔ @comp_fapp0
    C
    (@ordinal_simplex1_target C (@ordinal_simplex2_edge01 C H))
    (@ordinal_simplex1_target C (@ordinal_simplex2_edge12 C H))
    (@ordinal_simplex1_target C (@ordinal_simplex2_edge02 C H))
    (@path_to_hom
      C
      (@ordinal_simplex1_target C (@ordinal_simplex2_edge12 C H))
      (@ordinal_simplex1_target C (@ordinal_simplex2_edge02 C H))
      (@ordinal_simplex2_target12_path C H compat))
    (@comp_fapp0
      C
      (@ordinal_simplex1_target C (@ordinal_simplex2_edge01 C H))
      (@ordinal_simplex1_source C (@ordinal_simplex2_edge12 C H))
      (@ordinal_simplex1_target C (@ordinal_simplex2_edge12 C H))
      (@ordinal_simplex1_arrow C (@ordinal_simplex2_edge12 C H))
      (@path_to_hom
        C
        (@ordinal_simplex1_target C (@ordinal_simplex2_edge01 C H))
        (@ordinal_simplex1_source C (@ordinal_simplex2_edge12 C H))
        (@eq_sym
          (Obj C)
          (@ordinal_simplex1_source C (@ordinal_simplex2_edge12 C H))
          (@ordinal_simplex1_target C (@ordinal_simplex2_edge01 C H))
          (@ordinal_simplex2_source12_path C H compat))));

// After endpoint compatibility, one dependent filler is exactly the remaining
// full dimension-two adequacy datum.
symbol OrdinalDependentSimplex2Filler
  [C : Cat]
  [H : τ (Functor (@DirectedSimplex_cat (succ (succ zero))) C)]
  (compat : τ (@OrdinalDependentSimplex2Compatibility C H))
  : Grpd
≔ Obj (Fibre_cat
    (@DependentTriangle_catd
      C
      (@Rep_catd C
        (@ordinal_simplex1_source C (@ordinal_simplex2_edge01 C H)))
      (@ordinal_simplex1_target C (@ordinal_simplex2_edge01 C H))
      (@ordinal_simplex1_arrow C (@ordinal_simplex2_edge01 C H))
      (@ordinal_simplex1_target C (@ordinal_simplex2_edge02 C H))
      (@ordinal_simplex2_edge02_normalized C H compat))
    (@ordinal_simplex2_edge12_normalized C H compat));

// Given endpoint compatibility and the source-coherence filler, assemble the
// native triangle observation through the existing constructor.
symbol ordinal_dependent_simplex2_observe_with
  [C : Cat]
  (H : τ (Functor (@DirectedSimplex_cat (succ (succ zero))) C))
  (compat : τ (@OrdinalDependentSimplex2Compatibility C H))
  (alpha : τ (@OrdinalDependentSimplex2Filler C H compat))
  : τ (@DependentSimplexObservation C (succ (succ zero)))
≔ @dependent_simplex_observation
    C (succ (succ zero))
    (@dependent_simplex_code2
      C
      (@ordinal_simplex1_source C (@ordinal_simplex2_edge01 C H))
      (@dependent_simplex1
        C
        (@ordinal_simplex1_source C (@ordinal_simplex2_edge01 C H))
        (@ordinal_simplex1_target C (@ordinal_simplex2_edge01 C H))
        (@ordinal_simplex1_arrow C (@ordinal_simplex2_edge01 C H))))
    (@dependent_simplex2_visible
      C
      (@ordinal_simplex1_source C (@ordinal_simplex2_edge01 C H))
      (@ordinal_simplex1_target C (@ordinal_simplex2_edge01 C H))
      (@ordinal_simplex1_target C (@ordinal_simplex2_edge02 C H))
      (@ordinal_simplex1_arrow C (@ordinal_simplex2_edge01 C H))
      (@ordinal_simplex2_edge02_normalized C H compat)
      (@ordinal_simplex2_edge12_normalized C H compat)
      alpha);

// Canonical remaining question after shared-vertex computation: one dependent
// triangle filler relating the three restricted ordinal edges.
symbol OrdinalDependentSimplex2CanonicalFiller
  [C : Cat]
  (H : τ (Functor (@DirectedSimplex_cat (succ (succ zero))) C))
  : Grpd
≔ @OrdinalDependentSimplex2Filler
    C H (@ordinal_dependent_simplex2_compatibility C H);

symbol ordinal_dependent_simplex2_observe
  [C : Cat]
  (H : τ (Functor (@DirectedSimplex_cat (succ (succ zero))) C))
  (alpha : τ (@OrdinalDependentSimplex2CanonicalFiller C H))
  : τ (@DependentSimplexObservation C (succ (succ zero)))
≔ @ordinal_dependent_simplex2_observe_with
    C H
    (@ordinal_dependent_simplex2_compatibility C H)
    alpha;
