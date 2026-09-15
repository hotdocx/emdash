/* Existing fixed-arrow Ω evidence indexed by one existing arrow object.
   The object observations change no directed action or inverse choice. */
require open emdash.emdash3_2_cubical_internalization;

symbol ArrowOmegaEvidence [C : Cat] (a : τ (Obj (@LaxArrow_cat C))) : Grpd
≔ @OmegaEquivAlong C (sigma_Fst a) (sigma_Fst (sigma_Snd a)) (sigma_Snd (sigma_Snd a));

// Observe a complete whole transformation at x, keeping endpoints together.
symbol transf_arrow_observation_at [K C : Cat]
  (a : τ (Obj (@LaxArrow_cat (Functor_cat K C)))) (x : τ (Obj K))
  : τ (Obj (@LaxArrow_cat C))
≔ @lax_edge C (@fapp0 K C (sigma_Fst a) x) (@fapp0 K C (sigma_Fst (sigma_Snd a)) x)
    (@tapp0_fapp0 K C (sigma_Fst a) (sigma_Fst (sigma_Snd a)) x (sigma_Snd (sigma_Snd a)));

// The original evaluation functor maps the original Ω witness.
symbol transf_arrow_omega_at [K C : Cat]
  (a : τ (Obj (@LaxArrow_cat (Functor_cat K C))))
  (u : τ (@ArrowOmegaEvidence (Functor_cat K C) a)) (x : τ (Obj K))
  : τ (@ArrowOmegaEvidence C (@transf_arrow_observation_at K C a x))
≔ @omega_equiv_along_fapp1_fapp0 (Functor_cat K C) C (@fapp0_func K C x)
    (sigma_Fst a) (sigma_Fst (sigma_Snd a)) (sigma_Snd (sigma_Snd a)) u;

// Package the ORIGINAL indexed arrow and its existing Ω witness together.
symbol OmegaArrowData (C : Cat) : Grpd
≔ `Σ_ a : τ (Obj (@LaxArrow_cat C)), @ArrowOmegaEvidence C a;

symbol omega_arrow_data [C : Cat] [x y : τ (Obj C)] [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f)) : τ (OmegaArrowData C)
≔ Struct_sigma (@lax_edge C x y f) u;

// Evaluation preserves this package, through the already defined Ω action.
symbol omega_arrow_data_at [K C : Cat]
  (a : τ (OmegaArrowData (Functor_cat K C))) (x : τ (Obj K))
  : τ (OmegaArrowData C)
≔ Struct_sigma (@transf_arrow_observation_at K C (sigma_Fst a) x)
    (@transf_arrow_omega_at K C (sigma_Fst a) (sigma_Snd a) x);

// Typed projections keep the fixed data classifier at the consumer boundary.
symbol omega_arrow_observation [C : Cat] (d : τ (OmegaArrowData C))
  : τ (Obj (@LaxArrow_cat C)) ≔ sigma_Fst d;
symbol omega_arrow_observation_evidence [C : Cat] (d : τ (OmegaArrowData C))
  : τ (@ArrowOmegaEvidence C (@omega_arrow_observation C d)) ≔ sigma_Snd d;
