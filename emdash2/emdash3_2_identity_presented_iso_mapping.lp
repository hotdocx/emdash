/* Normal functors map identity-presented arrow pairs to inverse pairs.
   Equality is used only to transport the two laws; operational maps stay
   the original mapped arrows. No composition law is assumed for F. */
require open emdash.emdash3_2_iso_evidence_constructors;

symbol ArrowPairData (C : Cat) : Grpd
≔ `Σ_ x : τ (Obj C), `Σ_ y : τ (Obj C),
    @Product_grpd (Hom C x y) (Hom C y x);

symbol arrow_pair_data [C : Cat] (x y : τ (Obj C))
  (f : τ (Hom C x y)) (g : τ (Hom C y x)) : τ (ArrowPairData C)
≔ @Struct_sigma (Obj C)
    (λ a : τ (Obj C), `Σ_ b : τ (Obj C), @Product_grpd (Hom C a b) (Hom C b a)) x
    (@Struct_sigma (Obj C) (λ b : τ (Obj C), @Product_grpd (Hom C x b) (Hom C b x)) y
      (@Product_pair_grpd (Hom C x y) (Hom C y x) f g));

symbol arrow_pair_source [C : Cat] (z : τ (ArrowPairData C)) : τ (Obj C) ≔ sigma_Fst z;
symbol arrow_pair_target [C : Cat] (z : τ (ArrowPairData C)) : τ (Obj C) ≔ sigma_Fst (sigma_Snd z);
symbol arrow_pair_forward [C : Cat] (z : τ (ArrowPairData C))
  : τ (Hom C (@arrow_pair_source C z) (@arrow_pair_target C z))
≔ sigma_Fst (sigma_Snd (sigma_Snd z));
symbol arrow_pair_reverse [C : Cat] (z : τ (ArrowPairData C))
  : τ (Hom C (@arrow_pair_target C z) (@arrow_pair_source C z))
≔ sigma_Snd (sigma_Snd (sigma_Snd z));

symbol identity_arrow_pair [C : Cat] (x : τ (Obj C)) : τ (ArrowPairData C)
≔ @arrow_pair_data C x x (@id C x) (@id C x);

symbol arrow_pair_laws [C : Cat] (z : τ (ArrowPairData C)) : Grpd
≔ @Product_grpd
    (@= (Hom C (@arrow_pair_source C z) (@arrow_pair_source C z))
      (@comp_fapp0 C _ _ _ (@arrow_pair_reverse C z) (@arrow_pair_forward C z))
      (@id C (@arrow_pair_source C z)))
    (@= (Hom C (@arrow_pair_target C z) (@arrow_pair_target C z))
      (@comp_fapp0 C _ _ _ (@arrow_pair_forward C z) (@arrow_pair_reverse C z))
      (@id C (@arrow_pair_target C z)));

symbol identity_presented_pair_laws [C : Cat] (z : τ (ArrowPairData C))
  (x : τ (Obj C))
  (p : τ (@= (ArrowPairData C) z (@identity_arrow_pair C x)))
  : τ (@arrow_pair_laws C z)
≔ @ind_eq (ArrowPairData C) z (@identity_arrow_pair C x) p
    (λ w : τ (ArrowPairData C), @arrow_pair_laws C w)
    (Struct_sigma (@eq_refl (Hom C x x) (@id C x)) (@eq_refl (Hom C x x) (@id C x)));

symbol arrow_pair_map [C D : Cat] (F : τ (Functor C D))
  (z : τ (ArrowPairData C)) : τ (ArrowPairData D)
≔ @arrow_pair_data D
    (@fapp0 C D F (@arrow_pair_source C z))
    (@fapp0 C D F (@arrow_pair_target C z))
    (@fapp1_fapp0 C D F (@arrow_pair_source C z) (@arrow_pair_target C z)
      (@arrow_pair_forward C z))
    (@fapp1_fapp0 C D F (@arrow_pair_target C z) (@arrow_pair_source C z)
      (@arrow_pair_reverse C z));

symbol identity_pair_map_path [C D : Cat] (F : τ (Functor C D))
  (z : τ (ArrowPairData C)) (x : τ (Obj C))
  (p : τ (@= (ArrowPairData C) z (@identity_arrow_pair C x)))
  : τ (@= (ArrowPairData D) (@arrow_pair_map C D F z)
      (@identity_arrow_pair D (@fapp0 C D F x)))
≔ @eq_ap (ArrowPairData C) (ArrowPairData D)
    (λ w : τ (ArrowPairData C), @arrow_pair_map C D F w)
    z (@identity_arrow_pair C x) p;

symbol iso_evidence_from_identity_pair [C : Cat]
  (x y : τ (Obj C)) (f : τ (Hom C x y)) (g : τ (Hom C y x))
  (p : τ (@= (ArrowPairData C) (@arrow_pair_data C x y f g)
      (@identity_arrow_pair C x)))
  : τ (@IsoEvidence C x y)
≔ @iso_evidence_intro C x y f g
    (sigma_Fst (@identity_presented_pair_laws C (@arrow_pair_data C x y f g) x p))
    (sigma_Snd (@identity_presented_pair_laws C (@arrow_pair_data C x y f g) x p));
