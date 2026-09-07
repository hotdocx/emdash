/* Ordinary isomorphism evidence through the existing dependent Sigma. */

require open emdash.emdash3_2;

symbol iso_evidence_intro
  [C : Cat]
  [X Y : τ (Obj C)]
  (to : τ (Hom C X Y))
  (from : τ (Hom C Y X))
  (lawL : τ (@= (Hom C X X) (@comp_fapp0 C _ _ _ from to) (@id C X)))
  (lawR : τ (@= (Hom C Y Y) (@comp_fapp0 C _ _ _ to from) (@id C Y)))
  : τ (@IsoEvidence C X Y)
≔ @Struct_sigma (Hom C X Y)
    (λ to0 : τ (Hom C X Y),
      `Σ_ from0 : τ (Hom C Y X),
      `Σ_ left0 : τ (@= (Hom C X X)
        (@comp_fapp0 C _ _ _ from0 to0) (@id C X)),
        @= (Hom C Y Y) (@comp_fapp0 C _ _ _ to0 from0) (@id C Y))
    to
    (@Struct_sigma (Hom C Y X)
      (λ from0 : τ (Hom C Y X),
        `Σ_ left0 : τ (@= (Hom C X X)
          (@comp_fapp0 C _ _ _ from0 to) (@id C X)),
          @= (Hom C Y Y) (@comp_fapp0 C _ _ _ to from0) (@id C Y))
      from
      (@Struct_sigma
        (@= (Hom C X X) (@comp_fapp0 C _ _ _ from to) (@id C X))
        (λ _ : τ _, @= (Hom C Y Y)
          (@comp_fapp0 C _ _ _ to from) (@id C Y))
        lawL lawR));
