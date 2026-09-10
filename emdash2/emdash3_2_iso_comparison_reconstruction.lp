/* Reverse a source comparison along its actual isomorphism.
   This generic proof also owns the former kernel-domain specialization. */
require open emdash.emdash3_2;

symbol iso_source_comparison_reverse_path
  [C : Cat] [X Y B : τ (Obj C)]
  (d0 : τ (Hom C X B)) (d1 : τ (Hom C Y B))
  (iso : τ (@IsoEvidence C X Y))
  (comparison : τ (@= (Hom C X B) d0
    (@comp_fapp0 C X Y B d1 (@iso_evidence_to C X Y iso))))
  : τ (@= (Hom C Y B)
    (@comp_fapp0 C Y X B d0 (@iso_evidence_from C X Y iso)) d1)
≔ @eq_trans _ _ _ _
    (@eq_ap (Hom C X B) (Hom C Y B)
      (λ h : τ (Hom C X B), @comp_fapp0 C Y X B h (@iso_evidence_from C X Y iso))
      _ _ comparison)
    (@eq_trans _ _ _ _
      (@eq_sym _ _ _ (@comp_assoc C Y X Y B d1
        (@iso_evidence_to C X Y iso) (@iso_evidence_from C X Y iso)))
      (@eq_ap (Hom C Y Y) (Hom C Y B)
        (λ h : τ (Hom C Y Y), @comp_fapp0 C Y Y B d1 h)
        _ _ (@iso_evidence_right C X Y iso)));
