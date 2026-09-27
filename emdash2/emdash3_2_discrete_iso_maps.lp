/* Mapping into a discrete target retains both original mapped arrows. */
require open emdash.emdash3_2_eq1_evidence_property;
require open emdash.emdash3_2_iso_evidence_constructors;

symbol discrete_hom_path [D : Cat] (D0 : τ (IsDiscreteCat D))
  [x y : τ (Obj D)] (f g : τ (Hom D x y)) : τ (@= (Hom D x y) f g)
≔ @is_contr_center (@= (Hom D x y) f g) ((@discrete_hom_is_prop D D0 x y) f g);

symbol discrete_iso_evidence_fmap [C D : Cat]
  (D0 : τ (IsDiscreteCat D)) (F : τ (Functor C D))
  [x y : τ (Obj C)] (i : τ (@IsoEvidence C x y))
  : τ (@IsoEvidence D (@fapp0 C D F x) (@fapp0 C D F y))
≔ @iso_evidence_intro D (@fapp0 C D F x) (@fapp0 C D F y)
    (@fapp1_fapp0 C D F x y (@iso_evidence_to C x y i))
    (@fapp1_fapp0 C D F y x (@iso_evidence_from C x y i))
    (@discrete_hom_path D D0 (@fapp0 C D F x) (@fapp0 C D F x)
      (@comp_fapp0 D _ _ _
        (@fapp1_fapp0 C D F y x (@iso_evidence_from C x y i))
        (@fapp1_fapp0 C D F x y (@iso_evidence_to C x y i)))
      (@id D (@fapp0 C D F x)))
    (@discrete_hom_path D D0 (@fapp0 C D F y) (@fapp0 C D F y)
      (@comp_fapp0 D _ _ _
        (@fapp1_fapp0 C D F x y (@iso_evidence_to C x y i))
        (@fapp1_fapp0 C D F y x (@iso_evidence_from C x y i)))
      (@id D (@fapp0 C D F y)));
