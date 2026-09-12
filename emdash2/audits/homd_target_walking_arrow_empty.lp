/* NON-LIBRARY ordinary-shape control for the Homd target diagnostic.
   F is introduced from an actual arrow, with the existing walking-arrow
   recursor. Acceptance is a reproduced defect, not a positive library test.
   This is not a proof of independence from all other imported defects. */
require open emdash.audits.homd_target_empty_reproducer;
require open emdash.emdash3_2_walking_arrow_introduction;

symbol homd_target_walking_reverse [C : Cat]
  (x y : τ (Obj C)) (f : τ (Hom C x y))
  : τ (Hom C y x)
≔ @fapp0 (Hom_cat C y y) (Hom_cat C y x)
    (@homd_target_polarity_reverse_functor WalkingArrow_cat C
      (@walking_arrow_func C x y f)
      walking_arrow_src walking_arrow_tgt y walking_arrow_generator)
    (@id C y);

symbol homd_target_walking_empty : τ Empty_grpd
≔ (@homd_target_walking_reverse Grpd_cat Empty_grpd Unit_grpd
    (λ _ : τ Empty_grpd, tt)) tt;

assert ⊢ homd_target_walking_empty : τ Empty_grpd;
