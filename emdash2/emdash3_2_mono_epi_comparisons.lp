/* Monic factors and inverse comparisons at the generic cancellation owners. */

require open emdash.emdash3_2_iso_evidence_constructors;
require open emdash.emdash3_2_abelian_categories;

/* A monic composite makes its first factor monic. */


symbol is_monic_of_monic_factor
  [C : Cat]
  [A B D : τ (Obj C)]
  (a : τ (Hom C A B))
  (b : τ (Hom C B D))
  (m : τ (Hom C A D))
  (factor : τ (@= (Hom C A D) (@comp_fapp0 C _ _ _ b a) m))
  (monic : τ (@IsMonic C A D m))
  : τ (@IsMonic C A B a)
≔ λ T : τ (Obj C),
   λ u : τ (Hom C T A),
   λ v : τ (Hom C T A),
   λ p : τ (@= (Hom C T B)
      (@comp_fapp0 C _ _ _ a u)
      (@comp_fapp0 C _ _ _ a v)),
     monic T u v
       (@eq_trans _ _ _ _
         (@eq_ap (Hom C A D) (Hom C T D)
           (λ h : τ (Hom C A D), @comp_fapp0 C _ _ _ h u)
           _ _ (@eq_sym _ _ _ factor))
         (@eq_trans _ _ _ _
           (@eq_sym _ _ _ (@comp_assoc C _ _ _ _ b a u))
           (@eq_trans _ _ _ _
             (@eq_ap (Hom C T B) (Hom C T D)
               (λ h : τ (Hom C T B), @comp_fapp0 C _ _ _ b h)
               _ _ p)
             (@eq_trans _ _ _ _
               (@comp_assoc C _ _ _ _ b a v)
               (@eq_ap (Hom C A D) (Hom C T D)
                 (λ h : τ (Hom C A D), @comp_fapp0 C _ _ _ h v)
                 _ _ factor)))));

/* Mutually reconstructing comparisons of epic arrows are inverses. */


symbol epic_comparison_inverse_path
  [C : Cat]
  [B X Y : τ (Obj C)]
  (e : τ (Hom C B X))
  (d : τ (Hom C B Y))
  (to : τ (Hom C X Y))
  (from : τ (Hom C Y X))
  (epic : τ (@IsEpic C B X e))
  (forward : τ (@= (Hom C B Y) (@comp_fapp0 C _ _ _ to e) d))
  (backward : τ (@= (Hom C B X) (@comp_fapp0 C _ _ _ from d) e))
  : τ (@= (Hom C X X) (@comp_fapp0 C _ _ _ from to) (@id C X))
≔ epic X (@comp_fapp0 C _ _ _ from to) (@id C X)
    (@eq_trans _ _ _ _
      (@eq_sym _ _ _ (@comp_assoc C _ _ _ _ from to e))
      (@eq_trans _ _ _ _
        (@eq_ap (Hom C B Y) (Hom C B X)
          (λ h : τ (Hom C B Y), @comp_fapp0 C _ _ _ from h)
          _ _ forward)
        backward));

symbol iso_from_epic_comparisons
  [C : Cat]
  [B X Y : τ (Obj C)]
  (e : τ (Hom C B X))
  (d : τ (Hom C B Y))
  (to : τ (Hom C X Y))
  (from : τ (Hom C Y X))
  (e_epic : τ (@IsEpic C B X e))
  (d_epic : τ (@IsEpic C B Y d))
  (forward : τ (@= (Hom C B Y) (@comp_fapp0 C _ _ _ to e) d))
  (backward : τ (@= (Hom C B X) (@comp_fapp0 C _ _ _ from d) e))
  : τ (@IsoEvidence C X Y)
≔ @iso_evidence_intro C X Y to from
    (@epic_comparison_inverse_path C B X Y
      e d to from e_epic forward backward)
    (@epic_comparison_inverse_path C B Y X
      d e from to d_epic backward forward);

/* Mutually reconstructing comparisons of monic arrows are inverses. */


symbol monic_comparison_inverse_path
  [C : Cat]
  [X Y B : τ (Obj C)]
  (e : τ (Hom C X B))
  (d : τ (Hom C Y B))
  (to : τ (Hom C X Y))
  (from : τ (Hom C Y X))
  (monic : τ (@IsMonic C X B e))
  (forward : τ (@= (Hom C X B) (@comp_fapp0 C _ _ _ d to) e))
  (backward : τ (@= (Hom C Y B) (@comp_fapp0 C _ _ _ e from) d))
  : τ (@= (Hom C X X) (@comp_fapp0 C _ _ _ from to) (@id C X))
≔ monic X (@comp_fapp0 C _ _ _ from to) (@id C X)
    (@eq_trans _ _ _ _
      (@comp_assoc C _ _ _ _ e from to)
      (@eq_trans _ _ _ _
        (@eq_ap (Hom C Y B) (Hom C X B)
          (λ h : τ (Hom C Y B), @comp_fapp0 C _ _ _ h to)
          _ _ backward)
        forward));

symbol iso_from_monic_comparisons
  [C : Cat]
  [X Y B : τ (Obj C)]
  (e : τ (Hom C X B))
  (d : τ (Hom C Y B))
  (to : τ (Hom C X Y))
  (from : τ (Hom C Y X))
  (e_monic : τ (@IsMonic C X B e))
  (d_monic : τ (@IsMonic C Y B d))
  (forward : τ (@= (Hom C X B) (@comp_fapp0 C _ _ _ d to) e))
  (backward : τ (@= (Hom C Y B) (@comp_fapp0 C _ _ _ e from) d))
  : τ (@IsoEvidence C X Y)
≔ @iso_evidence_intro C X Y to from
    (@monic_comparison_inverse_path C X Y B
      e d to from e_monic forward backward)
    (@monic_comparison_inverse_path C Y X B
      d e from to d_monic backward forward);
