/*
  Focused reviewer for the set-truncated sequential-localization categorical
  HIT, its derived whole mapping-space universal property, and the executable
  inverse of the localized transition.
*/

require open emdash.emdash3_2_telescope_localization_hit;

assert [A : Grpd]
  (s : τ (@Function_grpd A A)) ⊢
  @TelescopeLocalization_grpd A s : Grpd;

assert [A : Grpd]
  (s : τ (@Function_grpd A A))
  (n : τ Nat_grpd)
  (x : τ A) ⊢
  @telescope_localization_inc A s n x
  : τ (@TelescopeLocalization_grpd A s);

assert [A : Grpd]
  (s : τ (@Function_grpd A A))
  (n : τ Nat_grpd)
  (x : τ A) ⊢
  @telescope_localization_step A s n x
  : τ (@=
      (@TelescopeLocalization_grpd A s)
      (@telescope_localization_inc A s (succ n) (s x))
      (@telescope_localization_inc A s n x));

assert [A : Grpd]
  (s : τ (@Function_grpd A A)) ⊢
  @telescope_localization_is_set A s
  : τ (IsSetGrpd (@TelescopeLocalization_grpd A s));

assert [A B : Grpd]
  (s : τ (@Function_grpd A A))
  (hB : τ (IsSetGrpd B))
  (d : τ (@TelescopeLocalizationCocone_grpd A s B))
  (n : τ Nat_grpd)
  (x : τ A) ⊢
  @telescope_localization_elim A s B hB d
    (@telescope_localization_inc A s n x)
  ≡ @telescope_localization_cocone_stage A s B d n x;

assert [A B : Grpd]
  (s : τ (@Function_grpd A A))
  (hB : τ (IsSetGrpd B))
  (d : τ (@TelescopeLocalizationCocone_grpd A s B))
  (n : τ Nat_grpd)
  (x : τ A) ⊢
  @telescope_localization_elim_step_beta A s B hB d n x
  : τ (@=
      (@= B
        (@telescope_localization_cocone_stage A s B d (succ n) (s x))
        (@telescope_localization_cocone_stage A s B d n x))
      (@eq_ap
        (@TelescopeLocalization_grpd A s)
        B
        (λ z : τ (@TelescopeLocalization_grpd A s),
          @telescope_localization_elim A s B hB d z)
        (@telescope_localization_inc A s (succ n) (s x))
        (@telescope_localization_inc A s n x)
        (@telescope_localization_step A s n x))
      (@telescope_localization_cocone_step A s B d n x));

assert [A B : Grpd]
  (s : τ (@Function_grpd A A))
  (hB : τ (IsSetGrpd B)) ⊢
  @telescope_localization_eliminator_equiv A s B hB
  : τ (@OmegaEquivAlong
      Grpd_cat
      (@Function_grpd (@TelescopeLocalization_grpd A s) B)
      (@TelescopeLocalizationCocone_grpd A s B)
      (@telescope_localization_restrict_map A s B));

assert [A : Grpd]
  (s : τ (@Function_grpd A A))
  (n : τ Nat_grpd)
  (x : τ A) ⊢
  @telescope_localization_forward A s
    (@telescope_localization_inc A s n x)
  ≡ @telescope_localization_inc A s n (s x);

assert [A : Grpd]
  (s : τ (@Function_grpd A A))
  (n : τ Nat_grpd)
  (x : τ A) ⊢
  @telescope_localization_inverse A s
    (@telescope_localization_inc A s n x)
  ≡ @telescope_localization_inc A s (succ n) x;

assert [A : Grpd]
  (s : τ (@Function_grpd A A)) ⊢
  @telescope_localization_forward_equiv A s
  : τ (@OmegaEquivAlong
      Grpd_cat
      (@TelescopeLocalization_grpd A s)
      (@TelescopeLocalization_grpd A s)
      (@telescope_localization_forward A s));

// The path constructor is proof data; its endpoints do not judgmentally fold.
assertnot [A : Grpd]
  (s : τ (@Function_grpd A A))
  (n : τ Nat_grpd)
  (x : τ A) ⊢
  @telescope_localization_inc A s (succ n) (s x)
  ≡ @telescope_localization_inc A s n x;
