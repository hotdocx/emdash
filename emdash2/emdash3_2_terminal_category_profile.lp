/* Closed profile for the literal terminal category.
   The ground proof-time eta instance states id₁ = const₍*₎ at the whole functor level.
   This is an explicit terminal-former conversion extension, not a theorem
   derived from the old beta interface. Runtime functor heads are retained.
   Both inverse functors below are explicit terms; only the inverse laws
   use equality evidence. No general higher terminality theorem is asserted. */
require open emdash.emdash3_2_discrete_functor_paths;
require open emdash.emdash3_2_nat_arithmetic;

// Literal source, target and canonical point delimit the terminal eta instance.
unif_rule @Const_func Terminal_cat Terminal_cat Terminal_obj
  ≡ @id Cat_cat Terminal_cat ↪ [ tt ≡ tt ];

symbol terminal_category_object_set : τ (IsSetGrpd Unit_grpd)
≔ @prop_is_trunc_cat_dim cat_zero Unit_grpd unit_is_prop;

symbol terminal_category_core_discrete : τ (IsDiscreteCat (Core_cat Terminal_cat))
≔ @discrete_cat_intro (Core_cat Terminal_cat) terminal_category_object_set
    (path_cat_is_groupoidal Unit_grpd);

// Both inverse projections retain this actual functor.
symbol terminal_category_core_inverse : τ (Functor Terminal_cat (Core_cat Terminal_cat))
≔ @Const_func Terminal_cat (Core_cat Terminal_cat) Terminal_obj;

// The target is Path(Unit); its genuinely discrete pointwise assembly suffices.
symbol terminal_category_core_left_law
  : τ (@= (Functor (Core_cat Terminal_cat) (Core_cat Terminal_cat))
      (@comp_cat_fapp0 (Core_cat Terminal_cat) Terminal_cat (Core_cat Terminal_cat)
        terminal_category_core_inverse (Core_incl_func Terminal_cat))
      (@id_func (Core_cat Terminal_cat)))
≔ @discrete_functor_path (Core_cat Terminal_cat) (Core_cat Terminal_cat)
    terminal_category_core_discrete
    (@comp_cat_fapp0 (Core_cat Terminal_cat) Terminal_cat (Core_cat Terminal_cat)
      terminal_category_core_inverse (Core_incl_func Terminal_cat))
    (@id_func (Core_cat Terminal_cat))
    (λ x : τ Unit_grpd, @is_contr_path Unit_grpd
      (@is_contr_recenter Unit_grpd unit_is_contr Terminal_obj) x);

// The other roundtrip computes to the constant canonical-point endofunctor.
symbol terminal_category_core_right_law
  : τ (@= (Functor Terminal_cat Terminal_cat)
      (@comp_cat_fapp0 Terminal_cat (Core_cat Terminal_cat) Terminal_cat
        (Core_incl_func Terminal_cat) terminal_category_core_inverse)
      (@id_func Terminal_cat))
≔ @eq_refl (Functor Terminal_cat Terminal_cat) (@id_func Terminal_cat);

symbol terminal_category_groupoidal : τ (IsGroupoidalCat Terminal_cat)
≔ @omega_equiv_along_intro Cat_cat (Core_cat Terminal_cat) Terminal_cat
    (Core_incl_func Terminal_cat)
    terminal_category_core_inverse terminal_category_core_inverse
    terminal_category_core_left_law terminal_category_core_right_law;

symbol terminal_category_discrete : τ (IsDiscreteCat Terminal_cat)
≔ @discrete_cat_intro Terminal_cat terminal_category_object_set terminal_category_groupoidal;

symbol terminal_category_one_cat : τ (IsNCat (cat_succ cat_zero) Terminal_cat)
≔ λ x : τ Unit_grpd, λ y : τ Unit_grpd, terminal_category_discrete;

// Explicit isomorphism between any two objects of the literal terminal category.
symbol terminal_category_arrow_iso (a b : τ (Obj Terminal_cat))
  : τ (IsoEvidence Terminal_cat a b)
≔ Struct_sigma Terminal_obj (Struct_sigma Terminal_obj
    (Struct_sigma (@eq_refl Unit_grpd Terminal_obj) (@eq_refl Unit_grpd Terminal_obj)));
