/*
  Ordinary subterminal sieves and pullback.

  This one-way module imports the basic Cat-valued presheaf/higher-sieve
  facade and the downstream evidence-property library.  It does not change
  the kernel and it does not identify ordinary sieves with arbitrary
  Cat-valued higher sieves.

  `Omega` remains deliberately unbound.  A genuine classifier still needs a
  setness theorem for the space of ordinary sieves and an owner-aligned
  contravariant family assembly whose identity law does not reconstruct a
  retained proposition-valued evidence field.
*/

require open emdash.emdash3_2_presheaves;
require open emdash.emdash3_2_eq1_evidence_property;

/*
  Native subterminal categories.

  Proposition-valued objects alone are insufficient: a one-object category
  can retain nontrivial directed endomorphisms.  `IsGroupoidalCat(C)` adds the
  exact native condition that every cell comes from equality.  Together the
  two fields describe the empty/terminal categorical possibilities without
  assuming a literal `Path_cat` presentation.
*/
symbol IsSubterminalCat (C : Cat) : Grpd
≔ `Σ_ obj_prop : τ (IsPropGrpd (Obj C)),
   @IsGroupoidalCat C;

symbol subterminal_cat_intro
  [C : Cat]
  (obj_prop : τ (IsPropGrpd (Obj C)))
  (groupoidal : τ (@IsGroupoidalCat C))
  : τ (IsSubterminalCat C)
≔ @Struct_sigma
    (IsPropGrpd (Obj C))
    (λ _ : τ (IsPropGrpd (Obj C)), @IsGroupoidalCat C)
    obj_prop
    groupoidal;

symbol is_subterminal_cat_obj_prop
  [C : Cat]
  (h : τ (IsSubterminalCat C))
  : τ (IsPropGrpd (Obj C))
≔ sigma_Fst h;

symbol is_subterminal_cat_groupoidal
  [C : Cat]
  (h : τ (IsSubterminalCat C))
  : τ (@IsGroupoidalCat C)
≔ sigma_Snd h;

// Subterminality canonically selects an arrow between any two objects.
// Object-propositionality supplies the equality; the generic path owner turns
// it into a directed arrow without inspecting a concrete Path_cat model.
symbol subterminal_cat_arrow
  [C : Cat]
  (h : τ (@IsSubterminalCat C))
  (x y : τ (Obj C))
  : τ (Hom C x y)
≔ @path_to_hom
    C x y
    (@is_contr_center
      (@= (Obj C) x y)
      ((@is_subterminal_cat_obj_prop C h) x y));

// Every subterminal category satisfies the existing exact discrete contract.
symbol subterminal_cat_is_discrete
  [C : Cat]
  (h : τ (IsSubterminalCat C))
  : τ (IsDiscreteCat C)
≔ @discrete_cat_intro
    C
    (@prop_is_trunc_succ
      trunc_minus_one
      (Obj C)
      (@is_subterminal_cat_obj_prop C h))
    (@is_subterminal_cat_groupoidal C h);

// Literal path categories of propositions are canonical subterminal examples.
symbol path_cat_is_subterminal
  [A : Grpd]
  (h : τ (IsPropGrpd A))
  : τ (IsSubterminalCat (Path_cat A))
≔ @subterminal_cat_intro
    (Path_cat A)
    h
    (@path_cat_is_groupoidal A);

// Both retained fields are properties, so their dependent pair is a property.
symbol is_subterminal_cat_evidence_is_prop
  (C : Cat)
  : τ (IsPropGrpd (IsSubterminalCat C))
≔ @is_trunc_sigma
    trunc_minus_one
    (IsPropGrpd (Obj C))
    (λ _ : τ (IsPropGrpd (Obj C)), @IsGroupoidalCat C)
    (@is_trunc_grpd_evidence_is_prop trunc_minus_one (Obj C))
    (λ _ : τ (IsPropGrpd (Obj C)),
      @omega_equiv_along_evidence_is_prop
        Cat_cat
        (Core_cat C)
        C
        (Core_incl_func C));

/*
  Ordinary sieves as the pointwise-subterminal specialization.

  The underlying higher sieve retains all restriction and higher functorial
  data.  The extra field merely certifies that each category over an arrow
  into U is subterminal; it does not create a second action calculus.
*/
symbol IsOrdinarySieve
  [K : Cat]
  [U : τ (Obj K)]
  (S : τ (@HigherSieve K U))
  : Grpd
≔ @Pi_grpd
    (Obj (@Into_restr_cat K U))
    (λ f : τ (Obj (@Into_restr_cat K U)),
      IsSubterminalCat
        (@Fibre_cat (@Into_restr_cat K U) S f));

symbol is_ordinary_sieve_evidence_is_prop
  [K : Cat]
  [U : τ (Obj K)]
  (S : τ (@HigherSieve K U))
  : τ (IsPropGrpd (@IsOrdinarySieve K U S))
≔ @is_prop_pi
    (Obj (@Into_restr_cat K U))
    (λ f : τ (Obj (@Into_restr_cat K U)),
      IsSubterminalCat
        (@Fibre_cat (@Into_restr_cat K U) S f))
    (λ f : τ (Obj (@Into_restr_cat K U)),
      @is_subterminal_cat_evidence_is_prop
        (@Fibre_cat (@Into_restr_cat K U) S f));

// Evidence-retaining classifier of ordinary sieves on U.
symbol Sieve
  [K : Cat]
  (U : τ (Obj K))
  : Grpd
≔ `Σ_ S : τ (@HigherSieve K U),
   @IsOrdinarySieve K U S;

symbol sieve_intro
  [K : Cat]
  [U : τ (Obj K)]
  (S : τ (@HigherSieve K U))
  (h : τ (@IsOrdinarySieve K U S))
  : τ (@Sieve K U)
≔ @Struct_sigma
    (@HigherSieve K U)
    (λ T : τ (@HigherSieve K U), @IsOrdinarySieve K U T)
    S
    h;

symbol sieve_higher
  [K : Cat]
  [U : τ (Obj K)]
  (R : τ (@Sieve K U))
  : τ (@HigherSieve K U)
≔ sigma_Fst R;

symbol sieve_subterminal
  [K : Cat]
  [U : τ (Obj K)]
  (R : τ (@Sieve K U))
  : τ (@IsOrdinarySieve K U (@sieve_higher K U R))
≔ sigma_Snd R;

/*
  Pullback of ordinary sieves.

  Higher-sieve restriction is already Catd pullback along the Sigma-total
  arrow map.  Pointwise subterminality is therefore preserved by selecting
  the witness at the image arrow; no new rewrite or unification rule is
  installed.
*/
symbol ordinary_sieve_pullback_evidence
  [K : Cat]
  [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (S : τ (@HigherSieve K U))
  (h : τ (@IsOrdinarySieve K U S))
  : τ (@IsOrdinarySieve K V (@higher_sieve_pullback K V U p S))
≔ λ f : τ (Obj (@Into_restr_cat K V)),
    h
      (@fapp0
        (@Into_restr_cat K V)
        (@Into_restr_cat K U)
        (@fapp1_fapp0 K Cat_cat (@arrow_into_catd K) V U p)
        f);

symbol sieve_pullback
  [K : Cat]
  [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (R : τ (@Sieve K U))
  : τ (@Sieve K V)
≔ @sieve_intro
    K V
    (@higher_sieve_pullback K V U p (@sieve_higher K U R))
    (@ordinary_sieve_pullback_evidence
      K V U p
      (@sieve_higher K U R)
      (@sieve_subterminal K U R));

symbol sieve_pullback_function
  [K : Cat]
  [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  : τ (@Function_grpd (@Sieve K U) (@Sieve K V))
≔ λ R : τ (@Sieve K U), @sieve_pullback K V U p R;
