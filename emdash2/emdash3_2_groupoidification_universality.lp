/*
  Whole universal property of category-indexed groupoidification.

  Restriction acts through Path_cat_func and precomposition with the whole
  groupoidification unit.  The primitive categorical-HIT recursor is its
  selected inverse.  Whole beta and eta are the scoped uniqueness clauses of
  this indexed HIT; they are equality evidence rather than runtime rewrites,
  so ordinary functoriality and all higher action remain owned by the two
  whole functors.

  This module constructs the mapping-object equivalence for arbitrary
  C : Cat and G : Grpd.  It does not yet package source action,
  Groupoidify_func, or an adjunction.
*/

require open emdash.emdash3_2_groupoidification_hit;

// Whole restriction along the generic unit.
symbol groupoidify_restrict_func
  (C : Cat)
  (G : Grpd)
  : τ (@Functor
      (@Hom_cat Grpd_cat (@Groupoidify C) G)
      (@Functor_cat C (Path_cat G)))
≔ @comp_cat_fapp0
    (@Hom_cat Grpd_cat (@Groupoidify C) G)
    (@Functor_cat (Path_cat (@Groupoidify C)) (Path_cat G))
    (@Functor_cat C (Path_cat G))
    (@comp_cat_con_func
      C (Path_cat (@Groupoidify C)) (Path_cat G)
      (@groupoidify_unit_func C))
    (@fapp1_func
      Grpd_cat Cat_cat Path_cat_func
      (@Groupoidify C) G);

// Representation selected by restricting one groupoidal map.
symbol groupoidify_restrict_at
  [C : Cat]
  [G : Grpd]
  (h : τ (@Function_grpd (@Groupoidify C) G))
  : τ (@Functor C (Path_cat G))
≔ @fapp0
    (@Hom_cat Grpd_cat (@Groupoidify C) G)
    (@Functor_cat C (Path_cat G))
    (@groupoidify_restrict_func C G)
    h;

// Whole proof-time comparison with literal Path action and composition.
symbol groupoidify_restrict_at_path
  [C : Cat]
  [G : Grpd]
  (h : τ (@Function_grpd (@Groupoidify C) G))
  : τ (@=
      (Functor C (Path_cat G))
      (@groupoidify_restrict_at C G h)
      (@comp_cat_fapp0
        C (Path_cat (@Groupoidify C)) (Path_cat G)
        (@path_map_func (@Groupoidify C) G h)
        (@groupoidify_unit_func C)))
≔ @eq_refl
    (Functor C (Path_cat G))
    (@hom_precomp_along_fapp0
      Cat_cat Cat_cat (@id Cat_cat Cat_cat)
      (Path_cat G)
      C (Path_cat (@Groupoidify C))
      (@groupoidify_unit_func C)
      (@path_map_func (@Groupoidify C) G h));

// Whole categorical-HIT beta: restriction after extension is identity.
constant symbol groupoidify_restrict_extend_beta_func_path
  [C : Cat]
  [G : Grpd]
  : τ (@=
      (Hom
        Cat_cat
        (Functor_cat C (Path_cat G))
        (Functor_cat C (Path_cat G)))
      (@comp_cat_fapp0
        (Functor_cat C (Path_cat G))
        (Hom_cat Grpd_cat (Groupoidify C) G)
        (Functor_cat C (Path_cat G))
        (@groupoidify_restrict_func C G)
        (@groupoidify_extend_func C G))
      (@id Cat_cat (Functor_cat C (Path_cat G))));

// Whole categorical-HIT eta/uniqueness: extension after restriction is id.
constant symbol groupoidify_extend_restrict_eta_func_path
  [C : Cat]
  [G : Grpd]
  : τ (@=
      (Hom
        Cat_cat
        (Hom_cat Grpd_cat (Groupoidify C) G)
        (Hom_cat Grpd_cat (Groupoidify C) G))
      (@comp_cat_fapp0
        (Hom_cat Grpd_cat (Groupoidify C) G)
        (Functor_cat C (Path_cat G))
        (Hom_cat Grpd_cat (Groupoidify C) G)
        (@groupoidify_extend_func C G)
        (@groupoidify_restrict_func C G))
      (@id Cat_cat
        (Hom_cat Grpd_cat (Groupoidify C) G)));

// Fixed-forward whole mapping-object equivalence.
symbol groupoidification_hom_omega
  [C : Cat]
  [G : Grpd]
  : τ (@OmegaEquivAlong
      Cat_cat
      (Hom_cat Grpd_cat (Groupoidify C) G)
      (Functor_cat C (Path_cat G))
      (@groupoidify_restrict_func C G))
≔ @omega_equiv_along_intro
    Cat_cat
    (Hom_cat Grpd_cat (Groupoidify C) G)
    (Functor_cat C (Path_cat G))
    (@groupoidify_restrict_func C G)
    (@groupoidify_extend_func C G)
    (@groupoidify_extend_func C G)
    (@groupoidify_extend_restrict_eta_func_path C G)
    (@groupoidify_restrict_extend_beta_func_path C G);

// Object projection of whole beta.
symbol groupoidify_restrict_extend_beta_at_path
  [C : Cat]
  [G : Grpd]
  (F : τ (@Functor C (Path_cat G)))
  : τ (@=
      (Functor C (Path_cat G))
      (@groupoidify_restrict_at C G (@groupoidify_extend_at C G F))
      F)
≔ @eq_ap
    (Hom
      Cat_cat
      (Functor_cat C (Path_cat G))
      (Functor_cat C (Path_cat G)))
    (Functor C (Path_cat G))
    (λ K : τ (Hom
      Cat_cat
      (Functor_cat C (Path_cat G))
      (Functor_cat C (Path_cat G))),
      @fapp0
        (Functor_cat C (Path_cat G))
        (Functor_cat C (Path_cat G))
        K F)
    (@comp_cat_fapp0
      (Functor_cat C (Path_cat G))
      (Hom_cat Grpd_cat (Groupoidify C) G)
      (Functor_cat C (Path_cat G))
      (@groupoidify_restrict_func C G)
      (@groupoidify_extend_func C G))
    (@id Cat_cat (Functor_cat C (Path_cat G)))
    (@groupoidify_restrict_extend_beta_func_path C G);

// Object projection of whole eta/uniqueness.
symbol groupoidify_extend_restrict_eta_at_path
  [C : Cat]
  [G : Grpd]
  (h : τ (@Function_grpd (@Groupoidify C) G))
  : τ (@=
      (@Function_grpd (@Groupoidify C) G)
      (@groupoidify_extend_at C G (@groupoidify_restrict_at C G h))
      h)
≔ @eq_ap
    (Hom
      Cat_cat
      (Hom_cat Grpd_cat (Groupoidify C) G)
      (Hom_cat Grpd_cat (Groupoidify C) G))
    (@Function_grpd (Groupoidify C) G)
    (λ K : τ (Hom
      Cat_cat
      (Hom_cat Grpd_cat (Groupoidify C) G)
      (Hom_cat Grpd_cat (Groupoidify C) G)),
      @fapp0
        (Hom_cat Grpd_cat (Groupoidify C) G)
        (Hom_cat Grpd_cat (Groupoidify C) G)
        K h)
    (@comp_cat_fapp0
      (Hom_cat Grpd_cat (Groupoidify C) G)
      (Functor_cat C (Path_cat G))
      (Hom_cat Grpd_cat (Groupoidify C) G)
      (@groupoidify_extend_func C G)
      (@groupoidify_restrict_func C G))
    (@id Cat_cat (Hom_cat Grpd_cat (Groupoidify C) G))
    (@groupoidify_extend_restrict_eta_func_path C G);

// Restriction itself retains its first hom action.
symbol groupoidify_restrict_hom_func
  [C : Cat]
  [G : Grpd]
  [h k : τ (@Function_grpd (@Groupoidify C) G)]
  : τ (@Functor
      (@Hom_cat
        (@Hom_cat Grpd_cat (@Groupoidify C) G)
        h k)
      (@Hom_cat
        (@Functor_cat C (Path_cat G))
        (@groupoidify_restrict_at C G h)
        (@groupoidify_restrict_at C G k)))
≔ @fapp1_func
    (@Hom_cat Grpd_cat (@Groupoidify C) G)
    (@Functor_cat C (Path_cat G))
    (@groupoidify_restrict_func C G)
    h k;
