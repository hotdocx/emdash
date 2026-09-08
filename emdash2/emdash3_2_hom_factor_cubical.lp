/*
  Hom-factor points as arrows of the existing derived lax-arrow category.

  For u:A0→B0 and v:A1→B1, the native Hom has objects (a,(b,α)),
  with α:b∘u⇒v∘a. This type comes from nested Sigma/opposite/homd_int,
  not an independently declared square grammar.

  These compatibility definitions reuse the factor's existing reconstruction
  path (symmetrized for postcomposition). No new equation is supplied or
  assumed. The whole comparisons lift the equality-valued factor spaces;
  no inverse from arbitrary directed squares is claimed.
*/
require open emdash.emdash3_2_hom_factor_spaces;
require open emdash.emdash3_2_cubical_internalization;

// A postcomposition factor v ∘ a = b ∘ u gives the existing native square.
symbol hom_postcomp_factor_square
  [C : Cat]
  [A0 B0 A1 B1 : τ (Obj C)]
  (u : τ (Hom C A0 B0))
  (v : τ (Hom C A1 B1))
  (b : τ (Hom C B0 B1))
  (factor : τ (@HomPostcompFactor C A1 B1 A0 v
    (@comp_fapp0 C A0 B0 B1 b u)))
  : τ (Hom (@LaxArrow_cat C)
      (@lax_edge C A0 B0 u) (@lax_edge C A1 B1 v))
≔ @lax_square C A0 A1 B0 B1 u v
    (@hom_postcomp_factor_arrow C A1 B1 A0 v
      (@comp_fapp0 C A0 B0 B1 b u) factor)
    b
    (@path_to_hom (Hom_cat C A0 B1)
      (@comp_fapp0 C A0 B0 B1 b u)
      (@comp_fapp0 C A0 A1 B1 v
        (@hom_postcomp_factor_arrow C A1 B1 A0 v
          (@comp_fapp0 C A0 B0 B1 b u) factor))
      (@eq_sym (Hom C A0 B1) _ _
        (@hom_postcomp_factor_path C A1 B1 A0 v
          (@comp_fapp0 C A0 B0 B1 b u) factor)));

// A precomposition factor b ∘ u = v ∘ a has the native orientation already.
symbol hom_precomp_factor_square
  [C : Cat]
  [A0 B0 A1 B1 : τ (Obj C)]
  (u : τ (Hom C A0 B0))
  (v : τ (Hom C A1 B1))
  (a : τ (Hom C A0 A1))
  (factor : τ (@HomPrecompFactor C A0 B0 B1 u
    (@comp_fapp0 C A0 A1 B1 v a)))
  : τ (Hom (@LaxArrow_cat C)
      (@lax_edge C A0 B0 u) (@lax_edge C A1 B1 v))
≔ @lax_square C A0 A1 B0 B1 u v a
    (@hom_precomp_factor_arrow C A0 B0 B1 u
      (@comp_fapp0 C A0 A1 B1 v a) factor)
    (@path_to_hom (Hom_cat C A0 B1)
      (@comp_fapp0 C A0 B0 B1
        (@hom_precomp_factor_arrow C A0 B0 B1 u
          (@comp_fapp0 C A0 A1 B1 v a) factor) u)
      (@comp_fapp0 C A0 A1 B1 v a)
      (@hom_precomp_factor_path C A0 B0 B1 u
        (@comp_fapp0 C A0 A1 B1 v a) factor));

// Whole fixed-boundary comparisons. Path lifting retains all higher action;
// it is not a construction of the globally varying category of chain maps.
symbol hom_postcomp_factor_square_func
  [C : Cat]
  [A0 B0 A1 B1 : τ (Obj C)]
  (u : τ (Hom C A0 B0))
  (v : τ (Hom C A1 B1))
  (b : τ (Hom C B0 B1))
  : τ (Functor
      (Path_cat (@HomPostcompFactor C A1 B1 A0 v
        (@comp_fapp0 C A0 B0 B1 b u)))
      (Hom_cat (@LaxArrow_cat C)
        (@lax_edge C A0 B0 u) (@lax_edge C A1 B1 v)))
≔ @fapp0 _ _
    (@path_lift_func
      (@HomPostcompFactor C A1 B1 A0 v
        (@comp_fapp0 C A0 B0 B1 b u))
      (Hom_cat (@LaxArrow_cat C)
        (@lax_edge C A0 B0 u) (@lax_edge C A1 B1 v)))
    (@hom_postcomp_factor_square C A0 B0 A1 B1 u v b);

symbol hom_precomp_factor_square_func
  [C : Cat]
  [A0 B0 A1 B1 : τ (Obj C)]
  (u : τ (Hom C A0 B0))
  (v : τ (Hom C A1 B1))
  (a : τ (Hom C A0 A1))
  : τ (Functor
      (Path_cat (@HomPrecompFactor C A0 B0 B1 u
        (@comp_fapp0 C A0 A1 B1 v a)))
      (Hom_cat (@LaxArrow_cat C)
        (@lax_edge C A0 B0 u) (@lax_edge C A1 B1 v)))
≔ @fapp0 _ _
    (@path_lift_func
      (@HomPrecompFactor C A0 B0 B1 u
        (@comp_fapp0 C A0 A1 B1 v a))
      (Hom_cat (@LaxArrow_cat C)
        (@lax_edge C A0 B0 u) (@lax_edge C A1 B1 v)))
    (@hom_precomp_factor_square C A0 B0 A1 B1 u v a);
