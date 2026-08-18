/*
  Category-indexed free groupoidification HIT.

  Groupoidify(C) freely realizes every represented directed cell of C as a
  groupoidal path cell.  The constructor is one whole functor rather than an
  object/arrow graph encoding.  Recursion into a groupoid G is selected by a
  whole representation F : C -> Path_cat(G): point computation is a runtime
  normal form and dependent action on every represented source arrow computes
  through the stable eq_apd owner.

  The target-varying whole extension is the categorical-HIT recursor owner.
  Its generic first and next hom actions remain available without a tactics
  layer or a handwritten hierarchy of cell constructors.  Whole uniqueness
  and the mapping-object equivalence are supplied by the subsequent
  universality module.
*/

require open emdash.emdash3_2;

// Category-indexed formation.  This is the eventual source-object action,
// not yet a declaration of Groupoidify_func : Cat_cat -> Grpd_cat.
constant symbol Groupoidify
  (C : Cat)
  : Grpd;

// One whole constructor represents objects, arrows, and all iterated cells.
injective symbol groupoidify_unit_func
  (C : Cat)
  : τ (@Functor C (Path_cat (@Groupoidify C)));

// Nondependent recursion selected by a complete path-valued representation.
injective symbol groupoidify_rec
  (C : Cat)
  (G : Grpd)
  (F : τ (@Functor C (Path_cat G)))
  (u : τ (@Groupoidify C))
  : τ G;

// Runtime point computation at every object selected by the whole unit.
rule @groupoidify_rec $C $G $F
      (@fapp0 _ _ (@groupoidify_unit_func $C) $x)
  ↪ @fapp0 $C (Path_cat $G) $F $x;

/*
  Dependent action on a represented source arrow computes to the selected
  representation arrow embedded in the constant motive.  The source category
  and inferred fapp1 endpoints are reconstructible.  The target groupoid and
  representation remain named beneath the lambda because each is required on
  the RHS; deleting either leaves an unbound pattern variable.
*/
// lhs-audit: keep 2,3 -- G/F are required RHS variables; either `_` is unbound
rule @eq_apd
      (@Groupoidify $C)
      _
      (λ u : τ _, @groupoidify_rec _ $G.[] $F.[] u)
      _ _
      (@fapp1_fapp0 _ _ (@groupoidify_unit_func $C) $x $y $f)
  ↪ @const_pathover
      (@Groupoidify $C) $G
      (@fapp0 $C (Path_cat (@Groupoidify $C))
        (@groupoidify_unit_func $C) $x)
      (@fapp0 $C (Path_cat (@Groupoidify $C))
        (@groupoidify_unit_func $C) $y)
      (@fapp0 $C (Path_cat $G) $F $x)
      (@fapp0 $C (Path_cat $G) $F $y)
      (@fapp1_fapp0
        $C (Path_cat (@Groupoidify $C))
        (@groupoidify_unit_func $C) $x $y $f)
      (@fapp1_fapp0 $C (Path_cat $G) $F $x $y $f);

// Raw function deployed by recursion.
symbol groupoidify_rec_function
  (C : Cat)
  (G : Grpd)
  (F : τ (@Functor C (Path_cat G)))
  : τ (@Function_grpd (@Groupoidify C) G)
≔ λ u : τ (@Groupoidify C), @groupoidify_rec C G F u;

// The recursor varies as one whole functor in the representation F.
injective symbol groupoidify_extend_func
  (C : Cat)
  (G : Grpd)
  : τ (@Functor
      (@Functor_cat C (Path_cat G))
      (@Hom_cat Grpd_cat (@Groupoidify C) G));

// Runtime object beta selects the deployed recursive function.
rule @fapp0 _ _ (@groupoidify_extend_func $C $G) $F
  ↪ @groupoidify_rec_function $C $G $F;

// Selected extension at one representation.
symbol groupoidify_extend_at
  [C : Cat]
  [G : Grpd]
  (F : τ (@Functor C (Path_cat G)))
  : τ (@Function_grpd (@Groupoidify C) G)
≔ @fapp0
    (@Functor_cat C (Path_cat G))
    (@Hom_cat Grpd_cat (@Groupoidify C) G)
    (@groupoidify_extend_func C G)
    F;

// The first hom action of the whole extension remains iterable.
symbol groupoidify_extend_hom_func
  [C : Cat]
  [G : Grpd]
  [F H : τ (@Functor C (Path_cat G))]
  : τ (@Functor
      (@Hom_cat (@Functor_cat C (Path_cat G)) F H)
      (@Hom_cat
        (@Hom_cat Grpd_cat (@Groupoidify C) G)
        (@groupoidify_extend_at C G F)
        (@groupoidify_extend_at C G H)))
≔ @fapp1_func
    (@Functor_cat C (Path_cat G))
    (@Hom_cat Grpd_cat (@Groupoidify C) G)
    (@groupoidify_extend_func C G)
    F H;

// One retained next action witnesses that extension is not object-only.
symbol groupoidify_extend_next_func
  [C : Cat]
  [G : Grpd]
  [F H : τ (@Functor C (Path_cat G))]
  [eta theta : τ (@Transf C (Path_cat G) F H)]
  : τ (@Functor
      (@Hom_cat
        (@Hom_cat (@Functor_cat C (Path_cat G)) F H)
        eta theta)
      (@Hom_cat
        (@Hom_cat
          (@Hom_cat Grpd_cat (@Groupoidify C) G)
          (@groupoidify_extend_at C G F)
          (@groupoidify_extend_at C G H))
        (@fapp1_fapp0
          (@Functor_cat C (Path_cat G))
          (@Hom_cat Grpd_cat (@Groupoidify C) G)
          (@groupoidify_extend_func C G)
          F H eta)
        (@fapp1_fapp0
          (@Functor_cat C (Path_cat G))
          (@Hom_cat Grpd_cat (@Groupoidify C) G)
          (@groupoidify_extend_func C G)
          F H theta)))
≔ @fapp1_func
    (@Hom_cat (@Functor_cat C (Path_cat G)) F H)
    (@Hom_cat
      (@Hom_cat Grpd_cat (@Groupoidify C) G)
      (@groupoidify_extend_at C G F)
      (@groupoidify_extend_at C G H))
    (@groupoidify_extend_hom_func C G F H)
    eta theta;
