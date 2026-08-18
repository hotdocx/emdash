/*
  Focused reviewer for category-indexed computational groupoidification.
*/

require open emdash.emdash3_2_groupoidification_universality;
require open emdash.emdash3_2_groupoidification_composition;

// Formation and the whole unit are generic in the complete source category.
assert [C : Cat] ⊢ Groupoidify C : Grpd;

assert [C : Cat] ⊢ groupoidify_unit_func C
  : τ (Functor C (Path_cat (Groupoidify C)));

// Recursion computes on every selected source object.
assert [C : Cat] [G : Grpd]
  (F : τ (Functor C (Path_cat G)))
  (x : τ (Obj C)) ⊢
  @groupoidify_rec C G F
    (@fapp0 C (Path_cat (Groupoidify C))
      (@groupoidify_unit_func C) x)
  ≡ @fapp0 C (Path_cat G) F x;

// Dependent action computes on an arbitrary represented source arrow.
assert [C : Cat] [G : Grpd]
  (F : τ (Functor C (Path_cat G)))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @eq_apd
    (Groupoidify C)
    (λ _ : τ (Groupoidify C), G)
    (λ u : τ (Groupoidify C), @groupoidify_rec C G F u)
    (@fapp0 C (Path_cat (Groupoidify C))
      (@groupoidify_unit_func C) x)
    (@fapp0 C (Path_cat (Groupoidify C))
      (@groupoidify_unit_func C) y)
    (@fapp1_fapp0 C (Path_cat (Groupoidify C))
      (@groupoidify_unit_func C) x y f)
  ≡ @const_pathover
      (Groupoidify C) G
      (@fapp0 C (Path_cat (Groupoidify C))
        (@groupoidify_unit_func C) x)
      (@fapp0 C (Path_cat (Groupoidify C))
        (@groupoidify_unit_func C) y)
      (@fapp0 C (Path_cat G) F x)
      (@fapp0 C (Path_cat G) F y)
      (@fapp1_fapp0 C (Path_cat (Groupoidify C))
        (@groupoidify_unit_func C) x y f)
      (@fapp1_fapp0 C (Path_cat G) F x y f);

// Arbitrary points and paths are not constructor redexes.
assertnot [C : Cat] [G : Grpd]
  (F : τ (Functor C (Path_cat G)))
  (u : τ (Groupoidify C))
  (x : τ (Obj C)) ⊢
  @groupoidify_rec C G F u
  ≡ @fapp0 C (Path_cat G) F x;

assertnot [C : Cat] [G : Grpd]
  (F : τ (Functor C (Path_cat G)))
  [u v : τ (Groupoidify C)]
  (p : τ (@= (Groupoidify C) u v))
  (q : τ (@= G
    (@groupoidify_rec C G F u)
    (@groupoidify_rec C G F v))) ⊢
  @eq_apd
    (Groupoidify C)
    (λ _ : τ (Groupoidify C), G)
    (λ w : τ (Groupoidify C), @groupoidify_rec C G F w)
    u v p
  ≡ @const_pathover
      (Groupoidify C) G
      u v
      (@groupoidify_rec C G F u)
      (@groupoidify_rec C G F v)
      p q;

// Whole extension/restriction form the selected mapping-object equivalence.
assert [C : Cat] [G : Grpd] ⊢ groupoidify_extend_func C G
  : τ (Functor
      (Functor_cat C (Path_cat G))
      (Hom_cat Grpd_cat (Groupoidify C) G));

assert [C : Cat] [G : Grpd] ⊢ groupoidify_restrict_func C G
  : τ (Functor
      (Hom_cat Grpd_cat (Groupoidify C) G)
      (Functor_cat C (Path_cat G)));

assert [C : Cat] [G : Grpd] ⊢ @groupoidification_hom_omega C G
  : τ (@OmegaEquivAlong
      Cat_cat
      (Hom_cat Grpd_cat (Groupoidify C) G)
      (Functor_cat C (Path_cat G))
      (@groupoidify_restrict_func C G));

assert [C : Cat] [G : Grpd] ⊢
  @omega_equiv_along_left_inv
    Cat_cat
    (Hom_cat Grpd_cat (Groupoidify C) G)
    (Functor_cat C (Path_cat G))
    (@groupoidify_restrict_func C G)
    (@groupoidification_hom_omega C G)
  ≡ @groupoidify_extend_func C G;

// Whole beta and eta have concrete object projections.
assert [C : Cat] [G : Grpd]
  (F : τ (Functor C (Path_cat G))) ⊢
  groupoidify_restrict_extend_beta_at_path F
  : τ (@=
      (Functor C (Path_cat G))
      (@groupoidify_restrict_at C G (@groupoidify_extend_at C G F))
      F);

assert [C : Cat] [G : Grpd]
  (h : τ (Function_grpd (Groupoidify C) G)) ⊢
  groupoidify_extend_restrict_eta_at_path h
  : τ (@=
      (Function_grpd (Groupoidify C) G)
      (@groupoidify_extend_at C G (@groupoidify_restrict_at C G h))
      h);

// The generic compositor is the existing internal-action cell.
assert [C : Cat]
  [x y z : τ (Obj C)]
  (g : τ (Hom C y z))
  (f : τ (Hom C x y)) ⊢
  @groupoidify_unit_compositor C x y z g f
  ≡ @fapp1_compositor
      C (Path_cat (Groupoidify C))
      (@groupoidify_unit_func C)
      x y z g f;

// Its next action is retained through the whole transformation owner.
assert [C : Cat]
  [x y z : τ (Obj C)]
  (g : τ (Hom C y z))
  (f0 f1 : τ (Hom C x y)) ⊢
  @groupoidify_unit_compositor_next_func C x y z g f0 f1
  ≡ @tapp1_func
      (@Hom_cat C x y)
      (@Hom_cat
        (Path_cat (Groupoidify C))
        (@fapp0 C (Path_cat (Groupoidify C))
          (@groupoidify_unit_func C) x)
        (@fapp0 C (Path_cat (Groupoidify C))
          (@groupoidify_unit_func C) z))
      (@groupoidify_unit_compositor_lhs_func C x y z g)
      (@groupoidify_unit_compositor_rhs_func C x y z g)
      f0 f1
      (@groupoidify_unit_compositor_transf C x y z g);

// The explicit compositor cell is not collapsed to an identity term.
assertnot [C : Cat]
  [x y z : τ (Obj C)]
  (g : τ (Hom C y z))
  (f : τ (Hom C x y)) ⊢
  @groupoidify_unit_compositor C x y z g f
  ≡ @id
      (@Hom_cat
        (Path_cat (Groupoidify C))
        (@fapp0 C (Path_cat (Groupoidify C))
          (@groupoidify_unit_func C) x)
        (@fapp0 C (Path_cat (Groupoidify C))
          (@groupoidify_unit_func C) z))
      (@fapp0
        (@Hom_cat C x y)
        (@Hom_cat
          (Path_cat (Groupoidify C))
          (@fapp0 C (Path_cat (Groupoidify C))
            (@groupoidify_unit_func C) x)
          (@fapp0 C (Path_cat (Groupoidify C))
            (@groupoidify_unit_func C) z))
        (@groupoidify_unit_compositor_lhs_func C x y z g)
        f);

// Source and target parameters are not erased by the generic facade.
assertnot [C D : Cat] ⊢ Groupoidify C ≡ Groupoidify D;

assertnot [C : Cat] [G H : Grpd] ⊢
  @Hom_cat Grpd_cat (Groupoidify C) G
  ≡ @Hom_cat Grpd_cat (Groupoidify C) H;
