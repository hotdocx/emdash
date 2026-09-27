/*
  Emdash v3.2: strict-package action on equality-valued equivalences.

  A classified strict functor maps equality-valued equivalences without a
  detached composition-law record. The component comparison below is a
  theorem of the stable `strict_functor` head. Both cancellation proofs and
  selected inverses remain computational, and the ambient lax carrier gains
  no equality.

  This is the first post-profile action family. Ordinary isomorphism evidence
  already reuses the same construction; computational isomorphism and
  profunctor-comparison action migrate here next.
*/

require open emdash.emdash3_2_gray_profiles;

symbol strict_functor_composition_path
  [A B : Cat]
  (S : τ (@StrictFunctor A B))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
  : τ (@=
      (Hom B
        (@fapp0 A B (@strict_functor A B S) X)
        (@fapp0 A B (@strict_functor A B S) Z))
      (@fapp1_fapp0 A B (@strict_functor A B S) X Z
        (@comp_fapp0 A X Y Z g f))
      (@comp_fapp0
        B
        (@fapp0 A B (@strict_functor A B S) X)
        (@fapp0 A B (@strict_functor A B S) Y)
        (@fapp0 A B (@strict_functor A B S) Z)
        (@fapp1_fapp0 A B (@strict_functor A B S) Y Z g)
        (@fapp1_fapp0 A B (@strict_functor A B S) X Y f)))
≔ @eq_refl
    (Hom B
      (@fapp0 A B (@strict_functor A B S) X)
      (@fapp0 A B (@strict_functor A B S) Z))
    (@fapp1_fapp0 A B (@strict_functor A B S) X Z
      (@comp_fapp0 A X Y Z g f));

symbol strict_omega_equiv_along_fapp1_left_law
  [A B : Cat]
  (S : τ (@StrictFunctor A B))
  [x y : τ (Obj A)]
  [f : τ (Hom A x y)]
  (u : τ (@OmegaEquivAlong A x y f))
  : τ (@=
      (Hom B
        (@fapp0 A B (@strict_functor A B S) x)
        (@fapp0 A B (@strict_functor A B S) x))
      (@comp_fapp0
        B
        (@fapp0 A B (@strict_functor A B S) x)
        (@fapp0 A B (@strict_functor A B S) y)
        (@fapp0 A B (@strict_functor A B S) x)
        (@fapp1_fapp0 A B (@strict_functor A B S) y x
          (@omega_equiv_along_left_inv A x y f u))
        (@fapp1_fapp0 A B (@strict_functor A B S) x y f))
      (@id B (@fapp0 A B (@strict_functor A B S) x)))
≔ @eq_trans
    (Hom B
      (@fapp0 A B (@strict_functor A B S) x)
      (@fapp0 A B (@strict_functor A B S) x))
    (@comp_fapp0
      B
      (@fapp0 A B (@strict_functor A B S) x)
      (@fapp0 A B (@strict_functor A B S) y)
      (@fapp0 A B (@strict_functor A B S) x)
      (@fapp1_fapp0 A B (@strict_functor A B S) y x
        (@omega_equiv_along_left_inv A x y f u))
      (@fapp1_fapp0 A B (@strict_functor A B S) x y f))
    (@fapp1_fapp0 A B (@strict_functor A B S) x x
      (@comp_fapp0 A x y x
        (@omega_equiv_along_left_inv A x y f u)
        f))
    (@id B (@fapp0 A B (@strict_functor A B S) x))
    (@eq_sym
      (Hom B
        (@fapp0 A B (@strict_functor A B S) x)
        (@fapp0 A B (@strict_functor A B S) x))
      (@fapp1_fapp0 A B (@strict_functor A B S) x x
        (@comp_fapp0 A x y x
          (@omega_equiv_along_left_inv A x y f u)
          f))
      (@comp_fapp0
        B
        (@fapp0 A B (@strict_functor A B S) x)
        (@fapp0 A B (@strict_functor A B S) y)
        (@fapp0 A B (@strict_functor A B S) x)
        (@fapp1_fapp0 A B (@strict_functor A B S) y x
          (@omega_equiv_along_left_inv A x y f u))
        (@fapp1_fapp0 A B (@strict_functor A B S) x y f))
      (@strict_functor_composition_path
        A B S x y x
        (@omega_equiv_along_left_inv A x y f u)
        f))
    (@eq_ap
      (Hom A x x)
      (Hom B
        (@fapp0 A B (@strict_functor A B S) x)
        (@fapp0 A B (@strict_functor A B S) x))
      (λ h : τ (Hom A x x),
        @fapp1_fapp0 A B (@strict_functor A B S) x x h)
      (@comp_fapp0 A x y x
        (@omega_equiv_along_left_inv A x y f u)
        f)
      (@id A x)
      (@omega_equiv_along_left_law A x y f u));

symbol strict_omega_equiv_along_fapp1_right_law
  [A B : Cat]
  (S : τ (@StrictFunctor A B))
  [x y : τ (Obj A)]
  [f : τ (Hom A x y)]
  (u : τ (@OmegaEquivAlong A x y f))
  : τ (@=
      (Hom B
        (@fapp0 A B (@strict_functor A B S) y)
        (@fapp0 A B (@strict_functor A B S) y))
      (@comp_fapp0
        B
        (@fapp0 A B (@strict_functor A B S) y)
        (@fapp0 A B (@strict_functor A B S) x)
        (@fapp0 A B (@strict_functor A B S) y)
        (@fapp1_fapp0 A B (@strict_functor A B S) x y f)
        (@fapp1_fapp0 A B (@strict_functor A B S) y x
          (@omega_equiv_along_right_inv A x y f u)))
      (@id B (@fapp0 A B (@strict_functor A B S) y)))
≔ @eq_trans
    (Hom B
      (@fapp0 A B (@strict_functor A B S) y)
      (@fapp0 A B (@strict_functor A B S) y))
    (@comp_fapp0
      B
      (@fapp0 A B (@strict_functor A B S) y)
      (@fapp0 A B (@strict_functor A B S) x)
      (@fapp0 A B (@strict_functor A B S) y)
      (@fapp1_fapp0 A B (@strict_functor A B S) x y f)
      (@fapp1_fapp0 A B (@strict_functor A B S) y x
        (@omega_equiv_along_right_inv A x y f u)))
    (@fapp1_fapp0 A B (@strict_functor A B S) y y
      (@comp_fapp0 A y x y
        f
        (@omega_equiv_along_right_inv A x y f u)))
    (@id B (@fapp0 A B (@strict_functor A B S) y))
    (@eq_sym
      (Hom B
        (@fapp0 A B (@strict_functor A B S) y)
        (@fapp0 A B (@strict_functor A B S) y))
      (@fapp1_fapp0 A B (@strict_functor A B S) y y
        (@comp_fapp0 A y x y
          f
          (@omega_equiv_along_right_inv A x y f u)))
      (@comp_fapp0
        B
        (@fapp0 A B (@strict_functor A B S) y)
        (@fapp0 A B (@strict_functor A B S) x)
        (@fapp0 A B (@strict_functor A B S) y)
        (@fapp1_fapp0 A B (@strict_functor A B S) x y f)
        (@fapp1_fapp0 A B (@strict_functor A B S) y x
          (@omega_equiv_along_right_inv A x y f u)))
      (@strict_functor_composition_path
        A B S y x y f
        (@omega_equiv_along_right_inv A x y f u)))
    (@eq_ap
      (Hom A y y)
      (Hom B
        (@fapp0 A B (@strict_functor A B S) y)
        (@fapp0 A B (@strict_functor A B S) y))
      (λ h : τ (Hom A y y),
        @fapp1_fapp0 A B (@strict_functor A B S) y y h)
      (@comp_fapp0 A y x y
        f
        (@omega_equiv_along_right_inv A x y f u))
      (@id A y)
      (@omega_equiv_along_right_law A x y f u));

symbol strict_omega_equiv_along_fapp1
  [A B : Cat]
  (S : τ (@StrictFunctor A B))
  [x y : τ (Obj A)]
  [f : τ (Hom A x y)]
  (u : τ (@OmegaEquivAlong A x y f))
  : τ (@OmegaEquivAlong
      B
      (@fapp0 A B (@strict_functor A B S) x)
      (@fapp0 A B (@strict_functor A B S) y)
      (@fapp1_fapp0 A B (@strict_functor A B S) x y f))
≔ @omega_equiv_along_intro
    B
    (@fapp0 A B (@strict_functor A B S) x)
    (@fapp0 A B (@strict_functor A B S) y)
    (@fapp1_fapp0 A B (@strict_functor A B S) x y f)
    (@fapp1_fapp0 A B (@strict_functor A B S) y x
      (@omega_equiv_along_left_inv A x y f u))
    (@fapp1_fapp0 A B (@strict_functor A B S) y x
      (@omega_equiv_along_right_inv A x y f u))
    (@strict_omega_equiv_along_fapp1_left_law A B S x y f u)
    (@strict_omega_equiv_along_fapp1_right_law A B S x y f u);

symbol strict_omega_equiv_left_projection
  [A B : Cat]
  (S : τ (@StrictFunctor A B))
  [x y : τ (Obj A)]
  [f : τ (Hom A x y)]
  (u : τ (@OmegaEquivAlong A x y f))
  : τ (@=
      (Hom B
        (@fapp0 A B (@strict_functor A B S) y)
        (@fapp0 A B (@strict_functor A B S) x))
      (@omega_equiv_along_left_inv
        B
        (@fapp0 A B (@strict_functor A B S) x)
        (@fapp0 A B (@strict_functor A B S) y)
        (@fapp1_fapp0 A B (@strict_functor A B S) x y f)
        (@strict_omega_equiv_along_fapp1 A B S x y f u))
      (@fapp1_fapp0 A B (@strict_functor A B S) y x
        (@omega_equiv_along_left_inv A x y f u)))
≔ @eq_refl
    (Hom B
      (@fapp0 A B (@strict_functor A B S) y)
      (@fapp0 A B (@strict_functor A B S) x))
    (@fapp1_fapp0 A B (@strict_functor A B S) y x
      (@omega_equiv_along_left_inv A x y f u));

symbol strict_omega_equiv_right_projection
  [A B : Cat]
  (S : τ (@StrictFunctor A B))
  [x y : τ (Obj A)]
  [f : τ (Hom A x y)]
  (u : τ (@OmegaEquivAlong A x y f))
  : τ (@=
      (Hom B
        (@fapp0 A B (@strict_functor A B S) y)
        (@fapp0 A B (@strict_functor A B S) x))
      (@omega_equiv_along_right_inv
        B
        (@fapp0 A B (@strict_functor A B S) x)
        (@fapp0 A B (@strict_functor A B S) y)
        (@fapp1_fapp0 A B (@strict_functor A B S) x y f)
        (@strict_omega_equiv_along_fapp1 A B S x y f u))
      (@fapp1_fapp0 A B (@strict_functor A B S) y x
        (@omega_equiv_along_right_inv A x y f u)))
≔ @eq_refl
    (Hom B
      (@fapp0 A B (@strict_functor A B S) y)
      (@fapp0 A B (@strict_functor A B S) x))
    (@fapp1_fapp0 A B (@strict_functor A B S) y x
      (@omega_equiv_along_right_inv A x y f u));

// Classified strict functors preserve ordinary isomorphism evidence.
symbol strict_iso_evidence_fmap
  [C D : Cat]
  (S : τ (@StrictFunctor C D))
  [x y : τ (Obj C)]
  (i : τ (@IsoEvidence C x y))
  : τ (@IsoEvidence
      D
      (@fapp0 C D (@strict_functor C D S) x)
      (@fapp0 C D (@strict_functor C D S) y))
≔ Struct_sigma
    (@fapp1_fapp0 C D (@strict_functor C D S) x y
      (@iso_evidence_to C x y i))
    (Struct_sigma
      (@fapp1_fapp0 C D (@strict_functor C D S) y x
        (@iso_evidence_from C x y i))
      (Struct_sigma
        (@strict_omega_equiv_along_fapp1_left_law
          C D S x y (@iso_evidence_to C x y i)
          (@iso_evidence_omega_along C x y i))
        (@strict_omega_equiv_along_fapp1_right_law
          C D S x y (@iso_evidence_to C x y i)
          (@iso_evidence_omega_along C x y i))));


/* Stable mapped-arrow owner for the stable StrictFunctor-based DefIso action. */

injective symbol strict_defiso_fmap_to
  [C D : Cat]
  (S : τ (@StrictFunctor C D))
  [x y : τ (Obj C)]
  (i : τ (@DefIso C x y))
  : τ (Hom D
      (@fapp0 C D (@strict_functor C D S) x)
      (@fapp0 C D (@strict_functor C D S) y));

injective symbol strict_defiso_fmap_from
  [C D : Cat]
  (S : τ (@StrictFunctor C D))
  [x y : τ (Obj C)]
  (i : τ (@DefIso C x y))
  : τ (Hom D
      (@fapp0 C D (@strict_functor C D S) y)
      (@fapp0 C D (@strict_functor C D S) x));

unif_rule
  @strict_defiso_fmap_to $C $D $S $x $y $i
  ≡ @fapp1_fapp0 $C $D (@strict_functor $C $D $S)
      $x $y (@defiso_to $C $x $y $i)
  ↪ [ tt ≡ tt ];

unif_rule
  @strict_defiso_fmap_from $C $D $S $x $y $i
  ≡ @fapp1_fapp0 $C $D (@strict_functor $C $D $S)
      $y $x (@defiso_from $C $x $y $i)
  ↪ [ tt ≡ tt ];

symbol strict_defiso_fmap_to_path
  [C D : Cat]
  (S : τ (@StrictFunctor C D))
  [x y : τ (Obj C)]
  (i : τ (@DefIso C x y))
  : τ (@=
      (Hom D
        (@fapp0 C D (@strict_functor C D S) x)
        (@fapp0 C D (@strict_functor C D S) y))
      (@strict_defiso_fmap_to C D S x y i)
      (@fapp1_fapp0 C D (@strict_functor C D S)
        x y (@defiso_to C x y i)))
≔ @eq_refl
    (Hom D
      (@fapp0 C D (@strict_functor C D S) x)
      (@fapp0 C D (@strict_functor C D S) y))
    (@strict_defiso_fmap_to C D S x y i);

symbol strict_defiso_fmap_from_path
  [C D : Cat]
  (S : τ (@StrictFunctor C D))
  [x y : τ (Obj C)]
  (i : τ (@DefIso C x y))
  : τ (@=
      (Hom D
        (@fapp0 C D (@strict_functor C D S) y)
        (@fapp0 C D (@strict_functor C D S) x))
      (@strict_defiso_fmap_from C D S x y i)
      (@fapp1_fapp0 C D (@strict_functor C D S)
        y x (@defiso_from C x y i)))
≔ @eq_refl
    (Hom D
      (@fapp0 C D (@strict_functor C D S) y)
      (@fapp0 C D (@strict_functor C D S) x))
    (@strict_defiso_fmap_from C D S x y i);

injective symbol strict_defiso_fmap
  [C D : Cat]
  (S : τ (@StrictFunctor C D))
  [x y : τ (Obj C)]
  (i : τ (@DefIso C x y))
  : τ (@DefIso
      D
      (@fapp0 C D (@strict_functor C D S) x)
      (@fapp0 C D (@strict_functor C D S) y));

rule @defiso_to
      $D _ _
      (@strict_defiso_fmap $C $D $S $x $y $i)
  ↪ @strict_defiso_fmap_to $C $D $S $x $y $i
with @defiso_from
      $D _ _
      (@strict_defiso_fmap $C $D $S $x $y $i)
  ↪ @strict_defiso_fmap_from $C $D $S $x $y $i;

rule @comp_fapp0
      _ _ _ _
      (@strict_defiso_fmap_from $C $D $S $x $y $i)
      (@strict_defiso_fmap_to $C $D $S $x $y $i)
  ↪ @id $D (@fapp0 $C $D (@strict_functor $C $D $S) $x)
with @comp_fapp0
      _ _ _ _
      (@strict_defiso_fmap_to $C $D $S $x $y $i)
      (@strict_defiso_fmap_from $C $D $S $x $y $i)
  ↪ @id $D (@fapp0 $C $D (@strict_functor $C $D $S) $y);

rule @hom_postcomp_fapp0
      $D $D (@id Cat_cat $D)
      _ _ _
      (@strict_defiso_fmap_from $C $D $S $x $y $i)
      (@strict_defiso_fmap_to $C $D $S $x $y $i)
  ↪ @id $D (@fapp0 $C $D (@strict_functor $C $D $S) $x)
with @hom_postcomp_fapp0
      $D $D (@id Cat_cat $D)
      _ _ _
      (@strict_defiso_fmap_to $C $D $S $x $y $i)
      (@strict_defiso_fmap_from $C $D $S $x $y $i)
  ↪ @id $D (@fapp0 $C $D (@strict_functor $C $D $S) $y);

rule @hom_postcomp_fapp0
      $D $D (@id Cat_cat $D)
      $W _ _
      (@strict_defiso_fmap_from $C $D $S $x $y $i)
      (@hom_postcomp_fapp0
        $D $D (@id Cat_cat $D)
        $W _ _
        (@strict_defiso_fmap_to $C $D $S $x $y $i)
        $f)
  ↪ $f
with @hom_postcomp_fapp0
      $D $D (@id Cat_cat $D)
      $W _ _
      (@strict_defiso_fmap_to $C $D $S $x $y $i)
      (@hom_postcomp_fapp0
        $D $D (@id Cat_cat $D)
        $W _ _
        (@strict_defiso_fmap_from $C $D $S $x $y $i)
        $g)
  ↪ $g;

rule @defiso_iso_evidence
      $D _ _
      (@strict_defiso_fmap $C $D $S $x $y $i)
  ↪ @strict_iso_evidence_fmap
      $C $D $S $x $y
      (@defiso_iso_evidence $C $x $y $i);

symbol strict_defiso_fmap_to_beta
  [C D : Cat]
  (S : τ (@StrictFunctor C D))
  [x y : τ (Obj C)]
  (i : τ (@DefIso C x y))
  : τ (@=
      (Hom D
        (@fapp0 C D (@strict_functor C D S) x)
        (@fapp0 C D (@strict_functor C D S) y))
      (@defiso_to
        D
        (@fapp0 C D (@strict_functor C D S) x)
        (@fapp0 C D (@strict_functor C D S) y)
        (@strict_defiso_fmap C D S x y i))
      (@strict_defiso_fmap_to C D S x y i))
≔ @eq_refl
    (Hom D
      (@fapp0 C D (@strict_functor C D S) x)
      (@fapp0 C D (@strict_functor C D S) y))
    (@strict_defiso_fmap_to C D S x y i);

symbol strict_defiso_fmap_cancel
  [C D : Cat]
  (S : τ (@StrictFunctor C D))
  [x y : τ (Obj C)]
  (i : τ (@DefIso C x y))
  : τ (@=
      (Hom D
        (@fapp0 C D (@strict_functor C D S) x)
        (@fapp0 C D (@strict_functor C D S) x))
      (@comp_fapp0
        D
        (@fapp0 C D (@strict_functor C D S) x)
        (@fapp0 C D (@strict_functor C D S) y)
        (@fapp0 C D (@strict_functor C D S) x)
        (@strict_defiso_fmap_from C D S x y i)
        (@strict_defiso_fmap_to C D S x y i))
      (@id D (@fapp0 C D (@strict_functor C D S) x)))
≔ @eq_refl
    (Hom D
      (@fapp0 C D (@strict_functor C D S) x)
      (@fapp0 C D (@strict_functor C D S) x))
    (@id D (@fapp0 C D (@strict_functor C D S) x));

// Functorial image of a profunctor comparison under one classified carrier.
symbol strict_prof_comparison_fmap
  [A B A' B' : Cat]
  (S : τ (@StrictFunctor
    (@Prof_cat A B) (@Prof_cat A' B')))
  [P Q : τ (Prof A B)]
  (i : τ (ProfComparison P Q))
  : τ (ProfComparison
      (@fapp0
        (@Prof_cat A B) (@Prof_cat A' B')
        (@strict_functor (@Prof_cat A B) (@Prof_cat A' B') S) P)
      (@fapp0
        (@Prof_cat A B) (@Prof_cat A' B')
        (@strict_functor (@Prof_cat A B) (@Prof_cat A' B') S) Q))
≔ @strict_defiso_fmap
    (@Prof_cat A B)
    (@Prof_cat A' B')
    S P Q i;

/*
  Selected named strict packages for the two maintained profunctor consumers.

  Their raw carriers already own guarded composition computation in the core.
  The whole-profile witnesses remain supplied until that named computation is
  reconstructed from the internal action; callers consume the package, never
  the evidence or a detached capped law.
*/
constant symbol prof_reindex_is_strict
  [A A' B B' : Cat]
  (F : τ (Functor A' A))
  (G : τ (Functor B' B))
  : τ (@IsStrictFunctor
      (@Prof_cat A B)
      (@Prof_cat A' B')
      (@Prof_reindex_func A A' B B' F G));

symbol strict_prof_reindex_func
  [A A' B B' : Cat]
  (F : τ (Functor A' A))
  (G : τ (Functor B' B))
  : τ (@StrictFunctor (@Prof_cat A B) (@Prof_cat A' B'))
≔ @make_strict_functor
    (@Prof_cat A B)
    (@Prof_cat A' B')
    (@Prof_reindex_func A A' B B' F G)
    (@prof_reindex_is_strict A A' B B' F G);

constant symbol prof_imply_cov_is_strict
  [A B X : Cat]
  (Q : τ (Prof B X))
  : τ (@IsStrictFunctor
      (@Prof_cat A X)
      (@Prof_cat A B)
      (@Prof_imply_cov_func A B X Q));

symbol strict_prof_imply_cov_func
  [A B X : Cat]
  (Q : τ (Prof B X))
  : τ (@StrictFunctor (@Prof_cat A X) (@Prof_cat A B))
≔ @make_strict_functor
    (@Prof_cat A X)
    (@Prof_cat A B)
    (@Prof_imply_cov_func A B X Q)
    (@prof_imply_cov_is_strict A B X Q);

// Selected path-symmetry strict package over its guarded anti-composition.
constant symbol path_sym_is_strict
  (A : Grpd)
  : τ (@IsStrictFunctor
      (Op_cat (Path_cat A))
      (Path_cat A)
      (@Path_sym_func A));

symbol strict_path_sym_func
  (A : Grpd)
  : τ (@StrictFunctor (Op_cat (Path_cat A)) (Path_cat A))
≔ @make_strict_functor
    (Op_cat (Path_cat A))
    (Path_cat A)
    (@Path_sym_func A)
    (@path_sym_is_strict A);

// Selected constant-functor package. Constant action already owns its named
// identity/composition computation; callers consume this whole profile.
constant symbol constant_functor_is_strict
  (A B : Cat)
  (y : τ (Obj B))
  : τ (@IsStrictFunctor A B (@Const_func A B y));

symbol strict_constant_func
  (A B : Cat)
  (y : τ (Obj B))
  : τ (@StrictFunctor A B)
≔ @make_strict_functor
    A B
    (@Const_func A B y)
    (@constant_functor_is_strict A B y);

// Named whole decoder is safe because Const_func owns compatible point,
// arrow, and composition computation.
rule @strict_functor _ _
      (@make_strict_functor _ _ (@Const_func $A $B $y) _)
  ↪ @Const_func $A $B $y;

// Selected universe-level Path action package.
constant symbol path_cat_func_is_strict
  : τ (@IsStrictFunctor Grpd_cat Cat_cat Path_cat_func);

symbol strict_path_cat_func
  : τ (@StrictFunctor Grpd_cat Cat_cat)
≔ @make_strict_functor
    Grpd_cat Cat_cat Path_cat_func path_cat_func_is_strict;

// Named whole decoder is safe because Path_cat_func owns guarded strict
// composition and its iterable path-map action.
rule @strict_functor _ _
      (@make_strict_functor _ _ Path_cat_func _)
  ↪ Path_cat_func;


/*
  Strict-package weighted-limit and adjunction actions.

  These declarations were moved after the strict profile so their public
  signatures remain mathematical while their implementation no longer passes
  a detached composition law.
*/

// Forward universal operation after reindexing the limit comparison along M.
symbol weighted_limit_cov_push
  [B J J' : Cat]
  [F : τ (Functor J B)]
  [W : τ (Prof J' J)]
  [L : τ (Functor J' B)]
  (isl : τ (@IsWeightedLimit_cov_comp B J J' F W L))
  [I : Cat]
  (M : τ (Functor I B))
  [R : τ (Prof I J')]
  (r : τ (ProfMap
      R
      (@Prof_imply_cov
        I J' J
        (@Hom_prof_along I J B M F)
        W)))
  : τ (ProfMap R (@Hom_prof_along I J' B M L))
≔ @prof_comparison_push
    I J'
    _
    _
    (@strict_prof_comparison_fmap
      B J' I J'
      (@strict_prof_reindex_func B I J' J' M (@id_func J'))
      _
      _
      isl)
    R
    r;

// Inverse universal operation after reindexing the limit comparison along M.
symbol weighted_limit_cov_pull
  [B J J' : Cat]
  [F : τ (Functor J B)]
  [W : τ (Prof J' J)]
  [L : τ (Functor J' B)]
  (isl : τ (@IsWeightedLimit_cov_comp B J J' F W L))
  [I : Cat]
  (M : τ (Functor I B))
  [R : τ (Prof I J')]
  (s : τ (ProfMap R (@Hom_prof_along I J' B M L)))
  : τ (ProfMap
      R
      (@Prof_imply_cov
        I J' J
        (@Hom_prof_along I J B M F)
        W))
≔ @prof_comparison_pull
    I J'
    _
    _
    (@strict_prof_comparison_fmap
      B J' I J'
      (@strict_prof_reindex_func B I J' J' M (@id_func J'))
      _
      _
      isl)
    R
    s;


// Reindexed adjunction mate: Hom_B(LM,F) ≃ Hom_A(M,RF).
symbol Adjunction_hom_prof_comparison_along
  [A B : Cat]
  [Ladj : τ (Functor A B)]
  [Radj : τ (Functor B A)]
  (adj : τ (@Adjunction A B Ladj Radj))
  [I K : Cat]
  (M : τ (Functor I A))
  (F : τ (Functor K B))
  : τ (ProfComparison
      (@Hom_prof_along
        I K B
        (@comp_cat_fapp0
          I A B
          Ladj
          M)
        F)
      (@Hom_prof_along
        I K A
        M
        (@comp_cat_fapp0
          K B A
          Radj
          F)))
≔ @strict_prof_comparison_fmap
    A B I K
    (@strict_prof_reindex_func A I B K M F)
    _
    _
    (@Adjunction_hom_prof_comparison A B Ladj Radj adj);


/*
  Computational right-adjoint preservation.

  This parallel API composes three certified comparisons:

    1. the inverse adjunction mate through fixed-weight implication;
    2. the given weighted-limit comparison reindexed along the left adjoint;
    3. the adjunction mate at the candidate limit.

  Its beta/eta laws are inherited from `prof_comparison_push/pull`; no
  theorem-specific fold or cancellation rule is added to ordinary equipment
  composition.
*/
symbol right_adjoint_weighted_limit_comp_step1
  [B J J' A : Cat]
  [Ladj : τ (Functor A B)]
  [Radj : τ (Functor B A)]
  [W : τ (Prof J' J)]
  [F : τ (Functor J B)]
  (adj : τ (@Adjunction A B Ladj Radj))
  : τ (ProfComparison
      (@Prof_imply_cov
        A J' J
        (@Hom_prof
          J A
          (@comp_cat_fapp0
            J B A
            Radj
            F))
        W)
      (@Prof_imply_cov
        A J' J
        (@Hom_prof_along
          A J B
          Ladj
          F)
        W))
≔ @strict_prof_comparison_fmap
    A J A J'
    (@strict_prof_imply_cov_func A J' J W)
    _
    _
    (@prof_comparison_sym
      A J
      _
      _
      (@Adjunction_hom_prof_comparison_along
        A B Ladj Radj adj
        A J
        (@id_func A)
        F));

// Preservation step 2: reindex the supplied weighted-limit comparison along L.
symbol right_adjoint_weighted_limit_comp_step2
  [B J J' A : Cat]
  [Ladj : τ (Functor A B)]
  [Radj : τ (Functor B A)]
  [W : τ (Prof J' J)]
  [F : τ (Functor J B)]
  [L : τ (Functor J' B)]
  (isl : τ (@IsWeightedLimit_cov_comp B J J' F W L))
  (adj : τ (@Adjunction A B Ladj Radj))
  : τ (ProfComparison
      (@Prof_imply_cov
        A J' J
        (@Hom_prof_along
          A J B
          Ladj
          F)
        W)
      (@Hom_prof_along
        A J' B
        Ladj
        L))
≔ @strict_prof_comparison_fmap
    B J' A J'
    (@strict_prof_reindex_func
      B A J' J'
      Ladj
      (@id_func J'))
    _
    _
    isl;

// Preservation step 3: apply the adjunction mate to the candidate limit L.
symbol right_adjoint_weighted_limit_comp_step3
  [B J J' A : Cat]
  [Ladj : τ (Functor A B)]
  [Radj : τ (Functor B A)]
  [L : τ (Functor J' B)]
  (adj : τ (@Adjunction A B Ladj Radj))
  : τ (ProfComparison
      (@Hom_prof_along
        A J' B
        Ladj
        L)
      (@Hom_prof
        J' A
        (@comp_cat_fapp0
          J' B A
          Radj
          L)))
≔ @Adjunction_hom_prof_comparison_along
    A B Ladj Radj adj
    A J'
    (@id_func A)
    L;

// Composite certificate that a right adjoint preserves the weighted limit.
symbol right_adjoint_preserves_weighted_limit_cov_comp
  [B J J' A : Cat]
  [Ladj : τ (Functor A B)]
  [Radj : τ (Functor B A)]
  [W : τ (Prof J' J)]
  [F : τ (Functor J B)]
  [L : τ (Functor J' B)]
  (isl : τ (@IsWeightedLimit_cov_comp B J J' F W L))
  (adj : τ (@Adjunction A B Ladj Radj))
  : τ (@IsWeightedLimit_cov_comp
      A J J'
      (@comp_cat_fapp0
        J B A
        Radj
        F)
      W
      (@comp_cat_fapp0
        J' B A
        Radj
        L))
≔ @prof_comparison_comp
    A J'
    _ _ _
    (@right_adjoint_weighted_limit_comp_step3
      B J J' A Ladj Radj L adj)
    (@prof_comparison_comp
      A J'
      _ _ _
      (@right_adjoint_weighted_limit_comp_step2
        B J J' A Ladj Radj W F L isl adj)
      (@right_adjoint_weighted_limit_comp_step1
        B J J' A Ladj Radj W F adj));


/*
  Left adjoints preserve weighted colimits.

  Applying right-adjoint preservation to Op_adjunction(adj) makes its right
  adjoint Op(left(adj)), so the result is definitionally the desired colimit
  witness after Op_func distributes over composition.
*/
symbol left_adjoint_preserves_weighted_colimit_con
  [A J J' B : Cat]
  [Ladj : τ (Functor A B)]
  [Radj : τ (Functor B A)]
  [F : τ (Functor J A)]
  [W : τ (Prof J J')]
  [L : τ (Functor J' A)]
  (isc : τ (@WeightedColimit_con A J J' F W L))
  (adj : τ (@Adjunction A B Ladj Radj))
  : τ (@WeightedColimit_con
      B J J'
      (@comp_cat_fapp0 J A B Ladj F)
      W
      (@comp_cat_fapp0 J' A B Ladj L))
≔ @right_adjoint_preserves_weighted_limit_cov_comp
    (Op_cat A)
    (Op_cat J)
    (Op_cat J')
    (Op_cat B)
    (@Op_func B A Radj)
    (@Op_func A B Ladj)
    (@Op_prof J J' W)
    (@Op_func J A F)
    (@Op_func J' A L)
    isc
    (@Op_adjunction A B Ladj Radj adj);
