/*
  Emdash v3.2: chosen pullbacks as coherent slice base change.

  The always-existing family SliceSigma_catd(C) sends X to C/X and a base
  arrow f:X→Y to postcomposition Σ_f:C/X→C/Y.  A PullbackStructure(C)
  supplies the opposite-variance whole family whose action is
  f*:C/Y→C/X, together with the existing adjunction Σ_f ⊣ f*.

  The whole families retain base-arrow and higher action.  This module does
  not identify categorical base change with the kernel's unrelated
  Pullback_catd(E,F) family substitution, does not add a second adjunction
  theory, and does not collapse directed ambient projection cells to strict
  arrow equalities. Whole cone recovery and uniqueness compute through the
  selected adjunction. Explicit pseudo invertibility, Π_f, Beck--Chevalley,
  products-in-slices, weighted comparisons, and pushouts remain later layers.
*/

require open emdash.emdash3_2_presheaves;

// Always-existing covariant slice family: X ↦ C/X, f ↦ Σ_f.
symbol SliceSigma_catd
  (C : Cat)
  : τ (Catd C)
≔ @CommaFib_catd C C (@id_func C);

// Whole postcomposition action on slices.
symbol slice_sigma_func
  [C : Cat]
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  : τ (Functor (@Slice_cat C X) (@Slice_cat C Y))
≔ @fapp1_fapp0
    C Cat_cat
    (@SliceSigma_catd C)
    X Y f;

/*
  Chosen coherent pullback structure.

  This is computational structure rather than a mere existence proposition.
  Its stable whole family below fixes the exact slice fibres definitionally.
*/
injective symbol PullbackStructure
  (C : Cat)
  : Grpd;

// Whole opposite-variance base change: X ↦ C/X, f^op ↦ f*.
injective symbol SliceBaseChange_catd
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  : τ (Catd (Op_cat C));

// Exact chosen fibre: SliceBaseChange(PB)[X] ↪ C/X.
rule @fapp0 _ Cat_cat
      (@SliceBaseChange_catd $C _)
      $X
  ↪ @Slice_cat $C $X;

// Whole categorical pullback along f:X→Y.
symbol slice_base_change_func
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  : τ (Functor (@Slice_cat C Y) (@Slice_cat C X))
≔ @fapp1_fapp0
    (Op_cat C)
    Cat_cat
    (@SliceBaseChange_catd C PB)
    Y X f;

// Object postcomposition in the covariant slice family.
symbol slice_sigma_obj
  [C : Cat]
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  : τ (Obj (@Slice_cat C Y))
≔ @fapp0
    (@Slice_cat C X)
    (@Slice_cat C Y)
    (@slice_sigma_func C X Y f)
    a;

// Object base change in the chosen opposite-variance slice family.
symbol slice_base_change_obj
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (b : τ (Obj (@Slice_cat C Y)))
  : τ (Obj (@Slice_cat C X))
≔ @fapp0
    (@Slice_cat C Y)
    (@Slice_cat C X)
    (@slice_base_change_func C PB X Y f)
    b;

/*
  Declaration-backed existing adjunction Σ_f ⊣ f*.

  Generic unit/counit observations and triangle computation remain the
  semantic owners.  Later post-projection rules, if any, are instances of
  those triangles at canonical surviving slice/action heads.
*/
injective symbol slice_base_change_adjunction
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  : τ (@Adjunction
      (@Slice_cat C X)
      (@Slice_cat C Y)
      (@slice_sigma_func C X Y f)
      (@slice_base_change_func C PB X Y f));

// Readable transparent unit of slice base change.
symbol slice_base_change_unit_transf
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  : τ (Transf
      (@id_func (@Slice_cat C X))
      (@comp_cat_fapp0
        (@Slice_cat C X)
        (@Slice_cat C Y)
        (@Slice_cat C X)
        (@slice_base_change_func C PB X Y f)
        (@slice_sigma_func C X Y f)))
≔ @unit_adj_transf
    (@Slice_cat C X)
    (@Slice_cat C Y)
    (@slice_sigma_func C X Y f)
    (@slice_base_change_func C PB X Y f)
    (@slice_base_change_adjunction C PB X Y f);

// Readable transparent counit of slice base change.
symbol slice_base_change_counit_transf
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  : τ (Transf
      (@comp_cat_fapp0
        (@Slice_cat C Y)
        (@Slice_cat C X)
        (@Slice_cat C Y)
        (@slice_sigma_func C X Y f)
        (@slice_base_change_func C PB X Y f))
      (@id_func (@Slice_cat C Y)))
≔ @counit_adj_transf
    (@Slice_cat C X)
    (@Slice_cat C Y)
    (@slice_sigma_func C X Y f)
    (@slice_base_change_func C PB X Y f)
    (@slice_base_change_adjunction C PB X Y f);

// Component of the base-change unit at an object a of C/X.
symbol slice_base_change_unit
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  : τ (Hom
      (@Slice_cat C X)
      a
      (@slice_base_change_obj C PB X Y f
        (@slice_sigma_obj C X Y f a)))
≔ @tapp0_fapp0
    (@Slice_cat C X)
    (@Slice_cat C X)
    _ _
    a
    (@slice_base_change_unit_transf C PB X Y f);

// Component of the base-change counit at an object b of C/Y.
symbol slice_base_change_counit
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (b : τ (Obj (@Slice_cat C Y)))
  : τ (Hom
      (@Slice_cat C Y)
      (@slice_sigma_obj C X Y f
        (@slice_base_change_obj C PB X Y f b))
      b)
≔ @tapp0_fapp0
    (@Slice_cat C Y)
    (@Slice_cat C Y)
    _ _
    b
    (@slice_base_change_counit_transf C PB X Y f);

/*
  Transparent semantic mate functors.

  Transpose acts by f* on a slice arrow and then precomposes with the unit.
  Untranspose acts by Σ_f and then postcomposes with the counit.  These
  functors make the selected adjunction semantics explicit and retain all hom
  action.  The stable computational functors below keep point discriminators
  for the triangle cuts; proof-time usability relates their points to these
  semantic projections without a runtime fold.
*/
symbol slice_base_change_transpose_semantic_func
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  (b : τ (Obj (@Slice_cat C Y)))
  : τ (Functor
      (Hom_cat
        (@Slice_cat C Y)
        (@slice_sigma_obj C X Y f a)
        b)
      (Hom_cat
        (@Slice_cat C X)
        a
        (@slice_base_change_obj C PB X Y f b)))
≔ @comp_cat_fapp0
    (Hom_cat
      (@Slice_cat C Y)
      (@slice_sigma_obj C X Y f a)
      b)
    (Hom_cat
      (@Slice_cat C X)
      (@slice_base_change_obj C PB X Y f
        (@slice_sigma_obj C X Y f a))
      (@slice_base_change_obj C PB X Y f b))
    (Hom_cat
      (@Slice_cat C X)
      a
      (@slice_base_change_obj C PB X Y f b))
    (@hom_precomp_along_func
      (@Slice_cat C X)
      (@Slice_cat C X)
      (@id_func (@Slice_cat C X))
      (@slice_base_change_obj C PB X Y f b)
      a
      (@slice_base_change_obj C PB X Y f
        (@slice_sigma_obj C X Y f a))
      (@slice_base_change_unit C PB X Y f a))
    (@fapp1_func
      (@Slice_cat C Y)
      (@Slice_cat C X)
      (@slice_base_change_func C PB X Y f)
      (@slice_sigma_obj C X Y f a)
      b);

symbol slice_base_change_untranspose_semantic_func
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  (b : τ (Obj (@Slice_cat C Y)))
  : τ (Functor
      (Hom_cat
        (@Slice_cat C X)
        a
        (@slice_base_change_obj C PB X Y f b))
      (Hom_cat
        (@Slice_cat C Y)
        (@slice_sigma_obj C X Y f a)
        b))
≔ @comp_cat_fapp0
    (Hom_cat
      (@Slice_cat C X)
      a
      (@slice_base_change_obj C PB X Y f b))
    (Hom_cat
      (@Slice_cat C Y)
      (@slice_sigma_obj C X Y f a)
      (@slice_sigma_obj C X Y f
        (@slice_base_change_obj C PB X Y f b)))
    (Hom_cat
      (@Slice_cat C Y)
      (@slice_sigma_obj C X Y f a)
      b)
    (@hom_postcomp_func
      (@Slice_cat C Y)
      (@Slice_cat C Y)
      (@id_func (@Slice_cat C Y))
      (@slice_sigma_obj C X Y f a)
      (@slice_sigma_obj C X Y f
        (@slice_base_change_obj C PB X Y f b))
      b
      (@slice_base_change_counit C PB X Y f b))
    (@fapp1_func
      (@Slice_cat C X)
      (@Slice_cat C Y)
      (@slice_sigma_func C X Y f)
      a
      (@slice_base_change_obj C PB X Y f b));

// Explicit point semantics f*[h] ∘ η_a.
symbol slice_base_change_transpose_semantic
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  [a : τ (Obj (@Slice_cat C X))]
  [b : τ (Obj (@Slice_cat C Y))]
  (h : τ (Hom (@Slice_cat C Y)
      (@slice_sigma_obj C X Y f a) b))
  : τ (Hom (@Slice_cat C X) a
      (@slice_base_change_obj C PB X Y f b))
≔ @fapp0
    (Hom_cat (@Slice_cat C Y) (@slice_sigma_obj C X Y f a) b)
    (Hom_cat (@Slice_cat C X) a
      (@slice_base_change_obj C PB X Y f b))
    (@slice_base_change_transpose_semantic_func C PB X Y f a b)
    h;

// Explicit inverse point semantics ε_b ∘ Σ_f[k].
symbol slice_base_change_untranspose_semantic
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  [a : τ (Obj (@Slice_cat C X))]
  [b : τ (Obj (@Slice_cat C Y))]
  (k : τ (Hom (@Slice_cat C X) a
      (@slice_base_change_obj C PB X Y f b)))
  : τ (Hom (@Slice_cat C Y)
      (@slice_sigma_obj C X Y f a) b)
≔ @fapp0
    (Hom_cat (@Slice_cat C X) a
      (@slice_base_change_obj C PB X Y f b))
    (Hom_cat (@Slice_cat C Y) (@slice_sigma_obj C X Y f a) b)
    (@slice_base_change_untranspose_semantic_func C PB X Y f a b)
    k;

/*
  Stable whole mate functors and point discriminators.

  The point heads are justified because the two triangle runtime rules must
  recognize nested transpose/untranspose after the explicit semantic
  composition has projected to stable hom-action heads. The whole heads retain
  action on higher cone arrows. They are not independent adjunction data:
  proof-time rules below identify each point with its explicit unit/counit
  semantics, while runtime keeps the two presentations distinct.
*/
injective symbol slice_base_change_transpose_func
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  (b : τ (Obj (@Slice_cat C Y)))
  : τ (Functor
      (Hom_cat (@Slice_cat C Y)
        (@slice_sigma_obj C X Y f a) b)
      (Hom_cat (@Slice_cat C X) a
        (@slice_base_change_obj C PB X Y f b)));

injective symbol slice_base_change_untranspose_func
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  (b : τ (Obj (@Slice_cat C Y)))
  : τ (Functor
      (Hom_cat (@Slice_cat C X) a
        (@slice_base_change_obj C PB X Y f b))
      (Hom_cat (@Slice_cat C Y)
        (@slice_sigma_obj C X Y f a) b));

injective symbol slice_base_change_transpose
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  [a : τ (Obj (@Slice_cat C X))]
  [b : τ (Obj (@Slice_cat C Y))]
  (h : τ (Hom (@Slice_cat C Y)
      (@slice_sigma_obj C X Y f a) b))
  : τ (Hom (@Slice_cat C X) a
      (@slice_base_change_obj C PB X Y f b));

injective symbol slice_base_change_untranspose
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  [a : τ (Obj (@Slice_cat C X))]
  [b : τ (Obj (@Slice_cat C Y))]
  (k : τ (Hom (@Slice_cat C X) a
      (@slice_base_change_obj C PB X Y f b)))
  : τ (Hom (@Slice_cat C Y)
      (@slice_sigma_obj C X Y f a) b);

// Whole-to-point projections.
rule @fapp0 _ _
      (@slice_base_change_transpose_func
        $C $PB $X $Y $f $a $b)
      $h
  ↪ @slice_base_change_transpose
      $C $PB $X $Y $f $a $b $h;

rule @fapp0 _ _
      (@slice_base_change_untranspose_func
        $C $PB $X $Y $f $a $b)
      $k
  ↪ @slice_base_change_untranspose
      $C $PB $X $Y $f $a $b $k;

// Direct stable instances of the two existing adjunction triangles.
rule @slice_base_change_untranspose
      $C $PB $X $Y $f $a $b
      (@slice_base_change_transpose
        $C $PB $X $Y $f $a $b $h)
  ↪ $h
with @slice_base_change_transpose
      $C $PB $X $Y $f $a $b
      (@slice_base_change_untranspose
        $C $PB $X $Y $f $a $b $k)
  ↪ $k;

/*
  Proof-time transpose usability.

  Keep the rigid hom_precomp head and recover its canonical slots in side
  conditions. This avoids embedding reducible slice/Sigma expressions in
  nondiscriminating LHS positions and supports both typed reflexivity
  orientations without changing runtime conversion.
*/
unif_rule
  @slice_base_change_transpose
    $C $PB $X $Y $f $a $b $h
  ≡ @hom_precomp_along_fapp0
    $R $R $Id $Z $a $GF $eta
    (@fapp1_fapp0 $L $R $G $Fa $b $h)
  ↪ [
    $R ≡ (@Slice_cat $C $X);
    $L ≡ (@Slice_cat $C $Y);
    $Id ≡ (@id_func $R);
    $Z ≡ (@slice_base_change_obj $C $PB $X $Y $f $b);
    $GF ≡ (@slice_base_change_obj $C $PB $X $Y $f
      (@slice_sigma_obj $C $X $Y $f $a));
    $eta ≡ (@slice_base_change_unit $C $PB $X $Y $f $a);
    $G ≡ (@slice_base_change_func $C $PB $X $Y $f);
    $Fa ≡ (@slice_sigma_obj $C $X $Y $f $a)
  ];

/*
  Proof-time inverse-transpose usability.

  Opposite slice action exposes the underlying Sigma-map functor and reverses
  its object endpoints. The side conditions record that canonical post-Op
  term rather than asking a defined `slice_sigma_func` head to discriminate.
*/
unif_rule
  @slice_base_change_untranspose
    $C $PB $X $Y $f $a $b $k
  ≡ @hom_postcomp_fapp0
    $L $L $Id $Fa $FGb $b $epsilon
    (@fapp1_fapp0 $IntoX $IntoY $SigmaRaw $Gb $a $k)
  ↪ [
    $L ≡ (@Slice_cat $C $Y);
    $Id ≡ (@id_func $L);
    $Fa ≡ (@slice_sigma_obj $C $X $Y $f $a);
    $FGb ≡ (@slice_sigma_obj $C $X $Y $f
      (@slice_base_change_obj $C $PB $X $Y $f $b));
    $epsilon ≡ (@slice_base_change_counit $C $PB $X $Y $f $b);
    $IntoX ≡ (@Into_restr_cat $C $X);
    $IntoY ≡ (@Into_restr_cat $C $Y);
    $SigmaRaw ≡ (@sigma_map_func
      (Op_cat $C)
      (@hom_con $C $X $C (@id_func $C))
      (@hom_con $C $Y $C (@id_func $C))
      (@hom_con_int_postcomp_func
        $C $C (@id_func $C) $X $Y $f));
    $Gb ≡ (@slice_base_change_obj $C $PB $X $Y $f $b)
  ];

/*
  Explicit non-opaque witnesses for the two proof-time usability agreements.
  Their bodies are typed reflexivity through the unifiers above. Runtime
  retains the stable mate heads; consumers that need semantic composition can
  apply ordinary equality functoriality to these paths.
*/
symbol slice_base_change_transpose_semantic_path
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  [a : τ (Obj (@Slice_cat C X))]
  [b : τ (Obj (@Slice_cat C Y))]
  (h : τ (Hom (@Slice_cat C Y)
      (@slice_sigma_obj C X Y f a) b))
  : τ (@=
      (Hom (@Slice_cat C X) a
        (@slice_base_change_obj C PB X Y f b))
      (@slice_base_change_transpose C PB X Y f a b h)
      (@slice_base_change_transpose_semantic C PB X Y f a b h))
≔ @eq_refl
    (Hom (@Slice_cat C X) a
      (@slice_base_change_obj C PB X Y f b))
    (@slice_base_change_transpose C PB X Y f a b h);

symbol slice_base_change_untranspose_semantic_path
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  [a : τ (Obj (@Slice_cat C X))]
  [b : τ (Obj (@Slice_cat C Y))]
  (k : τ (Hom (@Slice_cat C X) a
      (@slice_base_change_obj C PB X Y f b)))
  : τ (@=
      (Hom (@Slice_cat C Y)
        (@slice_sigma_obj C X Y f a) b)
      (@slice_base_change_untranspose C PB X Y f a b k)
      (@slice_base_change_untranspose_semantic C PB X Y f a b k))
≔ @eq_refl
    (Hom (@Slice_cat C Y)
      (@slice_sigma_obj C X Y f a) b)
    (@slice_base_change_untranspose C PB X Y f a b k);

/*
  Domain and structure-arrow observations of covariant slice action.

  Arbitrary Sigma objects deliberately do not satisfy runtime eta. The first
  two paths each use one proof-time owner and are composed explicitly, avoiding
  reliance on transitivity across unification rules.
*/
symbol slice_sigma_whole_domain
  [C : Cat]
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  : τ (Obj C)
≔ @fapp0
    (@Slice_cat C Y)
    C
    (@slice_domain_func C Y)
    (@slice_sigma_obj C X Y f a);

symbol slice_sigma_domain_to_whole_path
  [C : Cat]
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  : τ (@= (Obj C)
      (@slice_object_domain C X a)
      (@slice_sigma_whole_domain C X Y f a))
≔ @eq_refl (Obj C) (@slice_object_domain C X a);

symbol slice_sigma_whole_to_domain_path
  [C : Cat]
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  : τ (@= (Obj C)
      (@slice_sigma_whole_domain C X Y f a)
      (@slice_object_domain C Y (@slice_sigma_obj C X Y f a)))
≔ @eq_refl (Obj C) (@slice_sigma_whole_domain C X Y f a);

symbol slice_sigma_domain_path
  [C : Cat]
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  : τ (@= (Obj C)
      (@slice_object_domain C X a)
      (@slice_object_domain C Y (@slice_sigma_obj C X Y f a)))
≔ @eq_trans
    (Obj C)
    (@slice_object_domain C X a)
    (@slice_sigma_whole_domain C X Y f a)
    (@slice_object_domain C Y (@slice_sigma_obj C X Y f a))
    (@slice_sigma_domain_to_whole_path C X Y f a)
    (@slice_sigma_whole_to_domain_path C X Y f a);

// Structure arrow of Σ_f(a), recentered at the stable domain of a.
symbol slice_sigma_structure_arrow
  [C : Cat]
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  : τ (Hom C (@slice_object_domain C X a) Y)
≔ @comp_fapp0
    C
    (@slice_object_domain C X a)
    (@slice_object_domain C Y (@slice_sigma_obj C X Y f a))
    Y
    (@slice_object_arrow C Y (@slice_sigma_obj C X Y f a))
    (@path_to_hom
      C
      (@slice_object_domain C X a)
      (@slice_object_domain C Y (@slice_sigma_obj C X Y f a))
      (@slice_sigma_domain_path C X Y f a));

// -------------------------------------------------------------------------------------------------
// Chosen pullback object, projections, and retained square
// -------------------------------------------------------------------------------------------------

// Pullback of the slice object g:Z→Y along f:X→Y, still as an object of C/X.
symbol pullback_slice_obj
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (g : τ (Obj (@Slice_cat C Y)))
  : τ (Obj (@Slice_cat C X))
≔ @slice_base_change_obj C PB X Y f g;

// Ambient domain P of f*(g).
symbol pullback_domain
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (g : τ (Obj (@Slice_cat C Y)))
  : τ (Obj C)
≔ @slice_object_domain C X (@pullback_slice_obj C PB X Y f g);

// First projection π₁:P→X is the structure arrow of f*(g).
symbol pullback_fst
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (g : τ (Obj (@Slice_cat C Y)))
  : τ (Hom C (@pullback_domain C PB X Y f g) X)
≔ @slice_object_arrow C X (@pullback_slice_obj C PB X Y f g);

// Counit component Σ_f(f*(g)) → g in C/Y.
symbol pullback_counit_slice_arrow
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (g : τ (Obj (@Slice_cat C Y)))
  : τ (Hom
      (@Slice_cat C Y)
      (@slice_sigma_obj C X Y f
        (@pullback_slice_obj C PB X Y f g))
      g)
≔ @slice_base_change_counit C PB X Y f g;

// Native second projection before recentering its source at P.
symbol pullback_snd_native
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (g : τ (Obj (@Slice_cat C Y)))
  : τ (Hom C
      (@slice_object_domain C Y
        (@slice_sigma_obj C X Y f
          (@pullback_slice_obj C PB X Y f g)))
      (@slice_object_domain C Y g))
≔ @slice_arrow_underlying
    C Y
    (@slice_sigma_obj C X Y f
      (@pullback_slice_obj C PB X Y f g))
    g
    (@pullback_counit_slice_arrow C PB X Y f g);

// Domain recentering P → domain(Σ_f(f*(g))).
symbol pullback_domain_recenter_arrow
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (g : τ (Obj (@Slice_cat C Y)))
  : τ (Hom C
      (@pullback_domain C PB X Y f g)
      (@slice_object_domain C Y
        (@slice_sigma_obj C X Y f
          (@pullback_slice_obj C PB X Y f g))))
≔ @path_to_hom
    C
    (@pullback_domain C PB X Y f g)
    (@slice_object_domain C Y
      (@slice_sigma_obj C X Y f
        (@pullback_slice_obj C PB X Y f g)))
    (@slice_sigma_domain_path C X Y f
      (@pullback_slice_obj C PB X Y f g));

// Readable second projection π₂:P→domain(g).
symbol pullback_snd
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (g : τ (Obj (@Slice_cat C Y)))
  : τ (Hom C
      (@pullback_domain C PB X Y f g)
      (@slice_object_domain C Y g))
≔ @comp_fapp0
    C
    (@pullback_domain C PB X Y f g)
    (@slice_object_domain C Y
      (@slice_sigma_obj C X Y f
        (@pullback_slice_obj C PB X Y f g)))
    (@slice_object_domain C Y g)
    (@pullback_snd_native C PB X Y f g)
    (@pullback_domain_recenter_arrow C PB X Y f g);

// Native directed counit square at the unrecentered source object.
symbol pullback_square_native
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (g : τ (Obj (@Slice_cat C Y)))
  : τ (Hom
      (Hom_cat C
        (@slice_object_domain C Y
          (@slice_sigma_obj C X Y f
            (@pullback_slice_obj C PB X Y f g)))
        Y)
      (@comp_fapp0
        C
        (@slice_object_domain C Y
          (@slice_sigma_obj C X Y f
            (@pullback_slice_obj C PB X Y f g)))
        (@slice_object_domain C Y g)
        Y
        (@slice_object_arrow C Y g)
        (@pullback_snd_native C PB X Y f g))
      (@slice_object_arrow C Y
        (@slice_sigma_obj C X Y f
          (@pullback_slice_obj C PB X Y f g))))
≔ @slice_arrow_cell
    C Y
    (@slice_sigma_obj C X Y f
      (@pullback_slice_obj C PB X Y f g))
    g
    (@pullback_counit_slice_arrow C PB X Y f g);

// Whole precomposition used to recenter the square at P.
symbol pullback_square_recenter_func
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (g : τ (Obj (@Slice_cat C Y)))
  : τ (Functor
      (Hom_cat C
        (@slice_object_domain C Y
          (@slice_sigma_obj C X Y f
            (@pullback_slice_obj C PB X Y f g)))
        Y)
      (Hom_cat C (@pullback_domain C PB X Y f g) Y))
≔ @hom_precomp_along_func
    C C (@id_func C) Y
    (@pullback_domain C PB X Y f g)
    (@slice_object_domain C Y
      (@slice_sigma_obj C X Y f
        (@pullback_slice_obj C PB X Y f g)))
    (@pullback_domain_recenter_arrow C PB X Y f g);

symbol pullback_square_source
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (g : τ (Obj (@Slice_cat C Y)))
  : τ (Obj (Hom_cat C (@pullback_domain C PB X Y f g) Y))
≔ @fapp0
    _ _
    (@pullback_square_recenter_func C PB X Y f g)
    (@comp_fapp0
      C
      (@slice_object_domain C Y
        (@slice_sigma_obj C X Y f
          (@pullback_slice_obj C PB X Y f g)))
      (@slice_object_domain C Y g)
      Y
      (@slice_object_arrow C Y g)
      (@pullback_snd_native C PB X Y f g));

symbol pullback_square_target
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (g : τ (Obj (@Slice_cat C Y)))
  : τ (Obj (Hom_cat C (@pullback_domain C PB X Y f g) Y))
≔ @fapp0
    _ _
    (@pullback_square_recenter_func C PB X Y f g)
    (@slice_object_arrow C Y
      (@slice_sigma_obj C X Y f
        (@pullback_slice_obj C PB X Y f g)));

// Recentered directed pullback square, retaining the counit's higher cell.
symbol pullback_square_cell
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (g : τ (Obj (@Slice_cat C Y)))
  : τ (Hom
      (Hom_cat C (@pullback_domain C PB X Y f g) Y)
      (@pullback_square_source C PB X Y f g)
      (@pullback_square_target C PB X Y f g))
≔ @fapp1_fapp0
    _ _
    (@pullback_square_recenter_func C PB X Y f g)
    _ _
    (@pullback_square_native C PB X Y f g);

// Readable source g ∘ π₂ of the recentered square.
symbol pullback_square_readable_source
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (g : τ (Obj (@Slice_cat C Y)))
  : τ (Obj (Hom_cat C (@pullback_domain C PB X Y f g) Y))
≔ @comp_fapp0
    C
    (@pullback_domain C PB X Y f g)
    (@slice_object_domain C Y g)
    Y
    (@slice_object_arrow C Y g)
    (@pullback_snd C PB X Y f g);

// Readable target: the recentered structure arrow of Σ_f(f*(g)).
symbol pullback_square_readable_target
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (g : τ (Obj (@Slice_cat C Y)))
  : τ (Obj (Hom_cat C (@pullback_domain C PB X Y f g) Y))
≔ @slice_sigma_structure_arrow
    C X Y f (@pullback_slice_obj C PB X Y f g);

// Raw right-associated endpoint selected after stable precomposition unfolds.
symbol pullback_square_source_raw
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (g : τ (Obj (@Slice_cat C Y)))
  : τ (Obj (Hom_cat C (@pullback_domain C PB X Y f g) Y))
≔ @comp_fapp0
    C
    (@pullback_domain C PB X Y f g)
    (@slice_object_domain C Y
      (@slice_sigma_obj C X Y f
        (@pullback_slice_obj C PB X Y f g)))
    Y
    (@comp_fapp0
      C
      (@slice_object_domain C Y
        (@slice_sigma_obj C X Y f
          (@pullback_slice_obj C PB X Y f g)))
      (@slice_object_domain C Y g)
      Y
      (@slice_object_arrow C Y g)
      (@pullback_snd_native C PB X Y f g))
    (@pullback_domain_recenter_arrow C PB X Y f g);

// Stable precomposition has the raw composition reading at proof time.
symbol pullback_square_source_to_raw_path
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (g : τ (Obj (@Slice_cat C Y)))
  : τ (@=
      (Hom C (@pullback_domain C PB X Y f g) Y)
      (@pullback_square_source C PB X Y f g)
      (@pullback_square_source_raw C PB X Y f g))
≔ @eq_refl
    (Hom C (@pullback_domain C PB X Y f g) Y)
    (@pullback_square_source C PB X Y f g);

// Associativity changes `(g ∘ π₂_native) ∘ recenter` to `g ∘ π₂`.
symbol pullback_square_raw_to_readable_path
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (g : τ (Obj (@Slice_cat C Y)))
  : τ (@=
      (Hom C (@pullback_domain C PB X Y f g) Y)
      (@pullback_square_source_raw C PB X Y f g)
      (@pullback_square_readable_source C PB X Y f g))
≔ @eq_sym
    (Hom C (@pullback_domain C PB X Y f g) Y)
    (@pullback_square_readable_source C PB X Y f g)
    (@pullback_square_source_raw C PB X Y f g)
    (@comp_assoc
      C
      (@pullback_domain C PB X Y f g)
      (@slice_object_domain C Y
        (@slice_sigma_obj C X Y f
          (@pullback_slice_obj C PB X Y f g)))
      (@slice_object_domain C Y g)
      Y
      (@slice_object_arrow C Y g)
      (@pullback_snd_native C PB X Y f g)
      (@pullback_domain_recenter_arrow C PB X Y f g));

symbol pullback_square_source_path
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (g : τ (Obj (@Slice_cat C Y)))
  : τ (@=
      (Hom C (@pullback_domain C PB X Y f g) Y)
      (@pullback_square_source C PB X Y f g)
      (@pullback_square_readable_source C PB X Y f g))
≔ @eq_trans
    (Hom C (@pullback_domain C PB X Y f g) Y)
    (@pullback_square_source C PB X Y f g)
    (@pullback_square_source_raw C PB X Y f g)
    (@pullback_square_readable_source C PB X Y f g)
    (@pullback_square_source_to_raw_path C PB X Y f g)
    (@pullback_square_raw_to_readable_path C PB X Y f g);

// Target comparison is typed reflexivity through the selected recentering.
symbol pullback_square_target_path
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (g : τ (Obj (@Slice_cat C Y)))
  : τ (@=
      (Hom C (@pullback_domain C PB X Y f g) Y)
      (@pullback_square_target C PB X Y f g)
      (@pullback_square_readable_target C PB X Y f g))
≔ @eq_refl
    (Hom C (@pullback_domain C PB X Y f g) Y)
    (@pullback_square_target C PB X Y f g);

/*
  Fully readable recentered square. Equality paths only adjust the two object
  presentations in the ambient hom category; the directed middle cell remains
  the actual counit projection.
*/
symbol pullback_square_readable_cell
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (g : τ (Obj (@Slice_cat C Y)))
  : τ (Hom
      (Hom_cat C (@pullback_domain C PB X Y f g) Y)
      (@pullback_square_readable_source C PB X Y f g)
      (@pullback_square_readable_target C PB X Y f g))
  ≔ @comp_fapp0
    (Hom_cat C (@pullback_domain C PB X Y f g) Y)
    (@pullback_square_readable_source C PB X Y f g)
    (@pullback_square_target C PB X Y f g)
    (@pullback_square_readable_target C PB X Y f g)
    (@path_to_hom
      (Hom_cat C (@pullback_domain C PB X Y f g) Y)
      (@pullback_square_target C PB X Y f g)
      (@pullback_square_readable_target C PB X Y f g)
      (@pullback_square_target_path C PB X Y f g))
    (@comp_fapp0
      (Hom_cat C (@pullback_domain C PB X Y f g) Y)
      (@pullback_square_readable_source C PB X Y f g)
      (@pullback_square_source C PB X Y f g)
      (@pullback_square_target C PB X Y f g)
      (@pullback_square_cell C PB X Y f g)
      (@path_to_hom
        (Hom_cat C (@pullback_domain C PB X Y f g) Y)
        (@pullback_square_readable_source C PB X Y f g)
        (@pullback_square_source C PB X Y f g)
        (@eq_sym
          (Hom C (@pullback_domain C PB X Y f g) Y)
          (@pullback_square_source C PB X Y f g)
          (@pullback_square_readable_source C PB X Y f g)
          (@pullback_square_source_path C PB X Y f g))));

// -------------------------------------------------------------------------------------------------
// Whole cone category and computational universal lift
// -------------------------------------------------------------------------------------------------

/*
  Whole category of directed pullback cones from a slice object a over X to
  g over Y.  This is the left hom category of the selected adjunction, not a
  separate cone code: objects are slice arrows Σ_f(a)→g and higher arrows are
  retained by the existing hom-category tower.
*/
symbol pullback_cone_cat
  [C : Cat]
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  (g : τ (Obj (@Slice_cat C Y)))
  : Cat
≔ Hom_cat
    (@Slice_cat C Y)
    (@slice_sigma_obj C X Y f a)
    g;

// Native cone constructor for arbitrary slice objects and exact endpoints.
symbol pullback_cone_intro
  [C : Cat]
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  [a : τ (Obj (@Slice_cat C X))]
  [g : τ (Obj (@Slice_cat C Y))]
  (p : τ (Hom C
      (@slice_object_domain C Y (@slice_sigma_obj C X Y f a))
      (@slice_object_domain C Y g)))
  (alpha : τ (Hom
      (Hom_cat C
        (@slice_object_domain C Y (@slice_sigma_obj C X Y f a))
        Y)
      (@comp_fapp0
        C
        (@slice_object_domain C Y (@slice_sigma_obj C X Y f a))
        (@slice_object_domain C Y g)
        Y
        (@slice_object_arrow C Y g)
        p)
      (@slice_object_arrow C Y (@slice_sigma_obj C X Y f a))))
  : τ (Obj (@pullback_cone_cat C X Y f a g))
≔ @slice_arrow_intro
    C Y
    (@slice_sigma_obj C X Y f a)
    g
    p alpha;

/*
  Constructor-visible ambient cone:

    a : W→X,  b : W→dom(g),  alpha : g∘b ⇒ f∘a.

  The identity-family postcomposition unifier relates the readable target
  f∘a to the stable represented action selected by Σ_f.
*/
symbol pullback_cone_constructor
  [C : Cat]
  [W X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (a : τ (Hom C W X))
  [g : τ (Obj (@Slice_cat C Y))]
  (b : τ (Hom C W (@slice_object_domain C Y g)))
  (alpha : τ (Hom
      (Hom_cat C W Y)
      (@comp_fapp0
        C W (@slice_object_domain C Y g) Y
        (@slice_object_arrow C Y g)
        b)
      (@comp_fapp0 C W X Y f a)))
  : τ (Obj (@pullback_cone_cat
      C X Y f (Struct_sigma W a) g))
≔ @slice_arrow_intro
    C Y
    (@slice_sigma_obj C X Y f (Struct_sigma W a))
    g
    b alpha;

// Whole universal lift, retaining action on higher cone arrows.
symbol pullback_lift_func
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  (g : τ (Obj (@Slice_cat C Y)))
  : τ (Functor
      (@pullback_cone_cat C X Y f a g)
      (Hom_cat
        (@Slice_cat C X)
        a
        (@pullback_slice_obj C PB X Y f g)))
≔ @slice_base_change_transpose_func C PB X Y f a g;

// Whole inverse: a slice lift is sent to its induced cone.
symbol pullback_cone_of_lift_func
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  (g : τ (Obj (@Slice_cat C Y)))
  : τ (Functor
      (Hom_cat
        (@Slice_cat C X)
        a
        (@pullback_slice_obj C PB X Y f g))
      (@pullback_cone_cat C X Y f a g))
≔ @slice_base_change_untranspose_func C PB X Y f a g;

symbol pullback_lift_slice
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  [a : τ (Obj (@Slice_cat C X))]
  [g : τ (Obj (@Slice_cat C Y))]
  (h : τ (Obj (@pullback_cone_cat C X Y f a g)))
  : τ (Hom
      (@Slice_cat C X)
      a
      (@pullback_slice_obj C PB X Y f g))
≔ @slice_base_change_transpose C PB X Y f a g h;

symbol pullback_cone_of_lift
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  [a : τ (Obj (@Slice_cat C X))]
  [g : τ (Obj (@Slice_cat C Y))]
  (k : τ (Hom
      (@Slice_cat C X)
      a
      (@pullback_slice_obj C PB X Y f g)))
  : τ (Obj (@pullback_cone_cat C X Y f a g))
≔ @slice_base_change_untranspose C PB X Y f a g k;

// Ambient mediating arrow underlying the universal slice lift.
symbol pullback_lift
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  [a : τ (Obj (@Slice_cat C X))]
  [g : τ (Obj (@Slice_cat C Y))]
  (h : τ (Obj (@pullback_cone_cat C X Y f a g)))
  : τ (Hom C
      (@slice_object_domain C X a)
      (@pullback_domain C PB X Y f g))
≔ @slice_arrow_underlying
    C X
    a
    (@pullback_slice_obj C PB X Y f g)
    (@pullback_lift_slice C PB X Y f a g h);

/*
  First projection triangle of the mediator:

    π₁ ∘ lift(h) ⇒ arrow(a).

  In a locally discrete category this is the usual first projection equality;
  in the internal higher setting the directed cell is retained explicitly.
*/
symbol pullback_lift_fst_cell
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  [a : τ (Obj (@Slice_cat C X))]
  [g : τ (Obj (@Slice_cat C Y))]
  (h : τ (Obj (@pullback_cone_cat C X Y f a g)))
  : τ (Hom
      (Hom_cat C (@slice_object_domain C X a) X)
      (@comp_fapp0
        C
        (@slice_object_domain C X a)
        (@pullback_domain C PB X Y f g)
        X
        (@pullback_fst C PB X Y f g)
        (@pullback_lift C PB X Y f a g h))
      (@slice_object_arrow C X a))
≔ @slice_arrow_cell
    C X
    a
    (@pullback_slice_obj C PB X Y f g)
    (@pullback_lift_slice C PB X Y f a g h);
