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
  arrow equalities. A cone is exactly an object of the internal slice Hom;
  there is no pullback-specific record or constructor carrying a square.
  Whole Hom recovery and uniqueness compute through the selected adjunction.
  Explicit pseudo invertibility, Π_f, Beck--Chevalley, products-in-slices,
  weighted comparisons, and pushouts remain later layers.
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

// Stable whole categorical pullback along f:X→Y. The selected Catd action
// below is its semantic owner and projects to this runtime discriminator.
injective symbol slice_base_change_func
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  : τ (Functor (@Slice_cat C Y) (@Slice_cat C X));

// lhs-audit: keep 1 -- `Op_cat(C)` is the variance guard on the whole family action.
rule @fapp1_fapp0
      (Op_cat $C) Cat_cat
      (@SliceBaseChange_catd $C $PB)
      $Y $X $f
  ↪ @slice_base_change_func $C $PB $X $Y $f;

// Computational object postcomposition in the covariant slice family.
// The generic stable Sigma-map point retains a runtime discriminator while
// agreeing at proof time with the whole semantic `slice_sigma_func` action.
symbol slice_sigma_obj
  [C : Cat]
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  : τ (Obj (@Slice_cat C Y))
≔ @sigma_map_obj
    (Op_cat C)
    (@fapp0
      C (Catd_cat (Op_cat C))
      (@hom_con_int C C (@id Cat_cat C))
      X)
    (@fapp0
      C (Catd_cat (Op_cat C))
      (@hom_con_int C C (@id Cat_cat C))
      Y)
    (@hom_con_int_postcomp_func
      C C (@id Cat_cat C) X Y f)
    a;

// Whole semantic Σ_f object action projects to the selected generic Sigma
// point. The displayed postcomposition operation is the sole discriminator;
// reducible family/category slots remain inferred.
rule @fapp0 _ _
      (@sigma_map_func _ _ _
        (@hom_con_int_postcomp_func
          $C $C (@id Cat_cat $C) $X $Y $f))
      $a
  ↪ @slice_sigma_obj $C $X $Y $f $a;

// Stable object action of the selected f* functor.
injective symbol slice_base_change_obj
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (b : τ (Obj (@Slice_cat C Y)))
  : τ (Obj (@Slice_cat C X));

rule @fapp0 _ _
      (@slice_base_change_func $C $PB $X $Y $f)
      $b
  ↪ @slice_base_change_obj $C $PB $X $Y $f $b;

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

// Stable whole unit observation of slice base change.
injective symbol slice_base_change_unit_transf
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
        (@slice_sigma_func C X Y f)));

// Stable whole counit observation of slice base change.
injective symbol slice_base_change_counit_transf
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
      (@id_func (@Slice_cat C Y)));

// Declaration-backed generic observations compile to the stable whole heads.
rule @unit_adj_transf
      _ _ _ _
      (@slice_base_change_adjunction $C $PB $X $Y $f)
  ↪ @slice_base_change_unit_transf $C $PB $X $Y $f;

rule @counit_adj_transf
      _ _ _ _
      (@slice_base_change_adjunction $C $PB $X $Y $f)
  ↪ @slice_base_change_counit_transf $C $PB $X $Y $f;

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
  Stable `(ac)` off-diagonal observations and canonical rectangle cuts.

  The whole unit/counit transfors above retain the declaration indices. Their
  tapp1 projections below are Došen's γᶜ and φᵃ operations. Literal
  post-`Op` rules are required because the conventional slice aliases and
  opposite composition have reduced before runtime matching.
*/
injective symbol slice_base_change_gamma
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (u : τ (Hom C X Y))
  [a a' : τ (Obj (@Slice_cat C X))]
  (k : τ (Hom (@Slice_cat C X) a a'))
  : τ (Hom
      (@Slice_cat C X)
      a
      (@slice_base_change_obj C PB X Y u
        (@slice_sigma_obj C X Y u a')));

injective symbol slice_base_change_phi
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (u : τ (Hom C X Y))
  [b' b : τ (Obj (@Slice_cat C Y))]
  (h : τ (Hom (@Slice_cat C Y) b' b))
  : τ (Hom
      (@Slice_cat C Y)
      (@slice_sigma_obj C X Y u
        (@slice_base_change_obj C PB X Y u b'))
      b);

rule @tapp1_fapp0
      _ _ _ _
      $a $a'
      (@slice_base_change_unit_transf $C $PB $X $Y $u)
      $k
  ↪ @slice_base_change_gamma $C $PB $X $Y $u $a $a' $k;

rule @tapp1_fapp0
      _ _ _ _
      $b' $b
      (@slice_base_change_counit_transf $C $PB $X $Y $u)
      $h
  ↪ @slice_base_change_phi $C $PB $X $Y $u $b' $b $h;

// Identity boundaries recover the ordinary unit and counit components.
rule @slice_base_change_gamma
      $C $PB $X $Y $u $a $a
      (@id _ $a)
  ↪ @slice_base_change_unit $C $PB $X $Y $u $a;

rule @slice_base_change_phi
      $C $PB $X $Y $u $b $b
      (@id _ $b)
  ↪ @slice_base_change_counit $C $PB $X $Y $u $b;

// Canonical post-`Op` left triangle after γᶜ(id) and φᵃ(id) expose components.
// lhs-audit: keep 1,2,3,4 -- exact raw endpoints are the subject-reduction guards.
rule @comp_fapp0
      (@Sigma_cat
        (Op_cat $C)
        (@hom_con $C $Y $C (@id Cat_cat $C)))
      (@sigma_map_obj
        (Op_cat $C)
        (@hom_con $C $X $C (@id Cat_cat $C))
        (@hom_con $C $Y $C (@id Cat_cat $C))
        (@hom_con_int_postcomp_func
          $C $C (@id Cat_cat $C) $X $Y $u)
        $a)
      (@sigma_map_obj
        (Op_cat $C)
        (@hom_con $C $X $C (@id Cat_cat $C))
        (@hom_con $C $Y $C (@id Cat_cat $C))
        (@hom_con_int_postcomp_func
          $C $C (@id Cat_cat $C) $X $Y $u)
        (@slice_base_change_obj $C $PB $X $Y $u
          (@sigma_map_obj
            (Op_cat $C)
            (@hom_con $C $X $C (@id Cat_cat $C))
            (@hom_con $C $Y $C (@id Cat_cat $C))
            (@hom_con_int_postcomp_func
              $C $C (@id Cat_cat $C) $X $Y $u)
            $a)))
      (@sigma_map_obj
        (Op_cat $C)
        (@hom_con $C $X $C (@id Cat_cat $C))
        (@hom_con $C $Y $C (@id Cat_cat $C))
        (@hom_con_int_postcomp_func
          $C $C (@id Cat_cat $C) $X $Y $u)
        $a)
      (@fapp1_fapp0
        (@Sigma_cat
          (Op_cat $C)
          (@hom_con $C $X $C (@id Cat_cat $C)))
        (@Sigma_cat
          (Op_cat $C)
          (@hom_con $C $Y $C (@id Cat_cat $C)))
        (@sigma_map_func
          (Op_cat $C)
          (@hom_con $C $X $C (@id Cat_cat $C))
          (@hom_con $C $Y $C (@id Cat_cat $C))
          (@hom_con_int_postcomp_func
            $C $C (@id Cat_cat $C) $X $Y $u))
        (@slice_base_change_obj $C $PB $X $Y $u
          (@sigma_map_obj
            (Op_cat $C)
            (@hom_con $C $X $C (@id Cat_cat $C))
            (@hom_con $C $Y $C (@id Cat_cat $C))
            (@hom_con_int_postcomp_func
              $C $C (@id Cat_cat $C) $X $Y $u)
            $a))
        $a
        (@tapp0_fapp0
          _ _ _ _ $a
          (@slice_base_change_unit_transf $C $PB $X $Y $u)))
      (@tapp0_fapp0
        _ _ _ _
        (@sigma_map_obj
          (Op_cat $C)
          (@hom_con $C $X $C (@id Cat_cat $C))
          (@hom_con $C $Y $C (@id Cat_cat $C))
          (@hom_con_int_postcomp_func
            $C $C (@id Cat_cat $C) $X $Y $u)
          $a)
        (@slice_base_change_counit_transf $C $PB $X $Y $u))
  ↪ @id
      (@Sigma_cat
        (Op_cat $C)
        (@hom_con $C $Y $C (@id Cat_cat $C)))
      (@sigma_map_obj
        (Op_cat $C)
        (@hom_con $C $X $C (@id Cat_cat $C))
        (@hom_con $C $Y $C (@id Cat_cat $C))
        (@hom_con_int_postcomp_func
          $C $C (@id Cat_cat $C) $X $Y $u)
        $a);

// Canonical post-`Op` right triangle after γᶜ(id) and φᵃ(id) expose components.
// lhs-audit: keep 1,2,3,4 -- exact raw endpoints are the subject-reduction guards.
rule @comp_fapp0
      (@Sigma_cat
        (Op_cat $C)
        (@hom_con $C $X $C (@id Cat_cat $C)))
      (@slice_base_change_obj $C $PB $X $Y $u $b)
      (@slice_base_change_obj $C $PB $X $Y $u
        (@sigma_map_obj
          (Op_cat $C)
          (@hom_con $C $X $C (@id Cat_cat $C))
          (@hom_con $C $Y $C (@id Cat_cat $C))
          (@hom_con_int_postcomp_func
            $C $C (@id Cat_cat $C) $X $Y $u)
          (@slice_base_change_obj $C $PB $X $Y $u $b)))
      (@slice_base_change_obj $C $PB $X $Y $u $b)
      (@tapp0_fapp0
        _ _ _ _
        (@slice_base_change_obj $C $PB $X $Y $u $b)
        (@slice_base_change_unit_transf $C $PB $X $Y $u))
      (@fapp1_fapp0
        (Op_cat
          (@Sigma_cat
            (Op_cat $C)
            (@hom_con $C $Y $C (@id Cat_cat $C))))
        (Op_cat
          (@Sigma_cat
            (Op_cat $C)
            (@hom_con $C $X $C (@id Cat_cat $C))))
        (@slice_base_change_func $C $PB $X $Y $u)
        (@sigma_map_obj
          (Op_cat $C)
          (@hom_con $C $X $C (@id Cat_cat $C))
          (@hom_con $C $Y $C (@id Cat_cat $C))
          (@hom_con_int_postcomp_func
            $C $C (@id Cat_cat $C) $X $Y $u)
          (@slice_base_change_obj $C $PB $X $Y $u $b))
        $b
        (@tapp0_fapp0
          _ _ _ _ $b
          (@slice_base_change_counit_transf $C $PB $X $Y $u)))
  ↪ @id
      (@Sigma_cat
        (Op_cat $C)
        (@hom_con $C $X $C (@id Cat_cat $C)))
      (@slice_base_change_obj $C $PB $X $Y $u $b);

// Literal canonical F-side rectangle after all aliases have unfolded.
// lhs-audit: keep 1,3,4 -- exact raw category/middle/final guards prevent endpoint collapse.
rule @comp_fapp0
      (@Sigma_cat
        (Op_cat $C)
        (@hom_con $C $Y $C (@id Cat_cat $C)))
      $b
      (@sigma_map_obj
        (Op_cat $C)
        (@hom_con $C $X $C (@id Cat_cat $C))
        (@hom_con $C $Y $C (@id Cat_cat $C))
        (@hom_con_int_postcomp_func
          $C $C (@id Cat_cat $C) $X $Y $u)
        (@slice_base_change_obj $C $PB $X $Y $u
          (@sigma_map_obj
            (Op_cat $C)
            (@hom_con $C $X $C (@id Cat_cat $C))
            (@hom_con $C $Y $C (@id Cat_cat $C))
            (@hom_con_int_postcomp_func
              $C $C (@id Cat_cat $C) $X $Y $u)
            $a')))
      (@sigma_map_obj
        (Op_cat $C)
        (@hom_con $C $X $C (@id Cat_cat $C))
        (@hom_con $C $Y $C (@id Cat_cat $C))
        (@hom_con_int_postcomp_func
          $C $C (@id Cat_cat $C) $X $Y $u)
        $a)
      (@fapp1_fapp0
        (@Sigma_cat
          (Op_cat $C)
          (@hom_con $C $X $C (@id Cat_cat $C)))
        (@Sigma_cat
          (Op_cat $C)
          (@hom_con $C $Y $C (@id Cat_cat $C)))
        (@sigma_map_func
          (Op_cat $C)
          (@hom_con $C $X $C (@id Cat_cat $C))
          (@hom_con $C $Y $C (@id Cat_cat $C))
          (@hom_con_int_postcomp_func
            $C $C (@id Cat_cat $C) $X $Y $u))
        (@slice_base_change_obj $C $PB $X $Y $u
          (@sigma_map_obj
            (Op_cat $C)
            (@hom_con $C $X $C (@id Cat_cat $C))
            (@hom_con $C $Y $C (@id Cat_cat $C))
            (@hom_con_int_postcomp_func
              $C $C (@id Cat_cat $C) $X $Y $u)
            $a'))
        $a
        (@slice_base_change_gamma $C $PB $X $Y $u $a $a' $k))
      (@slice_base_change_phi $C $PB $X $Y $u
        (@sigma_map_obj
          (Op_cat $C)
          (@hom_con $C $X $C (@id Cat_cat $C))
          (@hom_con $C $Y $C (@id Cat_cat $C))
          (@hom_con_int_postcomp_func
            $C $C (@id Cat_cat $C) $X $Y $u)
          $a')
        $b $h)
  ↪ @comp_fapp0
      (@Sigma_cat
        (Op_cat $C)
        (@hom_con $C $Y $C (@id Cat_cat $C)))
      $b
      (@sigma_map_obj
        (Op_cat $C)
        (@hom_con $C $X $C (@id Cat_cat $C))
        (@hom_con $C $Y $C (@id Cat_cat $C))
        (@hom_con_int_postcomp_func
          $C $C (@id Cat_cat $C) $X $Y $u)
        $a')
      (@sigma_map_obj
        (Op_cat $C)
        (@hom_con $C $X $C (@id Cat_cat $C))
        (@hom_con $C $Y $C (@id Cat_cat $C))
        (@hom_con_int_postcomp_func
          $C $C (@id Cat_cat $C) $X $Y $u)
        $a)
      (@fapp1_fapp0
        (@Sigma_cat
          (Op_cat $C)
          (@hom_con $C $X $C (@id Cat_cat $C)))
        (@Sigma_cat
          (Op_cat $C)
          (@hom_con $C $Y $C (@id Cat_cat $C)))
        (@sigma_map_func
          (Op_cat $C)
          (@hom_con $C $X $C (@id Cat_cat $C))
          (@hom_con $C $Y $C (@id Cat_cat $C))
          (@hom_con_int_postcomp_func
            $C $C (@id Cat_cat $C) $X $Y $u))
        $a' $a $k)
      $h;

// Literal canonical G-side rectangle after all aliases have unfolded.
// lhs-audit: keep 1,2,3 -- exact raw category/source/middle guards retain Y.
rule @comp_fapp0
      (@Sigma_cat
        (Op_cat $C)
        (@hom_con $C $X $C (@id Cat_cat $C)))
      (@slice_base_change_obj $C $PB $X $Y $u $b)
      (@slice_base_change_obj $C $PB $X $Y $u
        (@sigma_map_obj
          (Op_cat $C)
          (@hom_con $C $X $C (@id Cat_cat $C))
          (@hom_con $C $Y $C (@id Cat_cat $C))
          (@hom_con_int_postcomp_func
            $C $C (@id Cat_cat $C) $X $Y $u)
          (@slice_base_change_obj $C $PB $X $Y $u $b')))
      $a
      (@slice_base_change_gamma $C $PB $X $Y $u
        $a (@slice_base_change_obj $C $PB $X $Y $u $b') $k)
      (@fapp1_fapp0
        (Op_cat
          (@Sigma_cat
            (Op_cat $C)
            (@hom_con $C $Y $C (@id Cat_cat $C))))
        (Op_cat
          (@Sigma_cat
            (Op_cat $C)
            (@hom_con $C $X $C (@id Cat_cat $C))))
        (@slice_base_change_func $C $PB $X $Y $u)
        (@sigma_map_obj
          (Op_cat $C)
          (@hom_con $C $X $C (@id Cat_cat $C))
          (@hom_con $C $Y $C (@id Cat_cat $C))
          (@hom_con_int_postcomp_func
            $C $C (@id Cat_cat $C) $X $Y $u)
          (@slice_base_change_obj $C $PB $X $Y $u $b'))
        $b
        (@slice_base_change_phi $C $PB $X $Y $u $b' $b $h))
  ↪ @comp_fapp0
      (@Sigma_cat
        (Op_cat $C)
        (@hom_con $C $X $C (@id Cat_cat $C)))
      (@slice_base_change_obj $C $PB $X $Y $u $b)
      (@slice_base_change_obj $C $PB $X $Y $u $b')
      $a
      $k
      (@fapp1_fapp0
        (Op_cat
          (@Sigma_cat
            (Op_cat $C)
            (@hom_con $C $Y $C (@id Cat_cat $C))))
        (Op_cat
          (@Sigma_cat
            (Op_cat $C)
            (@hom_con $C $X $C (@id Cat_cat $C))))
      (@slice_base_change_func $C $PB $X $Y $u)
        $b' $b $h);

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
  action on higher Hom arrows. They are not independent adjunction data:
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

// Structure arrow of Σ_f(a), whose generic Sigma action preserves the domain.
symbol slice_sigma_structure_arrow
  [C : Cat]
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C X)))
  : τ (Hom C (@slice_object_domain C X a) Y)
≔ @slice_object_arrow C Y (@slice_sigma_obj C X Y f a);

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

// Second projection π₂:P→domain(g), directly projected from the counit.
symbol pullback_snd
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (g : τ (Obj (@Slice_cat C Y)))
  : τ (Hom C
      (@pullback_domain C PB X Y f g)
      (@slice_object_domain C Y g))
≔ @slice_arrow_underlying
    C Y
    (@slice_sigma_obj C X Y f
      (@pullback_slice_obj C PB X Y f g))
    g
    (@pullback_counit_slice_arrow C PB X Y f g);

// Source g ∘ π₂ of the directed counit square.
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

// Target f ∘ π₁, selected by generic Sigma-map structure action.
symbol pullback_square_readable_target
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  (g : τ (Obj (@Slice_cat C Y)))
  : τ (Obj (Hom_cat C (@pullback_domain C PB X Y f g) Y))
≔ @slice_sigma_structure_arrow
    C X Y f (@pullback_slice_obj C PB X Y f g);

// Directed square, directly projected from the counit slice arrow.
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
  ≔ @slice_arrow_cell
    C Y
    (@slice_sigma_obj C X Y f
      (@pullback_slice_obj C PB X Y f g))
    g
    (@pullback_counit_slice_arrow C PB X Y f g);

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

// Whole universal lift, retaining action on higher Hom arrows.
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
