/*
  Emdash v3.2: selected coherent dependent products in slices.

  A PullbackStructure(C) already supplies the whole contravariant slice family
  u*:C/Y→C/X and the adjunction Σᵤ⊣u*. A DependentProductStructure(C,PB)
  supplies a third whole slice family, covariant in C, whose action at
  u:X→Y is Πᵤ:C/X→C/Y, together with the existing adjunction u*⊣Πᵤ.

  Generic unit_adj_transf and counit_adj_transf remain the actual whole
  transformations. Their selected tapp1 observations have stable γᶜ/φᵃ result
  heads because opposite-slice normalization erases the generic rectangle
  discriminator. The two exact post-opposite rectangles and their component
  joins are instances of the existing adjunction laws, not a second
  adjunction theory.

  Generic composed-functor object beta and functor identity remain the sole
  owners of composite points and identity action. The generic
  Adjunction_hom_prof_comparison remains the whole semantic Hom-equivalence
  owner. Beck--Chevalley, Frobenius, slice exponentials, comparison with the
  general Pi-along-functor proposal, and a thin LCCC package remain later
  layers.
*/

require open emdash.emdash3_2_pullbacks;

// Selected dependent products indexed by the already chosen pullbacks.
injective symbol DependentProductStructure
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  : Grpd;

// Whole covariant slice family: X ↦ C/X and u ↦ Πᵤ.
injective symbol SliceDependentProduct_catd
  [C : Cat]
  [PB : τ (@PullbackStructure C)]
  (DP : τ (@DependentProductStructure C PB))
  : τ (Catd C);

// Exact selected fibre.
rule @fapp0 _ Cat_cat
      (@SliceDependentProduct_catd $C _ _)
      $X
  ↪ @Slice_cat $C $X;

// Stable whole dependent-product action Πᵤ:C/X→C/Y.
injective symbol slice_dependent_product_func
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  [X Y : τ (Obj C)]
  (u : τ (Hom C X Y))
  : τ (Functor (@Slice_cat C X) (@Slice_cat C Y));

rule @fapp1_fapp0 _ Cat_cat
      (@SliceDependentProduct_catd $C $PB $DP)
      $X $Y $u
  ↪ @slice_dependent_product_func $C $PB $DP $X $Y $u;

// Stable object action Πᵤ(b).
injective symbol slice_dependent_product_obj
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  [X Y : τ (Obj C)]
  (u : τ (Hom C X Y))
  (b : τ (Obj (@Slice_cat C X)))
  : τ (Obj (@Slice_cat C Y));

rule @fapp0 _ _
      (@slice_dependent_product_func $C $PB $DP $X $Y $u)
      $b
  ↪ @slice_dependent_product_obj $C $PB $DP $X $Y $u $b;

// Existing indexed adjunction u* ⊣ Πᵤ.
injective symbol slice_dependent_product_adjunction
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  [X Y : τ (Obj C)]
  (u : τ (Hom C X Y))
  : τ (@Adjunction
      (@Slice_cat C Y)
      (@Slice_cat C X)
      (@slice_base_change_func C PB X Y u)
      (@slice_dependent_product_func C PB DP X Y u));

// Actual whole unit id_(C/Y) ⇒ Πᵤ u*, transparently reusing Adjunction.
symbol slice_dependent_product_unit_transf
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  [X Y : τ (Obj C)]
  (u : τ (Hom C X Y))
  : τ (Transf
      (@id_func (@Slice_cat C Y))
      (@comp_cat_fapp0
        (@Slice_cat C Y)
        (@Slice_cat C X)
        (@Slice_cat C Y)
        (@slice_dependent_product_func C PB DP X Y u)
        (@slice_base_change_func C PB X Y u)))
≔ @unit_adj_transf
    (@Slice_cat C Y) (@Slice_cat C X)
    (@slice_base_change_func C PB X Y u)
    (@slice_dependent_product_func C PB DP X Y u)
    (@slice_dependent_product_adjunction C PB DP X Y u);

// Actual whole counit u*Πᵤ ⇒ id_(C/X), transparently reusing Adjunction.
symbol slice_dependent_product_counit_transf
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  [X Y : τ (Obj C)]
  (u : τ (Hom C X Y))
  : τ (Transf
      (@comp_cat_fapp0
        (@Slice_cat C X)
        (@Slice_cat C Y)
        (@Slice_cat C X)
        (@slice_base_change_func C PB X Y u)
        (@slice_dependent_product_func C PB DP X Y u))
      (@id_func (@Slice_cat C X)))
≔ @counit_adj_transf
    (@Slice_cat C Y) (@Slice_cat C X)
    (@slice_base_change_func C PB X Y u)
    (@slice_dependent_product_func C PB DP X Y u)
    (@slice_dependent_product_adjunction C PB DP X Y u);

// Unit component ηΠᵤ(a):a→Πᵤ(u*a).
symbol slice_dependent_product_unit
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  [X Y : τ (Obj C)]
  (u : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C Y)))
  : τ (Hom
      (@Slice_cat C Y)
      a
      (@slice_dependent_product_obj C PB DP X Y u
        (@slice_base_change_obj C PB X Y u a)))
≔ @tapp0_fapp0
    (@Slice_cat C Y) (@Slice_cat C Y)
    _ _ a
    (@slice_dependent_product_unit_transf C PB DP X Y u);

// Counit component εΠᵤ(b):u*(Πᵤb)→b.
symbol slice_dependent_product_counit
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  [X Y : τ (Obj C)]
  (u : τ (Hom C X Y))
  (b : τ (Obj (@Slice_cat C X)))
  : τ (Hom
      (@Slice_cat C X)
      (@slice_base_change_obj C PB X Y u
        (@slice_dependent_product_obj C PB DP X Y u b))
      b)
≔ @tapp0_fapp0
    (@Slice_cat C X) (@Slice_cat C X)
    _ _ b
    (@slice_dependent_product_counit_transf C PB DP X Y u);

/*
  Stable Došen off-diagonal observations.

  These are the canonical result heads of the generic unit/counit tapp1
  operations. They are not independent unit/counit data.
*/
injective symbol slice_dependent_product_gamma
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  [X Y : τ (Obj C)]
  (u : τ (Hom C X Y))
  [a a' : τ (Obj (@Slice_cat C Y))]
  (k : τ (Hom (@Slice_cat C Y) a a'))
  : τ (Hom
      (@Slice_cat C Y)
      a
      (@slice_dependent_product_obj C PB DP X Y u
        (@slice_base_change_obj C PB X Y u a')));

injective symbol slice_dependent_product_phi
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  [X Y : τ (Obj C)]
  (u : τ (Hom C X Y))
  [b' b : τ (Obj (@Slice_cat C X))]
  (h : τ (Hom (@Slice_cat C X) b' b))
  : τ (Hom
      (@Slice_cat C X)
      (@slice_base_change_obj C PB X Y u
        (@slice_dependent_product_obj C PB DP X Y u b'))
      b);

rule @tapp1_fapp0 _ _ _ _ $a $a'
      (@unit_adj_transf _ _ _ _
        (@slice_dependent_product_adjunction $C $PB $DP $X $Y $u))
      $k
  ↪ @slice_dependent_product_gamma
      $C $PB $DP $X $Y $u $a $a' $k;

rule @tapp1_fapp0 _ _ _ _ $b' $b
      (@counit_adj_transf _ _ _ _
        (@slice_dependent_product_adjunction $C $PB $DP $X $Y $u))
      $h
  ↪ @slice_dependent_product_phi
      $C $PB $DP $X $Y $u $b' $b $h;

// Identity boundaries recover the ordinary unit and counit components.
rule @slice_dependent_product_gamma
      $C $PB $DP $X $Y $u $a $a (@id _ $a)
  ↪ @slice_dependent_product_unit $C $PB $DP $X $Y $u $a;

rule @slice_dependent_product_phi
      $C $PB $DP $X $Y $u $b $b (@id _ $b)
  ↪ @slice_dependent_product_counit $C $PB $DP $X $Y $u $b;

/*
  Canonical post-opposite Došen rectangles.

  Readable Slice_cat categories and composites have already normalized to the
  restriction-oriented Sigma totals and reversed arrow order. The exact raw
  categories and endpoints below are measured subject-reduction guards.
*/

// φΠᵃ(h) ∘ u*(γΠᶜ(k)) → h ∘ u*(k).
// lhs-audit: keep 1,2,3,4 -- raw slice and endpoint guards retain X and Y.
rule @comp_fapp0
      (@Sigma_cat
        (Op_cat $C)
        (@hom_con $C $X $C (@id Cat_cat $C)))
      $b
      (@slice_base_change_obj $C $PB $X $Y $u
        (@slice_dependent_product_obj $C $PB $DP $X $Y $u
          (@slice_base_change_obj $C $PB $X $Y $u $a')))
      (@slice_base_change_obj $C $PB $X $Y $u $a)
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
        $a
        (@slice_dependent_product_obj $C $PB $DP $X $Y $u
          (@slice_base_change_obj $C $PB $X $Y $u $a'))
        (@slice_dependent_product_gamma
          $C $PB $DP $X $Y $u $a $a' $k))
      (@slice_dependent_product_phi
        $C $PB $DP $X $Y $u
        (@slice_base_change_obj $C $PB $X $Y $u $a') $b $h)
  ↪ @comp_fapp0
      (@Sigma_cat
        (Op_cat $C)
        (@hom_con $C $X $C (@id Cat_cat $C)))
      $b
      (@slice_base_change_obj $C $PB $X $Y $u $a')
      (@slice_base_change_obj $C $PB $X $Y $u $a)
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
        $a $a' $k)
      $h;

// Πᵤ(φΠᵃ(h)) ∘ γΠᶜ(k) → Πᵤ(h) ∘ k.
// lhs-audit: keep 1,2,3,4 -- raw slice and endpoint guards retain X and Y.
rule @comp_fapp0
      (@Sigma_cat
        (Op_cat $C)
        (@hom_con $C $Y $C (@id Cat_cat $C)))
      (@slice_dependent_product_obj $C $PB $DP $X $Y $u $b)
      (@slice_dependent_product_obj $C $PB $DP $X $Y $u
        (@slice_base_change_obj $C $PB $X $Y $u
          (@slice_dependent_product_obj $C $PB $DP $X $Y $u $b')))
      $a
      (@slice_dependent_product_gamma
        $C $PB $DP $X $Y $u
        $a (@slice_dependent_product_obj $C $PB $DP $X $Y $u $b') $k)
      (@fapp1_fapp0
        (Op_cat
          (@Sigma_cat
            (Op_cat $C)
            (@hom_con $C $X $C (@id Cat_cat $C))))
        (Op_cat
          (@Sigma_cat
            (Op_cat $C)
            (@hom_con $C $Y $C (@id Cat_cat $C))))
        (@slice_dependent_product_func $C $PB $DP $X $Y $u)
        (@slice_base_change_obj $C $PB $X $Y $u
          (@slice_dependent_product_obj $C $PB $DP $X $Y $u $b'))
        $b
        (@slice_dependent_product_phi
          $C $PB $DP $X $Y $u $b' $b $h))
  ↪ @comp_fapp0
      (@Sigma_cat
        (Op_cat $C)
        (@hom_con $C $Y $C (@id Cat_cat $C)))
      (@slice_dependent_product_obj $C $PB $DP $X $Y $u $b)
      (@slice_dependent_product_obj $C $PB $DP $X $Y $u $b')
      $a
      $k
      (@fapp1_fapp0
        (Op_cat
          (@Sigma_cat
            (Op_cat $C)
            (@hom_con $C $X $C (@id Cat_cat $C))))
        (Op_cat
          (@Sigma_cat
            (Op_cat $C)
            (@hom_con $C $Y $C (@id Cat_cat $C))))
        (@slice_dependent_product_func $C $PB $DP $X $Y $u)
        $b' $b $h);

// Canonical F-side component triangle after identity tapp1 projections.
// lhs-audit: keep 1,2,3,4 -- exact raw endpoints retain the slice indices.
rule @comp_fapp0
      (@Sigma_cat
        (Op_cat $C)
        (@hom_con $C $X $C (@id Cat_cat $C)))
      (@slice_base_change_obj $C $PB $X $Y $u $a)
      (@slice_base_change_obj $C $PB $X $Y $u
        (@slice_dependent_product_obj $C $PB $DP $X $Y $u
          (@slice_base_change_obj $C $PB $X $Y $u $a)))
      (@slice_base_change_obj $C $PB $X $Y $u $a)
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
        $a
        (@slice_dependent_product_obj $C $PB $DP $X $Y $u
          (@slice_base_change_obj $C $PB $X $Y $u $a))
        (@tapp0_fapp0 _ _ _ _ $a
          (@unit_adj_transf _ _ _ _
            (@slice_dependent_product_adjunction
              $C $PB $DP $X $Y $u))))
      (@tapp0_fapp0 _ _ _ _
        (@slice_base_change_obj $C $PB $X $Y $u $a)
        (@counit_adj_transf _ _ _ _
          (@slice_dependent_product_adjunction
            $C $PB $DP $X $Y $u)))
  ↪ @id
      (@Sigma_cat
        (Op_cat $C)
        (@hom_con $C $X $C (@id Cat_cat $C)))
      (@slice_base_change_obj $C $PB $X $Y $u $a);

// Canonical G-side component triangle after identity tapp1 projections.
// lhs-audit: keep 1,2,3,4 -- exact raw endpoints retain the slice indices.
rule @comp_fapp0
      (@Sigma_cat
        (Op_cat $C)
        (@hom_con $C $Y $C (@id Cat_cat $C)))
      (@slice_dependent_product_obj $C $PB $DP $X $Y $u $b)
      (@slice_dependent_product_obj $C $PB $DP $X $Y $u
        (@slice_base_change_obj $C $PB $X $Y $u
          (@slice_dependent_product_obj $C $PB $DP $X $Y $u $b)))
      (@slice_dependent_product_obj $C $PB $DP $X $Y $u $b)
      (@tapp0_fapp0 _ _ _ _
        (@slice_dependent_product_obj $C $PB $DP $X $Y $u $b)
        (@unit_adj_transf _ _ _ _
          (@slice_dependent_product_adjunction
            $C $PB $DP $X $Y $u)))
      (@fapp1_fapp0
        (Op_cat
          (@Sigma_cat
            (Op_cat $C)
            (@hom_con $C $X $C (@id Cat_cat $C))))
        (Op_cat
          (@Sigma_cat
            (Op_cat $C)
            (@hom_con $C $Y $C (@id Cat_cat $C))))
        (@slice_dependent_product_func $C $PB $DP $X $Y $u)
        (@slice_base_change_obj $C $PB $X $Y $u
          (@slice_dependent_product_obj $C $PB $DP $X $Y $u $b))
        $b
        (@tapp0_fapp0 _ _ _ _ $b
          (@counit_adj_transf _ _ _ _
            (@slice_dependent_product_adjunction
              $C $PB $DP $X $Y $u))))
  ↪ @id
      (@Sigma_cat
        (Op_cat $C)
        (@hom_con $C $Y $C (@id Cat_cat $C)))
      (@slice_dependent_product_obj $C $PB $DP $X $Y $u $b);

// -------------------------------------------------------------------------------------------------
// Transparent Hom-mate usability and whole semantic comparison
// -------------------------------------------------------------------------------------------------

// Whole semantic transpose: h ↦ Πᵤ(h) ∘ ηΠᵤ(a).
symbol slice_dependent_product_transpose_func
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  [X Y : τ (Obj C)]
  (u : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C Y)))
  (b : τ (Obj (@Slice_cat C X)))
  : τ (Functor
      (Hom_cat
        (@Slice_cat C X)
        (@slice_base_change_obj C PB X Y u a)
        b)
      (Hom_cat
        (@Slice_cat C Y)
        a
        (@slice_dependent_product_obj C PB DP X Y u b)))
≔ @comp_cat_fapp0
    (Hom_cat
      (@Slice_cat C X)
      (@slice_base_change_obj C PB X Y u a)
      b)
    (Hom_cat
      (@Slice_cat C Y)
      (@slice_dependent_product_obj C PB DP X Y u
        (@slice_base_change_obj C PB X Y u a))
      (@slice_dependent_product_obj C PB DP X Y u b))
    (Hom_cat
      (@Slice_cat C Y)
      a
      (@slice_dependent_product_obj C PB DP X Y u b))
    (@hom_precomp_along_func
      (@Slice_cat C Y)
      (@Slice_cat C Y)
      (@id_func (@Slice_cat C Y))
      (@slice_dependent_product_obj C PB DP X Y u b)
      a
      (@slice_dependent_product_obj C PB DP X Y u
        (@slice_base_change_obj C PB X Y u a))
      (@slice_dependent_product_unit C PB DP X Y u a))
    (@fapp1_func
      (@Slice_cat C X)
      (@Slice_cat C Y)
      (@slice_dependent_product_func C PB DP X Y u)
      (@slice_base_change_obj C PB X Y u a)
      b);

// Whole semantic untranspose: k ↦ εΠᵤ(b) ∘ u*(k).
symbol slice_dependent_product_untranspose_func
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  [X Y : τ (Obj C)]
  (u : τ (Hom C X Y))
  (a : τ (Obj (@Slice_cat C Y)))
  (b : τ (Obj (@Slice_cat C X)))
  : τ (Functor
      (Hom_cat
        (@Slice_cat C Y)
        a
        (@slice_dependent_product_obj C PB DP X Y u b))
      (Hom_cat
        (@Slice_cat C X)
        (@slice_base_change_obj C PB X Y u a)
        b))
≔ @comp_cat_fapp0
    (Hom_cat
      (@Slice_cat C Y)
      a
      (@slice_dependent_product_obj C PB DP X Y u b))
    (Hom_cat
      (@Slice_cat C X)
      (@slice_base_change_obj C PB X Y u a)
      (@slice_base_change_obj C PB X Y u
        (@slice_dependent_product_obj C PB DP X Y u b)))
    (Hom_cat
      (@Slice_cat C X)
      (@slice_base_change_obj C PB X Y u a)
      b)
    (@hom_postcomp_func
      (@Slice_cat C X)
      (@Slice_cat C X)
      (@id_func (@Slice_cat C X))
      (@slice_base_change_obj C PB X Y u a)
      (@slice_base_change_obj C PB X Y u
        (@slice_dependent_product_obj C PB DP X Y u b))
      b
      (@slice_dependent_product_counit C PB DP X Y u b))
    (@fapp1_func
      (@Slice_cat C Y)
      (@Slice_cat C X)
      (@slice_base_change_func C PB X Y u)
      a
      (@slice_dependent_product_obj C PB DP X Y u b));

// Point transpose Πᵤ(h) ∘ ηΠᵤ(a).
symbol slice_dependent_product_transpose
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  [X Y : τ (Obj C)]
  (u : τ (Hom C X Y))
  [a : τ (Obj (@Slice_cat C Y))]
  [b : τ (Obj (@Slice_cat C X))]
  (h : τ (Hom
    (@Slice_cat C X)
    (@slice_base_change_obj C PB X Y u a)
    b))
  : τ (Hom
      (@Slice_cat C Y)
      a
      (@slice_dependent_product_obj C PB DP X Y u b))
≔ @fapp0
    (Hom_cat
      (@Slice_cat C X)
      (@slice_base_change_obj C PB X Y u a)
      b)
    (Hom_cat
      (@Slice_cat C Y)
      a
      (@slice_dependent_product_obj C PB DP X Y u b))
    (@slice_dependent_product_transpose_func C PB DP X Y u a b)
    h;

// Point untranspose εΠᵤ(b) ∘ u*(k).
symbol slice_dependent_product_untranspose
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  [X Y : τ (Obj C)]
  (u : τ (Hom C X Y))
  [a : τ (Obj (@Slice_cat C Y))]
  [b : τ (Obj (@Slice_cat C X))]
  (k : τ (Hom
    (@Slice_cat C Y)
    a
    (@slice_dependent_product_obj C PB DP X Y u b)))
  : τ (Hom
      (@Slice_cat C X)
      (@slice_base_change_obj C PB X Y u a)
      b)
≔ @fapp0
    (Hom_cat
      (@Slice_cat C Y)
      a
      (@slice_dependent_product_obj C PB DP X Y u b))
    (Hom_cat
      (@Slice_cat C X)
      (@slice_base_change_obj C PB X Y u a)
      b)
    (@slice_dependent_product_untranspose_func C PB DP X Y u a b)
    k;

// Whole varying-endpoint semantic equivalence, inherited from Adjunction.
symbol slice_dependent_product_hom_prof_comparison
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  [X Y : τ (Obj C)]
  (u : τ (Hom C X Y))
  : τ (ProfComparison
      (@Hom_prof_along
        (@Slice_cat C Y) (@Slice_cat C X) (@Slice_cat C X)
        (@slice_base_change_func C PB X Y u)
        (@id_func (@Slice_cat C X)))
      (@Hom_prof_along
        (@Slice_cat C Y) (@Slice_cat C X) (@Slice_cat C Y)
        (@id_func (@Slice_cat C Y))
        (@slice_dependent_product_func C PB DP X Y u)))
≔ @Adjunction_hom_prof_comparison
    (@Slice_cat C Y) (@Slice_cat C X)
    (@slice_base_change_func C PB X Y u)
    (@slice_dependent_product_func C PB DP X Y u)
    (@slice_dependent_product_adjunction C PB DP X Y u);

// -------------------------------------------------------------------------------------------------
// Thin total capability
// -------------------------------------------------------------------------------------------------

/*
  A category with selected slice dependent products packages the pullback
  structure first and the dependent-product structure indexed by it. This is
  the computational foundation for local cartesian closure. The stronger
  convention-sensitive `LocallyCartesianClosedCategory` name is deferred until
  the selected terminal/finite-limit and derived slice-exponential surfaces are
  assembled.
*/
symbol SliceDependentProducts
  (C : Cat)
  : Grpd
≔ `Σ_ PB : τ (@PullbackStructure C),
    @DependentProductStructure C PB;

// Constructor pairing the already selected pullback and dependent products.
symbol slice_dependent_products_intro
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  (DP : τ (@DependentProductStructure C PB))
  : τ (@SliceDependentProducts C)
≔ @Struct_sigma
    (@PullbackStructure C)
    (λ PB' : τ (@PullbackStructure C),
      @DependentProductStructure C PB')
    PB DP;

// Selected pullback projection.
symbol slice_dependent_products_pullbacks
  [C : Cat]
  (K : τ (@SliceDependentProducts C))
  : τ (@PullbackStructure C)
≔ sigma_Fst K;

// Selected dependent-product projection over the projected pullbacks.
symbol slice_dependent_products_structure
  [C : Cat]
  (K : τ (@SliceDependentProducts C))
  : τ (@DependentProductStructure C
      (@slice_dependent_products_pullbacks C K))
≔ sigma_Snd K;
