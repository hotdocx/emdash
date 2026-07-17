/*
  One-category ordinary-isomorphism lift.

  Strict ordinary inverse equations encode as recursive omega-equivalence
  cells. A packaged OneCat can therefore decode ordinary isomorphism evidence
  through canonical omega univalence, and decoder-after-encoder is
  propositional. Recursive cells now also construct a directed comparison
  between the separately selected left and right omega inverses, which OneCat
  hom discreteness decodes to a path. The decoded recursive laws and that path
  now reconstruct ordinary isomorphism evidence from arbitrary OneCat omega
  evidence. OneCat hom discreteness also makes the two inverse-law proof fields
  proposition-valued, so the existing nested-Sigma path view proves evidence
  reconstruction and the reverse round trip. Both round trips now derive the
  OneCat-scoped CatIsoUnivalence capability and its named path/isomorphism
  TypeEquiv without using the frozen arbitrary-category decoder.
*/

require open emdash.emdash3_2;

assert [C : Cat]
  [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y)) ⊢
  @iso_evidence_omega_equiv C x y i
  : τ (OmegaEquiv C x y);

assert [C : Cat]
  [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y)) ⊢
  @omega_equiv_to C x y (@iso_evidence_omega_equiv C x y i)
  ≡ @iso_evidence_to C x y i;

assert [C : Cat]
  [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y)) ⊢
  @omega_equiv_left_inv C x y (@iso_evidence_omega_equiv C x y i)
  ≡ @iso_evidence_from C x y i;

assert [C : Cat]
  [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y)) ⊢
  @omega_equiv_right_inv C x y (@iso_evidence_omega_equiv C x y i)
  ≡ @iso_evidence_from C x y i;

assert [C : Cat]
  [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y)) ⊢
  @omega_equiv_left_cell C x y (@iso_evidence_omega_equiv C x y i)
  ≡ @object_path_equiv_D0
      (Hom_cat C x x)
      (@comp_fapp0 C x y x
        (@iso_evidence_from C x y i)
        (@iso_evidence_to C x y i))
      (@id C x)
      (@iso_evidence_left C x y i);

assert [C : Cat]
  [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y)) ⊢
  @omega_equiv_right_cell C x y (@iso_evidence_omega_equiv C x y i)
  ≡ @object_path_equiv_D0
      (Hom_cat C y y)
      (@comp_fapp0 C y x y
        (@iso_evidence_to C x y i)
        (@iso_evidence_from C x y i))
      (@id C y)
      (@iso_evidence_right C x y i);

// The reflexive comparison is proof-time only, not a runtime package fold.
assert [C : Cat] (x : τ (Obj C)) ⊢
  eq_refl (@omega_equiv_refl C x)
  : τ (@=
      (OmegaEquiv C x x)
      (@iso_evidence_omega_equiv C x x (@iso_evidence_refl C x))
      (@omega_equiv_refl C x));

assert (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (i : τ (IsoEvidence
      (@ncat_carrier (cat_succ cat_zero) X)
      x
      y)) ⊢
  @one_cat_iso_path X x y i
  : τ (@= (Obj (@ncat_carrier (cat_succ cat_zero) X)) x y);

assert (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (p : τ (@= (Obj (@ncat_carrier (cat_succ cat_zero) X)) x y)) ⊢
  @one_cat_iso_path_idtoiso X x y p
  : τ (@=
      (@= (Obj (@ncat_carrier (cat_succ cat_zero) X)) x y)
      (@one_cat_iso_path X x y
        (@idtoiso_cat
          (@ncat_carrier (cat_succ cat_zero) X)
          x
          y
          p))
      p);

assertnot [C : Cat] (x : τ (Obj C)) ⊢
  @iso_evidence_omega_equiv C x x (@iso_evidence_refl C x)
  ≡ @omega_equiv_refl C x;

assertnot (X : τ OneCat)
  (x : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))) ⊢
  @one_cat_iso_path X x x
    (@iso_evidence_refl
      (@ncat_carrier (cat_succ cat_zero) X)
      x)
  ≡ eq_refl x;

assertnot (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (i : τ (IsoEvidence
      (@ncat_carrier (cat_succ cat_zero) X)
      x
      y)) ⊢
  @one_cat_iso_path X x y i
  ≡ @iso_evidence_path
      (@ncat_carrier (cat_succ cat_zero) X)
      x
      y
      i;

assertnot (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (i : τ (IsoEvidence
      (@ncat_carrier (cat_succ cat_zero) X)
      x
      y)) ⊢
  @idtoiso_cat
    (@ncat_carrier (cat_succ cat_zero) X)
    x
    y
    (@one_cat_iso_path X x y i)
  ≡ i;

// The two recursive cells supply the directed inverse comparison.
assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @omega_equiv_along_left_cell_to_D0 C x y f u
  : τ (Hom
      (Hom_cat C x x)
      (@comp_fapp0 C x y x
        (@omega_equiv_along_left_inv_D0 C x y f u)
        f)
      (@id C x));

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @omega_equiv_along_right_cell_from_D0 C x y f u
  : τ (Hom
      (Hom_cat C y y)
      (@id C y)
      (@comp_fapp0 C y x y
        f
        (@omega_equiv_along_right_inv_D0 C x y f u)));

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @omega_equiv_along_inverse_assoc_path_D0 C x y f u
  : τ (@=
      (Hom C y x)
      (@hom_postcomp_fapp0
        C C (@id Cat_cat C)
        y y x
        (@omega_equiv_along_left_inv_D0 C x y f u)
        (@comp_fapp0 C y x y
          f
          (@omega_equiv_along_right_inv_D0 C x y f u)))
      (@hom_precomp_along_fapp0
        C C (@id Cat_cat C)
        x y x
        (@omega_equiv_along_right_inv_D0 C x y f u)
        (@comp_fapp0 C x y x
          (@omega_equiv_along_left_inv_D0 C x y f u)
          f)));

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @omega_equiv_along_left_to_right_D0 C x y f u
  : τ (Hom
      (Hom_cat C y x)
      (@omega_equiv_along_left_inv_D0 C x y f u)
      (@omega_equiv_along_right_inv_D0 C x y f u));

// Canonical reflexivity reduces through generic whiskering and unit owners.
assert [C : Cat] (x : τ (Obj C)) ⊢
  @omega_equiv_along_left_to_right_D0
    C x x (@id C x) (@omega_equiv_along_refl_D0 C x)
  ≡ @id (Hom_cat C x x) (@id C x);

assert (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (e : τ (OmegaEquiv
      (@ncat_carrier (cat_succ cat_zero) X)
      x
      y)) ⊢
  @one_cat_omega_inverse_path X x y e
  : τ (@=
      (Hom (@ncat_carrier (cat_succ cat_zero) X) y x)
      (@omega_equiv_left_inv
        (@ncat_carrier (cat_succ cat_zero) X) x y e)
      (@omega_equiv_right_inv
        (@ncat_carrier (cat_succ cat_zero) X) x y e));

// The construction supplies evidence; it does not globally identify its inputs.
assertnot [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @omega_equiv_along_left_inv_D0 C x y f u
  ≡ @omega_equiv_along_right_inv_D0 C x y f u;

assertnot [C : Cat]
  [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y)) ⊢
  @omega_equiv_along_left_to_right_D0
    C x y
    (@iso_evidence_to C x y i)
    (@iso_evidence_omega_along_D0 C x y i)
  ≡ @id (Hom_cat C y x) (@iso_evidence_from C x y i);

assertnot (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (i : τ (IsoEvidence
      (@ncat_carrier (cat_succ cat_zero) X)
      x
      y)) ⊢
  @one_cat_omega_inverse_path
    X x y
    (@iso_evidence_omega_equiv
      (@ncat_carrier (cat_succ cat_zero) X)
      x
      y
      i)
  ≡ eq_refl
      (@iso_evidence_from
        (@ncat_carrier (cat_succ cat_zero) X)
        x
        y
        i);

// Recursive omega cells decode to ordinary inverse laws.
assert [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y)) ⊢
  @omega_equiv_left_law C x y e
  : τ (@=
      (Hom C x x)
      (@comp_fapp0 C x y x
        (@omega_equiv_left_inv C x y e)
        (@omega_equiv_to C x y e))
      (@id C x));

assert [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y)) ⊢
  @omega_equiv_right_law C x y e
  : τ (@=
      (Hom C y y)
      (@comp_fapp0 C y x y
        (@omega_equiv_to C x y e)
        (@omega_equiv_right_inv C x y e))
      (@id C y));

// The inverse path transports the right law to the selected left inverse.
assert (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (e : τ (OmegaEquiv
      (@ncat_carrier (cat_succ cat_zero) X) x y)) ⊢
  @one_cat_omega_right_law_at_left X x y e
  : τ (@=
      (Hom (@ncat_carrier (cat_succ cat_zero) X) y y)
      (@comp_fapp0
        (@ncat_carrier (cat_succ cat_zero) X)
        y x y
        (@omega_equiv_to
          (@ncat_carrier (cat_succ cat_zero) X) x y e)
        (@omega_equiv_left_inv
          (@ncat_carrier (cat_succ cat_zero) X) x y e))
      (@id (@ncat_carrier (cat_succ cat_zero) X) y));

assert (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (e : τ (OmegaEquiv
      (@ncat_carrier (cat_succ cat_zero) X) x y)) ⊢
  @one_cat_omega_iso_evidence X x y e
  : τ (IsoEvidence
      (@ncat_carrier (cat_succ cat_zero) X) x y);

assert (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (e : τ (OmegaEquiv
      (@ncat_carrier (cat_succ cat_zero) X) x y)) ⊢
  @iso_evidence_to
    (@ncat_carrier (cat_succ cat_zero) X) x y
    (@one_cat_omega_iso_evidence X x y e)
  ≡ @omega_equiv_to
      (@ncat_carrier (cat_succ cat_zero) X) x y e;

assert (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (e : τ (OmegaEquiv
      (@ncat_carrier (cat_succ cat_zero) X) x y)) ⊢
  @iso_evidence_from
    (@ncat_carrier (cat_succ cat_zero) X) x y
    (@one_cat_omega_iso_evidence X x y e)
  ≡ @omega_equiv_left_inv
      (@ncat_carrier (cat_succ cat_zero) X) x y e;

assert (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (e : τ (OmegaEquiv
      (@ncat_carrier (cat_succ cat_zero) X) x y)) ⊢
  @iso_evidence_left
    (@ncat_carrier (cat_succ cat_zero) X) x y
    (@one_cat_omega_iso_evidence X x y e)
  ≡ @omega_equiv_left_law
      (@ncat_carrier (cat_succ cat_zero) X) x y e;

assert (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (e : τ (OmegaEquiv
      (@ncat_carrier (cat_succ cat_zero) X) x y)) ⊢
  @iso_evidence_right
    (@ncat_carrier (cat_succ cat_zero) X) x y
    (@one_cat_omega_iso_evidence X x y e)
  ≡ @one_cat_omega_right_law_at_left X x y e;

// Reconstruction preserves proof provenance rather than adding package eta.
assertnot (X : τ OneCat)
  (x : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))) ⊢
  @one_cat_omega_right_law_at_left
    X x x
    (@omega_equiv_refl
      (@ncat_carrier (cat_succ cat_zero) X) x)
  ≡ eq_refl (@id (@ncat_carrier (cat_succ cat_zero) X) x);

assertnot (X : τ OneCat)
  (x : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))) ⊢
  @one_cat_omega_iso_evidence
    X x x
    (@omega_equiv_refl
      (@ncat_carrier (cat_succ cat_zero) X) x)
  ≡ @iso_evidence_refl
      (@ncat_carrier (cat_succ cat_zero) X) x;

assertnot (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (e : τ (OmegaEquiv
      (@ncat_carrier (cat_succ cat_zero) X) x y)) ⊢
  @iso_evidence_omega_equiv
    (@ncat_carrier (cat_succ cat_zero) X) x y
    (@one_cat_omega_iso_evidence X x y e)
  ≡ e;

// Ordinary evidence reconstructs propositionally after its recursive lift.
assert (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (i : τ (IsoEvidence
      (@ncat_carrier (cat_succ cat_zero) X) x y)) ⊢
  @one_cat_omega_iso_lift_retract X x y i
  : τ (@=
      (IsoEvidence (@ncat_carrier (cat_succ cat_zero) X) x y)
      (@one_cat_omega_iso_evidence
        X x y
        (@iso_evidence_omega_equiv
          (@ncat_carrier (cat_succ cat_zero) X) x y i))
      i);

assert (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (p : τ (@= (Obj (@ncat_carrier (cat_succ cat_zero) X)) x y)) ⊢
  @one_cat_omega_iso_evidence_idtoequiv X x y p
  : τ (@=
      (IsoEvidence (@ncat_carrier (cat_succ cat_zero) X) x y)
      (@one_cat_omega_iso_evidence
        X x y
        (@idtoequiv_cat
          (@ncat_carrier (cat_succ cat_zero) X) x y p))
      (@idtoiso_cat
        (@ncat_carrier (cat_succ cat_zero) X) x y p));

// This is the encoder-after-decoder round trip missing from the first slice.
assert (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (i : τ (IsoEvidence
      (@ncat_carrier (cat_succ cat_zero) X) x y)) ⊢
  @one_cat_idtoiso_iso_path X x y i
  : τ (@=
      (IsoEvidence (@ncat_carrier (cat_succ cat_zero) X) x y)
      (@idtoiso_cat
        (@ncat_carrier (cat_succ cat_zero) X)
        x
        y
        (@one_cat_iso_path X x y i))
      i);

// Both round trips derive a scoped capability, not a new global assumption.
assert (X : τ OneCat) ⊢
  one_cat_iso_univalence_by_decoder X
  : τ (OneCatIsoUnivalenceByDecoder X);

assert (X : τ OneCat) ⊢
  one_cat_iso_univalence X
  : τ (CatIsoUnivalence
      (@ncat_carrier (cat_succ cat_zero) X));

assert (X : τ OneCat)
  (x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))) ⊢
  @one_cat_iso_type_equiv X x y
  : τ (TypeEquiv
      (@= (Obj (@ncat_carrier (cat_succ cat_zero) X)) x y)
      (IsoEvidence (@ncat_carrier (cat_succ cat_zero) X) x y));

// The named TypeEquiv selects the intended encoder, decoder, and right law.
assert (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (p : τ (@= (Obj (@ncat_carrier (cat_succ cat_zero) X)) x y)) ⊢
  @type_equiv_to
    (@= (Obj (@ncat_carrier (cat_succ cat_zero) X)) x y)
    (IsoEvidence (@ncat_carrier (cat_succ cat_zero) X) x y)
    (@one_cat_iso_type_equiv X x y)
    p
  ≡ @idtoiso_cat
      (@ncat_carrier (cat_succ cat_zero) X) x y p;

assert (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (i : τ (IsoEvidence
      (@ncat_carrier (cat_succ cat_zero) X) x y)) ⊢
  @type_equiv_from
    (@= (Obj (@ncat_carrier (cat_succ cat_zero) X)) x y)
    (IsoEvidence (@ncat_carrier (cat_succ cat_zero) X) x y)
    (@one_cat_iso_type_equiv X x y)
    i
  ≡ @one_cat_iso_path X x y i;

assert (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (i : τ (IsoEvidence
      (@ncat_carrier (cat_succ cat_zero) X) x y)) ⊢
  @type_equiv_right
    (@= (Obj (@ncat_carrier (cat_succ cat_zero) X)) x y)
    (IsoEvidence (@ncat_carrier (cat_succ cat_zero) X) x y)
    (@one_cat_iso_type_equiv X x y)
    i
  ≡ @one_cat_idtoiso_iso_path X x y i;

// Contractible-fibre proof provenance remains distinct on the open left law.
assertnot (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (p : τ (@= (Obj (@ncat_carrier (cat_succ cat_zero) X)) x y)) ⊢
  @type_equiv_left
    (@= (Obj (@ncat_carrier (cat_succ cat_zero) X)) x y)
    (IsoEvidence (@ncat_carrier (cat_succ cat_zero) X) x y)
    (@one_cat_iso_type_equiv X x y)
    p
  ≡ @one_cat_iso_path_idtoiso X x y p;

// The generic ordinary-iso eliminator now consumes only the scoped inhabitant.
assert (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (i : τ (IsoEvidence
      (@ncat_carrier (cat_succ cat_zero) X) x y)) ⊢
  @isotoid_cat
    (@ncat_carrier (cat_succ cat_zero) X)
    (@one_cat_iso_univalence X)
    x
    y
    i
  ≡ @one_cat_iso_path X x y i;
