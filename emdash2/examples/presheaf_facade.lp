/*
  Reviewer-facing PSSS-01 example: Cat-valued presheaves are a visible
  category facade over directed Cat-valued families on the opposite base.

  Runtime object/hom observations reuse Catd.  The category-head comparison
  itself is proof-time only, and restriction reuses Catd pullback along the
  opposite functor.
*/

require open emdash.emdash3_2_presheaves;

// Abstract-base proof-time comparison with the underlying Catd presentation.
assert [K : Cat] ⊢
  @eq_refl Cat_grpd (@Psh_cat K)
  : τ (@= Cat_grpd
      (@Psh_cat K)
      (@Catd_cat (Op_cat K)));

// The facade remains a distinct runtime normal form.
assertnot [K : Cat] ⊢
  @Psh_cat K
  ≡ @Catd_cat (Op_cat K);

// Presheaf objects and maps expose the existing displayed-family hierarchy.
assert [K : Cat] ⊢
  Psh K
  ≡ Obj (@Catd_cat (Op_cat K));

assert [K : Cat] (P Q : τ (Psh K)) ⊢
  Hom_cat (@Psh_cat K) P Q
  ≡ @Functord_cat (Op_cat K) P Q;

// Restriction along F : A -> B is precomposition along F^op.
assert [A B : Cat]
  (F : τ (Functor A B))
  (P : τ (Psh B)) ⊢
  @fapp0
    (@Psh_cat B)
    (@Psh_cat A)
    (@Psh_pullback_func A B F)
    P
  ≡ @Pullback_catd
      (Op_cat A)
      (Op_cat B)
      P
      (@Op_func A B F);

// Restriction on maps remains the generic action of that same functor.
assert [A B : Cat]
  (F : τ (Functor A B))
  (P Q : τ (Psh B))
  (eta : τ (@Functord (Op_cat B) P Q)) ⊢
  @fapp1_fapp0
    (@Psh_cat B)
    (@Psh_cat A)
    (@Psh_pullback_func A B F)
    P Q eta
  : τ (@Functord
      (Op_cat A)
      (@Pullback_catd (Op_cat A) (Op_cat B) P (@Op_func A B F))
      (@Pullback_catd (Op_cat A) (Op_cat B) Q (@Op_func A B F)));

// Conventional slices are transparent opposite-Sigma consumers. This is the
// generic slice-arrow constructor, not a pullback-specific cone record.
assert [K : Cat]
  (U : τ (Obj K))
  (q r : τ (Obj (@Slice_cat K U)))
  (p : τ (Hom K
    (@slice_object_domain K U q)
    (@slice_object_domain K U r)))
  (alpha : τ (Hom
    (Hom_cat K (@slice_object_domain K U q) U)
    (@comp_fapp0 K
      (@slice_object_domain K U q)
      (@slice_object_domain K U r)
      U
      (@slice_object_arrow K U r)
      p)
    (@slice_object_arrow K U q))) ⊢
  @slice_arrow_underlying K U q r
    (@slice_arrow_intro K U q r p alpha)
  ≡ p;

assert [K : Cat]
  (U : τ (Obj K))
  (q r : τ (Obj (@Slice_cat K U)))
  (p : τ (Hom K
    (@slice_object_domain K U q)
    (@slice_object_domain K U r)))
  (alpha : τ (Hom
    (Hom_cat K (@slice_object_domain K U q) U)
    (@comp_fapp0 K
      (@slice_object_domain K U q)
      (@slice_object_domain K U r)
      U
      (@slice_object_arrow K U r)
      p)
    (@slice_object_arrow K U q))) ⊢
  @slice_arrow_cell K U q r
    (@slice_arrow_intro K U q r p alpha)
  ≡ alpha;

// Opposite-category composition reverses first, then the generic Sigma law
// composes the ambient arrows in the conventional slice direction.
assert [K : Cat]
  (U : τ (Obj K))
  (q r s : τ (Obj (@Slice_cat K U)))
  (p : τ (Hom K
    (@slice_object_domain K U q)
    (@slice_object_domain K U r)))
  (w : τ (Hom K
    (@slice_object_domain K U r)
    (@slice_object_domain K U s)))
  (alpha : τ (Hom
    (Hom_cat K (@slice_object_domain K U q) U)
    (@comp_fapp0 K
      (@slice_object_domain K U q)
      (@slice_object_domain K U r)
      U
      (@slice_object_arrow K U r)
      p)
    (@slice_object_arrow K U q)))
  (beta : τ (Hom
    (Hom_cat K (@slice_object_domain K U r) U)
    (@comp_fapp0 K
      (@slice_object_domain K U r)
      (@slice_object_domain K U s)
      U
      (@slice_object_arrow K U s)
      w)
    (@slice_object_arrow K U r))) ⊢
  @slice_arrow_underlying K U q s
    (@comp_fapp0
      (@Slice_cat K U) q r s
      (@slice_arrow_intro K U r s w beta)
      (@slice_arrow_intro K U q r p alpha))
  ≡ @comp_fapp0 K
      (@slice_object_domain K U q)
      (@slice_object_domain K U r)
      (@slice_object_domain K U s)
      w p;

// Arbitrary slice arrows do not eta-expand to the generic constructor.
assertnot [K : Cat]
  (U : τ (Obj K))
  (q r : τ (Obj (@Slice_cat K U)))
  (h : τ (Hom (@Slice_cat K U) q r)) ⊢
  @slice_arrow_intro K U q r
    (@slice_arrow_underlying K U q r h)
    (@slice_arrow_cell K U q r h)
  ≡ h;
