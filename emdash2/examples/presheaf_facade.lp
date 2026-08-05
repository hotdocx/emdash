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
