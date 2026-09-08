/* NON-LIBRARY contravariant-totalization candidate. The imported Sigma owner
   is still unrepaired. These are local type/projection and constant-family
   controls, not a global coherence proof. Do not register as a library test.
   See docs/TYPESCRIPT_EMDASH_SIGMA_HOM_VARIANCE_DIAGNOSTIC.md. */
require open emdash.audits.total_duality_negative_sections_prototype;

// Total duality preserves the ordinary cartesian product at every dimension.
rule All_cat (Product_cat $A $B)
  ↪ Product_cat (All_cat $A) (All_cat $B);

// H : K^op → Cat. Dualize the fibres and shift the base, then total-dualize
// the total. The final projection lands in K, not Co2(K).
symbol Sigma_con_candidate [K : Cat] (H : τ (Catd (Op_cat K))) : Cat
≔ All_cat (@Sigma_cat (CoAll_cat (Op_cat K)) (@All_catd (Op_cat K) H));

symbol sigma_con_candidate_proj [K : Cat] (H : τ (Catd (Op_cat K)))
  : τ (Functor (@Sigma_con_candidate K H) K)
≔ @All_func
    (@Sigma_cat (CoAll_cat (Op_cat K)) (@All_catd (Op_cat K) H))
    (CoAll_cat (Op_cat K))
    (@Sigma_proj1_func (CoAll_cat (Op_cat K)) (@All_catd (Op_cat K) H));

symbol sigma_con_candidate_obj [K : Cat] (H : τ (Catd (Op_cat K)))
  (k : τ (Obj K)) (h : τ (Obj (@Fibre_cat (Op_cat K) H k)))
  : τ (Obj (@Sigma_con_candidate K H))
≔ @Struct_sigma (Obj (CoAll_cat (Op_cat K)))
    (λ x : τ (Obj (CoAll_cat (Op_cat K))),
      Obj (@Fibre_cat (CoAll_cat (Op_cat K)) (@All_catd (Op_cat K) H) x))
    k h;

// Constant fibres remain C, not C^op. This is a whole-category equation.
assert [K C : Cat] ⊢
  @Sigma_con_candidate K (@Const_catd (Op_cat K) C)
  ≡ Product_cat K C;

assert [K : Cat] (H : τ (Catd (Op_cat K)))
  (k : τ (Obj K)) (h : τ (Obj (@Fibre_cat (Op_cat K) H k))) ⊢
  @fapp0 (@Sigma_con_candidate K H) K (@sigma_con_candidate_proj K H)
    (@sigma_con_candidate_obj K H k h) ≡ k;

// The next whole hom action is retained for arbitrary total objects.
assert [K : Cat] (H : τ (Catd (Op_cat K)))
  (p q : τ (Obj (@Sigma_con_candidate K H))) ⊢
  @fapp1_func (@Sigma_con_candidate K H) K (@sigma_con_candidate_proj K H) p q
  : τ (Functor
      (Hom_cat (@Sigma_con_candidate K H) p q)
      (Hom_cat K
        (@fapp0 (@Sigma_con_candidate K H) K (@sigma_con_candidate_proj K H) p)
        (@fapp0 (@Sigma_con_candidate K H) K (@sigma_con_candidate_proj K H) q)));

// Proposed Sigma-Hom reading using the original dependent Hom family.
symbol sigma_hom_total_dual_view [K : Cat] (E : τ (Catd K))
  (x y : τ (Obj K)) (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y))) : Cat
≔ @Sigma_con_candidate (Hom_cat K x y)
    (@homd_ K E E (@id_funcd K E) x u y v);

assert [C : Cat] (u v : τ (Obj C)) ⊢
  @sigma_hom_total_dual_view Terminal_cat (@Const_catd Terminal_cat C)
    Terminal_obj Terminal_obj u v
  ≡ Product_cat Terminal_cat (Hom_cat C u v);

// This candidate does not select the old flipped-fibre constant reading.
assertnot [C : Cat] (u v : τ (Obj C)) ⊢
  @sigma_hom_total_dual_view Terminal_cat (@Const_catd Terminal_cat C)
    Terminal_obj Terminal_obj u v
  ≡ Product_cat Terminal_cat (Op_cat (Hom_cat C u v));
