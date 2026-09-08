/* NON-LIBRARY owner-position Sigma repair reviewer.
   Run only with scripts/check_sigma_variance_repair.sh, which stages the
   candidate patch in a fresh package. The active kernel is unrepaired.
   These checks reject the known Sigma cast and retain directed higher action;
   they are not a global consistency result or a positive library target. */
require open emdash.emdash3_2;


assert [K : Cat] (E : τ (Catd K)) [x y : τ (Obj K)]
  (u : τ (Obj (Fibre_cat E x))) (v : τ (Obj (Fibre_cat E y))) ⊢
  Hom_cat (@Sigma_cat K E) (Struct_sigma x u) (Struct_sigma y v)
  ≡ All_cat (@Sigma_cat (CoAll_cat (Op_cat (Hom_cat K x y)))
      (@All_catd (Op_cat (Hom_cat K x y))
        (@homd_ K E E (@id_funcd K E) x u y v)));

assert [C : Cat] (u v : τ (Obj C)) ⊢
  Hom_cat (@Sigma_cat Terminal_cat (@Const_catd Terminal_cat C))
    (Struct_sigma Terminal_obj u) (Struct_sigma Terminal_obj v)
  ≡ Product_cat Terminal_cat (Hom_cat C u v);

// Reject the exact first invalid cast of the old empty-type derivation.
assertnot [K : Cat] (E : τ (Catd K)) [x y : τ (Obj K)]
  (u : τ (Obj (Fibre_cat E x))) (v : τ (Obj (Fibre_cat E y))) ⊢
  @id_func (Op_cat (@Sigma_cat (Op_cat (Hom_cat K x y))
    (@homd_ K E E (@id_funcd K E) x u y v)))
  : τ (Functor
      (Hom_cat (@Sigma_cat K E) (Struct_sigma x u) (Struct_sigma y v))
      (Op_cat (@Sigma_cat (Op_cat (Hom_cat K x y))
        (@homd_ K E E (@id_funcd K E) x u y v))));

// Arbitrary directed fibres are not identified with their 1-opposites.
assertnot [C : Cat] (u v : τ (Obj C)) ⊢
  @eq_refl (Obj Cat_cat) (Product_cat Terminal_cat (Hom_cat C u v))
  : τ (@= (Obj Cat_cat)
      (Product_cat Terminal_cat (Hom_cat C u v))
      (Product_cat Terminal_cat (Op_cat (Hom_cat C u v))));


symbol sigma_repair_two_cell [K : Cat] (E : τ (Catd K))
  [x y : τ (Obj K)] (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y)))
  [p q : τ (Hom K x y)]
  (alpha : τ (Obj (Fibre_cat (@homd_ K E E (@id_funcd K E) x u y v) p)))
  (beta : τ (Obj (Fibre_cat (@homd_ K E E (@id_funcd K E) x u y v) q)))
  (kappa : τ (Hom (Hom_cat K x y) p q))
  (gamma : τ (Hom
      (Fibre_cat (@homd_ K E E (@id_funcd K E) x u y v) p) alpha
      (@fapp0
        (Fibre_cat (@homd_ K E E (@id_funcd K E) x u y v) q)
        (Fibre_cat (@homd_ K E E (@id_funcd K E) x u y v) p)
        (@fapp1_fapp0 (Op_cat (Hom_cat K x y)) Cat_cat
          (@homd_ K E E (@id_funcd K E) x u y v) q p kappa) beta)))
  : τ (Hom
      (Hom_cat (@Sigma_cat K E) (Struct_sigma x u) (Struct_sigma y v))
      (Struct_sigma p alpha) (Struct_sigma q beta))
≔ Struct_sigma kappa gamma;

// Recover the original base 2-cell through the existing named projection.
assert [K : Cat] (E : τ (Catd K))
  [x y : τ (Obj K)] (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y))) [p q : τ (Hom K x y)]
  (alpha : τ (Obj (Fibre_cat (@homd_ K E E (@id_funcd K E) x u y v) p)))
  (beta : τ (Obj (Fibre_cat (@homd_ K E E (@id_funcd K E) x u y v) q)))
  (kappa : τ (Hom (Hom_cat K x y) p q))
  (gamma : τ (Hom
      (Fibre_cat (@homd_ K E E (@id_funcd K E) x u y v) p) alpha
      (@fapp0
        (Fibre_cat (@homd_ K E E (@id_funcd K E) x u y v) q)
        (Fibre_cat (@homd_ K E E (@id_funcd K E) x u y v) p)
        (@fapp1_fapp0 (Op_cat (Hom_cat K x y)) Cat_cat
          (@homd_ K E E (@id_funcd K E) x u y v) q p kappa) beta))) ⊢
  @sigma_proj1_hom_fapp1_fapp0 K E x y u v p q alpha beta
    (@sigma_repair_two_cell K E x y u v p q alpha beta kappa gamma)
  ≡ kappa;

// The fibre component is the supplied forward cell, not an inverse.
assert [K : Cat] (E : τ (Catd K))
  [x y : τ (Obj K)] (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y))) [p q : τ (Hom K x y)]
  (alpha : τ (Obj (Fibre_cat (@homd_ K E E (@id_funcd K E) x u y v) p)))
  (beta : τ (Obj (Fibre_cat (@homd_ K E E (@id_funcd K E) x u y v) q)))
  (kappa : τ (Hom (Hom_cat K x y) p q))
  (gamma : τ (Hom
      (Fibre_cat (@homd_ K E E (@id_funcd K E) x u y v) p) alpha
      (@fapp0
        (Fibre_cat (@homd_ K E E (@id_funcd K E) x u y v) q)
        (Fibre_cat (@homd_ K E E (@id_funcd K E) x u y v) p)
        (@fapp1_fapp0 (Op_cat (Hom_cat K x y)) Cat_cat
          (@homd_ K E E (@id_funcd K E) x u y v) q p kappa) beta))) ⊢
  sigma_Snd (@sigma_repair_two_cell K E x y u v p q alpha beta kappa gamma)
  ≡ gamma;

// The whole first projection also computes on the supplied nonidentity 2-cell;
// its generic action is not merely a typable but unconnected companion.
assert [K : Cat] (E : τ (Catd K))
  [x y : τ (Obj K)] (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y))) [p q : τ (Hom K x y)]
  (alpha : τ (Obj (Fibre_cat (@homd_ K E E (@id_funcd K E) x u y v) p)))
  (beta : τ (Obj (Fibre_cat (@homd_ K E E (@id_funcd K E) x u y v) q)))
  (kappa : τ (Hom (Hom_cat K x y) p q))
  (gamma : τ (Hom
      (Fibre_cat (@homd_ K E E (@id_funcd K E) x u y v) p) alpha
      (@fapp0
        (Fibre_cat (@homd_ K E E (@id_funcd K E) x u y v) q)
        (Fibre_cat (@homd_ K E E (@id_funcd K E) x u y v) p)
        (@fapp1_fapp0 (Op_cat (Hom_cat K x y)) Cat_cat
          (@homd_ K E E (@id_funcd K E) x u y v) q p kappa) beta))) ⊢
  @fapp1_fapp0 _ _
    (@fapp1_func _ _ (@Sigma_proj1_func K E)
      (Struct_sigma x u) (Struct_sigma y v))
    (Struct_sigma p alpha) (Struct_sigma q beta)
    (@sigma_repair_two_cell K E x y u v p q alpha beta kappa gamma)
  ≡ kappa;
