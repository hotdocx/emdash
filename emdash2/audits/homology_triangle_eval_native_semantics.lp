/* NON-LIBRARY: independent native semantics for the contravariant-evaluation
   consumer. No Op/Op_funcd/homd operation, new primitive, rule or unifier
   is used to obtain an arrow in the requested direction. */
require open emdash.emdash3_2;

// Use the actual represented reindexing owner from the triangle prototype.
symbol triangle_eval_reindexed [I A B : Cat]
  (G : τ (Functor A B)) (U : τ (Functor I A))
  : τ (Functor I B)
≔ @Hom_fapp0 Cat_cat I I A B (@id_func I) G U;

// The native whole functor evaluates a transformation together with a shape
// arrow. Its action on all further Hom categories remains available.
symbol triangle_eval_native_hom_func [I A B : Cat]
  (G : τ (Functor A B)) (U : τ (Functor I A))
  (V : τ (Functor I B)) (j i : τ (Obj I))
  : τ (Functor
      (Product_cat (@Transf_cat I B V (@triangle_eval_reindexed I A B G U))
        (Hom_cat I j i))
      (Hom_cat B (@fapp0 I B V j)
        (@fapp0 I B (@triangle_eval_reindexed I A B G U) i)))
≔ @Eval_fapp1_func I B V (@triangle_eval_reindexed I A B G U) j i;

assert [I A B : Cat] (G : τ (Functor A B)) (U : τ (Functor I A))
  (i : τ (Obj I)) ⊢
  @fapp0 I B (@triangle_eval_reindexed I A B G U) i
  ≡ @fapp0 A B G (@fapp0 I A U i);

assert [I A B : Cat] (G : τ (Functor A B)) (U : τ (Functor I A))
  (V : τ (Functor I B)) [j i : τ (Obj I)]
  (eta : τ (@Transf I B V (@triangle_eval_reindexed I A B G U)))
  (q : τ (Hom I j i)) ⊢
  @fapp0 _ _ (@triangle_eval_native_hom_func I A B G U V j i)
    (Struct_sigma eta q)
  ≡ @tapp1_fapp0 I B V (@triangle_eval_reindexed I A B G U) j i eta q;

// The fixed-index case required by the triangle edge is exactly eta[i].
assert [I A B : Cat] (G : τ (Functor A B)) (U : τ (Functor I A))
  (V : τ (Functor I B)) (i : τ (Obj I))
  (eta : τ (@Transf I B V (@triangle_eval_reindexed I A B G U))) ⊢
  @fapp0 _ _ (@triangle_eval_native_hom_func I A B G U V i i)
    (Struct_sigma eta (@id I i))
  ≡ @tapp0_fapp0 I B V (@triangle_eval_reindexed I A B G U) i eta;

// This component has the forward, not an invented reverse, Hom type.
assert [I A B : Cat] (G : τ (Functor A B)) (U : τ (Functor I A))
  (V : τ (Functor I B)) (i : τ (Obj I))
  (eta : τ (@Transf I B V (@triangle_eval_reindexed I A B G U))) ⊢
  @tapp0_fapp0 I B V (@triangle_eval_reindexed I A B G U) i eta
  : τ (Hom B (@fapp0 I B V i) (@fapp0 A B G (@fapp0 I A U i)));

assertnot [I A B : Cat] (G : τ (Functor A B)) (U : τ (Functor I A))
  (V : τ (Functor I B)) (i : τ (Obj I))
  (eta : τ (@Transf I B V (@triangle_eval_reindexed I A B G U))) ⊢
  @tapp0_fapp0 I B V (@triangle_eval_reindexed I A B G U) i eta
  : τ (Hom B (@fapp0 A B G (@fapp0 I A U i)) (@fapp0 I B V i));

type λ I : Cat, λ A : Cat, λ B : Cat,
  λ G : τ (Functor A B), λ U : τ (Functor I A), λ V : τ (Functor I B),
  λ j : τ (Obj I), λ i : τ (Obj I),
  λ r : τ (Obj (Product_cat
    (@Transf_cat I B V (@triangle_eval_reindexed I A B G U)) (Hom_cat I j i))),
  λ s : τ (Obj (Product_cat
    (@Transf_cat I B V (@triangle_eval_reindexed I A B G U)) (Hom_cat I j i))),
  @fapp1_func _ _ (@triangle_eval_native_hom_func I A B G U V j i) r s;
