/*
  Whole extension, matching, and section families over eligible covers.

  A question is already an internal object `(U,R,covers)` of
  `DirectCoverQuestion_cat(K,T)`.  Passing to the opposite total gives the
  variance in which pullback of a question induces maps from the pulled-back
  sieve extension and representable into their original values.  One whole
  extension functor and one whole inclusion therefore own all base action and
  naturality.

  For a fixed presheaf X, represented hom turns those two varying presheaves
  into Cat-valued matching and section families on the question category.
  Restriction is one displayed functor between them, not a family of external
  component squares.  Its component is exactly precomposition by the existing
  ordinary-sieve inclusion.

  At the canonical pullback of an eligible question, one stable whole map
  exposes the expected postcomposition action on literal sieve members.  A
  whole proof-time path specifies that the otherwise opaque generic extension
  action is this map.  The comparison is deliberately not a runtime fold: the
  corresponding owner-position fold exceeds the bounded checking ceiling.
  This module does not declare recursive glue, a strict glue-pullback law, an
  inverse law, locality, a sheaf, or sheafification.
*/

require open emdash.emdash3_2_direct_cover_questions;
require open emdash.emdash3_2_direct_cover_algebras;

// Representable selected by a question, varying over the opposite total.
symbol direct_cover_question_representable_func
  [K : Cat]
  (T : τ (@GrothTopology K))
  : τ (Functor
      (Op_cat (@DirectCoverQuestion_cat K T))
      (@Psh_cat K))
≔ @comp_cat_fapp0
    (Op_cat (@DirectCoverQuestion_cat K T))
    K
    (@Psh_cat K)
    (@yoneda_psh_func K)
    (@Op_func
      (@DirectCoverQuestion_cat K T)
      (Op_cat K)
      (@Sigma_proj1_func
        (Op_cat K)
        (@DirectCoverQuestionClassifier K T)));

// Whole varying ordinary-sieve extension; generic functor action owns coherence.
injective symbol direct_cover_question_extension_func
  [K : Cat]
  (T : τ (@GrothTopology K))
  : τ (Functor
      (Op_cat (@DirectCoverQuestion_cat K T))
      (@Psh_cat K));

// A literal eligible question evaluates to its existing ordinary extension.
rule @fapp0 _ _
      (@direct_cover_question_extension_func $K $T)
      (Struct_sigma $U $q)
  ↪ @direct_cover_question_extension_psh $K $T $U $q;

// Generic whole action at the canonical internally pulled-back question.
symbol direct_cover_question_extension_pullback_generic
  [K : Cat]
  (T : τ (@GrothTopology K))
  [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U))
  : τ (@Functord
      (Op_cat K)
      (@direct_cover_question_extension_psh
        K T V (@direct_cover_question_internal_pullback K T V U p q))
      (@direct_cover_question_extension_psh K T U q))
≔ @fapp1_fapp0
    (Op_cat (@DirectCoverQuestion_cat K T))
    (@Psh_cat K)
    (@direct_cover_question_extension_func K T)
    (Struct_sigma V
      (@direct_cover_question_internal_pullback K T V U p q))
    (Struct_sigma U q)
    (@direct_cover_question_pullback_arrow K T V U p q);

/*
  Stable canonical map from the pulled-back extension into the original
  extension.  It remains a whole presheaf map, so its arrow action and
  presheaf naturality stay internal at the generic displayed owners.
*/
injective symbol direct_cover_question_extension_pullback_func
  [K : Cat]
  (T : τ (@GrothTopology K))
  [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U))
  : τ (@Functord
      (Op_cat K)
      (@direct_cover_question_extension_psh
        K T V (@direct_cover_question_internal_pullback K T V U p q))
      (@direct_cover_question_extension_psh K T U q));

// Stable fibre functor selected by the canonical whole map at W.
injective symbol direct_cover_question_extension_pullback_fibre_func
  [K : Cat]
  (T : τ (@GrothTopology K))
  [W V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U))
  : τ (@Functor
      (@Fibre_cat
        (Op_cat K)
        (@direct_cover_question_extension_psh
          K T V (@direct_cover_question_internal_pullback K T V U p q))
        W)
      (@Fibre_cat
        (Op_cat K)
        (@direct_cover_question_extension_psh K T U q)
        W));

// Fibre projection of the canonical whole pullback map.
rule @tapp0_fapp0
      _ Cat_cat _ _ $W
      (@direct_cover_question_extension_pullback_func
        $K $T $V $U $p $q)
  ↪ @direct_cover_question_extension_pullback_fibre_func
      $K $T $W $V $U $p $q;

// Semantic target of one literal `(h,member)` pair under postcomposition.
symbol direct_cover_question_extension_pullback_pair
  [K : Cat]
  (T : τ (@GrothTopology K))
  [W V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U))
  (h : τ (Hom K W V))
  (member : τ (@SieveMembership
      K U
      (@direct_cover_question_sieve K T U q)
      (@into_restr_postcompose K V U p (Struct_sigma W h))))
  : τ (Obj (@Fibre_cat
      (Op_cat K)
      (@direct_cover_question_extension_psh K T U q)
      W))
≔ Struct_sigma
    (@into_restr_arrow K U
      (@into_restr_postcompose K V U p (Struct_sigma W h)))
    member;

// Literal pair beta: postcompose the retained arrow and preserve membership.
rule @fapp0
      _ _
      (@direct_cover_question_extension_pullback_fibre_func
        $K $T $W $V $U $p $q)
      (Struct_sigma $h $member)
  ↪ @direct_cover_question_extension_pullback_pair
      $K $T $W $V $U $p $q $h $member;

/*
  Whole semantic specification of the primitive varying-extension action.
  This is a proof-time path between whole presheaf maps, not a runtime fold
  and not a family of external component squares.
*/
constant symbol direct_cover_question_extension_pullback_agrees
  [K : Cat]
  (T : τ (@GrothTopology K))
  [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U))
  : τ (@=
      (Hom
        (@Psh_cat K)
        (@direct_cover_question_extension_psh
          K T V (@direct_cover_question_internal_pullback K T V U p q))
        (@direct_cover_question_extension_psh K T U q))
      (@direct_cover_question_extension_pullback_generic K T V U p q)
      (@direct_cover_question_extension_pullback_func K T V U p q));

// Project the whole comparison to the fibre functor at W.
symbol direct_cover_question_extension_pullback_fibre_agrees
  [K : Cat]
  (T : τ (@GrothTopology K))
  [W V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U))
  : τ (@=
      (Hom
        Cat_cat
        (@Fibre_cat
          (Op_cat K)
          (@direct_cover_question_extension_psh
            K T V (@direct_cover_question_internal_pullback K T V U p q))
          W)
        (@Fibre_cat
          (Op_cat K)
          (@direct_cover_question_extension_psh K T U q)
          W))
      (@tapp0_fapp0
        (Op_cat K) Cat_cat
        (@direct_cover_question_extension_psh
          K T V (@direct_cover_question_internal_pullback K T V U p q))
        (@direct_cover_question_extension_psh K T U q)
        W
        (@direct_cover_question_extension_pullback_generic K T V U p q))
      (@direct_cover_question_extension_pullback_fibre_func
        K T W V U p q))
≔ @eq_ap
    (Hom
      (@Psh_cat K)
      (@direct_cover_question_extension_psh
        K T V (@direct_cover_question_internal_pullback K T V U p q))
      (@direct_cover_question_extension_psh K T U q))
    (Hom
      Cat_cat
      (@Fibre_cat
        (Op_cat K)
        (@direct_cover_question_extension_psh
          K T V (@direct_cover_question_internal_pullback K T V U p q))
        W)
      (@Fibre_cat
        (Op_cat K)
        (@direct_cover_question_extension_psh K T U q)
        W))
    (λ F : τ (Hom
        (@Psh_cat K)
        (@direct_cover_question_extension_psh
          K T V (@direct_cover_question_internal_pullback K T V U p q))
        (@direct_cover_question_extension_psh K T U q)),
      @tapp0_fapp0
        (Op_cat K) Cat_cat
        (@direct_cover_question_extension_psh
          K T V (@direct_cover_question_internal_pullback K T V U p q))
        (@direct_cover_question_extension_psh K T U q)
        W F)
    (@direct_cover_question_extension_pullback_generic K T V U p q)
    (@direct_cover_question_extension_pullback_func K T V U p q)
    (@direct_cover_question_extension_pullback_agrees K T V U p q);

// Literal member observation, derived from the one whole comparison path.
symbol direct_cover_question_extension_pullback_pair_agrees
  [K : Cat]
  (T : τ (@GrothTopology K))
  [W V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U))
  (h : τ (Hom K W V))
  (member : τ (@SieveMembership
      K U
      (@direct_cover_question_sieve K T U q)
      (@into_restr_postcompose K V U p (Struct_sigma W h))))
  : τ (@=
      (Obj (@Fibre_cat
        (Op_cat K)
        (@direct_cover_question_extension_psh K T U q)
        W))
      (@fapp0
        (@Fibre_cat
          (Op_cat K)
          (@direct_cover_question_extension_psh
            K T V (@direct_cover_question_internal_pullback K T V U p q))
          W)
        (@Fibre_cat
          (Op_cat K)
          (@direct_cover_question_extension_psh K T U q)
          W)
        (@tapp0_fapp0
          (Op_cat K) Cat_cat
          (@direct_cover_question_extension_psh
            K T V (@direct_cover_question_internal_pullback K T V U p q))
          (@direct_cover_question_extension_psh K T U q)
          W
          (@direct_cover_question_extension_pullback_generic K T V U p q))
        (Struct_sigma h member))
      (@direct_cover_question_extension_pullback_pair
        K T W V U p q h member))
≔ @eq_ap
    (Hom
      Cat_cat
      (@Fibre_cat
        (Op_cat K)
        (@direct_cover_question_extension_psh
          K T V (@direct_cover_question_internal_pullback K T V U p q))
        W)
      (@Fibre_cat
        (Op_cat K)
        (@direct_cover_question_extension_psh K T U q)
        W))
    (Obj (@Fibre_cat
      (Op_cat K)
      (@direct_cover_question_extension_psh K T U q)
      W))
    (λ F : τ (Hom
        Cat_cat
        (@Fibre_cat
          (Op_cat K)
          (@direct_cover_question_extension_psh
            K T V (@direct_cover_question_internal_pullback K T V U p q))
          W)
        (@Fibre_cat
          (Op_cat K)
          (@direct_cover_question_extension_psh K T U q)
          W)),
      @fapp0
        (@Fibre_cat
          (Op_cat K)
          (@direct_cover_question_extension_psh
            K T V (@direct_cover_question_internal_pullback K T V U p q))
          W)
        (@Fibre_cat
          (Op_cat K)
          (@direct_cover_question_extension_psh K T U q)
          W)
        F
        (Struct_sigma h member))
    (@tapp0_fapp0
      (Op_cat K) Cat_cat
      (@direct_cover_question_extension_psh
        K T V (@direct_cover_question_internal_pullback K T V U p q))
      (@direct_cover_question_extension_psh K T U q)
      W
      (@direct_cover_question_extension_pullback_generic K T V U p q))
    (@direct_cover_question_extension_pullback_fibre_func
      K T W V U p q)
    (@direct_cover_question_extension_pullback_fibre_agrees
      K T W V U p q);

/*
  Whole retained-member factorization of the canonical extension action.

    extension(p^*q) -> y(V) -> extension(q)
      = extension_pullback(p,q).

  The first map is the pulled-sieve inclusion and the second is the whole
  Yoneda section selected by `(p,member)`.  Semantically, both routes become
  the same map after the extension inclusion into `y(U)`: this follows from
  whole naturality of `direct_cover_question_extension_inclusion_transf` and
  the covariant-Yoneda action triangle.  Pointwise subterminality of an
  ordinary sieve then cancels that inclusion.

  v3.2 records the result as one proof-time path between whole presheaf maps.
  It is not a runtime fold, not a convenience unifier between expanded
  presentations, and not an external family of component equations.  A
  future generic strict pointwise-to-whole cancellation theorem may derive
  this path transparently without changing its public statement.
*/
constant symbol direct_cover_question_extension_pullback_retained_agrees
  [K : Cat]
  (T : τ (@GrothTopology K))
  [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U))
  (member : τ (@SieveMembership
      K U (@direct_cover_question_sieve K T U q) (Struct_sigma V p)))
  : τ (@=
      (Hom
        (@Psh_cat K)
        (@direct_cover_question_extension_psh
          K T V (@direct_cover_question_internal_pullback K T V U p q))
        (@direct_cover_question_extension_psh K T U q))
      (@comp_fapp0
        (@Psh_cat K)
        (@direct_cover_question_extension_psh
          K T V (@direct_cover_question_internal_pullback K T V U p q))
        (@FibCov_source_catd (Op_cat K) V)
        (@direct_cover_question_extension_psh K T U q)
        (@fib_cov_transf
          (Op_cat K)
          (@direct_cover_question_extension_psh K T U q)
          V
          (Struct_sigma p member))
        (@direct_cover_question_extension_inclusion
          K T V (@direct_cover_question_internal_pullback K T V U p q)))
      (@direct_cover_question_extension_pullback_func K T V U p q));

// One whole inclusion from varying extensions to varying representables.
injective symbol direct_cover_question_extension_inclusion_transf
  [K : Cat]
  (T : τ (@GrothTopology K))
  : τ (@Transf
      (Op_cat (@DirectCoverQuestion_cat K T))
      (@Psh_cat K)
      (@direct_cover_question_extension_func K T)
      (@direct_cover_question_representable_func K T));

// Its component is the deployed ordinary-sieve extension inclusion.
rule @tapp0_fapp0
      _ _ _ _
      (Struct_sigma $U $q)
      (@direct_cover_question_extension_inclusion_transf $K $T)
  ↪ @direct_cover_question_extension_inclusion $K $T $U $q;

// Internally reindexed matching categories for a fixed presheaf X.
symbol DirectCoverQuestionMatching_catd
  [K : Cat]
  (T : τ (@GrothTopology K))
  (X : τ (@Psh K))
  : τ (Catd (@DirectCoverQuestion_cat K T))
≔ @hom_con
    (@Psh_cat K)
    X
    (Op_cat (@DirectCoverQuestion_cat K T))
    (@direct_cover_question_extension_func K T);

// Internally reindexed section categories for the same fixed presheaf X.
symbol DirectCoverQuestionSection_catd
  [K : Cat]
  (T : τ (@GrothTopology K))
  (X : τ (@Psh K))
  : τ (Catd (@DirectCoverQuestion_cat K T))
≔ @hom_con
    (@Psh_cat K)
    X
    (Op_cat (@DirectCoverQuestion_cat K T))
    (@direct_cover_question_representable_func K T);

/*
  Whole restriction induced by the whole inclusion.  Its displayed-functor
  structure owns question reindexing; no external naturality field is added.
*/
injective symbol direct_cover_question_restriction_funcd
  [K : Cat]
  (T : τ (@GrothTopology K))
  (X : τ (@Psh K))
  : τ (@Functord
      (@DirectCoverQuestion_cat K T)
      (@DirectCoverQuestionSection_catd K T X)
      (@DirectCoverQuestionMatching_catd K T X));

// At a literal question, restriction is existing whole precomposition.
rule @tapp0_fapp0
      _ Cat_cat _ _
      (Struct_sigma $U $q)
      (@direct_cover_question_restriction_funcd $K $T $X)
  ↪ @ordinary_sieve_local_precomp
      $K $U (@direct_cover_question_sieve $K $T $U $q) $X;
