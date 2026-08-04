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

  The canonical pullback action of the extension is intentionally opaque at
  this first boundary.  A later locality proof may select a narrow computing
  observer for that action.  This module does not declare recursive glue, an
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
