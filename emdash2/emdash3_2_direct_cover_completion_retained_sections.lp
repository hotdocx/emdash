/* Whole glue substitution, before any value/section naturality argument.
   All proofs use existing action, profile and comparison owners. */
require open emdash.emdash3_2_direct_cover_completion_hit;
require open emdash.emdash3_2_yoneda_precomposition_value;

// Stage the existing proof-time precomposition reading before specialization.
symbol precomposition_point_path
  [A B : Cat] (F : τ (Functor A B)) [W X : τ (Obj A)]
  (h : τ (Hom A W X)) [Z : τ (Obj B)]
  (g : τ (Hom B (@fapp0 A B F X) Z))
  : τ (@= (Hom B (@fapp0 A B F W) Z)
    (@hom_precomp_along_fapp0 A B F Z W X h g)
    (@comp_fapp0 B (@fapp0 A B F W) (@fapp0 A B F X) Z g (@fapp1_fapp0 A B F W X h)))
≔ @eq_refl (Hom B (@fapp0 A B F W) Z)
    (@hom_precomp_along_fapp0 A B F Z W X h g);

// Section pullback of glue is glue of matching pullback, on actual whole maps.
symbol cover_whole_glue_substitution_path
  [K : Cat] (T : τ (@GrothTopology K)) (P : τ (@Psh K))
  [V U : τ (Obj K)] (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U))
  (m : τ (Hom (@Psh_cat K) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P)))
  : τ (@= (Hom (@Psh_cat K) (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P))
    (@comp_fapp0 (@Psh_cat K) (@yoneda_psh K V) (@yoneda_psh K U) (@DirectCoverCompletionPsh K T P) (@direct_cover_completion_glue K T P U (@direct_cover_question_sieve K T U q) (@direct_cover_question_cover K T U q) m) (@fapp1_fapp0 (Op_cat (@DirectCoverQuestion_cat K T)) (@Psh_cat K) (@direct_cover_question_representable_func K T) (Struct_sigma V (@direct_cover_question_internal_pullback K T V U p q)) (Struct_sigma U q) (@direct_cover_question_pullback_arrow K T V U p q)))
    (@fapp0 (@DirectCoverMatching_cat K V (@direct_cover_question_sieve K T V (@direct_cover_question_internal_pullback K T V U p q)) (@DirectCoverCompletionPsh K T P)) (@DirectCoverSection_cat K V (@DirectCoverCompletionPsh K T P)) (@direct_cover_completion_glue_func K T P V (@direct_cover_question_sieve K T V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_cover K T V (@direct_cover_question_internal_pullback K T V U p q))) (@comp_fapp0 (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P) m (@direct_cover_question_extension_pullback_generic K T V U p q))))
≔ @eq_trans (Hom (@Psh_cat K) (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P)) (@comp_fapp0 (@Psh_cat K) (@yoneda_psh K V) (@yoneda_psh K U) (@DirectCoverCompletionPsh K T P) (@direct_cover_completion_glue K T P U (@direct_cover_question_sieve K T U q) (@direct_cover_question_cover K T U q) m) (@fapp1_fapp0 (Op_cat (@DirectCoverQuestion_cat K T)) (@Psh_cat K) (@direct_cover_question_representable_func K T) (Struct_sigma V (@direct_cover_question_internal_pullback K T V U p q)) (Struct_sigma U q) (@direct_cover_question_pullback_arrow K T V U p q))) (@fapp0 (@DirectCoverMatching_cat K U (@direct_cover_question_sieve K T U q) (@DirectCoverCompletionPsh K T P)) (@DirectCoverSection_cat K V (@DirectCoverCompletionPsh K T P)) (@functord_transport_lhs_func (@DirectCoverQuestion_cat K T) (@DirectCoverQuestionMatching_catd K T (@DirectCoverCompletionPsh K T P)) (@DirectCoverQuestionSection_catd K T (@DirectCoverCompletionPsh K T P)) (@direct_cover_completion_glue_funcd K T P) (Struct_sigma U q) (Struct_sigma V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_pullback_arrow K T V U p q)) m) (@fapp0 (@DirectCoverMatching_cat K V (@direct_cover_question_sieve K T V (@direct_cover_question_internal_pullback K T V U p q)) (@DirectCoverCompletionPsh K T P)) (@DirectCoverSection_cat K V (@DirectCoverCompletionPsh K T P)) (@direct_cover_completion_glue_func K T P V (@direct_cover_question_sieve K T V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_cover K T V (@direct_cover_question_internal_pullback K T V U p q))) (@comp_fapp0 (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P) m (@direct_cover_question_extension_pullback_generic K T V U p q)))
    (@eq_sym (Hom (@Psh_cat K) (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P)) (@fapp0 (@DirectCoverMatching_cat K U (@direct_cover_question_sieve K T U q) (@DirectCoverCompletionPsh K T P)) (@DirectCoverSection_cat K V (@DirectCoverCompletionPsh K T P)) (@functord_transport_lhs_func (@DirectCoverQuestion_cat K T) (@DirectCoverQuestionMatching_catd K T (@DirectCoverCompletionPsh K T P)) (@DirectCoverQuestionSection_catd K T (@DirectCoverCompletionPsh K T P)) (@direct_cover_completion_glue_funcd K T P) (Struct_sigma U q) (Struct_sigma V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_pullback_arrow K T V U p q)) m) (@comp_fapp0 (@Psh_cat K) (@yoneda_psh K V) (@yoneda_psh K U) (@DirectCoverCompletionPsh K T P) (@direct_cover_completion_glue K T P U (@direct_cover_question_sieve K T U q) (@direct_cover_question_cover K T U q) m) (@fapp1_fapp0 (Op_cat (@DirectCoverQuestion_cat K T)) (@Psh_cat K) (@direct_cover_question_representable_func K T) (Struct_sigma V (@direct_cover_question_internal_pullback K T V U p q)) (Struct_sigma U q) (@direct_cover_question_pullback_arrow K T V U p q)))
      (@precomposition_point_path (Op_cat (@DirectCoverQuestion_cat K T)) (@Psh_cat K) (@direct_cover_question_representable_func K T) (Struct_sigma V (@direct_cover_question_internal_pullback K T V U p q)) (Struct_sigma U q) (@direct_cover_question_pullback_arrow K T V U p q) (@DirectCoverCompletionPsh K T P) (@direct_cover_completion_glue K T P U (@direct_cover_question_sieve K T U q) (@direct_cover_question_cover K T U q) m)))
    (@eq_trans (Hom (@Psh_cat K) (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P)) (@fapp0 (@DirectCoverMatching_cat K U (@direct_cover_question_sieve K T U q) (@DirectCoverCompletionPsh K T P)) (@DirectCoverSection_cat K V (@DirectCoverCompletionPsh K T P)) (@functord_transport_lhs_func (@DirectCoverQuestion_cat K T) (@DirectCoverQuestionMatching_catd K T (@DirectCoverCompletionPsh K T P)) (@DirectCoverQuestionSection_catd K T (@DirectCoverCompletionPsh K T P)) (@direct_cover_completion_glue_funcd K T P) (Struct_sigma U q) (Struct_sigma V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_pullback_arrow K T V U p q)) m) (@fapp0 (@DirectCoverMatching_cat K U (@direct_cover_question_sieve K T U q) (@DirectCoverCompletionPsh K T P)) (@DirectCoverSection_cat K V (@DirectCoverCompletionPsh K T P)) (@functord_transport_rhs_func (@DirectCoverQuestion_cat K T) (@DirectCoverQuestionMatching_catd K T (@DirectCoverCompletionPsh K T P)) (@DirectCoverQuestionSection_catd K T (@DirectCoverCompletionPsh K T P)) (@direct_cover_completion_glue_funcd K T P) (Struct_sigma U q) (Struct_sigma V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_pullback_arrow K T V U p q)) m) (@fapp0 (@DirectCoverMatching_cat K V (@direct_cover_question_sieve K T V (@direct_cover_question_internal_pullback K T V U p q)) (@DirectCoverCompletionPsh K T P)) (@DirectCoverSection_cat K V (@DirectCoverCompletionPsh K T P)) (@direct_cover_completion_glue_func K T P V (@direct_cover_question_sieve K T V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_cover K T V (@direct_cover_question_internal_pullback K T V U p q))) (@comp_fapp0 (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P) m (@direct_cover_question_extension_pullback_generic K T V U p q)))
      (@eq_ap (Functor (@DirectCoverMatching_cat K U (@direct_cover_question_sieve K T U q) (@DirectCoverCompletionPsh K T P)) (@DirectCoverSection_cat K V (@DirectCoverCompletionPsh K T P))) (Hom (@Psh_cat K) (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P))
        (λ F : τ (Functor (@DirectCoverMatching_cat K U (@direct_cover_question_sieve K T U q) (@DirectCoverCompletionPsh K T P)) (@DirectCoverSection_cat K V (@DirectCoverCompletionPsh K T P))), @fapp0 (@DirectCoverMatching_cat K U (@direct_cover_question_sieve K T U q) (@DirectCoverCompletionPsh K T P)) (@DirectCoverSection_cat K V (@DirectCoverCompletionPsh K T P)) F m)
        (@functord_transport_lhs_func (@DirectCoverQuestion_cat K T) (@DirectCoverQuestionMatching_catd K T (@DirectCoverCompletionPsh K T P)) (@DirectCoverQuestionSection_catd K T (@DirectCoverCompletionPsh K T P)) (@direct_cover_completion_glue_funcd K T P) (Struct_sigma U q) (Struct_sigma V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_pullback_arrow K T V U p q)) (@functord_transport_rhs_func (@DirectCoverQuestion_cat K T) (@DirectCoverQuestionMatching_catd K T (@DirectCoverCompletionPsh K T P)) (@DirectCoverQuestionSection_catd K T (@DirectCoverCompletionPsh K T P)) (@direct_cover_completion_glue_funcd K T P) (Struct_sigma U q) (Struct_sigma V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_pullback_arrow K T V U p q)) (@direct_cover_completion_glue_pullback_agrees K T P V U p q))
      (@eq_ap (Hom (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@DirectCoverCompletionPsh K T P)) (Hom (@Psh_cat K) (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P))
        (λ n : τ (Hom (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@DirectCoverCompletionPsh K T P)), @fapp0 (@DirectCoverMatching_cat K V (@direct_cover_question_sieve K T V (@direct_cover_question_internal_pullback K T V U p q)) (@DirectCoverCompletionPsh K T P)) (@DirectCoverSection_cat K V (@DirectCoverCompletionPsh K T P)) (@direct_cover_completion_glue_func K T P V (@direct_cover_question_sieve K T V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_cover K T V (@direct_cover_question_internal_pullback K T V U p q))) n)
        (@hom_precomp_along_fapp0 (Op_cat (@DirectCoverQuestion_cat K T)) (@Psh_cat K) (@direct_cover_question_extension_func K T) (@DirectCoverCompletionPsh K T P) (Struct_sigma V (@direct_cover_question_internal_pullback K T V U p q)) (Struct_sigma U q) (@direct_cover_question_pullback_arrow K T V U p q) m) (@comp_fapp0 (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P) m (@direct_cover_question_extension_pullback_generic K T V U p q))
        (@precomposition_point_path (Op_cat (@DirectCoverQuestion_cat K T)) (@Psh_cat K) (@direct_cover_question_extension_func K T) (Struct_sigma V (@direct_cover_question_internal_pullback K T V U p q)) (Struct_sigma U q) (@direct_cover_question_pullback_arrow K T V U p q) (@DirectCoverCompletionPsh K T P) m)));

// Retain m composed with the represented member; no matching naturality is used.
symbol cover_retained_section
  [K : Cat] (T : τ (@GrothTopology K)) (P : τ (@Psh K))
  [V U : τ (Obj K)] (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U))
  (member : τ (@SieveMembership K U (@direct_cover_question_sieve K T U q) (Struct_sigma V p)))
  (m : τ (Hom (@Psh_cat K) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P)))
  : τ (Hom (@Psh_cat K) (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P))
≔ (@comp_fapp0 (@Psh_cat K) (@FibCov_source_catd (Op_cat K) V) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P) m (@fib_cov_transf (Op_cat K) (@direct_cover_question_extension_psh K T U q) V (Struct_sigma p member)));

// Whole factorization, associativity and the existing restriction presentation.
symbol cover_pulled_matching_restriction_path
  [K : Cat] (T : τ (@GrothTopology K)) (P : τ (@Psh K))
  [V U : τ (Obj K)] (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U))
  (member : τ (@SieveMembership K U (@direct_cover_question_sieve K T U q) (Struct_sigma V p)))
  (m : τ (Hom (@Psh_cat K) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P)))
  : τ (@= (Hom (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@DirectCoverCompletionPsh K T P)) (@comp_fapp0 (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P) m (@direct_cover_question_extension_pullback_generic K T V U p q)) (@direct_cover_completion_restrict K T P V (@direct_cover_question_sieve K T V (@direct_cover_question_internal_pullback K T V U p q)) (@cover_retained_section K T P V U p q member m)))
≔ @eq_trans (Hom (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@DirectCoverCompletionPsh K T P)) (@comp_fapp0 (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P) m (@direct_cover_question_extension_pullback_generic K T V U p q)) (@comp_fapp0 (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P) m (@comp_fapp0 (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@FibCov_source_catd (Op_cat K) V) (@direct_cover_question_extension_psh K T U q) (@fib_cov_transf (Op_cat K) (@direct_cover_question_extension_psh K T U q) V (Struct_sigma p member)) (@direct_cover_question_extension_inclusion K T V (@direct_cover_question_internal_pullback K T V U p q)))) (@direct_cover_completion_restrict K T P V (@direct_cover_question_sieve K T V (@direct_cover_question_internal_pullback K T V U p q)) (@cover_retained_section K T P V U p q member m))
    (@eq_ap (Hom (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_extension_psh K T U q)) (Hom (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@DirectCoverCompletionPsh K T P))
      (λ e : τ (Hom (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_extension_psh K T U q)), @comp_fapp0 (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P) m e)
      (@direct_cover_question_extension_pullback_generic K T V U p q) (@comp_fapp0 (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@FibCov_source_catd (Op_cat K) V) (@direct_cover_question_extension_psh K T U q) (@fib_cov_transf (Op_cat K) (@direct_cover_question_extension_psh K T U q) V (Struct_sigma p member)) (@direct_cover_question_extension_inclusion K T V (@direct_cover_question_internal_pullback K T V U p q))) (@eq_trans (Hom (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_extension_psh K T U q)) (@direct_cover_question_extension_pullback_generic K T V U p q) (@direct_cover_question_extension_pullback_func K T V U p q) (@comp_fapp0 (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@FibCov_source_catd (Op_cat K) V) (@direct_cover_question_extension_psh K T U q) (@fib_cov_transf (Op_cat K) (@direct_cover_question_extension_psh K T U q) V (Struct_sigma p member)) (@direct_cover_question_extension_inclusion K T V (@direct_cover_question_internal_pullback K T V U p q)))
      (@direct_cover_question_extension_pullback_agrees K T V U p q)
      (@eq_sym (Hom (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_extension_psh K T U q)) (@comp_fapp0 (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@FibCov_source_catd (Op_cat K) V) (@direct_cover_question_extension_psh K T U q) (@fib_cov_transf (Op_cat K) (@direct_cover_question_extension_psh K T U q) V (Struct_sigma p member)) (@direct_cover_question_extension_inclusion K T V (@direct_cover_question_internal_pullback K T V U p q))) (@direct_cover_question_extension_pullback_func K T V U p q)
        (@direct_cover_question_extension_pullback_retained_agrees K T V U p q member))))
    (@eq_trans (Hom (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@DirectCoverCompletionPsh K T P)) (@comp_fapp0 (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P) m (@comp_fapp0 (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@FibCov_source_catd (Op_cat K) V) (@direct_cover_question_extension_psh K T U q) (@fib_cov_transf (Op_cat K) (@direct_cover_question_extension_psh K T U q) V (Struct_sigma p member)) (@direct_cover_question_extension_inclusion K T V (@direct_cover_question_internal_pullback K T V U p q)))) (@comp_fapp0 (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@FibCov_source_catd (Op_cat K) V) (@DirectCoverCompletionPsh K T P) (@cover_retained_section K T P V U p q member m) (@direct_cover_question_extension_inclusion K T V (@direct_cover_question_internal_pullback K T V U p q))) (@direct_cover_completion_restrict K T P V (@direct_cover_question_sieve K T V (@direct_cover_question_internal_pullback K T V U p q)) (@cover_retained_section K T P V U p q member m))
      (@comp_assoc (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@FibCov_source_catd (Op_cat K) V) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P) m (@fib_cov_transf (Op_cat K) (@direct_cover_question_extension_psh K T U q) V (Struct_sigma p member)) (@direct_cover_question_extension_inclusion K T V (@direct_cover_question_internal_pullback K T V U p q)))
      (@eq_sym (Hom (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@DirectCoverCompletionPsh K T P)) (@direct_cover_completion_restrict K T P V (@direct_cover_question_sieve K T V (@direct_cover_question_internal_pullback K T V U p q)) (@cover_retained_section K T P V U p q member m)) (@comp_fapp0 (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@FibCov_source_catd (Op_cat K) V) (@DirectCoverCompletionPsh K T P) (@cover_retained_section K T P V U p q member m) (@direct_cover_question_extension_inclusion K T V (@direct_cover_question_internal_pullback K T V U p q)))
        (@precomposition_point_path (@Psh_cat K) (@Psh_cat K) (@id_func (@Psh_cat K)) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@FibCov_source_catd (Op_cat K) V) (@direct_cover_question_extension_inclusion K T V (@direct_cover_question_internal_pullback K T V U p q)) (@DirectCoverCompletionPsh K T P) (@cover_retained_section K T P V U p q member m))));

// The pulled whole glue section is the retained composed section, by silent.
symbol cover_whole_retained_section_path
  [K : Cat] (T : τ (@GrothTopology K)) (P : τ (@Psh K))
  [V U : τ (Obj K)] (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U))
  (member : τ (@SieveMembership K U (@direct_cover_question_sieve K T U q) (Struct_sigma V p)))
  (m : τ (Hom (@Psh_cat K) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P)))
  : τ (@= (Hom (@Psh_cat K) (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P)) (@comp_fapp0 (@Psh_cat K) (@yoneda_psh K V) (@yoneda_psh K U) (@DirectCoverCompletionPsh K T P) (@direct_cover_completion_glue K T P U (@direct_cover_question_sieve K T U q) (@direct_cover_question_cover K T U q) m) (@fapp1_fapp0 (Op_cat (@DirectCoverQuestion_cat K T)) (@Psh_cat K) (@direct_cover_question_representable_func K T) (Struct_sigma V (@direct_cover_question_internal_pullback K T V U p q)) (Struct_sigma U q) (@direct_cover_question_pullback_arrow K T V U p q))) (@cover_retained_section K T P V U p q member m))
≔ @eq_trans (Hom (@Psh_cat K) (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P)) (@comp_fapp0 (@Psh_cat K) (@yoneda_psh K V) (@yoneda_psh K U) (@DirectCoverCompletionPsh K T P) (@direct_cover_completion_glue K T P U (@direct_cover_question_sieve K T U q) (@direct_cover_question_cover K T U q) m) (@fapp1_fapp0 (Op_cat (@DirectCoverQuestion_cat K T)) (@Psh_cat K) (@direct_cover_question_representable_func K T) (Struct_sigma V (@direct_cover_question_internal_pullback K T V U p q)) (Struct_sigma U q) (@direct_cover_question_pullback_arrow K T V U p q))) (@fapp0 (@DirectCoverMatching_cat K V (@direct_cover_question_sieve K T V (@direct_cover_question_internal_pullback K T V U p q)) (@DirectCoverCompletionPsh K T P)) (@DirectCoverSection_cat K V (@DirectCoverCompletionPsh K T P)) (@direct_cover_completion_glue_func K T P V (@direct_cover_question_sieve K T V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_cover K T V (@direct_cover_question_internal_pullback K T V U p q))) (@comp_fapp0 (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P) m (@direct_cover_question_extension_pullback_generic K T V U p q))) (@cover_retained_section K T P V U p q member m)
    (@cover_whole_glue_substitution_path K T P V U p q m)
    (@eq_trans (Hom (@Psh_cat K) (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P)) (@fapp0 (@DirectCoverMatching_cat K V (@direct_cover_question_sieve K T V (@direct_cover_question_internal_pullback K T V U p q)) (@DirectCoverCompletionPsh K T P)) (@DirectCoverSection_cat K V (@DirectCoverCompletionPsh K T P)) (@direct_cover_completion_glue_func K T P V (@direct_cover_question_sieve K T V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_cover K T V (@direct_cover_question_internal_pullback K T V U p q))) (@comp_fapp0 (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P) m (@direct_cover_question_extension_pullback_generic K T V U p q))) (@fapp0 (@DirectCoverMatching_cat K V (@direct_cover_question_sieve K T V (@direct_cover_question_internal_pullback K T V U p q)) (@DirectCoverCompletionPsh K T P)) (@DirectCoverSection_cat K V (@DirectCoverCompletionPsh K T P)) (@direct_cover_completion_glue_func K T P V (@direct_cover_question_sieve K T V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_cover K T V (@direct_cover_question_internal_pullback K T V U p q))) (@direct_cover_completion_restrict K T P V (@direct_cover_question_sieve K T V (@direct_cover_question_internal_pullback K T V U p q)) (@cover_retained_section K T P V U p q member m))) (@cover_retained_section K T P V U p q member m)
      (@eq_ap (Hom (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@DirectCoverCompletionPsh K T P)) (Hom (@Psh_cat K) (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P))
        (λ n : τ (Hom (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@DirectCoverCompletionPsh K T P)), @fapp0 (@DirectCoverMatching_cat K V (@direct_cover_question_sieve K T V (@direct_cover_question_internal_pullback K T V U p q)) (@DirectCoverCompletionPsh K T P)) (@DirectCoverSection_cat K V (@DirectCoverCompletionPsh K T P)) (@direct_cover_completion_glue_func K T P V (@direct_cover_question_sieve K T V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_cover K T V (@direct_cover_question_internal_pullback K T V U p q))) n)
        (@comp_fapp0 (@Psh_cat K) (@direct_cover_question_extension_psh K T V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P) m (@direct_cover_question_extension_pullback_generic K T V U p q)) (@direct_cover_completion_restrict K T P V (@direct_cover_question_sieve K T V (@direct_cover_question_internal_pullback K T V U p q)) (@cover_retained_section K T P V U p q member m))
        (@cover_pulled_matching_restriction_path K T P V U p q member m))
      (@direct_cover_completion_silent_at K T P V (@direct_cover_question_sieve K T V (@direct_cover_question_internal_pullback K T V U p q)) (@direct_cover_question_cover K T V (@direct_cover_question_internal_pullback K T V U p q)) (@cover_retained_section K T P V U p q member m)));

// Canonical question projection retains the ordinary Yoneda action at p.
symbol cover_represented_pullback_path
  [K : Cat] (T : τ (@GrothTopology K)) [V U : τ (Obj K)]
  (p : τ (Hom K V U)) (q : τ (@DirectCoverQuestionData K T U))
  : τ (@= (Hom (@Psh_cat K) (@yoneda_psh K V) (@yoneda_psh K U)) (@fapp1_fapp0 (Op_cat (@DirectCoverQuestion_cat K T)) (@Psh_cat K) (@direct_cover_question_representable_func K T) (Struct_sigma V (@direct_cover_question_internal_pullback K T V U p q)) (Struct_sigma U q) (@direct_cover_question_pullback_arrow K T V U p q))
    (@fapp1_fapp0 K (@Psh_cat K) (@yoneda_psh_func K) V U p))
≔ @eq_refl (Hom (@Psh_cat K) (@yoneda_psh K V) (@yoneda_psh K U))
    (@fapp1_fapp0 K (@Psh_cat K) (@yoneda_psh_func K) V U p);

// Evaluate public presheaf composition through its existing whole comparison.
symbol psh_composition_value_path
  [K : Cat] [A B D : τ (@Psh K)]
  (g : τ (Hom (@Psh_cat K) B D)) (f : τ (Hom (@Psh_cat K) A B))
  (V : τ (Obj K)) (a : τ (Obj (@Fibre_cat (Op_cat K) A V)))
  : τ (@= (Obj (@Fibre_cat (Op_cat K) D V))
    (@fapp0 (@Fibre_cat (Op_cat K) A V) (@Fibre_cat (Op_cat K) D V)
      (@tapp0_fapp0 (Op_cat K) Cat_cat A D V (@comp_fapp0 (@Psh_cat K) A B D g f)) a)
    (@fapp0 (@Fibre_cat (Op_cat K) B V) (@Fibre_cat (Op_cat K) D V)
      (@tapp0_fapp0 (Op_cat K) Cat_cat B D V g)
      (@fapp0 (@Fibre_cat (Op_cat K) A V) (@Fibre_cat (Op_cat K) B V)
        (@tapp0_fapp0 (Op_cat K) Cat_cat A B V f) a)))
≔ @eq_ap (Hom (@Psh_cat K) A D) (Obj (@Fibre_cat (Op_cat K) D V))
    (λ z : τ (Hom (@Psh_cat K) A D),
      @fapp0 (@Fibre_cat (Op_cat K) A V) (@Fibre_cat (Op_cat K) D V)
        (@tapp0_fapp0 (Op_cat K) Cat_cat A D V z) a)
    (@comp_fapp0 (@Psh_cat K) A B D g f)
    (@comp_catd_fapp0 (Op_cat K) A B D g f)
    (@psh_comp_representation_agrees K A B D g f);

// Stage both existing raw-composition readings through the same stable head.
// This is a proof-time path on the same m and represented member, not a rule.
symbol cover_retained_section_presentation_path
  [K : Cat] (T : τ (@GrothTopology K)) (P : τ (@Psh K))
  [V U : τ (Obj K)] (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U))
  (member : τ (@SieveMembership K U (@direct_cover_question_sieve K T U q) (Struct_sigma V p)))
  (m : τ (Hom (@Psh_cat K) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P)))
  : τ (@= (Hom (@Psh_cat K) (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P)) (@cover_retained_section K T P V U p q member m) (@comp_fapp0 (@Psh_cat K) (@yoneda_psh K V) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P) m (@fib_cov_transf (Op_cat K) (@direct_cover_question_extension_psh K T U q) V (Struct_sigma p member))))
≔ @eq_trans (Hom (@Psh_cat K) (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P)) (@cover_retained_section K T P V U p q member m) (@hom_precomp_along_fapp0 (@Psh_cat K) (@Psh_cat K) (@id_func (@Psh_cat K)) (@DirectCoverCompletionPsh K T P) (@yoneda_psh K V) (@direct_cover_question_extension_psh K T U q) (@fib_cov_transf (Op_cat K) (@direct_cover_question_extension_psh K T U q) V (Struct_sigma p member)) m) (@comp_fapp0 (@Psh_cat K) (@yoneda_psh K V) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P) m (@fib_cov_transf (Op_cat K) (@direct_cover_question_extension_psh K T U q) V (Struct_sigma p member)))
    (@eq_refl (Hom (@Psh_cat K) (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P)) (@hom_precomp_along_fapp0 (@Psh_cat K) (@Psh_cat K) (@id_func (@Psh_cat K)) (@DirectCoverCompletionPsh K T P) (@yoneda_psh K V) (@direct_cover_question_extension_psh K T U q) (@fib_cov_transf (Op_cat K) (@direct_cover_question_extension_psh K T U q) V (Struct_sigma p member)) m))
    (@eq_refl (Hom (@Psh_cat K) (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P)) (@hom_precomp_along_fapp0 (@Psh_cat K) (@Psh_cat K) (@id_func (@Psh_cat K)) (@DirectCoverCompletionPsh K T P) (@yoneda_psh K V) (@direct_cover_question_extension_psh K T U q) (@fib_cov_transf (Op_cat K) (@direct_cover_question_extension_psh K T U q) V (Struct_sigma p member)) m));

// Identity evaluation of the retained composed section is m's literal value.
symbol cover_retained_section_value_path
  [K : Cat] (T : τ (@GrothTopology K)) (P : τ (@Psh K))
  [V U : τ (Obj K)] (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U))
  (member : τ (@SieveMembership K U (@direct_cover_question_sieve K T U q) (Struct_sigma V p)))
  (m : τ (Hom (@Psh_cat K) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P)))
  : τ (@= (Obj (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V)) (@fapp0 (@Hom_cat K V V) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P) V (@cover_retained_section K T P V U p q member m)) (@id K V)) (@fapp0 (@Fibre_cat (Op_cat K) (@direct_cover_question_extension_psh K T U q) V) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P) V m) (Struct_sigma p member)))
≔ @eq_trans (Obj (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V)) (@fapp0 (@Hom_cat K V V) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P) V (@cover_retained_section K T P V U p q member m)) (@id K V)) (@fapp0 (@Hom_cat K V V) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P) V (@comp_fapp0 (@Psh_cat K) (@yoneda_psh K V) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P) m (@fib_cov_transf (Op_cat K) (@direct_cover_question_extension_psh K T U q) V (Struct_sigma p member)))) (@id K V)) (@fapp0 (@Fibre_cat (Op_cat K) (@direct_cover_question_extension_psh K T U q) V) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P) V m) (Struct_sigma p member))
    (@eq_ap (Hom (@Psh_cat K) (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P)) (Obj (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V)) (λ z : τ (Hom (@Psh_cat K) (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P)), (@fapp0 (@Hom_cat K V V) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P) V z) (@id K V))) (@cover_retained_section K T P V U p q member m) (@comp_fapp0 (@Psh_cat K) (@yoneda_psh K V) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P) m (@fib_cov_transf (Op_cat K) (@direct_cover_question_extension_psh K T U q) V (Struct_sigma p member)))
      (@cover_retained_section_presentation_path K T P V U p q member m))
    (@psh_composition_value_path K (@yoneda_psh K V) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P) m (@fib_cov_transf (Op_cat K) (@direct_cover_question_extension_psh K T U q) V (Struct_sigma p member)) V (@id K V));

// Direct evaluation of the pulled glue section; no section naturality premise.
symbol cover_pulled_glue_value_path
  [K : Cat] (T : τ (@GrothTopology K)) (P : τ (@Psh K))
  [V U : τ (Obj K)] (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U))
  (m : τ (Hom (@Psh_cat K) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P)))
  : τ (@= (Obj (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V)) (@fapp0 (@Hom_cat K V V) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P) V (@comp_fapp0 (@Psh_cat K) (@yoneda_psh K V) (@yoneda_psh K U) (@DirectCoverCompletionPsh K T P) (@direct_cover_completion_glue K T P U (@direct_cover_question_sieve K T U q) (@direct_cover_question_cover K T U q) m) (@fapp1_fapp0 (Op_cat (@DirectCoverQuestion_cat K T)) (@Psh_cat K) (@direct_cover_question_representable_func K T) (Struct_sigma V (@direct_cover_question_internal_pullback K T V U p q)) (Struct_sigma U q) (@direct_cover_question_pullback_arrow K T V U p q)))) (@id K V)) (@fapp0 (@Hom_cat K V U) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@yoneda_psh K U) (@DirectCoverCompletionPsh K T P) V (@direct_cover_completion_glue K T P U (@direct_cover_question_sieve K T U q) (@direct_cover_question_cover K T U q) m)) p))
≔ @eq_trans (Obj (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V)) (@fapp0 (@Hom_cat K V V) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P) V (@comp_fapp0 (@Psh_cat K) (@yoneda_psh K V) (@yoneda_psh K U) (@DirectCoverCompletionPsh K T P) (@direct_cover_completion_glue K T P U (@direct_cover_question_sieve K T U q) (@direct_cover_question_cover K T U q) m) (@fapp1_fapp0 (Op_cat (@DirectCoverQuestion_cat K T)) (@Psh_cat K) (@direct_cover_question_representable_func K T) (Struct_sigma V (@direct_cover_question_internal_pullback K T V U p q)) (Struct_sigma U q) (@direct_cover_question_pullback_arrow K T V U p q)))) (@id K V)) (@fapp0 (@Hom_cat K V V) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P) V (@comp_fapp0 (@Psh_cat K) (@yoneda_psh K V) (@yoneda_psh K U) (@DirectCoverCompletionPsh K T P) (@direct_cover_completion_glue K T P U (@direct_cover_question_sieve K T U q) (@direct_cover_question_cover K T U q) m) (@fapp1_fapp0 K (@Psh_cat K) (@yoneda_psh_func K) V U p))) (@id K V)) (@fapp0 (@Hom_cat K V U) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@yoneda_psh K U) (@DirectCoverCompletionPsh K T P) V (@direct_cover_completion_glue K T P U (@direct_cover_question_sieve K T U q) (@direct_cover_question_cover K T U q) m)) p)
    (@eq_ap (Hom (@Psh_cat K) (@yoneda_psh K V) (@yoneda_psh K U)) (Obj (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V))
      (λ h : τ (Hom (@Psh_cat K) (@yoneda_psh K V) (@yoneda_psh K U)), (@fapp0 (@Hom_cat K V V) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P) V (@comp_fapp0 (@Psh_cat K) (@yoneda_psh K V) (@yoneda_psh K U) (@DirectCoverCompletionPsh K T P) (@direct_cover_completion_glue K T P U (@direct_cover_question_sieve K T U q) (@direct_cover_question_cover K T U q) m) h)) (@id K V)))
      (@fapp1_fapp0 (Op_cat (@DirectCoverQuestion_cat K T)) (@Psh_cat K) (@direct_cover_question_representable_func K T) (Struct_sigma V (@direct_cover_question_internal_pullback K T V U p q)) (Struct_sigma U q) (@direct_cover_question_pullback_arrow K T V U p q)) (@fapp1_fapp0 K (@Psh_cat K) (@yoneda_psh_func K) V U p)
      (@cover_represented_pullback_path K T V U p q))
    (@yoneda_precomposition_value_path K (@DirectCoverCompletionPsh K T P) V U p (@direct_cover_completion_glue K T P U (@direct_cover_question_sieve K T U q) (@direct_cover_question_cover K T U q) m));

// The whole retained-section path gives the literal glue/member value equation.
symbol cover_glue_retained_value_path
  [K : Cat] (T : τ (@GrothTopology K)) (P : τ (@Psh K))
  [V U : τ (Obj K)] (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U))
  (member : τ (@SieveMembership K U (@direct_cover_question_sieve K T U q) (Struct_sigma V p)))
  (m : τ (Hom (@Psh_cat K) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P)))
  : τ (@= (Obj (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V)) (@fapp0 (@Hom_cat K V U) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@yoneda_psh K U) (@DirectCoverCompletionPsh K T P) V (@direct_cover_completion_glue K T P U (@direct_cover_question_sieve K T U q) (@direct_cover_question_cover K T U q) m)) p) (@fapp0 (@Fibre_cat (Op_cat K) (@direct_cover_question_extension_psh K T U q) V) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P) V m) (Struct_sigma p member)))
≔ @eq_trans (Obj (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V)) (@fapp0 (@Hom_cat K V U) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@yoneda_psh K U) (@DirectCoverCompletionPsh K T P) V (@direct_cover_completion_glue K T P U (@direct_cover_question_sieve K T U q) (@direct_cover_question_cover K T U q) m)) p) (@fapp0 (@Hom_cat K V V) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P) V (@comp_fapp0 (@Psh_cat K) (@yoneda_psh K V) (@yoneda_psh K U) (@DirectCoverCompletionPsh K T P) (@direct_cover_completion_glue K T P U (@direct_cover_question_sieve K T U q) (@direct_cover_question_cover K T U q) m) (@fapp1_fapp0 (Op_cat (@DirectCoverQuestion_cat K T)) (@Psh_cat K) (@direct_cover_question_representable_func K T) (Struct_sigma V (@direct_cover_question_internal_pullback K T V U p q)) (Struct_sigma U q) (@direct_cover_question_pullback_arrow K T V U p q)))) (@id K V)) (@fapp0 (@Fibre_cat (Op_cat K) (@direct_cover_question_extension_psh K T U q) V) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P) V m) (Struct_sigma p member))
    (@eq_sym (Obj (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V)) (@fapp0 (@Hom_cat K V V) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P) V (@comp_fapp0 (@Psh_cat K) (@yoneda_psh K V) (@yoneda_psh K U) (@DirectCoverCompletionPsh K T P) (@direct_cover_completion_glue K T P U (@direct_cover_question_sieve K T U q) (@direct_cover_question_cover K T U q) m) (@fapp1_fapp0 (Op_cat (@DirectCoverQuestion_cat K T)) (@Psh_cat K) (@direct_cover_question_representable_func K T) (Struct_sigma V (@direct_cover_question_internal_pullback K T V U p q)) (Struct_sigma U q) (@direct_cover_question_pullback_arrow K T V U p q)))) (@id K V)) (@fapp0 (@Hom_cat K V U) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@yoneda_psh K U) (@DirectCoverCompletionPsh K T P) V (@direct_cover_completion_glue K T P U (@direct_cover_question_sieve K T U q) (@direct_cover_question_cover K T U q) m)) p)
      (@cover_pulled_glue_value_path K T P V U p q m))
    (@eq_trans (Obj (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V)) (@fapp0 (@Hom_cat K V V) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P) V (@comp_fapp0 (@Psh_cat K) (@yoneda_psh K V) (@yoneda_psh K U) (@DirectCoverCompletionPsh K T P) (@direct_cover_completion_glue K T P U (@direct_cover_question_sieve K T U q) (@direct_cover_question_cover K T U q) m) (@fapp1_fapp0 (Op_cat (@DirectCoverQuestion_cat K T)) (@Psh_cat K) (@direct_cover_question_representable_func K T) (Struct_sigma V (@direct_cover_question_internal_pullback K T V U p q)) (Struct_sigma U q) (@direct_cover_question_pullback_arrow K T V U p q)))) (@id K V)) (@fapp0 (@Hom_cat K V V) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P) V (@cover_retained_section K T P V U p q member m)) (@id K V)) (@fapp0 (@Fibre_cat (Op_cat K) (@direct_cover_question_extension_psh K T U q) V) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P) V m) (Struct_sigma p member))
      (@eq_ap (Hom (@Psh_cat K) (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P)) (Obj (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V))
        (λ z : τ (Hom (@Psh_cat K) (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P)), (@fapp0 (@Hom_cat K V V) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@yoneda_psh K V) (@DirectCoverCompletionPsh K T P) V z) (@id K V)))
        (@comp_fapp0 (@Psh_cat K) (@yoneda_psh K V) (@yoneda_psh K U) (@DirectCoverCompletionPsh K T P) (@direct_cover_completion_glue K T P U (@direct_cover_question_sieve K T U q) (@direct_cover_question_cover K T U q) m) (@fapp1_fapp0 (Op_cat (@DirectCoverQuestion_cat K T)) (@Psh_cat K) (@direct_cover_question_representable_func K T) (Struct_sigma V (@direct_cover_question_internal_pullback K T V U p q)) (Struct_sigma U q) (@direct_cover_question_pullback_arrow K T V U p q))) (@cover_retained_section K T P V U p q member m)
        (@cover_whole_retained_section_path K T P V U p q member m))
      (@cover_retained_section_value_path K T P V U p q member m));

// Conventional restriction-after-glue endofunctor at one eligible question.
symbol cover_restriction_glue_func
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  [U : τ (@Obj K)]
  (q : τ (@DirectCoverQuestionData K T U))
  : τ (@Functor
      (@DirectCoverMatching_cat
        K U (@direct_cover_question_sieve K T U q)
        (@DirectCoverCompletionPsh K T P))
      (@DirectCoverMatching_cat
        K U (@direct_cover_question_sieve K T U q)
        (@DirectCoverCompletionPsh K T P)))
≔ @comp_cat_fapp0
    (@DirectCoverMatching_cat
      K U (@direct_cover_question_sieve K T U q)
      (@DirectCoverCompletionPsh K T P))
    (@DirectCoverSection_cat K U (@DirectCoverCompletionPsh K T P))
    (@DirectCoverMatching_cat
      K U (@direct_cover_question_sieve K T U q)
      (@DirectCoverCompletionPsh K T P))
    (@ordinary_sieve_local_precomp
      K U
      (@direct_cover_question_sieve K T U q)
      (@DirectCoverCompletionPsh K T P))
    (@direct_cover_completion_glue_func
      K T P U
      (@direct_cover_question_sieve K T U q)
      (@direct_cover_question_cover K T U q));

// Matching map selected by restriction after glue.
symbol cover_restriction_glue_matching
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  [U : τ (@Obj K)]
  (q : τ (@DirectCoverQuestionData K T U))
  (m : τ (Hom
      (@Psh_cat K)
      (@direct_cover_question_extension_psh K T U q)
      (@DirectCoverCompletionPsh K T P)))
  : τ (Hom
      (@Psh_cat K)
      (@direct_cover_question_extension_psh K T U q)
      (@DirectCoverCompletionPsh K T P))
≔ @fapp0
    (@DirectCoverMatching_cat
      K U (@direct_cover_question_sieve K T U q)
      (@DirectCoverCompletionPsh K T P))
    (@DirectCoverMatching_cat
      K U (@direct_cover_question_sieve K T U q)
      (@DirectCoverCompletionPsh K T P))
    (@cover_restriction_glue_func K T P U q)
    m;


// Read the original restriction/glue endpoint via the existing facade path.
symbol cover_restriction_glue_value_path
  [K : Cat] (T : τ (@GrothTopology K)) (P : τ (@Psh K))
  [V U : τ (Obj K)] (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U))
  (member : τ (@SieveMembership K U (@direct_cover_question_sieve K T U q) (Struct_sigma V p)))
  (m : τ (Hom (@Psh_cat K) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P)))
  : τ (@= (Obj (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V)) (@fapp0 (@Fibre_cat (Op_cat K) (@direct_cover_question_extension_psh K T U q) V) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P) V (@cover_restriction_glue_matching K T P U q m)) (Struct_sigma p member)) (@fapp0 (@Hom_cat K V U) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@yoneda_psh K U) (@DirectCoverCompletionPsh K T P) V (@direct_cover_completion_glue K T P U (@direct_cover_question_sieve K T U q) (@direct_cover_question_cover K T U q) m)) p))
≔ @eq_trans (Obj (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V)) (@fapp0 (@Fibre_cat (Op_cat K) (@direct_cover_question_extension_psh K T U q) V) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P) V (@cover_restriction_glue_matching K T P U q m)) (Struct_sigma p member)) (@fapp0 (@Fibre_cat (Op_cat K) (@direct_cover_question_extension_psh K T U q) V) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P) V (@comp_fapp0 (@Psh_cat K) (@direct_cover_question_extension_psh K T U q) (@yoneda_psh K U) (@DirectCoverCompletionPsh K T P) (@direct_cover_completion_glue K T P U (@direct_cover_question_sieve K T U q) (@direct_cover_question_cover K T U q) m) (@direct_cover_question_extension_inclusion K T U q))) (Struct_sigma p member)) (@fapp0 (@Hom_cat K V U) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@yoneda_psh K U) (@DirectCoverCompletionPsh K T P) V (@direct_cover_completion_glue K T P U (@direct_cover_question_sieve K T U q) (@direct_cover_question_cover K T U q) m)) p)
    (@eq_ap (Hom (@Psh_cat K) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P)) (Obj (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V))
      (λ z : τ (Hom (@Psh_cat K) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P)), (@fapp0 (@Fibre_cat (Op_cat K) (@direct_cover_question_extension_psh K T U q) V) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P) V z) (Struct_sigma p member)))
      (@cover_restriction_glue_matching K T P U q m) (@comp_fapp0 (@Psh_cat K) (@direct_cover_question_extension_psh K T U q) (@yoneda_psh K U) (@DirectCoverCompletionPsh K T P) (@direct_cover_completion_glue K T P U (@direct_cover_question_sieve K T U q) (@direct_cover_question_cover K T U q) m) (@direct_cover_question_extension_inclusion K T U q))
      (@eq_refl (Hom (@Psh_cat K) (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P)) (@cover_restriction_glue_matching K T P U q m)))
    (@psh_composition_value_path K (@direct_cover_question_extension_psh K T U q) (@yoneda_psh K U) (@DirectCoverCompletionPsh K T P) (@direct_cover_completion_glue K T P U (@direct_cover_question_sieve K T U q) (@direct_cover_question_cover K T U q) m) (@direct_cover_question_extension_inclusion K T U q) V (Struct_sigma p member));

// Exact original retained-member statement, with no added premise.
symbol cover_retained_member_path
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  [V U : τ (@Obj K)]
  (p : τ (@Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U))
  (member : τ (@SieveMembership
      K U (@direct_cover_question_sieve K T U q) (Struct_sigma V p)))
  (m : τ (Hom
      (@Psh_cat K)
      (@direct_cover_question_extension_psh K T U q)
      (@DirectCoverCompletionPsh K T P)))
  : τ (@=
      (Obj (@Fibre_cat
        (Op_cat K) (@DirectCoverCompletionPsh K T P) V))
      (@fapp0
        (@Fibre_cat
          (Op_cat K)
          (@direct_cover_question_extension_psh K T U q)
          V)
        (@Fibre_cat
          (Op_cat K) (@DirectCoverCompletionPsh K T P) V)
        (@tapp0_fapp0
          (Op_cat K) Cat_cat
          (@direct_cover_question_extension_psh K T U q)
          (@DirectCoverCompletionPsh K T P)
          V
          (@cover_restriction_glue_matching
            K T P U q m))
        (Struct_sigma p member))
      (@fapp0
        (@Fibre_cat
          (Op_cat K)
          (@direct_cover_question_extension_psh K T U q)
          V)
        (@Fibre_cat
          (Op_cat K) (@DirectCoverCompletionPsh K T P) V)
        (@tapp0_fapp0
          (Op_cat K) Cat_cat
          (@direct_cover_question_extension_psh K T U q)
          (@DirectCoverCompletionPsh K T P)
          V m)
        (Struct_sigma p member)))
≔ @eq_trans (Obj (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V)) (@fapp0 (@Fibre_cat (Op_cat K) (@direct_cover_question_extension_psh K T U q) V) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P) V (@cover_restriction_glue_matching K T P U q m)) (Struct_sigma p member)) (@fapp0 (@Hom_cat K V U) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@yoneda_psh K U) (@DirectCoverCompletionPsh K T P) V (@direct_cover_completion_glue K T P U (@direct_cover_question_sieve K T U q) (@direct_cover_question_cover K T U q) m)) p) (@fapp0 (@Fibre_cat (Op_cat K) (@direct_cover_question_extension_psh K T U q) V) (@Fibre_cat (Op_cat K) (@DirectCoverCompletionPsh K T P) V) (@tapp0_fapp0 (Op_cat K) Cat_cat (@direct_cover_question_extension_psh K T U q) (@DirectCoverCompletionPsh K T P) V m) (Struct_sigma p member))
    (@cover_restriction_glue_value_path K T P V U p q member m)
    (@cover_glue_retained_value_path K T P V U p q member m);
