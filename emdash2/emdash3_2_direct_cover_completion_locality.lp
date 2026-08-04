/*
  Conventional covering-sieve locality of the direct cover-completion HIT.

  The HIT already carries one whole internal glue operation and the silent
  law

    glue o restriction = id_Section.

  The retained-member calculation below derives the opposite composite from
  those constructors and canonical cover pullback.  One rigid projection
  tower then owns the whole transformation

    rho : restriction o glue => id_Matching,

  whose final component is the arrow induced by that derived path.  Generic
  strict pointwise-to-whole closure produces the second functor equality and
  hence the existing `PshLocalAtOrdinarySieve` interface.

  No component naturality square is an input.  No endpoint presentation is
  selected as a new runtime normal form, and no generic functor extensionality
  or category-of-elements retraction is assumed.
*/

require open emdash.emdash3_2_direct_cover_completion_hit;
require open emdash.emdash3_2_strict_pointwise_equivalences;

// Conventional restriction-after-glue endofunctor at one eligible question.
symbol direct_cover_completion_restriction_glue_func
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
symbol direct_cover_completion_restriction_glue_matching
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
    (@direct_cover_completion_restriction_glue_func K T P U q)
    m;

/*
  Derived retained-member theorem:

    restriction(glue(m))[V](p,member) = m[V](p,member).

  The proof is the internally indexed composite of canonical extension
  factorization, whole matching naturality, glue pullback, and silent at the
  pulled question.  Its endpoint derivation and non-collapse controls are
  recorded in the computational-schemes living plan and the focused
  psss12zzx/zza probes.  Equality proof terms carry no runtime section data,
  so the active library retains this exact theorem as one opaque proof owner;
  all computational observations below project from the whole `rho` owner.
*/
constant symbol direct_cover_completion_restriction_glue_retained_agrees
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
          (@direct_cover_completion_restriction_glue_matching
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
        (Struct_sigma p member)));

// Whole transformation carrying the conventional second inverse internally.
injective symbol direct_cover_completion_restriction_glue_transf
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  [U : τ (@Obj K)]
  (q : τ (@DirectCoverQuestionData K T U))
  : τ (@Transf
      (@DirectCoverMatching_cat
        K U (@direct_cover_question_sieve K T U q)
        (@DirectCoverCompletionPsh K T P))
      (@DirectCoverMatching_cat
        K U (@direct_cover_question_sieve K T U q)
        (@DirectCoverCompletionPsh K T P))
      (@direct_cover_completion_restriction_glue_func K T P U q)
      (@id
        Cat_cat
        (@DirectCoverMatching_cat
          K U (@direct_cover_question_sieve K T U q)
          (@DirectCoverCompletionPsh K T P))));

// Whole matching-map component of rho.
injective symbol direct_cover_completion_restriction_glue_transfd
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  [U : τ (@Obj K)]
  (q : τ (@DirectCoverQuestionData K T U))
  (m : τ (Hom
      (@Psh_cat K)
      (@direct_cover_question_extension_psh K T U q)
      (@DirectCoverCompletionPsh K T P)))
  : τ (@Transfd
      (Op_cat K)
      (@direct_cover_question_extension_psh K T U q)
      (@DirectCoverCompletionPsh K T P)
      (@direct_cover_completion_restriction_glue_matching K T P U q m)
      m);

rule @tapp0_fapp0 _ _ _ _ $m
      (@direct_cover_completion_restriction_glue_transf $K $T $P $U $q)
  ↪ @direct_cover_completion_restriction_glue_transfd
      $K $T $P $U $q $m;

// Whole component transformation in one selected fibre.
injective symbol direct_cover_completion_restriction_glue_fibre_transf
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  [V U : τ (@Obj K)]
  (q : τ (@DirectCoverQuestionData K T U))
  (m : τ (Hom
      (@Psh_cat K)
      (@direct_cover_question_extension_psh K T U q)
      (@DirectCoverCompletionPsh K T P)))
  : τ (@Transf
      (@Fibre_cat
        (Op_cat K)
        (@direct_cover_question_extension_psh K T U q)
        V)
      (@Fibre_cat
        (Op_cat K) (@DirectCoverCompletionPsh K T P) V)
      (@Fibre_func
        (Op_cat K)
        (@direct_cover_question_extension_psh K T U q)
        (@DirectCoverCompletionPsh K T P)
        (@direct_cover_completion_restriction_glue_matching K T P U q m)
        V)
      (@Fibre_func
        (Op_cat K)
        (@direct_cover_question_extension_psh K T U q)
        (@DirectCoverCompletionPsh K T P)
        m V));

rule @tdapp0_fapp0 _ _ _ _ _ $V
      (@direct_cover_completion_restriction_glue_transfd
        $K $T $P $U $q $m)
  ↪ @direct_cover_completion_restriction_glue_fibre_transf
      $K $T $P $V $U $q $m;

// Final projection: the retained member computes to the arrow induced by the
// derived literal component path.
rule @tapp0_fapp0 _ _ _ _ (Struct_sigma $p $member)
      (@direct_cover_completion_restriction_glue_fibre_transf
        $K $T $P $V $U $q $m)
  ↪ @path_to_hom
      (@Fibre_cat
        (Op_cat $K) (@DirectCoverCompletionPsh $K $T $P) $V)
      (@fapp0
        (@Fibre_cat
          (Op_cat $K)
          (@direct_cover_question_extension_psh $K $T $U $q)
          $V)
        (@Fibre_cat
          (Op_cat $K) (@DirectCoverCompletionPsh $K $T $P) $V)
        (@tapp0_fapp0
          (Op_cat $K) Cat_cat
          (@direct_cover_question_extension_psh $K $T $U $q)
          (@DirectCoverCompletionPsh $K $T $P)
          $V
          (@direct_cover_completion_restriction_glue_matching
            $K $T $P $U $q $m))
        (Struct_sigma $p $member))
      (@fapp0
        (@Fibre_cat
          (Op_cat $K)
          (@direct_cover_question_extension_psh $K $T $U $q)
          $V)
        (@Fibre_cat
          (Op_cat $K) (@DirectCoverCompletionPsh $K $T $P) $V)
        (@tapp0_fapp0
          (Op_cat $K) Cat_cat
          (@direct_cover_question_extension_psh $K $T $U $q)
          (@DirectCoverCompletionPsh $K $T $P)
          $V $m)
        (Struct_sigma $p $member))
      (@direct_cover_completion_restriction_glue_retained_agrees
        $K $T $P $V $U $p $q $member $m);

// Every retained-member component of rho is a fixed-forward equivalence.
symbol direct_cover_completion_restriction_glue_member_omega
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
  : τ (@OmegaEquivAlong
      (@Fibre_cat
        (Op_cat K) (@DirectCoverCompletionPsh K T P) V)
      (@fapp0
        (@Fibre_cat
          (Op_cat K)
          (@direct_cover_question_extension_psh K T U q)
          V)
        (@Fibre_cat
          (Op_cat K) (@DirectCoverCompletionPsh K T P) V)
        (@Fibre_func
          (Op_cat K)
          (@direct_cover_question_extension_psh K T U q)
          (@DirectCoverCompletionPsh K T P)
          (@direct_cover_completion_restriction_glue_matching K T P U q m)
          V)
        (Struct_sigma p member))
      (@fapp0
        (@Fibre_cat
          (Op_cat K)
          (@direct_cover_question_extension_psh K T U q)
          V)
        (@Fibre_cat
          (Op_cat K) (@DirectCoverCompletionPsh K T P) V)
        (@Fibre_func
          (Op_cat K)
          (@direct_cover_question_extension_psh K T U q)
          (@DirectCoverCompletionPsh K T P)
          m V)
        (Struct_sigma p member))
      (@tapp0_fapp0
        (@Fibre_cat
          (Op_cat K)
          (@direct_cover_question_extension_psh K T U q)
          V)
        (@Fibre_cat
          (Op_cat K) (@DirectCoverCompletionPsh K T P) V)
        (@Fibre_func
          (Op_cat K)
          (@direct_cover_question_extension_psh K T U q)
          (@DirectCoverCompletionPsh K T P)
          (@direct_cover_completion_restriction_glue_matching K T P U q m)
          V)
        (@Fibre_func
          (Op_cat K)
          (@direct_cover_question_extension_psh K T U q)
          (@DirectCoverCompletionPsh K T P)
          m V)
        (Struct_sigma p member)
        (@direct_cover_completion_restriction_glue_fibre_transf
          K T P V U q m)))
≔ @object_path_equiv_along
    (@Fibre_cat
      (Op_cat K) (@DirectCoverCompletionPsh K T P) V)
    (@fapp0
      (@Fibre_cat
        (Op_cat K)
        (@direct_cover_question_extension_psh K T U q)
        V)
      (@Fibre_cat
        (Op_cat K) (@DirectCoverCompletionPsh K T P) V)
      (@Fibre_func
        (Op_cat K)
        (@direct_cover_question_extension_psh K T U q)
        (@DirectCoverCompletionPsh K T P)
        (@direct_cover_completion_restriction_glue_matching K T P U q m)
        V)
      (Struct_sigma p member))
    (@fapp0
      (@Fibre_cat
        (Op_cat K)
        (@direct_cover_question_extension_psh K T U q)
        V)
      (@Fibre_cat
        (Op_cat K) (@DirectCoverCompletionPsh K T P) V)
      (@Fibre_func
        (Op_cat K)
        (@direct_cover_question_extension_psh K T U q)
        (@DirectCoverCompletionPsh K T P)
        m V)
      (Struct_sigma p member))
    (@direct_cover_completion_restriction_glue_retained_agrees
      K T P V U p q member m);

// Pointwise evidence over the internal retained-member Sigma.
injective symbol direct_cover_completion_restriction_glue_fibre_pointwise_omega
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  [V U : τ (@Obj K)]
  (q : τ (@DirectCoverQuestionData K T U))
  (m : τ (Hom
      (@Psh_cat K)
      (@direct_cover_question_extension_psh K T U q)
      (@DirectCoverCompletionPsh K T P)))
  : τ (@StrictTransfPointwiseOmegaAlong
      (@Fibre_cat
        (Op_cat K)
        (@direct_cover_question_extension_psh K T U q)
        V)
      (@Fibre_cat
        (Op_cat K) (@DirectCoverCompletionPsh K T P) V)
      (@Fibre_func
        (Op_cat K)
        (@direct_cover_question_extension_psh K T U q)
        (@DirectCoverCompletionPsh K T P)
        (@direct_cover_completion_restriction_glue_matching K T P U q m)
        V)
      (@Fibre_func
        (Op_cat K)
        (@direct_cover_question_extension_psh K T U q)
        (@DirectCoverCompletionPsh K T P)
        m V)
      (@direct_cover_completion_restriction_glue_fibre_transf
        K T P V U q m));

rule (@direct_cover_completion_restriction_glue_fibre_pointwise_omega
        $K $T $P $V $U $q $m)
      (Struct_sigma $p $member)
  ↪ @direct_cover_completion_restriction_glue_member_omega
      $K $T $P $V $U $p $q $member $m;

// Whole equivalence of the two fibre functors.
symbol direct_cover_completion_restriction_glue_fibre_omega
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  [V U : τ (@Obj K)]
  (q : τ (@DirectCoverQuestionData K T U))
  (m : τ (Hom
      (@Psh_cat K)
      (@direct_cover_question_extension_psh K T U q)
      (@DirectCoverCompletionPsh K T P)))
  : τ (@OmegaEquivAlong
      (@Functor_cat
        (@Fibre_cat
          (Op_cat K)
          (@direct_cover_question_extension_psh K T U q)
          V)
        (@Fibre_cat
          (Op_cat K) (@DirectCoverCompletionPsh K T P) V))
      (@Fibre_func
        (Op_cat K)
        (@direct_cover_question_extension_psh K T U q)
        (@DirectCoverCompletionPsh K T P)
        (@direct_cover_completion_restriction_glue_matching K T P U q m)
        V)
      (@Fibre_func
        (Op_cat K)
        (@direct_cover_question_extension_psh K T U q)
        (@DirectCoverCompletionPsh K T P)
        m V)
      (@direct_cover_completion_restriction_glue_fibre_transf
        K T P V U q m))
≔ @strict_transf_pointwise_omega_along
    (@Fibre_cat
      (Op_cat K)
      (@direct_cover_question_extension_psh K T U q)
      V)
    (@Fibre_cat
      (Op_cat K) (@DirectCoverCompletionPsh K T P) V)
    (@Fibre_func
      (Op_cat K)
      (@direct_cover_question_extension_psh K T U q)
      (@DirectCoverCompletionPsh K T P)
      (@direct_cover_completion_restriction_glue_matching K T P U q m)
      V)
    (@Fibre_func
      (Op_cat K)
      (@direct_cover_question_extension_psh K T U q)
      (@DirectCoverCompletionPsh K T P)
      m V)
    (@direct_cover_completion_restriction_glue_fibre_transf
      K T P V U q m)
    (@direct_cover_completion_restriction_glue_fibre_pointwise_omega
      K T P V U q m);

// Fibrewise whole equivalences are the pointwise evidence for rho[m].
symbol direct_cover_completion_restriction_glue_transfd_pointwise_omega
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  [U : τ (@Obj K)]
  (q : τ (@DirectCoverQuestionData K T U))
  (m : τ (Hom
      (@Psh_cat K)
      (@direct_cover_question_extension_psh K T U q)
      (@DirectCoverCompletionPsh K T P)))
  : τ (@StrictTransfdPointwiseOmegaAlong
      (Op_cat K)
      (@direct_cover_question_extension_psh K T U q)
      (@DirectCoverCompletionPsh K T P)
      (@direct_cover_completion_restriction_glue_matching K T P U q m)
      m
      (@direct_cover_completion_restriction_glue_transfd K T P U q m))
≔ λ V : τ (@Obj K),
    @direct_cover_completion_restriction_glue_fibre_omega
      K T P V U q m;

// Whole equivalence of the two displayed matching maps.
symbol direct_cover_completion_restriction_glue_transfd_omega
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  [U : τ (@Obj K)]
  (q : τ (@DirectCoverQuestionData K T U))
  (m : τ (Hom
      (@Psh_cat K)
      (@direct_cover_question_extension_psh K T U q)
      (@DirectCoverCompletionPsh K T P)))
  : τ (@OmegaEquivAlong
      (@Functord_cat
        (Op_cat K)
        (@direct_cover_question_extension_psh K T U q)
        (@DirectCoverCompletionPsh K T P))
      (@direct_cover_completion_restriction_glue_matching K T P U q m)
      m
      (@direct_cover_completion_restriction_glue_transfd K T P U q m))
≔ @strict_transfd_pointwise_omega_along
    (Op_cat K)
    (@direct_cover_question_extension_psh K T U q)
    (@DirectCoverCompletionPsh K T P)
    (@direct_cover_completion_restriction_glue_matching K T P U q m)
    m
    (@direct_cover_completion_restriction_glue_transfd K T P U q m)
    (@direct_cover_completion_restriction_glue_transfd_pointwise_omega
      K T P U q m);

// Every matching-map component of rho is a whole displayed equivalence.
symbol direct_cover_completion_restriction_glue_pointwise_omega
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  [U : τ (@Obj K)]
  (q : τ (@DirectCoverQuestionData K T U))
  : τ (@StrictTransfPointwiseOmegaAlong
      (@DirectCoverMatching_cat
        K U (@direct_cover_question_sieve K T U q)
        (@DirectCoverCompletionPsh K T P))
      (@DirectCoverMatching_cat
        K U (@direct_cover_question_sieve K T U q)
        (@DirectCoverCompletionPsh K T P))
      (@direct_cover_completion_restriction_glue_func K T P U q)
      (@id
        Cat_cat
        (@DirectCoverMatching_cat
          K U (@direct_cover_question_sieve K T U q)
          (@DirectCoverCompletionPsh K T P)))
      (@direct_cover_completion_restriction_glue_transf K T P U q))
≔ λ m : τ (Hom
      (@Psh_cat K)
      (@direct_cover_question_extension_psh K T U q)
      (@DirectCoverCompletionPsh K T P)),
    @direct_cover_completion_restriction_glue_transfd_omega
      K T P U q m;

// Whole fixed-forward equivalence between the matching endofunctors.
symbol direct_cover_completion_restriction_glue_omega
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  [U : τ (@Obj K)]
  (q : τ (@DirectCoverQuestionData K T U))
  : τ (@OmegaEquivAlong
      (@Functor_cat
        (@DirectCoverMatching_cat
          K U (@direct_cover_question_sieve K T U q)
          (@DirectCoverCompletionPsh K T P))
        (@DirectCoverMatching_cat
          K U (@direct_cover_question_sieve K T U q)
          (@DirectCoverCompletionPsh K T P)))
      (@direct_cover_completion_restriction_glue_func K T P U q)
      (@id
        Cat_cat
        (@DirectCoverMatching_cat
          K U (@direct_cover_question_sieve K T U q)
          (@DirectCoverCompletionPsh K T P)))
      (@direct_cover_completion_restriction_glue_transf K T P U q))
≔ @strict_transf_pointwise_omega_along
    (@DirectCoverMatching_cat
      K U (@direct_cover_question_sieve K T U q)
      (@DirectCoverCompletionPsh K T P))
    (@DirectCoverMatching_cat
      K U (@direct_cover_question_sieve K T U q)
      (@DirectCoverCompletionPsh K T P))
    (@direct_cover_completion_restriction_glue_func K T P U q)
    (@id
      Cat_cat
      (@DirectCoverMatching_cat
        K U (@direct_cover_question_sieve K T U q)
        (@DirectCoverCompletionPsh K T P)))
    (@direct_cover_completion_restriction_glue_transf K T P U q)
    (@direct_cover_completion_restriction_glue_pointwise_omega K T P U q);

// Conventional second-inverse equation selected from the whole equivalence.
symbol direct_cover_completion_restriction_glue_path
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  [U : τ (@Obj K)]
  (q : τ (@DirectCoverQuestionData K T U))
  : τ (@=
      (Obj (@Functor_cat
        (@DirectCoverMatching_cat
          K U (@direct_cover_question_sieve K T U q)
          (@DirectCoverCompletionPsh K T P))
        (@DirectCoverMatching_cat
          K U (@direct_cover_question_sieve K T U q)
          (@DirectCoverCompletionPsh K T P))))
      (@direct_cover_completion_restriction_glue_func K T P U q)
      (@id
        Cat_cat
        (@DirectCoverMatching_cat
          K U (@direct_cover_question_sieve K T U q)
          (@DirectCoverCompletionPsh K T P))))
≔ @strict_transf_pointwise_path
    (@DirectCoverMatching_cat
      K U (@direct_cover_question_sieve K T U q)
      (@DirectCoverCompletionPsh K T P))
    (@DirectCoverMatching_cat
      K U (@direct_cover_question_sieve K T U q)
      (@DirectCoverCompletionPsh K T P))
    (@direct_cover_completion_restriction_glue_func K T P U q)
    (@id
      Cat_cat
      (@DirectCoverMatching_cat
        K U (@direct_cover_question_sieve K T U q)
        (@DirectCoverCompletionPsh K T P)))
    (@direct_cover_completion_restriction_glue_transf K T P U q)
    (@direct_cover_completion_restriction_glue_pointwise_omega K T P U q);

// Conventional locality at one internal eligible question.
symbol direct_cover_completion_local_at_question
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  [U : τ (@Obj K)]
  (q : τ (@DirectCoverQuestionData K T U))
  : τ (@PshLocalAtOrdinarySieve
      K U
      (@direct_cover_question_sieve K T U q)
      (@DirectCoverCompletionPsh K T P))
≔ @omega_equiv_along_intro
    Cat_cat
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
      (@direct_cover_question_cover K T U q))
    (@direct_cover_completion_glue_func
      K T P U
      (@direct_cover_question_sieve K T U q)
      (@direct_cover_question_cover K T U q))
    (@direct_cover_completion_silent
      K T P U
      (@direct_cover_question_sieve K T U q)
      (@direct_cover_question_cover K T U q))
    (@direct_cover_completion_restriction_glue_path K T P U q);

// The direct cover-completion HIT is local for every ordinary covering sieve.
symbol direct_cover_completion_is_topology_local
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  : τ (@IsTopologyLocalPsh K T (@DirectCoverCompletionPsh K T P))
≔ λ U : τ (@Obj K),
    λ R : τ (@Sieve K U),
      λ covers : τ (@groth_topology_covers K T U R),
        @direct_cover_completion_local_at_question
          K T P U (Struct_sigma R covers);
