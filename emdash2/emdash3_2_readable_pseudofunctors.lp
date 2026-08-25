/*
  Emdash v3.2: readable pseudofunctor profiles over ambient functor carriers.

  The active generic functor/transfor calculus exposes normal-lax compositor
  cells at formal internal-action endpoints. Consumers such as intrinsic
  cubical arrows require an invertible compositor at the two stable readable
  cut presentations retained by ordinary post- and precomposition.

  ReadablePseudoFunctorProfile is an abstract coherent capability indexed by
  its already-existing Functor carrier. IsoEvidence supplies both directions
  and their cancellation paths. Unit/pentagon/triangle coherence is part of
  the capability boundary; only the observations selected by current
  consumers are exposed here. This adds no rewrite or proof-time unifier.

  This capability is evidence over an already-existing ambient Functor; it is
  not a separate lax-carrier classifier and does not disable the historical
  global strict cuts. Conversely, those temporary cuts must not be used to
  veto an intended lax consumer beta that otherwise passes its owner and
  subject-reduction checks; their migration remains profile-local future work.
*/

require open emdash.emdash3_2;

// Coherent readable pseudofunctor capability for one ambient carrier.
injective symbol ReadablePseudoFunctorProfile
  [A B : Cat]
  (F : τ (Functor A B))
  : Grpd;

// Readable unit comparison id_(F[X]) ~= F[id_X].
injective symbol readable_pseudo_unitor
  [A B : Cat]
  [F : τ (Functor A B)]
  (P : τ (@ReadablePseudoFunctorProfile A B F))
  (X : τ (Obj A))
  : τ (@IsoEvidence
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F X))
      (@id B (@fapp0 A B F X))
      (@fapp1_fapp0 A B F X X (@id A X)));

// Post/left readable compositor:
//   F[g] o F[f] ~= F[g o f]
// at the stable hom_postcomp owner used by source-varying hom families.
injective symbol readable_pseudo_post_compositor
  [A B : Cat]
  [F : τ (Functor A B)]
  (P : τ (@ReadablePseudoFunctorProfile A B F))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
  : τ (@IsoEvidence
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
      (@hom_postcomp_fapp0
        B B (@id_func B)
        (@fapp0 A B F X)
        (@fapp0 A B F Y)
        (@fapp0 A B F Z)
        (@fapp1_fapp0 A B F Y Z g)
        (@fapp1_fapp0 A B F X Y f))
      (@fapp1_fapp0 A B F X Z
        (@comp_fapp0 A X Y Z g f)));

// Pre/right readable view of the same pseudofunctor compositor. The separate
// stable endpoint is intentional: the kernel preserves the two cut histories.
injective symbol readable_pseudo_pre_compositor
  [A B : Cat]
  [F : τ (Functor A B)]
  (P : τ (@ReadablePseudoFunctorProfile A B F))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
  : τ (@IsoEvidence
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
      (@hom_precomp_along_fapp0
        B B (@id_func B)
        (@fapp0 B B (@id_func B) (@fapp0 A B F Z))
        (@fapp0 A B F X)
        (@fapp0 A B F Y)
        (@fapp1_fapp0 A B F X Y f)
        (@fapp1_fapp0 A B F Y Z g))
      (@fapp1_fapp0 A B F X Z
        (@comp_fapp0 A X Y Z g f)));

// Selected coherent profiles are closed under identity and composition.
constant symbol readable_pseudo_identity_profile
  (A : Cat)
  : τ (@ReadablePseudoFunctorProfile A A (@id_func A));

constant symbol readable_pseudo_comp_profile
  [A B C : Cat]
  [F : τ (Functor A B)]
  (PF : τ (@ReadablePseudoFunctorProfile A B F))
  [G : τ (Functor B C)]
  (PG : τ (@ReadablePseudoFunctorProfile B C G))
  : τ (@ReadablePseudoFunctorProfile
      A C (@comp_cat_fapp0 A B C G F));
