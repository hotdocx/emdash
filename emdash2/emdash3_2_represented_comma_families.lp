/* Native represented-comma classification of a whole internal Hom action.
   The shared graph accepts Θ:Hom_K(−,−)⇒Hom_Y(JA−,D−). The original Γ
   interface supplies the native Hom action of h:J∘A⇒D. No objectwise square
   is caller data. Both interfaces retain the same projection inverse data.
   Protected helpers retain the original internal graph derivation. The whole
   target comparison is qualified for OneCat(Y); higher Op/profile repair
   remains outside this module. All declarations here are definitions. */

require open emdash.emdash3_2_gray_transformation_graph;

require open emdash.emdash3_2_zero_arrow_cones;

require open emdash.emdash3_2_iso_evidence_constructors;

require open emdash.emdash3_2_one_cat_adjunction_family_views;

require open emdash.emdash3_2_strict_pointwise_equivalences;

require open emdash.emdash3_2_omega_equiv_composition;

require open emdash.emdash3_2_transfor_whiskering;

// Source, middle, and target families for a transformation graph.
protected symbol comma_graph_source_raw_catd
  [B : Cat]
  : τ (Catd (Op_cat B))
≔ @homdc_edge_catd
    B B (@hom_int B B (@id_func B));

protected symbol comma_graph_source_catd
  [B : Cat]
  : τ (Catd (Op_cat B))
≔ @hom_identity_graph_catd B;

protected symbol comma_graph_middle_inner_catd
  [B C : Cat]
  (F G : τ (Functor B C))
  : τ (Functor (Op_cat B) (@Catd_cat B))
≔ @comp_cat_fapp0
    (Op_cat B)
    (Op_cat C)
    (@Catd_cat B)
    (@hom_int C B G)
    (@Op_func B C F);

protected symbol comma_graph_middle_raw_catd
  [B C : Cat]
  (F G : τ (Functor B C))
  : τ (Catd (Op_cat B))
≔ @comp_cat_fapp0
    (Op_cat B)
    (@Catd_cat B)
    Cat_cat
    (@Sigma_func B)
    (@comma_graph_middle_inner_catd B C F G);

protected symbol comma_graph_middle_catd
  [B C : Cat]
  (F G : τ (Functor B C))
  : τ (Catd (Op_cat B))
≔ @Op_catd
    (Op_cat B)
    (@comma_graph_middle_raw_catd B C F G);

protected symbol comma_graph_target_base_catd
  [C : Cat]
  : τ (Catd (Op_cat C))
≔ @homdc_op_edge_catd
    C C (@hom_int C C (@id_func C));

protected symbol comma_graph_target_catd
  [B C : Cat]
  (F : τ (Functor B C))
  : τ (Catd (Op_cat B))
≔ @Pullback_catd
    (Op_cat B)
    (Op_cat C)
    (@comma_graph_target_base_catd C)
    (@Op_func B C F);

// Fibrewise Sigma of the existing whole internal action.
protected symbol comma_graph_sigma_transf
  [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (@Transf (Op_cat B) (@Catd_cat B)
    (@hom_int B B (@id_func B))
    (@comp_cat_fapp0 (Op_cat B) (Op_cat C) (@Catd_cat B)
      (@hom_int C B G) (@Op_func B C F))))
  : τ (Transf
      (@comma_graph_source_raw_catd B)
      (@comma_graph_middle_raw_catd B C F G))
≔ @fapp0
    (@Transf_cat
      (Op_cat B)
      (@Catd_cat B)
      (@hom_int B B (@id_func B))
      (@comma_graph_middle_inner_catd B C F G))
    (@Transf_cat
      (Op_cat B)
      Cat_cat
      (@comma_graph_source_raw_catd B)
      (@comma_graph_middle_raw_catd B C F G))
    (@comp_cat_cov_fapp1_func
      (Op_cat B)
      (@Catd_cat B)
      Cat_cat
      (@Sigma_func B)
      (@hom_int B B (@id_func B))
      (@comma_graph_middle_inner_catd B C F G))
    epsilon;

// Pointwise opposite turns that whole transformation into the displayed map
// used by the variance-correct lax-arrow total.
protected symbol comma_graph_sigma_op_funcd
  [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (@Transf (Op_cat B) (@Catd_cat B)
    (@hom_int B B (@id_func B))
    (@comp_cat_fapp0 (Op_cat B) (Op_cat C) (@Catd_cat B)
      (@hom_int C B G) (@Op_func B C F))))
  : τ (Functord
      (@comma_graph_source_catd B)
      (@comma_graph_middle_catd B C F G))
≔ @Op_funcd
    (Op_cat B)
    (@comma_graph_source_raw_catd B)
    (@comma_graph_middle_raw_catd B C F G)
    (@comma_graph_sigma_transf B C F G epsilon);

protected symbol comma_graph_identity_sec
  [B : Cat]
  : τ (Obj (@Pi_cat (Op_cat B) (@comma_graph_source_catd B)))
≔ @hom_identity_graph_sec B;

protected symbol comma_graph_middle_sec
  [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (@Transf (Op_cat B) (@Catd_cat B)
    (@hom_int B B (@id_func B))
    (@comp_cat_fapp0 (Op_cat B) (Op_cat C) (@Catd_cat B)
      (@hom_int C B G) (@Op_func B C F))))
  : τ (Obj (@Pi_cat
      (Op_cat B)
      (@comma_graph_middle_catd B C F G)))
≔ @section_postcomp_sec
    (Op_cat B)
    (@comma_graph_source_catd B)
    (@comma_graph_middle_catd B C F G)
    (@comma_graph_sigma_op_funcd B C F G epsilon)
    (@comma_graph_identity_sec B);

// The represented C-family at the varying source F[x].
protected symbol comma_graph_rep_catd
  [B C : Cat]
  (F : τ (Functor B C))
  : τ (Functor (Op_cat B) (@Catd_cat C))
≔ @comp_cat_fapp0
    (Op_cat B)
    (Op_cat C)
    (@Catd_cat C)
    (@hom_int C C (@id_func C))
    (@Op_func B C F);

// The two family-valued endpoints of total base change by G.
protected symbol comma_graph_basechange_source_func
  [B C : Cat]
  (G : τ (Functor B C))
  : τ (Functor (@Catd_cat C) Cat_cat)
≔ @comp_cat_fapp0
    (@Catd_cat C)
    (@Catd_cat B)
    Cat_cat
    (@Sigma_func B)
    (@Pullback_catd_func B C G);

protected symbol comma_graph_basechange_source_catd
  [B C : Cat]
  (F G : τ (Functor B C))
  : τ (Catd (Op_cat B))
≔ @comp_cat_fapp0
    (Op_cat B)
    (@Catd_cat C)
    Cat_cat
    (@comma_graph_basechange_source_func B C G)
    (@comma_graph_rep_catd B C F);

protected symbol comma_graph_target_raw_catd
  [B C : Cat]
  (F : τ (Functor B C))
  : τ (Catd (Op_cat B))
≔ @comp_cat_fapp0
    (Op_cat B)
    (Op_cat C)
    Cat_cat
    (@homdc_edge_catd C C (@hom_int C C (@id_func C)))
    (@Op_func B C F);

// Precompose the family-natural total-base-change transformation by the
// represented family x |-> Hom_C(F[x],-).
protected symbol comma_graph_basechange_transf
  [B C : Cat]
  (F G : τ (Functor B C))
  : τ (Transf
      (@comma_graph_basechange_source_catd B C F G)
      (@comma_graph_target_raw_catd B C F))
≔ @fapp0
    (@Transf_cat
      (@Catd_cat C)
      Cat_cat
      (@comma_graph_basechange_source_func B C G)
      (@Sigma_func C))
    (@Transf_cat
      (Op_cat B)
      Cat_cat
      (@comma_graph_basechange_source_catd B C F G)
      (@comma_graph_target_raw_catd B C F))
    (@comp_cat_con_fapp1_func
      (Op_cat B)
      (@Catd_cat C)
      Cat_cat
      (@comma_graph_rep_catd B C F)
      (@comma_graph_basechange_source_func B C G)
      (@Sigma_func C))
    (@sigma_pullback_total_transf B C G);

// Pointwise opposite of the actual base-change transformation.
protected symbol comma_graph_basechange_op_raw_funcd
  [B C : Cat]
  (F G : τ (Functor B C))
  : τ (Functord
      (@Op_catd
        (Op_cat B)
        (@comma_graph_basechange_source_catd B C F G))
      (@Op_catd
        (Op_cat B)
        (@comma_graph_target_raw_catd B C F)))
≔ @Op_funcd
    (Op_cat B)
    (@comma_graph_basechange_source_catd B C F G)
    (@comma_graph_target_raw_catd B C F)
    (@comma_graph_basechange_transf B C F G);

protected symbol comma_graph_basechange_source_reframe_funcd
  [B C : Cat]
  (F G : τ (Functor B C))
  : τ (Functord
      (@comma_graph_middle_catd B C F G)
      (@Op_catd
        (Op_cat B)
        (@comma_graph_basechange_source_catd B C F G)))
≔ @id_funcd
    (Op_cat B)
    (@comma_graph_middle_catd B C F G);

protected symbol comma_graph_basechange_target_reframe_funcd
  [B C : Cat]
  (F : τ (Functor B C))
  : τ (Functord
      (@Op_catd
        (Op_cat B)
        (@comma_graph_target_raw_catd B C F))
      (@comma_graph_target_catd B C F))
≔ @id_funcd
    (Op_cat B)
    (@Op_catd
      (Op_cat B)
      (@comma_graph_target_raw_catd B C F));

protected symbol comma_graph_basechange_op_funcd
  [B C : Cat]
  (F G : τ (Functor B C))
  : τ (Functord
      (@comma_graph_middle_catd B C F G)
      (@comma_graph_target_catd B C F))
≔ @comp_catd_fapp0
    (Op_cat B)
    (@comma_graph_middle_catd B C F G)
    (@Op_catd
      (Op_cat B)
      (@comma_graph_target_raw_catd B C F))
    (@comma_graph_target_catd B C F)
    (@comma_graph_basechange_target_reframe_funcd B C F)
    (@comp_catd_fapp0
      (Op_cat B)
      (@comma_graph_middle_catd B C F G)
      (@Op_catd
        (Op_cat B)
        (@comma_graph_basechange_source_catd B C F G))
      (@Op_catd
        (Op_cat B)
        (@comma_graph_target_raw_catd B C F))
      (@comma_graph_basechange_op_raw_funcd B C F G)
      (@comma_graph_basechange_source_reframe_funcd B C F G));

protected symbol comma_graph_target_sec
  [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (@Transf (Op_cat B) (@Catd_cat B)
    (@hom_int B B (@id_func B))
    (@comp_cat_fapp0 (Op_cat B) (Op_cat C) (@Catd_cat B)
      (@hom_int C B G) (@Op_func B C F))))
  : τ (Obj (@Pi_cat
      (Op_cat B)
      (@comma_graph_target_catd B C F)))
≔ @section_postcomp_sec
    (Op_cat B)
    (@comma_graph_middle_catd B C F G)
    (@comma_graph_target_catd B C F)
    (@comma_graph_basechange_op_funcd B C F G)
    (@comma_graph_middle_sec B C F G epsilon);

// Totalize the section, move its outer base along F^op, then take opposites.
protected symbol comma_graph_underlying_func
  [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (@Transf (Op_cat B) (@Catd_cat B)
    (@hom_int B B (@id_func B))
    (@comp_cat_fapp0 (Op_cat B) (Op_cat C) (@Catd_cat B)
      (@hom_int C B G) (@Op_func B C F))))
  : τ (Functor
      (Op_cat B)
      (@Sigma_cat
        (Op_cat C)
        (@comma_graph_target_base_catd C)))
≔ @comp_cat_fapp0
    (Op_cat B)
    (@Sigma_cat
      (Op_cat B)
      (@comma_graph_target_catd B C F))
    (@Sigma_cat
      (Op_cat C)
      (@comma_graph_target_base_catd C))
    (@sigma_pullback_total_func
      (Op_cat B)
      (Op_cat C)
      (@Op_func B C F)
      (@comma_graph_target_base_catd C))
    (@section_total_func
      (Op_cat B)
      (@comma_graph_target_catd B C F)
      (@comma_graph_target_sec B C F G epsilon));

// Protected transparent derivation retained for architecture evidence.
protected symbol comma_graph_internal_func
  [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (@Transf (Op_cat B) (@Catd_cat B)
    (@hom_int B B (@id_func B))
    (@comp_cat_fapp0 (Op_cat B) (Op_cat C) (@Catd_cat B)
      (@hom_int C B G) (@Op_func B C F))))
  : τ (Functor B (@LaxArrow_cat C))
≔ @Op_func
    (Op_cat B)
    (@Sigma_cat
      (Op_cat C)
      (@comma_graph_target_base_catd C))
    (@comma_graph_underlying_func B C F G epsilon);



// The actual whole input classifier.

protected symbol represented_comma_family_catd [X Y : Cat] (J : τ (Functor X Y))
  : τ (Catd (Op_cat X))
≔ @Pullback_catd (Op_cat X) (Op_cat Y)
    (@comma_graph_target_base_catd Y) (@Op_func X Y J);

protected symbol represented_comma_family_reframe [X Y : Cat] (J : τ (Functor X Y))
  : τ (@Functord (Op_cat X) (@represented_comma_family_catd X Y J)
      (@homdc_op_edge_catd X Y (@represented_comma_prof X Y J)))
≔ @id_funcd (Op_cat X) (@represented_comma_family_catd X Y J);

protected symbol represented_comma_family_target [K X Y : Cat]
  (J : τ (Functor X Y)) (A : τ (Functor K X))
  : τ (Catd (Op_cat K))
≔ @Pullback_catd (Op_cat K) (Op_cat X)
    (@represented_comma_family_catd X Y J) (@Op_func K X A);

protected symbol represented_comma_family_section [K X Y : Cat]
  (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y))
  (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A)))))
  : τ (Obj (@Pi_cat (Op_cat K) (@represented_comma_family_target K X Y J A)))
≔ @comma_graph_target_sec K Y (@comp_cat_fapp0 K X Y J A) D h;

protected symbol represented_comma_family_underlying_func [K X Y : Cat]
  (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y))
  (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A)))))
  : τ (Functor (Op_cat K) (@Sigma_cat (Op_cat X) (@represented_comma_family_catd X Y J)))
≔ @comp_cat_fapp0 (Op_cat K)
    (@Sigma_cat (Op_cat K) (@represented_comma_family_target K X Y J A))
    (@Sigma_cat (Op_cat X) (@represented_comma_family_catd X Y J))
    (@sigma_pullback_total_func (Op_cat K) (Op_cat X) (@Op_func K X A)
      (@represented_comma_family_catd X Y J))
    (@section_total_func (Op_cat K) (@represented_comma_family_target K X Y J A)
      (@represented_comma_family_section K X Y J A D h));

// Classify Θ:Hom_K(−,−)⇒Hom_Y(JA−,D−), retaining the whole action.
symbol represented_comma_hom_action_func [K X Y : Cat]
  (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y))
  (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A)))))
  : τ (Functor K (@RepresentedComma_cat X Y J))
≔ @Op_func (Op_cat K)
    (@Sigma_cat (Op_cat X) (@homdc_op_edge_catd X Y (@represented_comma_prof X Y J)))
    (@comp_cat_fapp0 (Op_cat K)
      (@Sigma_cat (Op_cat X) (@represented_comma_family_catd X Y J))
      (@Sigma_cat (Op_cat X) (@homdc_op_edge_catd X Y (@represented_comma_prof X Y J)))
      (@sigma_map_func (Op_cat X) (@represented_comma_family_catd X Y J)
        (@homdc_op_edge_catd X Y (@represented_comma_prof X Y J))
        (@represented_comma_family_reframe X Y J))
      (@represented_comma_family_underlying_func K X Y J A D h));

// Whole source projection with its original inverse data.

protected symbol comma_source_op_total_projection [K : Cat] (E : τ (Catd K)) (s : τ (Obj (@Pi_cat K E)))
 : τ (Functor (Op_cat K) (Op_cat K))
≔ @comp_cat_fapp0 (Op_cat K) (Op_cat (@Sigma_cat K E)) (Op_cat K)
 (@Op_func (@Sigma_cat K E) K (@Sigma_proj1_func K E))
 (@Op_func K (@Sigma_cat K E) (@section_total_func K E s));

protected symbol comma_source_op_map_projection [K : Cat] (E D : τ (Catd K)) (FF : τ (@Functord K E D))
 : τ (Functor (Op_cat (@Sigma_cat K E)) (Op_cat K))
≔ @comp_cat_fapp0 (Op_cat (@Sigma_cat K E)) (Op_cat (@Sigma_cat K D)) (Op_cat K)
 (@Op_func (@Sigma_cat K D) K (@Sigma_proj1_func K D))
 (@Op_func (@Sigma_cat K E) (@Sigma_cat K D) (@sigma_map_func K E D FF));

protected symbol comma_source_op_basechange_projection [A K : Cat] (F : τ (Functor A K)) (E : τ (Catd K))
 : τ (Functor (Op_cat (@Sigma_cat A (@Pullback_catd A K E F))) (Op_cat K))
≔ @comp_cat_fapp0 (Op_cat (@Sigma_cat A (@Pullback_catd A K E F))) (Op_cat (@Sigma_cat K E)) (Op_cat K)
 (@Op_func (@Sigma_cat K E) K (@Sigma_proj1_func K E))
 (@Op_func (@Sigma_cat A (@Pullback_catd A K E F)) (@Sigma_cat K E) (@sigma_pullback_total_func A K F E));

protected symbol comma_source_op_basechange_projected [A K : Cat] (F : τ (Functor A K)) (E : τ (Catd K))
 : τ (Functor (Op_cat (@Sigma_cat A (@Pullback_catd A K E F))) (Op_cat K))
≔ @comp_cat_fapp0 (Op_cat (@Sigma_cat A (@Pullback_catd A K E F))) (Op_cat A) (Op_cat K)
 (@Op_func A K F) (@Op_func (@Sigma_cat A (@Pullback_catd A K E F)) A (@Sigma_proj1_func A (@Pullback_catd A
   K E F)));

protected symbol comma_source_op_total_evidence [K : Cat] (E : τ (Catd K)) (s : τ (Obj (@Pi_cat K E)))
 : τ (IsoEvidence (Functor_cat (Op_cat K) (Op_cat K)) (@comma_source_op_total_projection K E s) (@id_func (Op_cat
   K)))
≔ @iso_evidence_intro (Functor_cat (Op_cat K) (Op_cat K)) (@comma_source_op_total_projection K E s) (@id_func
  (Op_cat K))
 (@id (Functor_cat (Op_cat K) (Op_cat K)) (@comma_source_op_total_projection K E s)) (@id (Functor_cat (Op_cat K)
   (Op_cat K)) (@id_func (Op_cat K)))
 (eq_refl (@id (Functor_cat (Op_cat K) (Op_cat K)) (@comma_source_op_total_projection K E s))) (eq_refl (@id
   (Functor_cat (Op_cat K) (Op_cat K)) (@id_func (Op_cat K))));

protected symbol comma_source_op_map_evidence [K : Cat] (E D : τ (Catd K)) (FF : τ (@Functord K E D))
 : τ (IsoEvidence (Functor_cat (Op_cat (@Sigma_cat K E)) (Op_cat K)) (@comma_source_op_map_projection K E D FF)
   (@Op_func (@Sigma_cat K E) K (@Sigma_proj1_func K E)))
≔ @iso_evidence_intro (Functor_cat (Op_cat (@Sigma_cat K E)) (Op_cat K)) (@comma_source_op_map_projection K E D FF)
  (@Op_func (@Sigma_cat K E) K (@Sigma_proj1_func K E))
 (@id (Functor_cat (Op_cat (@Sigma_cat K E)) (Op_cat K)) (@comma_source_op_map_projection K E D FF)) (@id
   (Functor_cat (Op_cat (@Sigma_cat K E)) (Op_cat K)) (@Op_func (@Sigma_cat K E) K (@Sigma_proj1_func K E)))
 (eq_refl (@id (Functor_cat (Op_cat (@Sigma_cat K E)) (Op_cat K)) (@comma_source_op_map_projection K E D FF)))
   (eq_refl (@id (Functor_cat (Op_cat (@Sigma_cat K E)) (Op_cat K)) (@Op_func (@Sigma_cat K E) K
   (@Sigma_proj1_func K E))));

protected symbol comma_source_op_basechange_evidence [A K : Cat] (F : τ (Functor A K)) (E : τ (Catd K))
 : τ (IsoEvidence (Functor_cat (Op_cat (@Sigma_cat A (@Pullback_catd A K E F))) (Op_cat K))
   (@comma_source_op_basechange_projection A K F E) (@comma_source_op_basechange_projected A K F E))
≔ @iso_evidence_intro (Functor_cat (Op_cat (@Sigma_cat A (@Pullback_catd A K E F))) (Op_cat K))
  (@comma_source_op_basechange_projection A K F E) (@comma_source_op_basechange_projected A K F E)
 (@id (Functor_cat (Op_cat (@Sigma_cat A (@Pullback_catd A K E F))) (Op_cat K))
   (@comma_source_op_basechange_projection A K F E)) (@id (Functor_cat (Op_cat (@Sigma_cat A (@Pullback_catd A K E
   F))) (Op_cat K)) (@comma_source_op_basechange_projected A K F E))
 (eq_refl (@id (Functor_cat (Op_cat (@Sigma_cat A (@Pullback_catd A K E F))) (Op_cat K))
   (@comma_source_op_basechange_projection A K F E))) (eq_refl (@id (Functor_cat (Op_cat (@Sigma_cat A
   (@Pullback_catd A K E F))) (Op_cat K)) (@comma_source_op_basechange_projected A K F E)));

// The actual source projection p∘Γ.
symbol represented_comma_hom_action_source_func [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A))))) : τ (Functor K X)
≔ (@comp_cat_fapp0 K (@RepresentedComma_cat X Y J) X (@represented_comma_source_func X Y J)
  (@represented_comma_hom_action_func K X Y J A D h));

protected symbol comma_source_gamma_source1 [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A))))) : τ (Functor K X)
≔ (@comp_cat_fapp0 K (Op_cat (@Sigma_cat (Op_cat K) (@represented_comma_family_target K X Y J A))) X
  (@comp_cat_fapp0 (Op_cat (@Sigma_cat (Op_cat K) (@represented_comma_family_target K X Y J A))) (Op_cat
  (@Sigma_cat (Op_cat X) (@represented_comma_family_catd X Y J))) X (@Op_func (@Sigma_cat (Op_cat X)
  (@represented_comma_family_catd X Y J)) (Op_cat X) (@Sigma_proj1_func (Op_cat X)
  (@represented_comma_family_catd X Y J))) (@Op_func (@Sigma_cat (Op_cat K)
  (@represented_comma_family_target K X Y J A)) (@Sigma_cat (Op_cat X) (@represented_comma_family_catd X Y
  J)) (@sigma_pullback_total_func (Op_cat K) (Op_cat X) (@Op_func K X A) (@represented_comma_family_catd X Y
  J)))) (@Op_func (Op_cat K) (@Sigma_cat (Op_cat K) (@represented_comma_family_target K X Y J A))
  (@section_total_func (Op_cat K) (@represented_comma_family_target K X Y J A)
  (@represented_comma_family_section K X Y J A D h))));

protected symbol comma_source_gamma_source2 [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A))))) : τ (Functor K X)
≔ (@comp_cat_fapp0 K (Op_cat (@Sigma_cat (Op_cat K) (@represented_comma_family_target K X Y J A))) X
  (@comp_cat_fapp0 (Op_cat (@Sigma_cat (Op_cat K) (@represented_comma_family_target K X Y J A))) K X A
  (@Op_func (@Sigma_cat (Op_cat K) (@represented_comma_family_target K X Y J A)) (Op_cat K)
  (@Sigma_proj1_func (Op_cat K) (@represented_comma_family_target K X Y J A)))) (@Op_func (Op_cat K)
  (@Sigma_cat (Op_cat K) (@represented_comma_family_target K X Y J A)) (@section_total_func (Op_cat K)
  (@represented_comma_family_target K X Y J A) (@represented_comma_family_section K X Y J A D h))));

protected symbol comma_source_gamma_step1 [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A)))))
 : τ (IsoEvidence (Functor_cat K X) (@represented_comma_hom_action_source_func K X Y J A D h) (@comma_source_gamma_source1 K X Y J A D h))
≔ @iso_evidence_prewhisker K (Op_cat (@Sigma_cat (Op_cat K) (@represented_comma_family_target K X Y J A))) X
  (@Op_func (Op_cat K) (@Sigma_cat (Op_cat K) (@represented_comma_family_target K X Y J A))
  (@section_total_func (Op_cat K) (@represented_comma_family_target K X Y J A)
  (@represented_comma_family_section K X Y J A D h))) (@comp_cat_fapp0 (Op_cat (@Sigma_cat (Op_cat K)
  (@represented_comma_family_target K X Y J A))) (Op_cat (@Sigma_cat (Op_cat X)
  (@represented_comma_family_catd X Y J))) X (@comma_source_op_map_projection (Op_cat X)
  (@represented_comma_family_catd X Y J) (@homdc_op_edge_catd X Y (@represented_comma_prof X Y J))
  (@represented_comma_family_reframe X Y J)) (@Op_func (@Sigma_cat (Op_cat K)
  (@represented_comma_family_target K X Y J A)) (@Sigma_cat (Op_cat X) (@represented_comma_family_catd X Y
  J)) (@sigma_pullback_total_func (Op_cat K) (Op_cat X) (@Op_func K X A) (@represented_comma_family_catd X Y
  J)))) (@comp_cat_fapp0 (Op_cat (@Sigma_cat (Op_cat K) (@represented_comma_family_target K X Y J A)))
  (Op_cat (@Sigma_cat (Op_cat X) (@represented_comma_family_catd X Y J))) X (@Op_func (@Sigma_cat (Op_cat X)
  (@represented_comma_family_catd X Y J)) (Op_cat X) (@Sigma_proj1_func (Op_cat X)
  (@represented_comma_family_catd X Y J))) (@Op_func (@Sigma_cat (Op_cat K)
  (@represented_comma_family_target K X Y J A)) (@Sigma_cat (Op_cat X) (@represented_comma_family_catd X Y
  J)) (@sigma_pullback_total_func (Op_cat K) (Op_cat X) (@Op_func K X A) (@represented_comma_family_catd X Y
  J)))) (@iso_evidence_prewhisker (Op_cat (@Sigma_cat (Op_cat K) (@represented_comma_family_target K X Y J A)))
  (Op_cat (@Sigma_cat (Op_cat X) (@represented_comma_family_catd X Y J))) X (@Op_func (@Sigma_cat (Op_cat K)
  (@represented_comma_family_target K X Y J A)) (@Sigma_cat (Op_cat X) (@represented_comma_family_catd X Y
  J)) (@sigma_pullback_total_func (Op_cat K) (Op_cat X) (@Op_func K X A) (@represented_comma_family_catd X Y
  J))) (@comma_source_op_map_projection (Op_cat X) (@represented_comma_family_catd X Y J) (@homdc_op_edge_catd X Y
  (@represented_comma_prof X Y J)) (@represented_comma_family_reframe X Y J)) (@Op_func (@Sigma_cat (Op_cat
  X) (@represented_comma_family_catd X Y J)) (Op_cat X) (@Sigma_proj1_func (Op_cat X)
  (@represented_comma_family_catd X Y J))) (@comma_source_op_map_evidence (Op_cat X) (@represented_comma_family_catd
  X Y J) (@homdc_op_edge_catd X Y (@represented_comma_prof X Y J)) (@represented_comma_family_reframe X Y
  J)));

protected symbol comma_source_gamma_step2 [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A)))))
 : τ (IsoEvidence (Functor_cat K X) (@comma_source_gamma_source1 K X Y J A D h) (@comma_source_gamma_source2 K X Y J A D h))
≔ @iso_evidence_prewhisker K (Op_cat (@Sigma_cat (Op_cat K) (@represented_comma_family_target K X Y J A))) X
  (@Op_func (Op_cat K) (@Sigma_cat (Op_cat K) (@represented_comma_family_target K X Y J A))
  (@section_total_func (Op_cat K) (@represented_comma_family_target K X Y J A)
  (@represented_comma_family_section K X Y J A D h))) (@comma_source_op_basechange_projection (Op_cat K) (Op_cat X)
  (@Op_func K X A) (@represented_comma_family_catd X Y J)) (@comma_source_op_basechange_projected (Op_cat K) (Op_cat
  X) (@Op_func K X A) (@represented_comma_family_catd X Y J)) (@comma_source_op_basechange_evidence (Op_cat K)
  (Op_cat X) (@Op_func K X A) (@represented_comma_family_catd X Y J));

protected symbol comma_source_gamma_step3 [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A)))))
 : τ (IsoEvidence (Functor_cat K X) (@comma_source_gamma_source2 K X Y J A D h) A)
≔ @iso_evidence_postwhisker K K X A (@comma_source_op_total_projection (Op_cat K) (@represented_comma_family_target K X Y J
  A) (@represented_comma_family_section K X Y J A D h)) (@id_func K) (@comma_source_op_total_evidence (Op_cat K)
  (@represented_comma_family_target K X Y J A) (@represented_comma_family_section K X Y J A D h));

// Retained whole source comparison p∘Γ≅A, with both selected maps and laws.
symbol represented_comma_hom_action_source_evidence [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor
  K Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A)))))
 : τ (IsoEvidence (Functor_cat K X) (@represented_comma_hom_action_source_func K X Y J A D h) A)
≔ @iso_evidence_comp (Functor_cat K X) (@represented_comma_hom_action_source_func K X Y J A D h) (@comma_source_gamma_source1 K X Y J A D
  h) A
 (@iso_evidence_comp (Functor_cat K X) (@comma_source_gamma_source1 K X Y J A D h) (@comma_source_gamma_source2 K X Y J A D
   h) A (@comma_source_gamma_step3 K X Y J A D h) (@comma_source_gamma_step2 K X Y J A D h))
 (@comma_source_gamma_step1 K X Y J A D h);

// Forward transformation of that same source comparison.
symbol represented_comma_hom_action_source_to [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y))
  (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A)))))
 : τ (@Transf K X (@represented_comma_hom_action_source_func K X Y J A D h) A)
≔ @iso_evidence_to (Functor_cat K X) (@represented_comma_hom_action_source_func K X Y J A D h) A (@represented_comma_hom_action_source_evidence K X
  Y J A D h);

protected symbol comma_source_gamma_source_to_arrow [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor
  K Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A)))))
 (x y : τ (Obj K)) (g : τ (Hom K x y))
 : τ (Hom X (@fapp0 K X (@represented_comma_hom_action_source_func K X Y J A D h) x) (@fapp0 K X A y))
≔ @tapp1_fapp0 K X (@represented_comma_hom_action_source_func K X Y J A D h) A x y
    (@represented_comma_hom_action_source_to K X Y J A D h) g;

// Extract the actual target section before taking the outer opposite.

protected symbol comma_section_section_observed [K A : Cat] (E : τ (Catd K))
 (FF : τ (@Functord K E (@Const_catd K A))) (s : τ (Obj (@Pi_cat K E)))
 : τ (Functor K A)
≔ @comp_cat_fapp0 K (Product_cat K A) A (@Product_projR_func K A)
   (@section_total_mapped_func K E (@Const_catd K A) FF s);

protected symbol comma_section_section_observation_target [K A : Cat] (E : τ (Catd K))
 (FF : τ (@Functord K E (@Const_catd K A))) (s : τ (Obj (@Pi_cat K E)))
 : τ (Functor K A)
≔ @section_postcomp_sec K E (@Const_catd K A) FF s;

protected symbol comma_section_section_observation_transf [K A : Cat] (E : τ (Catd K))
 (FF : τ (@Functord K E (@Const_catd K A))) (s : τ (Obj (@Pi_cat K E)))
 : τ (@Transf K A (@comma_section_section_observed K A E FF s)
     (@comma_section_section_observation_target K A E FF s))
≔ @fapp0 _ _
   (@comp_cat_cov_fapp1_func K (Product_cat K A) A (@Product_projR_func K A)
     (@section_total_mapped_func K E (@Const_catd K A) FF s)
     (@section_total_postcomp_func K E (@Const_catd K A) FF s))
   (@section_total_postcomp_transf K E (@Const_catd K A) FF s);

protected symbol comma_section_section_observation_equiv [K A : Cat]
 (A1 : τ (IsNCat (cat_succ cat_zero) A)) (E : τ (Catd K))
 (FF : τ (@Functord K E (@Const_catd K A))) (s : τ (Obj (@Pi_cat K E)))
 : τ (@OmegaEquivAlong (Functor_cat K A)
     (@comma_section_section_observed K A E FF s) (@comma_section_section_observation_target K A E FF s)
     (@comma_section_section_observation_transf K A E FF s))
≔ @strict_transf_pointwise_omega_along K A
   (@comma_section_section_observed K A E FF s) (@comma_section_section_observation_target K A E FF s)
   (@comma_section_section_observation_transf K A E FF s)
   (λ x : τ (Obj K), @omega_equiv_along_refl A
     (@fapp0 K A (@comma_section_section_observation_target K A E FF s) x));

protected symbol comma_section_section_observation_iso [K A : Cat]
 (A1 : τ (IsNCat (cat_succ cat_zero) A)) (E : τ (Catd K))
 (FF : τ (@Functord K E (@Const_catd K A))) (s : τ (Obj (@Pi_cat K E)))
 : τ (IsoEvidence (Functor_cat K A) (@comma_section_section_observed K A E FF s)
     (@comma_section_section_observation_target K A E FF s))
≔ @omega_equiv_along_iso_evidence (Functor_cat K A)
   (@comma_section_section_observed K A E FF s) (@comma_section_section_observation_target K A E FF s)
   (@comma_section_section_observation_transf K A E FF s)
   (@comma_section_section_observation_equiv K A A1 E FF s);

protected symbol comma_section_gamma_target_family_map [X Y : Cat] (J : τ (Functor X Y))
 : τ (@Functord (Op_cat X) (@represented_comma_family_catd X Y J)
     (@Const_catd (Op_cat X) (Op_cat Y)))
≔ @comp_catd_fapp0 (Op_cat X)
    (@represented_comma_family_catd X Y J)
    (@homdc_op_edge_catd X Y (@represented_comma_prof X Y J))
    (@Const_catd (Op_cat X) (Op_cat Y))
    (@homdc_total_target_funcd X Y (@represented_comma_prof X Y J))
    (@represented_comma_family_reframe X Y J);

protected symbol comma_section_gamma_target_section_map [K X Y : Cat]
 (J : τ (Functor X Y)) (A : τ (Functor K X))
 : τ (@Functord (Op_cat K) (@represented_comma_family_target K X Y J A)
     (@Const_catd (Op_cat K) (Op_cat Y)))
≔ @fapp1_fapp0 (@Catd_cat (Op_cat X)) (@Catd_cat (Op_cat K))
   (@Pullback_catd_func (Op_cat K) (Op_cat X) (@Op_func K X A))
   (@represented_comma_family_catd X Y J)
   (@Const_catd (Op_cat X) (Op_cat Y))
   (@comma_section_gamma_target_family_map X Y J);

protected symbol comma_section_gamma_target_section [K X Y : Cat] (J : τ (Functor X Y))
 (A : τ (Functor K X)) (D : τ (Functor K Y))
 (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A)))))
 : τ (Functor (Op_cat K) (Op_cat Y))
≔ @comma_section_section_observation_target (Op_cat K) (Op_cat Y)
   (@represented_comma_family_target K X Y J A)
   (@comma_section_gamma_target_section_map K X Y J A)
   (@represented_comma_family_section K X Y J A D h);

protected symbol comma_section_gamma_target_extraction [K X Y : Cat]
 (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y))
 (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A)))))
 : τ (@Transf (Op_cat K) (Op_cat Y)
   (@comma_section_section_observed (Op_cat K) (Op_cat Y)
     (@represented_comma_family_target K X Y J A)
     (@comma_section_gamma_target_section_map K X Y J A)
     (@represented_comma_family_section K X Y J A D h))
   (@comma_section_gamma_target_section K X Y J A D h))
≔ @comma_section_section_observation_transf (Op_cat K) (Op_cat Y)
   (@represented_comma_family_target K X Y J A)
   (@comma_section_gamma_target_section_map K X Y J A)
   (@represented_comma_family_section K X Y J A D h);

protected symbol comma_section_gamma_target_section_op [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ
  (Functor K Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A))))) : τ (Functor K Y)
≔ @Op_func (Op_cat K) (Op_cat Y) (@comma_section_gamma_target_section K X Y J A D h);

protected symbol comma_section_gamma_target_observed_op [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ
  (Functor K Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A))))) : τ (Functor K Y)
≔ @Op_func (Op_cat K) (Op_cat Y) (@comma_section_section_observed (Op_cat K) (Op_cat Y)
  (@represented_comma_family_target K X Y J A) (@comma_section_gamma_target_section_map K X Y J A)
  (@represented_comma_family_section K X Y J A D h));

protected symbol comma_section_gamma_target_extraction_op [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ
  (Functor K Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A)))))
 : τ (@Transf K Y (@comma_section_gamma_target_section_op K X Y J A D h)
     (@comma_section_gamma_target_observed_op K X Y J A D h))
≔ @Op_transf (Op_cat K) (Op_cat Y) (@comma_section_section_observed (Op_cat K) (Op_cat Y)
  (@represented_comma_family_target K X Y J A) (@comma_section_gamma_target_section_map K X Y J A)
  (@represented_comma_family_section K X Y J A D h)) (@comma_section_gamma_target_section K X Y J A D h)
   (@comma_section_gamma_target_extraction K X Y J A D h);

protected symbol comma_section_gamma_target_extraction_equiv [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ
  (Functor K Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A)))))
 (Y1 : τ (IsNCat (cat_succ cat_zero) Y))
 : τ (@OmegaEquivAlong (Functor_cat K Y)
     (@comma_section_gamma_target_section_op K X Y J A D h)
     (@comma_section_gamma_target_observed_op K X Y J A D h)
     (@comma_section_gamma_target_extraction_op K X Y J A D h))
≔ @strict_transf_pointwise_omega_along K Y
   (@comma_section_gamma_target_section_op K X Y J A D h)
   (@comma_section_gamma_target_observed_op K X Y J A D h)
   (@comma_section_gamma_target_extraction_op K X Y J A D h)
   (λ x : τ (Obj K), @omega_equiv_along_refl Y (@fapp0 K Y D x));

protected symbol comma_section_constant_section_projection [K A : Cat]
 (s : τ (Obj (@Pi_cat K (@Const_catd K A))))
 : τ (Functor K A)
≔ @comp_cat_fapp0 K (Product_cat K A) A
   (@Product_projR_func K A) (@section_total_func K (@Const_catd K A) s);

protected symbol comma_section_constant_section_arrow_agrees [K A : Cat]
 (s : τ (Obj (@Pi_cat K (@Const_catd K A))))
 (x y : τ (Obj K)) (p : τ (Hom K x y))
 : τ (@= (Hom A (@fapp0 K A s x) (@fapp0 K A s y))
   (@fapp1_fapp0 K A (@comma_section_constant_section_projection K A s) x y p)
   (@fapp1_fapp0 K A s x y p))
≔ @piapp1_const_fapp0_eq K A s x y p;

// Link that section to the original total base change.

protected symbol comma_basechange_sigma_basechange_source [A K : Cat] (F : τ (Functor A K))
 : τ (Functor (@Catd_cat K) Cat_cat)
≔ @comp_cat_fapp0 (@Catd_cat K) (@Catd_cat A) Cat_cat
   (@Sigma_func A) (@Pullback_catd_func A K F);

protected symbol comma_basechange_sigma_basechange_left [A K : Cat] (F : τ (Functor A K))
 (E D : τ (Catd K)) (FF : τ (@Functord K E D))
 : τ (Functor (@Sigma_cat A (@Pullback_catd A K E F)) (@Sigma_cat K D))
≔ @comp_cat_fapp0 (@Sigma_cat A (@Pullback_catd A K E F)) (@Sigma_cat K E) (@Sigma_cat K D)
   (@sigma_map_func K E D FF) (@sigma_pullback_total_func A K F E);

protected symbol comma_basechange_sigma_basechange_right [A K : Cat] (F : τ (Functor A K))
 (E D : τ (Catd K)) (FF : τ (@Functord K E D))
 : τ (Functor (@Sigma_cat A (@Pullback_catd A K E F)) (@Sigma_cat K D))
≔ @comp_cat_fapp0 (@Sigma_cat A (@Pullback_catd A K E F))
   (@Sigma_cat A (@Pullback_catd A K D F)) (@Sigma_cat K D)
   (@sigma_pullback_total_func A K F D)
   (@sigma_map_func A (@Pullback_catd A K E F) (@Pullback_catd A K D F)
     (@fapp1_fapp0 (@Catd_cat K) (@Catd_cat A) (@Pullback_catd_func A K F) E D FF));

protected symbol comma_basechange_sigma_basechange_naturality [A K : Cat] (F : τ (Functor A K))
 (E D : τ (Catd K)) (FF : τ (@Functord K E D))
 : τ (@Transf (@Sigma_cat A (@Pullback_catd A K E F)) (@Sigma_cat K D)
     (@comma_basechange_sigma_basechange_left A K F E D FF)
     (@comma_basechange_sigma_basechange_right A K F E D FF))
≔ @gray_transf_standard_cell (@Catd_cat K) Cat_cat
   (@comma_basechange_sigma_basechange_source A K F) (@Sigma_func K)
   (@sigma_pullback_total_transf A K F) E D FF;

protected symbol comma_basechange_sigma_map_composition [K : Cat] (E M D : τ (Catd K))
 (FF : τ (@Functord K E M)) (GG : τ (@Functord K M D))
 : τ (@Transf (@Sigma_cat K E) (@Sigma_cat K D)
   (@comp_cat_fapp0 (@Sigma_cat K E) (@Sigma_cat K M) (@Sigma_cat K D)
     (@sigma_map_func K M D GG) (@sigma_map_func K E M FF))
   (@sigma_map_func K E D (@comp_catd_fapp0 K E M D GG FF)))
≔ @fapp1_compositor (@Catd_cat K) Cat_cat (@Sigma_func K) E M D GG FF;

protected symbol comma_basechange_reindexed_observation [A K C : Cat] (F : τ (Functor A K)) (E : τ (Catd K))
 (P : τ (@Functord K E (@Const_catd K C)))
 : τ (Functor (@Sigma_cat A (@Pullback_catd A K E F)) (Product_cat A C))
≔ @sigma_map_func A (@Pullback_catd A K E F) (@Const_catd A C)
   (@fapp1_fapp0 (@Catd_cat K) (@Catd_cat A) (@Pullback_catd_func A K F)
     E (@Const_catd K C) P);

protected symbol comma_basechange_observation_outer [A K C : Cat] (F : τ (Functor A K)) (E : τ (Catd K))
 (P : τ (@Functord K E (@Const_catd K C)))
 : τ (Functor (@Sigma_cat A (@Pullback_catd A K E F)) C)
≔ @comp_cat_fapp0 (@Sigma_cat A (@Pullback_catd A K E F)) (Product_cat K C) C
   (@Product_projR_func K C) (@comma_basechange_sigma_basechange_left A K F E (@Const_catd K C) P);

protected symbol comma_basechange_observation_inner [A K C : Cat] (F : τ (Functor A K)) (E : τ (Catd K))
 (P : τ (@Functord K E (@Const_catd K C)))
 : τ (Functor (@Sigma_cat A (@Pullback_catd A K E F)) C)
≔ @comp_cat_fapp0 (@Sigma_cat A (@Pullback_catd A K E F)) (Product_cat A C) C
   (@Product_projR_func A C) (@comma_basechange_reindexed_observation A K C F E P);

protected symbol comma_basechange_observation_basechange [A K C : Cat] (F : τ (Functor A K)) (E : τ (Catd K))
 (P : τ (@Functord K E (@Const_catd K C)))
 : τ (@Transf (@Sigma_cat A (@Pullback_catd A K E F)) C
     (@comma_basechange_observation_outer A K C F E P) (@comma_basechange_observation_inner A K C F E P))
≔ @transf_postwhisker (@Sigma_cat A (@Pullback_catd A K E F)) (Product_cat K C) C
     (@Product_projR_func K C)
     (@comma_basechange_sigma_basechange_left A K F E (@Const_catd K C) P)
     (@comma_basechange_sigma_basechange_right A K F E (@Const_catd K C) P)
     (@comma_basechange_sigma_basechange_naturality A K F E (@Const_catd K C) P);

protected symbol comma_basechange_observation_basechange_component [A K C : Cat]
 (F : τ (Functor A K)) (E : τ (Catd K)) (P : τ (@Functord K E (@Const_catd K C)))
 (a : τ (Obj A)) (u : τ (Obj (@Fibre_cat K E (@fapp0 A K F a))))
 : τ (Hom C
   (@fapp0 (@Fibre_cat K E (@fapp0 A K F a)) C (@Fibre_func K E (@Const_catd K C) P (@fapp0 A K F a)) u)
   (@fapp0 (@Fibre_cat K E (@fapp0 A K F a)) C (@Fibre_func K E (@Const_catd K C) P (@fapp0 A K F a)) u))
≔ @tapp0_fapp0 (@Sigma_cat A (@Pullback_catd A K E F)) C
   (@comma_basechange_observation_outer A K C F E P) (@comma_basechange_observation_inner A K C F E P)
   (Struct_sigma a u) (@comma_basechange_observation_basechange A K C F E P);

protected symbol comma_basechange_gamma_target_raw0 [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K
  Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A))))) : τ (Functor (Op_cat K) (Op_cat Y))
≔ @comp_cat_fapp0 (Op_cat K) (@Sigma_cat (Op_cat X) (@homdc_op_edge_catd X Y (@represented_comma_prof X Y
  J))) (Op_cat Y)
   (@homdc_total_target_underlying_func X Y (@represented_comma_prof X Y J))
   (@comp_cat_fapp0 (Op_cat K) (@Sigma_cat (Op_cat X) (@represented_comma_family_catd X Y J)) (@Sigma_cat
     (Op_cat X) (@homdc_op_edge_catd X Y (@represented_comma_prof X Y J))) (@sigma_map_func (Op_cat X)
     (@represented_comma_family_catd X Y J) (@homdc_op_edge_catd X Y (@represented_comma_prof X Y J))
     (@represented_comma_family_reframe X Y J)) (@represented_comma_family_underlying_func K X Y J A D h));

protected symbol comma_basechange_gamma_target_raw1 [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K
  Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A))))) : τ (Functor (Op_cat K) (Op_cat Y))
≔ @comp_cat_fapp0 (Op_cat K) (@Sigma_cat (Op_cat K) (@represented_comma_family_target K X Y J A)) (Op_cat Y)
   (@comma_basechange_observation_outer (Op_cat K) (Op_cat X) (Op_cat Y) (@Op_func K X A)
     (@represented_comma_family_catd X Y J) (@comma_section_gamma_target_family_map X Y J)) (@section_total_func
     (Op_cat K) (@represented_comma_family_target K X Y J A) (@represented_comma_family_section K X Y J A D
     h));

protected symbol comma_basechange_gamma_target_raw2 [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K
  Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A))))) : τ (Functor (Op_cat K) (Op_cat Y))
≔ @comma_section_section_observed (Op_cat K) (Op_cat Y) (@represented_comma_family_target K X Y J A)
   (@comma_section_gamma_target_section_map K X Y J A)
   (@represented_comma_family_section K X Y J A D h);

protected symbol comma_basechange_gamma_target_step1 [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K
  Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A))))) : τ (@Transf (Op_cat K) (Op_cat Y)
  (@comma_basechange_gamma_target_raw0 K X Y J A D h) (@comma_basechange_gamma_target_raw1 K X Y J A D h))
≔ @transf_postwhisker (Op_cat K) (Product_cat (Op_cat X) (Op_cat Y)) (Op_cat Y) (@Product_projR_func (Op_cat X)
  (Op_cat Y)) (@comp_cat_fapp0 (Op_cat K) (@Sigma_cat (Op_cat X) (@represented_comma_family_catd X Y J))
  (Product_cat (Op_cat X) (Op_cat Y)) (@comp_cat_fapp0 (@Sigma_cat (Op_cat X)
  (@represented_comma_family_catd X Y J)) (@Sigma_cat (Op_cat X) (@homdc_op_edge_catd X Y
  (@represented_comma_prof X Y J))) (Product_cat (Op_cat X) (Op_cat Y)) (@sigma_map_func (Op_cat X)
  (@homdc_op_edge_catd X Y (@represented_comma_prof X Y J)) (@Const_catd (Op_cat X) (Op_cat Y))
  (@homdc_total_target_funcd X Y (@represented_comma_prof X Y J))) (@sigma_map_func (Op_cat X)
  (@represented_comma_family_catd X Y J) (@homdc_op_edge_catd X Y (@represented_comma_prof X Y J))
  (@represented_comma_family_reframe X Y J))) (@represented_comma_family_underlying_func K X Y J A D h))
  (@comp_cat_fapp0 (Op_cat K) (@Sigma_cat (Op_cat X) (@represented_comma_family_catd X Y J)) (Product_cat
  (Op_cat X) (Op_cat Y)) (@sigma_map_func (Op_cat X) (@represented_comma_family_catd X Y J) (@Const_catd
  (Op_cat X) (Op_cat Y)) (@comma_section_gamma_target_family_map X Y J)) (@represented_comma_family_underlying_func K
  X Y J A D h))
   (@transf_prewhisker (Op_cat K) (@Sigma_cat (Op_cat X) (@represented_comma_family_catd X Y J)) (Product_cat (Op_cat
     X) (Op_cat Y)) (@represented_comma_family_underlying_func K X Y J A D h) (@comp_cat_fapp0 (@Sigma_cat
     (Op_cat X) (@represented_comma_family_catd X Y J)) (@Sigma_cat (Op_cat X) (@homdc_op_edge_catd X Y
     (@represented_comma_prof X Y J))) (Product_cat (Op_cat X) (Op_cat Y)) (@sigma_map_func (Op_cat X)
     (@homdc_op_edge_catd X Y (@represented_comma_prof X Y J)) (@Const_catd (Op_cat X) (Op_cat Y))
     (@homdc_total_target_funcd X Y (@represented_comma_prof X Y J))) (@sigma_map_func (Op_cat X)
     (@represented_comma_family_catd X Y J) (@homdc_op_edge_catd X Y (@represented_comma_prof X Y J))
     (@represented_comma_family_reframe X Y J))) (@sigma_map_func (Op_cat X) (@represented_comma_family_catd
     X Y J) (@Const_catd (Op_cat X) (Op_cat Y)) (@comma_section_gamma_target_family_map X Y J))
     (@comma_basechange_sigma_map_composition (Op_cat X) (@represented_comma_family_catd X Y J) (@homdc_op_edge_catd X Y
     (@represented_comma_prof X Y J)) (@Const_catd (Op_cat X) (Op_cat Y)) (@represented_comma_family_reframe
     X Y J) (@homdc_total_target_funcd X Y (@represented_comma_prof X Y J))));

protected symbol comma_basechange_gamma_target_step2 [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K
  Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A))))) : τ (@Transf (Op_cat K) (Op_cat Y)
  (@comma_basechange_gamma_target_raw1 K X Y J A D h) (@comma_basechange_gamma_target_raw2 K X Y J A D h))
≔ @transf_prewhisker (Op_cat K) (@Sigma_cat (Op_cat K) (@represented_comma_family_target K X Y J A)) (Op_cat Y)
  (@section_total_func (Op_cat K) (@represented_comma_family_target K X Y J A)
  (@represented_comma_family_section K X Y J A D h))
   (@comma_basechange_observation_outer (Op_cat K) (Op_cat X) (Op_cat Y) (@Op_func K X A)
     (@represented_comma_family_catd X Y J) (@comma_section_gamma_target_family_map X Y J))
   (@comma_basechange_observation_inner (Op_cat K) (Op_cat X) (Op_cat Y) (@Op_func K X A)
     (@represented_comma_family_catd X Y J) (@comma_section_gamma_target_family_map X Y J))
   (@comma_basechange_observation_basechange (Op_cat K) (Op_cat X) (Op_cat Y) (@Op_func K X A)
     (@represented_comma_family_catd X Y J) (@comma_section_gamma_target_family_map X Y J));

protected symbol comma_basechange_gamma_target_raw_link [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor
  K Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A))))) : τ (@Transf (Op_cat K) (Op_cat Y)
  (@comma_basechange_gamma_target_raw0 K X Y J A D h) (@comma_basechange_gamma_target_raw2 K X Y J A D h))
≔ @comp_fapp0 (Functor_cat (Op_cat K) (Op_cat Y)) (@comma_basechange_gamma_target_raw0 K X Y J A D h)
  (@comma_basechange_gamma_target_raw1 K X Y J A D h) (@comma_basechange_gamma_target_raw2 K X Y J A D h)
   (@comma_basechange_gamma_target_step2 K X Y J A D h) (@comma_basechange_gamma_target_step1 K X Y J A D h);

// The actual target projection q∘Γ.
symbol represented_comma_hom_action_target_func [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K
  Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A))))) : τ (Functor K Y)
≔ @comp_cat_fapp0 K (@RepresentedComma_cat X Y J) Y
   (@represented_comma_target_func X Y J) (@represented_comma_hom_action_func K X Y J A D h);

protected symbol comma_basechange_gamma_target_link [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K
  Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A)))))
 : τ (@Transf K Y (@comma_section_gamma_target_observed_op K X Y J A D h)
     (@represented_comma_hom_action_target_func K X Y J A D h))
≔ @Op_transf (Op_cat K) (Op_cat Y) (@comma_basechange_gamma_target_raw0 K X Y J A D h) (@comma_basechange_gamma_target_raw2 K X Y J
  A D h) (@comma_basechange_gamma_target_raw_link K X Y J A D h);

protected symbol comma_basechange_gamma_target_link_equiv [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ
  (Functor K Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A))))) (Y1 : τ (IsNCat (cat_succ cat_zero) Y))
 : τ (@OmegaEquivAlong (Functor_cat K Y) (@comma_section_gamma_target_observed_op K X Y J A D h)
   (@represented_comma_hom_action_target_func K X Y J A D h) (@comma_basechange_gamma_target_link K X Y J A D h))
≔ @strict_transf_pointwise_omega_along K Y (@comma_section_gamma_target_observed_op K X Y J A D h)
  (@represented_comma_hom_action_target_func K X Y J A D h) (@comma_basechange_gamma_target_link K X Y J A D h)
   (λ x : τ (Obj K), @omega_equiv_along_refl Y (@fapp0 K Y D x));

protected symbol comma_basechange_gamma_target_section_to_native [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ
  (Functor K Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A))))) : τ (@Transf K Y
  (@comma_section_gamma_target_section_op K X Y J A D h) (@represented_comma_hom_action_target_func K X Y J A D h))
≔ @comp_fapp0 (Functor_cat K Y) (@comma_section_gamma_target_section_op K X Y J A D h)
  (@comma_section_gamma_target_observed_op K X Y J A D h) (@represented_comma_hom_action_target_func K X Y J A D h)
  (@comma_basechange_gamma_target_link K X Y J A D h) (@comma_section_gamma_target_extraction_op K X Y J A D h);

protected symbol comma_basechange_gamma_target_section_to_native_equiv [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X))
  (D : τ (Functor K Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A))))) (Y1 : τ (IsNCat (cat_succ
  cat_zero) Y))
 : τ (@OmegaEquivAlong (Functor_cat K Y) (@comma_section_gamma_target_section_op K X Y J A D h)
   (@represented_comma_hom_action_target_func K X Y J A D h)
     (@comma_basechange_gamma_target_section_to_native K X Y J A D h))
≔ @omega_equiv_along_comp (Functor_cat K Y) (@comma_section_gamma_target_section_op K X Y J A D h)
  (@comma_section_gamma_target_observed_op K X Y J A D h) (@represented_comma_hom_action_target_func K X Y J A D h)
  (@comma_section_gamma_target_extraction_op K X Y J A D h) (@comma_basechange_gamma_target_link K X Y J A D h)
  (@comma_section_gamma_target_extraction_equiv K X Y J A D h Y1) (@comma_basechange_gamma_target_link_equiv K X Y J A D h Y1);

// Group the original mapped graph section.

protected symbol comma_grouped_graph_section_stage1 [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor
  K Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A))))) : τ (Functor (Op_cat K) (Op_cat Y))
≔ @section_postcomp_sec (Op_cat K) (@comma_graph_middle_catd K Y (@comp_cat_fapp0 K X Y J A) D)
  (@Const_catd (Op_cat K) (Op_cat Y)) (@comp_catd_fapp0 (Op_cat K) (@comma_graph_middle_catd K Y
  (@comp_cat_fapp0 K X Y J A) D) (@represented_comma_family_target K X Y J A) (@Const_catd (Op_cat K)
  (Op_cat Y)) (@comma_section_gamma_target_section_map K X Y J A) (@comma_graph_basechange_op_funcd K Y
  (@comp_cat_fapp0 K X Y J A) D)) (@comma_graph_middle_sec K Y (@comp_cat_fapp0 K X Y J A) D h);

protected symbol comma_grouped_graph_section_stage2 [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor
  K Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A))))) : τ (Functor (Op_cat K) (Op_cat Y))
≔ @section_postcomp_sec (Op_cat K) (@comma_graph_source_catd K) (@Const_catd (Op_cat K) (Op_cat Y))
  (@comp_catd_fapp0 (Op_cat K) (@comma_graph_source_catd K) (@comma_graph_middle_catd K Y
  (@comp_cat_fapp0 K X Y J A) D) (@Const_catd (Op_cat K) (Op_cat Y)) (@comp_catd_fapp0 (Op_cat K)
  (@comma_graph_middle_catd K Y (@comp_cat_fapp0 K X Y J A) D) (@represented_comma_family_target K X
  Y J A) (@Const_catd (Op_cat K) (Op_cat Y)) (@comma_section_gamma_target_section_map K X Y J A)
  (@comma_graph_basechange_op_funcd K Y (@comp_cat_fapp0 K X Y J A) D))
  (@comma_graph_sigma_op_funcd K Y (@comp_cat_fapp0 K X Y J A) D h)) (@hom_identity_graph_sec K);

// Classify the target section and retain the whole target inverse.

protected symbol comma_classification_target_projection [K X Y : Cat]
 (J : τ (Functor X Y)) (A : τ (Functor K X))
 : τ (@Functord (Op_cat K)
     (@represented_comma_family_target K X Y J A)
     (@Const_catd (Op_cat K) (Op_cat Y)))
≔ @Op_funcd (Op_cat K)
    (@comma_graph_target_raw_catd K Y (@comp_cat_fapp0 K X Y J A))
    (@Const_catd (Op_cat K) Y)
    (@sigma_proj1_family_funcd (Op_cat K) Y
      (@comma_graph_rep_catd K Y (@comp_cat_fapp0 K X Y J A)));

protected symbol comma_classification_target_section_canonical [K X Y : Cat]
 (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y))
 (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A)))))
 : τ (Functor (Op_cat K) (Op_cat Y))
≔ @section_postcomp_sec (Op_cat K)
   (@represented_comma_family_target K X Y J A)
   (@Const_catd (Op_cat K) (Op_cat Y))
   (@comma_classification_target_projection K X Y J A)
   (@represented_comma_family_section K X Y J A D h);

protected symbol comma_classification_middle_projection [K Y : Cat] (F D : τ (Functor K Y))
 : τ (@Functord (Op_cat K) (@comma_graph_middle_catd K Y F D)
     (@Const_catd (Op_cat K) (Op_cat K)))
≔ @Op_funcd (Op_cat K) (@comma_graph_middle_raw_catd K Y F D)
   (@Const_catd (Op_cat K) K)
   (@sigma_proj1_family_funcd (Op_cat K) K (@comma_graph_middle_inner_catd K Y F D));

protected symbol comma_classification_middle_section_projected [K X Y : Cat]
 (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y))
 (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A)))))
 : τ (Functor (Op_cat K) (Op_cat K))
≔ @section_postcomp_sec (Op_cat K)
   (@comma_graph_middle_catd K Y (@comp_cat_fapp0 K X Y J A) D)
   (@Const_catd (Op_cat K) (Op_cat K))
   (@comma_classification_middle_projection K Y (@comp_cat_fapp0 K X Y J A) D)
   (@comma_graph_middle_sec K Y (@comp_cat_fapp0 K X Y J A) D h);

protected symbol comma_classification_target_section_after_basechange [K X Y : Cat]
 (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y))
 (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A)))))
 : τ (Functor (Op_cat K) (Op_cat Y))
≔ @comp_cat_fapp0 (Op_cat K) (Op_cat K) (Op_cat Y)
   (@Op_func K Y D) (@comma_classification_middle_section_projected K X Y J A D h);

protected symbol comma_classification_identity_section_projected (K : Cat)
 : τ (Functor (Op_cat K) (Op_cat K))
≔ @section_postcomp_sec (Op_cat K) (@comma_graph_source_catd K)
   (@Const_catd (Op_cat K) (Op_cat K))
   (@Op_funcd (Op_cat K) (@comma_graph_source_raw_catd K)
     (@Const_catd (Op_cat K) K)
     (@sigma_proj1_family_funcd (Op_cat K) K (@hom_int K K (@id_func K))))
   (@hom_identity_graph_sec K);

protected symbol comma_classification_raw_reindex [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X))
 (D : τ (Functor K Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A)))))
 : τ (@Transf (Op_cat K) (Op_cat Y) (@comma_classification_target_section_canonical K X Y J A D h)
  (@comma_section_gamma_target_section K X Y J A D h))
≔ @id (Functor_cat (Op_cat K) (Op_cat Y)) (@comma_classification_target_section_canonical K X Y J A D h);

protected symbol comma_classification_raw_basechange [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X))
 (D : τ (Functor K Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A)))))
 : τ (@Transf (Op_cat K) (Op_cat Y) (@comma_classification_target_section_after_basechange K X Y J A D h)
  (@comma_classification_target_section_canonical K X Y J A D h))
≔ @id (Functor_cat (Op_cat K) (Op_cat Y)) (@comma_classification_target_section_after_basechange K X Y J A D h);

protected symbol comma_classification_raw_sigma [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X))
 (D : τ (Functor K Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A)))))
 : τ (@Transf (Op_cat K) (Op_cat K) (@comma_classification_identity_section_projected K) (@comma_classification_middle_section_projected K
  X Y J A D h))
≔ @id (Functor_cat (Op_cat K) (Op_cat K)) (@comma_classification_identity_section_projected K);

protected symbol comma_classification_raw_identity [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X))
 (D : τ (Functor K Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A)))))
 : τ (@Transf (Op_cat K) (Op_cat K) (@id_func (Op_cat K)) (@comma_classification_identity_section_projected K))
≔ @id (Functor_cat (Op_cat K) (Op_cat K)) (@id_func (Op_cat K));

protected symbol comma_classification_raw_middle [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X))
 (D : τ (Functor K Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A)))))
 : τ (@Transf (Op_cat K) (Op_cat K) (@id_func (Op_cat K)) (@comma_classification_middle_section_projected K X Y J A D h))
≔ @comp_fapp0 (Functor_cat (Op_cat K) (Op_cat K)) (@id_func (Op_cat K)) (@comma_classification_identity_section_projected
  K) (@comma_classification_middle_section_projected K X Y J A D h)
   (@comma_classification_raw_sigma K X Y J A D h) (@comma_classification_raw_identity K X Y J A D h);

protected symbol comma_classification_raw_post [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X))
 (D : τ (Functor K Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A)))))
 : τ (@Transf (Op_cat K) (Op_cat Y) (@Op_func K Y D) (@comma_classification_target_section_after_basechange K X Y J A D
  h))
≔ @transf_postwhisker (Op_cat K) (Op_cat K) (Op_cat Y) (@Op_func K Y D) (@id_func (Op_cat K))
  (@comma_classification_middle_section_projected K X Y J A D h)
   (@comma_classification_raw_middle K X Y J A D h);

protected symbol comma_classification_raw_classification [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X))
 (D : τ (Functor K Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A)))))
 : τ (@Transf (Op_cat K) (Op_cat Y) (@Op_func K Y D) (@comma_section_gamma_target_section K X Y J A D h))
≔ @comp_fapp0 (Functor_cat (Op_cat K) (Op_cat Y)) (@Op_func K Y D) (@comma_classification_target_section_canonical K X Y J
  A D h) (@comma_section_gamma_target_section K X Y J A D h)
   (@comma_classification_raw_reindex K X Y J A D h)
   (@comp_fapp0 (Functor_cat (Op_cat K) (Op_cat Y)) (@Op_func K Y D)
  (@comma_classification_target_section_after_basechange K X Y J A D h) (@comma_classification_target_section_canonical K X Y J A D h)
     (@comma_classification_raw_basechange K X Y J A D h) (@comma_classification_raw_post K X Y J A D h));

protected symbol comma_classification_target_section_to_supplied [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X))
 (D : τ (Functor K Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A)))))
 : τ (@Transf K Y (@comma_section_gamma_target_section_op K X Y J A D h) D)
≔ @Op_transf (Op_cat K) (Op_cat Y) (@Op_func K Y D) (@comma_section_gamma_target_section K X Y J A D h)
   (@comma_classification_raw_classification K X Y J A D h);

protected symbol comma_classification_target_section_equiv [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X))
 (D : τ (Functor K Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A))))) (Y1 : τ (IsNCat (cat_succ
  cat_zero) Y))
 : τ (@OmegaEquivAlong (Functor_cat K Y) (@comma_section_gamma_target_section_op K X Y J A D h) D
  (@comma_classification_target_section_to_supplied K X Y J A D h))
≔ @strict_transf_pointwise_omega_along K Y (@comma_section_gamma_target_section_op K X Y J A D h) D
  (@comma_classification_target_section_to_supplied K X Y J A D h)
   (λ x : τ (Obj K), @omega_equiv_along_refl Y (@fapp0 K Y D x));

// The original whole target comparison q∘Γ⇒D for OneCat(Y).
symbol one_cat_represented_comma_hom_action_target_to [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X))
 (D : τ (Functor K Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A))))) (Y1 : τ (IsNCat (cat_succ
  cat_zero) Y))
 : τ (@Transf K Y (@represented_comma_hom_action_target_func K X Y J A D h) D)
≔ @comp_fapp0 (Functor_cat K Y) (@represented_comma_hom_action_target_func K X Y J A D h) (@comma_section_gamma_target_section_op K X
  Y J A D h) D (@comma_classification_target_section_to_supplied K X Y J A D h)
   (@omega_equiv_along_left_inv (Functor_cat K Y) (@comma_section_gamma_target_section_op K X Y J A D h)
  (@represented_comma_hom_action_target_func K X Y J A D h) (@comma_basechange_gamma_target_section_to_native K X Y J A D h)
  (@comma_basechange_gamma_target_section_to_native_equiv K X Y J A D h Y1));

// Its fixed-forward equivalence retains the selected inverse and whole laws.
symbol one_cat_represented_comma_hom_action_target_equiv [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X))
 (D : τ (Functor K Y)) (h : τ (@Transf (Op_cat K) (@Catd_cat K)
    (@hom_int K K (@id_func K))
    (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
      (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A))))) (Y1 : τ (IsNCat (cat_succ
  cat_zero) Y))
 : τ (@OmegaEquivAlong (Functor_cat K Y) (@represented_comma_hom_action_target_func K X Y J A D h) D
  (@one_cat_represented_comma_hom_action_target_to K X Y J A D h Y1))
≔ @iso_evidence_omega_along (Functor_cat K Y) (@represented_comma_hom_action_target_func K X Y J A D h) D
   (@iso_evidence_comp (Functor_cat K Y) (@represented_comma_hom_action_target_func K X Y J A D h)
  (@comma_section_gamma_target_section_op K X Y J A D h) D
     (@omega_equiv_along_iso_evidence (Functor_cat K Y) (@comma_section_gamma_target_section_op K X Y J A D h) D
  (@comma_classification_target_section_to_supplied K X Y J A D h) (@comma_classification_target_section_equiv K X Y J A D h Y1))
     (@iso_evidence_sym (Functor_cat K Y) (@comma_section_gamma_target_section_op K X Y J A D h)
  (@represented_comma_hom_action_target_func K X Y J A D h)
       (@omega_equiv_along_iso_evidence (Functor_cat K Y) (@comma_section_gamma_target_section_op K X Y J A D h)
  (@represented_comma_hom_action_target_func K X Y J A D h) (@comma_basechange_gamma_target_section_to_native K X Y J A D h)
  (@comma_basechange_gamma_target_section_to_native_equiv K X Y J A D h Y1))));


// Original Γ interface, specialized to the native Hom action of h.

symbol represented_comma_family_func [K X Y : Cat]
  (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y))
  (h : τ (@Transf K Y (@comp_cat_fapp0 K X Y J A) D))
  : τ (Functor K (@RepresentedComma_cat X Y J))
≔ @represented_comma_hom_action_func K X Y J A D (@tapp1_int_fapp0_transf K Y (@comp_cat_fapp0 K X Y J A) D h);

symbol represented_comma_family_source_func [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y)) (h
  : τ (@Transf K Y (@comp_cat_fapp0 K X Y J A) D)) : τ (Functor K X)
≔ @represented_comma_hom_action_source_func K X Y J A D (@tapp1_int_fapp0_transf K Y (@comp_cat_fapp0 K X Y J A) D h);

symbol represented_comma_family_source_evidence [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor
  K Y)) (h : τ (@Transf K Y (@comp_cat_fapp0 K X Y J A) D))
 : τ (IsoEvidence (Functor_cat K X) (@represented_comma_family_source_func K X Y J A D h) A)
≔ @represented_comma_hom_action_source_evidence K X Y J A D (@tapp1_int_fapp0_transf K Y (@comp_cat_fapp0 K X Y J A) D h);

symbol represented_comma_family_source_to [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y))
  (h : τ (@Transf K Y (@comp_cat_fapp0 K X Y J A) D))
 : τ (@Transf K X (@represented_comma_family_source_func K X Y J A D h) A)
≔ @represented_comma_hom_action_source_to K X Y J A D (@tapp1_int_fapp0_transf K Y (@comp_cat_fapp0 K X Y J A) D h);

symbol represented_comma_family_target_func [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K
  Y)) (h : τ (@Transf K Y (@comp_cat_fapp0 K X Y J A) D)) : τ (Functor K Y)
≔ @represented_comma_hom_action_target_func K X Y J A D (@tapp1_int_fapp0_transf K Y (@comp_cat_fapp0 K X Y J A) D h);

symbol one_cat_represented_comma_family_target_to [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X))
 (D : τ (Functor K Y)) (h : τ (@Transf K Y (@comp_cat_fapp0 K X Y J A) D)) (Y1 : τ (IsNCat (cat_succ
  cat_zero) Y))
 : τ (@Transf K Y (@represented_comma_family_target_func K X Y J A D h) D)
≔ @one_cat_represented_comma_hom_action_target_to K X Y J A D (@tapp1_int_fapp0_transf K Y (@comp_cat_fapp0 K X Y J A) D h) Y1;

symbol one_cat_represented_comma_family_target_equiv [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X))
 (D : τ (Functor K Y)) (h : τ (@Transf K Y (@comp_cat_fapp0 K X Y J A) D)) (Y1 : τ (IsNCat (cat_succ
  cat_zero) Y))
 : τ (@OmegaEquivAlong (Functor_cat K Y) (@represented_comma_family_target_func K X Y J A D h) D
  (@one_cat_represented_comma_family_target_to K X Y J A D h Y1))
≔ @one_cat_represented_comma_hom_action_target_equiv K X Y J A D (@tapp1_int_fapp0_transf K Y (@comp_cat_fapp0 K X Y J A) D h) Y1;
