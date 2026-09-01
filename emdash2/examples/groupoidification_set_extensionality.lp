/* Reviewer-facing set-target extensionality for generic groupoidification. */

require open emdash.emdash3_2_groupoidification_set_extensionality;

// Point components compute to the supplied paths without manual naturality.
assert [C : Cat] [S : Grpd]
  (S_set : τ (IsSetGrpd S))
  [F G : τ (Functor C (Path_cat S))]
  (p : τ (@SetPathPointwiseData C S F G))
  (x : τ (Obj C)) ⊢
  @tapp0_fapp0 C (Path_cat S) F G x
    (@set_path_pointwise_transf C S S_set F G p)
  ≡ p x;

// The assembled arrow is a whole transformation with retained higher action.
assert [C : Cat] [S : Grpd]
  (S_set : τ (IsSetGrpd S))
  [F G : τ (Functor C (Path_cat S))]
  (p : τ (@SetPathPointwiseData C S F G))
  (x : τ (Obj C)) ⊢
  @tapp0_hom_fapp0
    C (Path_cat S) F G
    (@set_path_pointwise_transf C S S_set F G p)
    (@set_path_pointwise_transf C S S_set F G p)
    x
    (@id
      (@Transf_cat C (Path_cat S) F G)
      (@set_path_pointwise_transf C S S_set F G p))
  ≡ @id
      (Hom_cat (Path_cat S)
        (@fapp0 C (Path_cat S) F x)
        (@fapp0 C (Path_cat S) G x))
      (p x);

// Distinct arbitrary pointwise inputs do not collapse definitionally.
assertnot [C : Cat] [S : Grpd]
  (S_set : τ (IsSetGrpd S))
  [F G : τ (Functor C (Path_cat S))]
  (p q : τ (@SetPathPointwiseData C S F G)) ⊢
  @set_path_pointwise_transf C S S_set F G p
  ≡ @set_path_pointwise_transf C S S_set F G q;

// Agreement on unit points gives equality of arbitrary maps into a set.
assert [C : Cat] [S : Grpd]
  (S_set : τ (IsSetGrpd S))
  [h k : τ (Function_grpd (Groupoidify C) S)]
  (p : τ (@GroupoidifySetUnitPaths C S h k)) ⊢
  @groupoidify_set_map_ext C S S_set h k p
  : τ (@= (@Function_grpd (Groupoidify C) S) h k);

// The source remains visible; unrelated groupoidifications do not collapse.
assertnot [C D : Cat] [S : Grpd]
  (S_set : τ (IsSetGrpd S)) ⊢
  @Function_grpd (Groupoidify C) S
  ≡ @Function_grpd (Groupoidify D) S;
