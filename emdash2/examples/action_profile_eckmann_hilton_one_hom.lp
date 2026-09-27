/* Actual ordinary-hom consumer of the migrated EH statement. */
require open emdash.emdash3_2_profiled_interchange;
require open emdash.emdash3_2_one_cat_transfor_profiles;

symbol api_EH_comm_one_hom
  [B : Cat] (x : τ (Obj B))
  (D1 : τ (IsNCat (cat_succ cat_zero) (Hom_cat B x x)))
  (alpha beta : τ (Obj (@EH_2End B x)))
  : τ (@= (Obj (@EH_2End B x)) (@EH_vcomp B x beta alpha) (@EH_vcomp B x alpha beta))
≔ @EH_comm B x alpha beta
    (@one_cat_transfor_is_strict (Hom_cat B x x) (Hom_cat B x x) D1
      (@id_func (Hom_cat B x x)) (@id_func (Hom_cat B x x))
      (@hom_postcomp_tele_fapp1_fapp0 B B (@id_func B) x x x
        (@id B x) (@id B x) beta));

assert [B : Cat] (x : τ (Obj B))
  (D1 : τ (IsNCat (cat_succ cat_zero) (Hom_cat B x x)))
  (alpha beta : τ (Obj (@EH_2End B x))) ⊢
  @api_EH_comm_one_hom B x D1 alpha beta
  : τ (@= (Obj (@EH_2End B x)) (@EH_vcomp B x beta alpha) (@EH_vcomp B x alpha beta));

assertnot [B : Cat] (x : τ (Obj B))
  (alpha beta : τ (Obj (@EH_2End B x))) ⊢
  @EH_comm B x alpha beta
  : τ (@= (Obj (@EH_2End B x)) (@EH_vcomp B x beta alpha) (@EH_vcomp B x alpha beta));
