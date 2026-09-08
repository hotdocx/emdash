/* NON-LIBRARY SOUNDNESS DIAGNOSTIC: the old same-base opposite-family
   interface reconstructs a covariant universe op and hence a decoded Empty.
   Acceptance reproduces the defect, not a positive mathematical feature.
   No primitive witness, rewrite or unifier is added. Do not import into the
   library or register as a positive reviewer. The deferred repair runner is
   scripts/check_total_op_prefix.sh. */
require open emdash.emdash3_2;

symbol reconstructed_covariant_op : τ (Functor Cat_cat Cat_cat)
≔ @Op_catd Cat_cat (@id_func Cat_cat);

symbol family_op_arrow_reverse
  [C : Cat] (x y : τ (Obj C)) (f : τ (Hom C x y))
  : τ (Hom C y x)
≔ @tapp0_fapp0 Terminal_cat (Op_cat C)
    (@Op_func Terminal_cat C (@Obj_func C x))
    (@Op_func Terminal_cat C (@Obj_func C y))
    Terminal_obj
    (@fapp1_fapp0
      (Functor_cat Terminal_cat C)
      (Functor_cat Terminal_cat (Op_cat C))
      (@fapp1_func Cat_cat Cat_cat reconstructed_covariant_op Terminal_cat C)
      (@Obj_func C x) (@Obj_func C y)
      (@Const_transf Terminal_cat C x y f));

symbol family_op_empty_witness : τ Empty_grpd
≔ (@family_op_arrow_reverse Grpd_cat Empty_grpd Unit_grpd
    (λ _ : τ Empty_grpd, tt)) tt;

assert ⊢ family_op_empty_witness : τ Empty_grpd;
