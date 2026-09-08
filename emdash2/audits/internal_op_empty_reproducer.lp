/*
  NON-LIBRARY SOUNDNESS DIAGNOSTIC — internal opposite variance.

  This reproducer is accepted by the pre-repair kernel and derives its
  decoded empty carrier. Acceptance reproduces the defect; it is not a green
  mathematical feature test. After a proper variance repair, this derivation
  must be rejected while legitimate opposite operations still check.

  Do not import this module into the library or register it as a positive
  reviewer. It adds no rewrite, unifier, primitive witness or extra axiom.
  See docs/TYPESCRIPT_EMDASH_INTERNAL_OP_VARIANCE_DIAGNOSTIC.md at Git root.
*/
require open emdash.emdash3_2;

symbol internal_op_arrow_reverse
  [C : Cat] (x y : τ (Obj C)) (f : τ (Hom C x y))
  : τ (Hom C y x)
≔ @tapp0_fapp0 Terminal_cat (Op_cat C)
    (@Op_func Terminal_cat C (@Obj_func C x))
    (@Op_func Terminal_cat C (@Obj_func C y))
    Terminal_obj
    (@fapp1_fapp0
      (Functor_cat Terminal_cat C)
      (Functor_cat Terminal_cat (Op_cat C))
      (@fapp1_func Cat_cat Cat_cat op Terminal_cat C)
      (@Obj_func C x) (@Obj_func C y)
      (@Const_transf Terminal_cat C x y f));

// Reverse the ordinary function Empty→Unit, then apply it to tt.
symbol internal_op_empty_witness
  : τ Empty_grpd
≔ (@internal_op_arrow_reverse Grpd_cat Empty_grpd Unit_grpd
    (λ _ : τ Empty_grpd, tt)) tt;

assert ⊢ internal_op_empty_witness : τ Empty_grpd;
