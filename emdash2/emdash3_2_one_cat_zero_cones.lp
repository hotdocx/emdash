/* Whole universal observation on the EXISTING native comma.
   For a one-categorical C, the native comma's modification cells express
   equalities of arrow-diagram transformations, so the tautological family
   is natural. This does not convert arbitrary cells in an arbitrary C. */
require open emdash.emdash3_2_zero_arrow_cones;

// Canonical assembly owner, not an opaque equality or a new comma category.
// C1 ensures the required pointwise naturality and higher coherence; callers
// supply no additional square or prism field.
injective symbol zero_arrow_cone_universal_transf
  [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  : τ (@Transf (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
      (@comp_cat_fapp0 (@ZeroArrowCone_cat C t T) C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T) (@zero_arrow_cone_first_func C t T))
      (@zero_arrow_cone_diagram_func C t T));

rule @tapp0_fapp0 _ _ _ _
      (Struct_sigma _ (Struct_sigma _ $h))
      (@zero_arrow_cone_universal_transf _ _ _ _)
  ↪ $h;

// The generic transfor identity cut has lost its literal opposite identity.
// Observe the original cone arrow at this constructor-visible universal cell.
// lhs-audit: keep 1,5,6 -- retain the qualified opposite-source, constructor-visible identity endpoints.
rule @tapp1_fapp0 (Op_cat $K) _ _ _
    (Struct_sigma $a (Struct_sigma $d $h))
    (Struct_sigma $a (Struct_sigma $d $h))
    (@zero_arrow_cone_universal_transf _ _ _ _)
    (@id $K (Struct_sigma $a (Struct_sigma $d $h)))
  ↪ $h;
