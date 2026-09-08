/* NON-LIBRARY whole opposite-family prototype. The imported old kernel is
   still unrepaired. Do not import into the library or register as a positive
   feature. See docs/TYPESCRIPT_EMDASH_INTERNAL_OP_VARIANCE_REPAIR_PLAN.md. */
require open emdash.audits.internal_op_co2_prototype;

// Co2 acts on the whole functor category with dimension-two variance.
injective symbol Co2_functor_cat_func (A B : Cat)
  : τ (Functor (Co2_cat (Functor_cat A B))
      (Functor_cat (Co2_cat A) (Co2_cat B)));
rule @fapp0 _ _ (Co2_functor_cat_func $A $B) $F
  ↪ @Co2_func $A $B $F;

// A readable transfor view of that functor's existing full hom action.
symbol Co2_transf [A B : Cat] [F G : τ (Functor A B)]
  (eta : τ (Transf F G))
  : τ (Transf (@Co2_func A B F) (@Co2_func A B G))
≔ @fapp1_fapp0 (Co2_cat (Functor_cat A B))
    (Functor_cat (Co2_cat A) (Co2_cat B))
    (Co2_functor_cat_func A B) F G eta;

// Transformation components are 1-arrows, so their direction is unchanged.
rule @tapp0_fapp0 _ _ _ _ $x
      (@fapp1_fapp0 _ _ (Co2_functor_cat_func $A $B) $F $G $eta)
  ↪ @tapp0_fapp0 $A $B $F $G $x $eta;

// Keep the whole off-diagonal action through Op_func, not only its cap.
rule @tapp1_func _ _ _ _ $x $y
      (@fapp1_fapp0 _ _ (Co2_functor_cat_func $A $B) $F $G $eta)
  ↪ @Op_func (Hom_cat $A $x $y)
      (Hom_cat $B (@fapp0 $A $B $F $x) (@fapp0 $A $B $G $y))
      (@tapp1_func $A $B $F $G $x $y $eta);
rule @tapp1_fapp0 _ _ _ _ $x $y
      (@fapp1_fapp0 _ _ (Co2_functor_cat_func $A $B) $F $G $eta) $f
  ↪ @tapp1_fapp0 $A $B $F $G $x $y $eta $f;

// Compose the two generic whole operators; no new family-operation primitive.
symbol op_co2_catd_func (K : Cat)
  : τ (Functor (Co2_cat (Catd_cat K)) (Catd_cat (Co2_cat K)))
≔ @comp_cat_fapp0
    (Co2_cat (Catd_cat K))
    (Functor_cat (Co2_cat K) (Co2_cat Cat_cat))
    (Catd_cat (Co2_cat K))
    (@comp_cat_cov_func (Co2_cat K) (Co2_cat Cat_cat) Cat_cat op_co2)
    (Co2_functor_cat_func K Cat_cat);

symbol op_co2_funcd [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  : τ (@Functord (Co2_cat K) (@op_co2_catd K E) (@op_co2_catd K D))
≔ @fapp1_fapp0 (Co2_cat (Catd_cat K)) (Catd_cat (Co2_cat K))
    (op_co2_catd_func K) E D FF;

// The existing whole hom actions provide both displayed comparison levels.
symbol op_co2_funcd_func [K : Cat] (E D : τ (Catd K))
  : τ (Functor (Op_cat (@Functord_cat K E D))
      (@Functord_cat (Co2_cat K) (@op_co2_catd K E) (@op_co2_catd K D)))
≔ @fapp1_func (Co2_cat (Catd_cat K)) (Catd_cat (Co2_cat K))
    (op_co2_catd_func K) E D;

symbol op_co2_transfd_func [K : Cat] [E D : τ (Catd K)]
  (FF GG : τ (Functord E D))
  : τ (Functor (@Transfd_cat K E D FF GG)
      (@Transfd_cat (Co2_cat K) (@op_co2_catd K E) (@op_co2_catd K D)
        (@op_co2_funcd K E D GG) (@op_co2_funcd K E D FF)))
≔ @fapp1_func (Op_cat (@Functord_cat K E D))
    (@Functord_cat (Co2_cat K) (@op_co2_catd K E) (@op_co2_catd K D))
    (@op_co2_funcd_func K E D) GG FF;

symbol op_co2_transfd [K : Cat] [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)] (eta : τ (@Transfd K E D FF GG))
  : τ (@Transfd (Co2_cat K) (@op_co2_catd K E) (@op_co2_catd K D)
      (@op_co2_funcd K E D GG) (@op_co2_funcd K E D FF))
≔ @fapp0 (@Transfd_cat K E D FF GG)
    (@Transfd_cat (Co2_cat K) (@op_co2_catd K E) (@op_co2_catd K D)
      (@op_co2_funcd K E D GG) (@op_co2_funcd K E D FF))
    (@op_co2_transfd_func K E D FF GG) eta;

// The Co2 functor-category action reverses modifications; evaluation reads
// the underlying 2-cell in the reversed Hom, rather than choosing an inverse.
rule @tapp0_hom_fapp0 _ _ _ _ _ _ $x
      (@fapp1_fapp0 _ _
        (@fapp1_func _ _ (Co2_functor_cat_func $A $B) $F $G)
        $eta $theta $alpha)
  ↪ @tapp0_hom_fapp0 $A $B $F $G $theta $eta $x $alpha;

// Generic Cat-valued postcomposition of a modification, not an op-specific
// rule. In a kernel migration this belongs with the component/whiskering
// owner. The RHS uses G's whole Hom action and the original higher component.
// lhs-audit: keep 1,2 -- Cat_cat identifies composition of actual functors.
// The inner literal universe identity is an SR guard: id _ _ leaves its
// fapp0/fapp1 actions unresolved in the wildcard control.
rule @tdapp0_fapp0 _ _ _ _ _ $x
      (@fapp1_fapp0 _ _
        (@hom_postcomp_fapp1_func Cat_cat Cat_cat (@id Cat_cat Cat_cat)
          $X $Y Cat_cat $G $F $H)
        $eta $theta $alpha)
  ↪ @fapp1_fapp0
      (Hom_cat $Y (@fapp0 $X $Y $F $x) (@fapp0 $X $Y $H $x))
      (Functor_cat
        (@fapp0 $Y Cat_cat $G (@fapp0 $X $Y $F $x))
        (@fapp0 $Y Cat_cat $G (@fapp0 $X $Y $H $x)))
      (@fapp1_func $Y Cat_cat $G
        (@fapp0 $X $Y $F $x) (@fapp0 $X $Y $H $x))
      (@tapp0_fapp0 $X $Y $F $H $x $eta)
      (@tapp0_fapp0 $X $Y $F $H $x $theta)
      (@tapp0_hom_fapp0 $X $Y $F $H $eta $theta $x $alpha);
