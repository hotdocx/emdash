/* NON-LIBRARY opposite-family observations on arbitrary bases and maps.
   These checks do not assert that the imported old kernel is repaired. */
require open emdash.audits.internal_op_co2_families_prototype;

assert [K : Cat] (E : τ (Catd K)) ⊢
  @fapp0 (Co2_cat (Catd_cat K)) (Catd_cat (Co2_cat K))
    (op_co2_catd_func K) E
  ≡ @op_co2_catd K E;

assert [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D)) (k : τ (Obj K)) ⊢
  @tapp0_fapp0 (Co2_cat K) Cat_cat
    (@op_co2_catd K E) (@op_co2_catd K D) k
    (@op_co2_funcd K E D FF)
  ≡ @Op_func (@fapp0 K Cat_cat E k) (@fapp0 K Cat_cat D k)
      (@tapp0_fapp0 K Cat_cat E D k FF);

assert [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D)) [x y : τ (Obj K)]
  (p : τ (Hom K x y)) ⊢
  @tapp1_fapp0 (Co2_cat K) Cat_cat
    (@op_co2_catd K E) (@op_co2_catd K D) x y
    (@op_co2_funcd K E D FF) p
  ≡ @Op_func (@fapp0 K Cat_cat E x) (@fapp0 K Cat_cat D y)
      (@tapp1_fapp0 K Cat_cat E D x y FF p);

assert [K : Cat] [E D : τ (Catd K)] ⊢
  @fapp1_func (Co2_cat (Catd_cat K)) (Catd_cat (Co2_cat K))
    (op_co2_catd_func K) E D
  : τ (Functor
      (Op_cat (@Functord_cat K E D))
      (@Functord_cat (Co2_cat K) (@op_co2_catd K E) (@op_co2_catd K D)));

// No implicit same-base identification is added by the prototype.
assertnot [K : Cat] (E : τ (Catd K)) ⊢
  @op_co2_catd K E : τ (Catd K);

// The prior raw-composition view remains a proof-time comparison, supplied
// by the existing generic postcomposition usability rule.
assert [K : Cat] (E : τ (Catd K)) ⊢
  @eq_refl (Catd (Co2_cat K)) (@op_co2_catd K E)
  : τ (@= (Catd (Co2_cat K)) (@op_co2_catd K E)
      (@comp_cat_fapp0 (Co2_cat K) (Co2_cat Cat_cat) Cat_cat
        op_co2 (@Co2_func K Cat_cat E)));

assert [K : Cat] [E D : τ (Catd K)] [FF GG : τ (Functord E D)]
  (eta : τ (@Transfd K E D FF GG)) (k : τ (Obj K)) ⊢
  @tdapp0_fapp0 (Co2_cat K) (@op_co2_catd K E) (@op_co2_catd K D)
    (@op_co2_funcd K E D GG) (@op_co2_funcd K E D FF) k
    (@op_co2_transfd K E D FF GG eta)
  ≡ @Op_transf (@fapp0 K Cat_cat E k) (@fapp0 K Cat_cat D k)
      (@tapp0_fapp0 K Cat_cat E D k FF)
      (@tapp0_fapp0 K Cat_cat E D k GG)
      (@tdapp0_fapp0 K E D FF GG k eta);

// A genuine base 2-cell tests action of the retained whole tapp1 functor.
assert [K : Cat] [E D : τ (Catd K)] (FF : τ (Functord E D))
  [x y : τ (Obj K)] [p q : τ (Hom K x y)]
  (a : τ (Hom (Hom_cat K x y) p q)) ⊢
  @fapp1_fapp0
    (Op_cat (Hom_cat K x y))
    (Functor_cat (Op_cat (@fapp0 K Cat_cat E x))
      (Op_cat (@fapp0 K Cat_cat D y)))
    (@tapp1_func (Co2_cat K) Cat_cat
      (@op_co2_catd K E) (@op_co2_catd K D) x y
      (@op_co2_funcd K E D FF)) q p a
  ≡ @Op_transf
      (@fapp0 K Cat_cat E x) (@fapp0 K Cat_cat D y)
      (@tapp1_fapp0 K Cat_cat E D x y FF p)
      (@tapp1_fapp0 K Cat_cat E D x y FF q)
      (@fapp1_fapp0
        (Hom_cat K x y)
        (Functor_cat (@fapp0 K Cat_cat E x) (@fapp0 K Cat_cat D y))
        (@tapp1_func K Cat_cat E D x y FF) p q a);

// A further whole action remains after displayed-transformation projection.
assert [K : Cat] [E D : τ (Catd K)] [FF GG : τ (Functord E D)]
  [eta theta : τ (@Transfd K E D FF GG)] ⊢
  @fapp1_func (@Transfd_cat K E D FF GG)
    (@Transfd_cat (Co2_cat K) (@op_co2_catd K E) (@op_co2_catd K D)
      (@op_co2_funcd K E D GG) (@op_co2_funcd K E D FF))
    (@op_co2_transfd_func K E D FF GG) eta theta
  : τ (Functor
      (Hom_cat (@Transfd_cat K E D FF GG) eta theta)
      (Hom_cat
        (@Transfd_cat (Co2_cat K) (@op_co2_catd K E) (@op_co2_catd K D)
          (@op_co2_funcd K E D GG) (@op_co2_funcd K E D FF))
        (@op_co2_transfd K E D FF GG eta)
        (@op_co2_transfd K E D FF GG theta)));

assertnot [K : Cat] [E D : τ (Catd K)] [FF GG : τ (Functord E D)]
  (eta : τ (@Transfd K E D FF GG)) ⊢
  @op_co2_transfd K E D FF GG eta
  : τ (@Transfd (Co2_cat K) (@op_co2_catd K E) (@op_co2_catd K D)
      (@op_co2_funcd K E D FF) (@op_co2_funcd K E D GG));
