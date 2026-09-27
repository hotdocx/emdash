/*
  Inherited pointwise-to-whole fixed-forward equivalence assembly.

  This module takes an existing whole ordinary Transf or displayed Transfd
  and pointwise OmegaEquivAlong evidence. It declares whole left and right
  inverse transformations, preserves both selected component inverse choices
  through beta rules, and assumes whole cancellation paths.

  The historical strict_* names do not impose an IsStrictTransfor premise.
  Assembly is a primitive assumption of the selected integration baseline,
  not a derivation from strict or lax naturality. Its interpretation is not
  established merely by the downstream checks; explicit-profile replacement
  research is deferred separately.

  Consumers supply no new component naturality square. This interface does
  not turn an arbitrary family of arrows into a transformation, identify all
  pointwise-equal functors, or add runtime extensionality or univalence.
*/

require open emdash.emdash3_2;

// Fixed-forward pointwise equivalence evidence for one whole transformation.
symbol StrictTransfPointwiseOmegaAlong
  [A B : Cat]
  [F G : τ (@Functor A B)]
  (eta : τ (@Transf A B F G))
  : Grpd
≔ @Pi_grpd
    (Obj A)
    (λ x : τ (Obj A),
      @OmegaEquivAlong
        B
        (@fapp0 A B F x)
        (@fapp0 A B G x)
        (@tapp0_fapp0 A B F G x eta));

// Whole left inverse assembled from the selected component inverses.
injective symbol strict_transf_pointwise_left_inverse
  [A B : Cat]
  [F G : τ (@Functor A B)]
  (eta : τ (@Transf A B F G))
  (u : τ (@StrictTransfPointwiseOmegaAlong A B F G eta))
  : τ (@Transf A B G F);

rule @tapp0_fapp0 _ _ _ _ $x
      (@strict_transf_pointwise_left_inverse $A $B $F $G $eta $u)
  ↪ @omega_equiv_along_left_inv
      $B
      (@fapp0 $A $B $F $x)
      (@fapp0 $A $B $G $x)
      (@tapp0_fapp0 $A $B $F $G $x $eta)
      ($u $x);

// Whole right inverse assembled from the selected component inverses.
injective symbol strict_transf_pointwise_right_inverse
  [A B : Cat]
  [F G : τ (@Functor A B)]
  (eta : τ (@Transf A B F G))
  (u : τ (@StrictTransfPointwiseOmegaAlong A B F G eta))
  : τ (@Transf A B G F);

rule @tapp0_fapp0 _ _ _ _ $x
      (@strict_transf_pointwise_right_inverse $A $B $F $G $eta $u)
  ↪ @omega_equiv_along_right_inv
      $B
      (@fapp0 $A $B $F $x)
      (@fapp0 $A $B $G $x)
      (@tapp0_fapp0 $A $B $F $G $x $eta)
      ($u $x);

/*
  Primitive whole cancellation assembly.  These are generic strict-
  transformation structure, necessitated by the primitive `Transf`
  classifier; they are not consumer-supplied coherence and do not compute on
  arbitrary component families.
*/
constant symbol strict_transf_pointwise_left_law
  [A B : Cat]
  [F G : τ (@Functor A B)]
  (eta : τ (@Transf A B F G))
  (u : τ (@StrictTransfPointwiseOmegaAlong A B F G eta))
  : τ (@=
      (Hom (@Functor_cat A B) F F)
      (@comp_fapp0
        (@Functor_cat A B)
        F G F
        (@strict_transf_pointwise_left_inverse A B F G eta u)
        eta)
      (@id (@Functor_cat A B) F));

constant symbol strict_transf_pointwise_right_law
  [A B : Cat]
  [F G : τ (@Functor A B)]
  (eta : τ (@Transf A B F G))
  (u : τ (@StrictTransfPointwiseOmegaAlong A B F G eta))
  : τ (@=
      (Hom (@Functor_cat A B) G G)
      (@comp_fapp0
        (@Functor_cat A B)
        G F G
        eta
        (@strict_transf_pointwise_right_inverse A B F G eta u))
      (@id (@Functor_cat A B) G));

// Whole fixed-forward equivalence selected by strict pointwise evidence.
symbol strict_transf_pointwise_omega_along
  [A B : Cat]
  [F G : τ (@Functor A B)]
  (eta : τ (@Transf A B F G))
  (u : τ (@StrictTransfPointwiseOmegaAlong A B F G eta))
  : τ (@OmegaEquivAlong (@Functor_cat A B) F G eta)
≔ @omega_equiv_along_intro
    (@Functor_cat A B)
    F G eta
    (@strict_transf_pointwise_left_inverse A B F G eta u)
    (@strict_transf_pointwise_right_inverse A B F G eta u)
    (@strict_transf_pointwise_left_law A B F G eta u)
    (@strict_transf_pointwise_right_law A B F G eta u);

// Equality observation obtained from the whole fixed-forward equivalence.
symbol strict_transf_pointwise_path
  [A B : Cat]
  [F G : τ (@Functor A B)]
  (eta : τ (@Transf A B F G))
  (u : τ (@StrictTransfPointwiseOmegaAlong A B F G eta))
  : τ (@= (Obj (@Functor_cat A B)) F G)
≔ @omega_cast_to_object_path
    (@Functor_cat A B)
    F G
    (@omega_equiv_pack
      (@Functor_cat A B)
      F G eta
      (@strict_transf_pointwise_omega_along A B F G eta u));

// Displayed fixed-forward pointwise evidence over one whole transformation.
symbol StrictTransfdPointwiseOmegaAlong
  [K : Cat]
  [E D : τ (@Catd K)]
  [FF GG : τ (@Functord K E D)]
  (eta : τ (@Transfd K E D FF GG))
  : Grpd
≔ @Pi_grpd
    (Obj K)
    (λ x : τ (Obj K),
      @OmegaEquivAlong
        (@Functor_cat
          (@Fibre_cat K E x)
          (@Fibre_cat K D x))
        (@Fibre_func K E D FF x)
        (@Fibre_func K E D GG x)
        (@tdapp0_fapp0 K E D FF GG x eta));

// Whole displayed left inverse with selected fibre components.
injective symbol strict_transfd_pointwise_left_inverse
  [K : Cat]
  [E D : τ (@Catd K)]
  [FF GG : τ (@Functord K E D)]
  (eta : τ (@Transfd K E D FF GG))
  (u : τ (@StrictTransfdPointwiseOmegaAlong K E D FF GG eta))
  : τ (@Transfd K E D GG FF);

rule @tdapp0_fapp0 _ _ _ _ _ $x
      (@strict_transfd_pointwise_left_inverse
        $K $E $D $FF $GG $eta $u)
  ↪ @omega_equiv_along_left_inv
      (@Functor_cat
        (@Fibre_cat $K $E $x)
        (@Fibre_cat $K $D $x))
      (@Fibre_func $K $E $D $FF $x)
      (@Fibre_func $K $E $D $GG $x)
      (@tdapp0_fapp0 $K $E $D $FF $GG $x $eta)
      ($u $x);

// Whole displayed right inverse with selected fibre components.
injective symbol strict_transfd_pointwise_right_inverse
  [K : Cat]
  [E D : τ (@Catd K)]
  [FF GG : τ (@Functord K E D)]
  (eta : τ (@Transfd K E D FF GG))
  (u : τ (@StrictTransfdPointwiseOmegaAlong K E D FF GG eta))
  : τ (@Transfd K E D GG FF);

rule @tdapp0_fapp0 _ _ _ _ _ $x
      (@strict_transfd_pointwise_right_inverse
        $K $E $D $FF $GG $eta $u)
  ↪ @omega_equiv_along_right_inv
      (@Functor_cat
        (@Fibre_cat $K $E $x)
        (@Fibre_cat $K $D $x))
      (@Fibre_func $K $E $D $FF $x)
      (@Fibre_func $K $E $D $GG $x)
      (@tdapp0_fapp0 $K $E $D $FF $GG $x $eta)
      ($u $x);

// Generic whole cancellation assembly for displayed transformations.
constant symbol strict_transfd_pointwise_left_law
  [K : Cat]
  [E D : τ (@Catd K)]
  [FF GG : τ (@Functord K E D)]
  (eta : τ (@Transfd K E D FF GG))
  (u : τ (@StrictTransfdPointwiseOmegaAlong K E D FF GG eta))
  : τ (@=
      (Hom (@Functord_cat K E D) FF FF)
      (@comp_fapp0
        (@Functord_cat K E D)
        FF GG FF
        (@strict_transfd_pointwise_left_inverse K E D FF GG eta u)
        eta)
      (@id (@Functord_cat K E D) FF));

constant symbol strict_transfd_pointwise_right_law
  [K : Cat]
  [E D : τ (@Catd K)]
  [FF GG : τ (@Functord K E D)]
  (eta : τ (@Transfd K E D FF GG))
  (u : τ (@StrictTransfdPointwiseOmegaAlong K E D FF GG eta))
  : τ (@=
      (Hom (@Functord_cat K E D) GG GG)
      (@comp_fapp0
        (@Functord_cat K E D)
        GG FF GG
        eta
        (@strict_transfd_pointwise_right_inverse K E D FF GG eta u))
      (@id (@Functord_cat K E D) GG));

// Whole displayed fixed-forward equivalence.
symbol strict_transfd_pointwise_omega_along
  [K : Cat]
  [E D : τ (@Catd K)]
  [FF GG : τ (@Functord K E D)]
  (eta : τ (@Transfd K E D FF GG))
  (u : τ (@StrictTransfdPointwiseOmegaAlong K E D FF GG eta))
  : τ (@OmegaEquivAlong (@Functord_cat K E D) FF GG eta)
≔ @omega_equiv_along_intro
    (@Functord_cat K E D)
    FF GG eta
    (@strict_transfd_pointwise_left_inverse K E D FF GG eta u)
    (@strict_transfd_pointwise_right_inverse K E D FF GG eta u)
    (@strict_transfd_pointwise_left_law K E D FF GG eta u)
    (@strict_transfd_pointwise_right_law K E D FF GG eta u);
