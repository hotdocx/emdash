/*
  Emdash v3.2: computational strict-functor codes and one Gray-hom profile.

  Strictness is a syntactic, sorted boundary.  A StrictFunctorData code
  decodes through a stable carrier head into the shared ambient Functor
  classifier.  The existing extracted compositor computes to identity only
  at that decoded shape; ordinary ambient functors retain their laxity cell.

  GrayHom_oplax is the selected strict-object/lax-arrow category.  Its homs
  are the existing Transf_cat homs between decoded carriers, so modifications
  and every subsequent iterated hom remain owned by the ambient calculus.
  The oplax name remains provisional until the right-closure I tensor I
  consumer confirms the direction of the interchanger.
*/

require open emdash.emdash3_2;

// Primitive code sort for functors carrying selected computational strictness.
injective symbol StrictFunctorData
  (A B : Cat)
  : Grpd;

// Stable decoding into the shared ambient functor classifier.
injective symbol strict_functor_carrier
  [A B : Cat]
  (S : τ (@StrictFunctorData A B))
  : τ (Functor A B);

// Formal post/left endpoint of the extracted ordinary compositor.
symbol strict_functor_compositor_lhs
  [A B : Cat]
  (F : τ (Functor A B))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
  : τ (Hom B (fapp0 F X) (fapp0 F Z))
≔ @fapp0
    (Hom_cat A X Y)
    (Hom_cat B (fapp0 F X) (fapp0 F Z))
    (@functord_transport_lhs_func
      A
      (@hom_ A A (@id_func A) X)
      (@hom_ B A F (@fapp0 A B F X))
      (@fapp1_at_transf A B F X)
      Y Z g)
    f;

// Formal pre/right endpoint of the extracted ordinary compositor.
symbol strict_functor_compositor_rhs
  [A B : Cat]
  (F : τ (Functor A B))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
  : τ (Hom B (fapp0 F X) (fapp0 F Z))
≔ @fapp0
    (Hom_cat A X Y)
    (Hom_cat B (fapp0 F X) (fapp0 F Z))
    (@functord_transport_rhs_func
      A
      (@hom_ A A (@id_func A) X)
      (@hom_ B A F (@fapp0 A B F X))
      (@fapp1_at_transf A B F X)
      Y Z g)
    f;

/*
  Selected strict compositor computation at the active stable owner.

  The current prototype's tracked global strict cuts already identify the
  formal endpoints.  A later cut migration must re-home that conversion at
  the same strict_functor_carrier shape; this rule does not add a generic
  endpoint comparison.

  lhs-audit: keep 1,2,3,4 -- the represented source, represented target,
  decoded carrier, and fixed source object guard this strict specialization.
*/
rule @fdapp1_int_cell
      $A
      (@hom_ $A $A (@id Cat_cat $A) $X)
      (@hom_
        $B $A
        (@strict_functor_carrier $A $B $S)
        (@fapp0
          $A $B
          (@strict_functor_carrier $A $B $S)
          $X))
      (@fapp1_at_transf
        $A $B
        (@strict_functor_carrier $A $B $S)
        $X)
      $Y $Z $g $f
  ↪ @id
      (Hom_cat
        $B
        (@fapp0
          $A $B
          (@strict_functor_carrier $A $B $S)
          $X)
        (@fapp0
          $A $B
          (@strict_functor_carrier $A $B $S)
          $Z))
      (@strict_functor_compositor_lhs
        $A $B
        (@strict_functor_carrier $A $B $S)
        $X $Y $Z $g $f);

// Selected identity code. Its stable carrier remains the strict discriminator.
injective symbol strict_identity_data
  (A : Cat)
  : τ (@StrictFunctorData A A);

// Whole semantic observation of the selected identity carrier.
constant symbol strict_identity_carrier_path
  (A : Cat)
  : τ (@=
      (Functor A A)
      (@strict_functor_carrier A A (@strict_identity_data A))
      (@id_func A));

// Strict-object/lax-arrow right-hom profile.
injective symbol GrayHom_oplax
  (A B : Cat)
  : Cat;

rule Obj (@GrayHom_oplax $A $B)
  ↪ @StrictFunctorData $A $B;

rule Hom_cat (@GrayHom_oplax $A $B) $X $Y
  ↪ @Transf_cat
      $A $B
      (@strict_functor_carrier $A $B $X)
      (@strict_functor_carrier $A $B $Y);

// Identity delegates to the ambient functor category.
rule @id (@GrayHom_oplax $A $B) $X
  ↪ @id
      (@Functor_cat $A $B)
      (@strict_functor_carrier $A $B $X);

// Composition delegates to the ambient functor category.
// lhs-audit: keep 2,3,4 -- the carrier projections occur on the RHS.
rule @comp_fapp0
      (@GrayHom_oplax $A $B) $X $Y $Z $g $f
  ↪ @comp_fapp0
      (@Functor_cat $A $B)
      (@strict_functor_carrier $A $B $X)
      (@strict_functor_carrier $A $B $Y)
      (@strict_functor_carrier $A $B $Z)
      $g $f;

// Whole inclusion into the shared ambient functor category.
injective symbol grayhom_oplax_include_func
  (A B : Cat)
  : τ (Functor
      (@GrayHom_oplax A B)
      (@Functor_cat A B));

rule @fapp0 _ _ (@grayhom_oplax_include_func $A $B) $X
  ↪ @strict_functor_carrier $A $B $X;

// The profile is full on the reused ambient transformation homs.
rule @fapp1_func _ _
      (@grayhom_oplax_include_func $A $B) $X $Y
  ↪ @id_func
      (@Transf_cat
        $A $B
        (@strict_functor_carrier $A $B $X)
        (@strict_functor_carrier $A $B $Y));
