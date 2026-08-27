/*
  Emdash v3.2: strict-functor property packages and one Gray-hom profile.

  IsStrictFunctor constrains the existing extracted compositor by an endpoint
  path and equality to the corresponding path_to_hom. StrictFunctor is the
  exact dependent package of an ambient carrier and that property. Its stable
  strict_functor view retains the evidence discriminator while point and hom
  action expose the underlying carrier.

  GrayHom_lax is the selected strict-object/lax-arrow category.  Its homs
  are the existing Transf_cat homs between evidence-bearing carriers, so modifications
  and every subsequent iterated hom remain owned by the ambient calculus.
  The I tensor I consumer confirms the selected post/left interchanger as
  the project's standard lax direction.
*/

require open emdash.emdash3_2;

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
  Semantic strictness of one existing cell. The endpoint path is explicit, so
  the property remains meaningful after the global strict endpoint cuts are
  migrated. The second field constrains the existing cell; it does not supply
  another compositor.
*/
symbol IsStrictCell
  [C : Cat]
  [x y : τ (Obj C)]
  (cell : τ (Hom C x y))
  : Grpd
≔ `Σ_ p : τ (@= (Obj C) x y),
    @= (Hom C x y) cell (@path_to_hom C x y p);

symbol strict_cell_path
  [C : Cat]
  [x y : τ (Obj C)]
  [cell : τ (Hom C x y)]
  (e : τ (@IsStrictCell C x y cell))
  : τ (@= (Obj C) x y)
≔ sigma_Fst e;

symbol strict_cell_agreement
  [C : Cat]
  [x y : τ (Obj C)]
  [cell : τ (Hom C x y)]
  (e : τ (@IsStrictCell C x y cell))
  : τ (@= (Hom C x y)
      cell
      (@path_to_hom C x y (@strict_cell_path C x y cell e)))
≔ sigma_Snd e;

// Normal strict-functor property over the existing intrinsic compositor.
symbol IsStrictFunctor
  [A B : Cat]
  (F : τ (Functor A B))
  : Grpd
≔ @Pi_grpd
    (Obj A)
    (λ X : τ (Obj A),
      @Pi_grpd
        (Obj A)
        (λ Y : τ (Obj A),
          @Pi_grpd
            (Obj A)
            (λ Z : τ (Obj A),
              @Pi_grpd
                (Hom A Y Z)
                (λ g : τ (Hom A Y Z),
                  @Pi_grpd
                    (Hom A X Y)
                    (λ f : τ (Hom A X Y),
                      @IsStrictCell
                        (Hom_cat B
                          (@fapp0 A B F X)
                          (@fapp0 A B F Z))
                        (@strict_functor_compositor_lhs
                          A B F X Y Z g f)
                        (@strict_functor_compositor_rhs
                          A B F X Y Z g f)
                        (@fapp1_compositor
                          A B F X Y Z g f))))));

// Rigid record-like facade decoding to exactly Sigma(F,IsStrictFunctor(F)).
injective symbol StrictFunctor
  (A B : Cat)
  : Grpd;

rule τ (@StrictFunctor $A $B)
  ↪ `τΣ_ F : τ (Functor $A $B), @IsStrictFunctor $A $B F;

injective symbol strict_functor_intro
  [A B : Cat]
  (F : τ (Functor A B))
  (p : τ (@IsStrictFunctor A B F))
  : τ (@StrictFunctor A B);

rule sigma_Fst (@strict_functor_intro _ _ $F _)
  ↪ $F;

rule sigma_Snd (@strict_functor_intro _ _ _ $p)
  ↪ $p;

symbol strict_functor_underlying
  [A B : Cat]
  (S : τ (@StrictFunctor A B))
  : τ (Functor A B)
≔ sigma_Fst S;

symbol strict_functor_evidence
  [A B : Cat]
  (S : τ (@StrictFunctor A B))
  : τ (@IsStrictFunctor A B (@strict_functor_underlying A B S))
≔ sigma_Snd S;

// Evidence-bearing ambient view. It is an inclusion projection, not a code.
injective symbol strict_functor
  [A B : Cat]
  (S : τ (@StrictFunctor A B))
  : τ (Functor A B);

// Constructor-visible package action exposes the underlying carrier. Opaque
// packages returned by higher functors retain the strict_functor head.
// lhs-audit: keep 3 -- the strict_functor_intro constructor is the semantic
// discriminator and preserves the evidence-bearing whole view otherwise.
rule @fapp0 _ _
      (@strict_functor $A $B (@strict_functor_intro $A $B $F _)) $x
  ↪ @fapp0 $A $B $F $x;

// lhs-audit: keep 3 -- same constructor-scoped projection ladder.
rule @fapp1_func _ _
      (@strict_functor $A $B (@strict_functor_intro $A $B $F _)) $x $y
  ↪ @fapp1_func $A $B $F $x $y;

// lhs-audit: keep 3 -- same constructor-scoped projection ladder.
rule @fapp1_fapp0 _ _
      (@strict_functor $A $B (@strict_functor_intro $A $B $F _)) $x $y $f
  ↪ @fapp1_fapp0 $A $B $F $x $y $f;

// Supplied identity strictness proof; its internal derivation remains later.
constant symbol identity_is_strict
  (A : Cat)
  : τ (@IsStrictFunctor A A (@id_func A));

symbol strict_identity
  (A : Cat)
  : τ (@StrictFunctor A A)
≔ @strict_functor_intro A A (@id_func A) (@identity_is_strict A);

// Whole semantic observation of the evidence-bearing identity view.
constant symbol strict_identity_carrier_path
  (A : Cat)
  : τ (@=
      (Functor A A)
      (@strict_functor A A (@strict_identity A))
      (@id_func A));

// Strict-object/lax-arrow right-hom profile.
injective symbol GrayHom_lax
  (A B : Cat)
  : Cat;

rule Obj (@GrayHom_lax $A $B)
  ↪ @StrictFunctor $A $B;

rule Hom_cat (@GrayHom_lax $A $B) $X $Y
  ↪ @Transf_cat
      $A $B
      (@strict_functor $A $B $X)
      (@strict_functor $A $B $Y);

// Identity delegates to the ambient functor category.
rule @id (@GrayHom_lax $A $B) $X
  ↪ @id
      (@Functor_cat $A $B)
      (@strict_functor $A $B $X);

// Composition delegates to the ambient functor category.
// lhs-audit: keep 2,3,4 -- the carrier projections occur on the RHS.
rule @comp_fapp0
      (@GrayHom_lax $A $B) $X $Y $Z $g $f
  ↪ @comp_fapp0
      (@Functor_cat $A $B)
      (@strict_functor $A $B $X)
      (@strict_functor $A $B $Y)
      (@strict_functor $A $B $Z)
      $g $f;

// Whole inclusion into the shared ambient functor category.
injective symbol grayhom_lax_include_func
  (A B : Cat)
  : τ (Functor
      (@GrayHom_lax A B)
      (@Functor_cat A B));

rule @fapp0 _ _ (@grayhom_lax_include_func $A $B) $X
  ↪ @strict_functor $A $B $X;

// The profile is full on the reused ambient transformation homs.
rule @fapp1_func _ _
      (@grayhom_lax_include_func $A $B) $X $Y
  ↪ @id_func
      (@Transf_cat
        $A $B
        (@strict_functor $A $B $X)
        (@strict_functor $A $B $Y));
