/*
  Internal preadditive-category structure.

  An abelian-group structure consists of a set-valued carrier, zero, addition,
  negation, and a sufficient one-sided law basis: associativity,
  commutativity, right zero, and right inverse. A preadditive category equips
  every existing Hom carrier with such a structure and retains both
  distributivity orientations for the existing categorical composition.

  This is evidence over the ordinary `Cat`/`Hom`/`comp_fapp0` grammar. It
  introduces no parallel category syntax, runtime rule, biproduct, zero
  object, or additive-category claim.
*/

require open emdash.emdash3_2;

// Zero, curried addition, and negation on one carrier.
symbol AbelianGroupOps
  (A : Grpd)
  : Grpd
≔ `Σ_ zero : τ A,
   `Σ_ add : τ (@Function_grpd A (@Function_grpd A A)),
       @Function_grpd A A;

symbol abelian_group_ops_intro
  [A : Grpd]
  (zero : τ A)
  (add : τ (@Function_grpd A (@Function_grpd A A)))
  (neg : τ (@Function_grpd A A))
  : τ (@AbelianGroupOps A)
≔ @Struct_sigma A
    (λ _ : τ A,
      `Σ_ add : τ (@Function_grpd A (@Function_grpd A A)),
        @Function_grpd A A)
    zero
    (@Struct_sigma
      (@Function_grpd A (@Function_grpd A A))
      (λ _ : τ (@Function_grpd A (@Function_grpd A A)),
        @Function_grpd A A)
      add neg);

symbol abelian_group_ops_zero
  [A : Grpd]
  (ops : τ (@AbelianGroupOps A))
  : τ A
≔ sigma_Fst ops;

symbol abelian_group_ops_add_function
  [A : Grpd]
  (ops : τ (@AbelianGroupOps A))
  : τ (@Function_grpd A (@Function_grpd A A))
≔ sigma_Fst (sigma_Snd ops);

symbol abelian_group_ops_neg_function
  [A : Grpd]
  (ops : τ (@AbelianGroupOps A))
  : τ (@Function_grpd A A)
≔ sigma_Snd (sigma_Snd ops);

symbol abelian_group_ops_add
  [A : Grpd]
  (ops : τ (@AbelianGroupOps A))
  (x y : τ A)
  : τ A
≔ (@abelian_group_ops_add_function A ops) x y;

symbol abelian_group_ops_neg
  [A : Grpd]
  (ops : τ (@AbelianGroupOps A))
  (x : τ A)
  : τ A
≔ (@abelian_group_ops_neg_function A ops) x;

// Sufficient abelian-group law basis.
symbol AbelianGroupAddAssoc
  [A : Grpd]
  (ops : τ (@AbelianGroupOps A))
  : Grpd
≔ @Pi_grpd A (λ x : τ A,
    @Pi_grpd A (λ y : τ A,
      @Pi_grpd A (λ z : τ A,
        @= A
          (@abelian_group_ops_add A ops
            (@abelian_group_ops_add A ops x y) z)
          (@abelian_group_ops_add A ops
            x (@abelian_group_ops_add A ops y z)))));

symbol AbelianGroupAddComm
  [A : Grpd]
  (ops : τ (@AbelianGroupOps A))
  : Grpd
≔ @Pi_grpd A (λ x : τ A,
    @Pi_grpd A (λ y : τ A,
      @= A
        (@abelian_group_ops_add A ops x y)
        (@abelian_group_ops_add A ops y x)));

symbol AbelianGroupAddZero
  [A : Grpd]
  (ops : τ (@AbelianGroupOps A))
  : Grpd
≔ @Pi_grpd A (λ x : τ A,
    @= A
      (@abelian_group_ops_add A ops x
        (@abelian_group_ops_zero A ops))
      x);

symbol AbelianGroupAddInv
  [A : Grpd]
  (ops : τ (@AbelianGroupOps A))
  : Grpd
≔ @Pi_grpd A (λ x : τ A,
    @= A
      (@abelian_group_ops_add A ops x
        (@abelian_group_ops_neg A ops x))
      (@abelian_group_ops_zero A ops));

symbol IsAbelianGroup
  [A : Grpd]
  (ops : τ (@AbelianGroupOps A))
  : Grpd
≔ @Product_grpd
    (@AbelianGroupAddAssoc A ops)
    (@Product_grpd
      (@AbelianGroupAddComm A ops)
      (@Product_grpd
        (@AbelianGroupAddZero A ops)
        (@AbelianGroupAddInv A ops)));

symbol abelian_group_laws_intro
  [A : Grpd]
  [ops : τ (@AbelianGroupOps A)]
  (assoc : τ (@AbelianGroupAddAssoc A ops))
  (comm : τ (@AbelianGroupAddComm A ops))
  (zero : τ (@AbelianGroupAddZero A ops))
  (inv : τ (@AbelianGroupAddInv A ops))
  : τ (@IsAbelianGroup A ops)
≔ @Product_pair_grpd _ _ assoc
    (@Product_pair_grpd _ _ comm
      (@Product_pair_grpd _ _ zero inv));

// Set-valued abelian-group structure on a selected carrier.
symbol AbelianGroupStructure
  (A : Grpd)
  : Grpd
≔ `Σ_ A_set : τ (IsSetGrpd A),
   `Σ_ ops : τ (@AbelianGroupOps A),
       @IsAbelianGroup A ops;

symbol abelian_group_structure_intro
  [A : Grpd]
  (A_set : τ (IsSetGrpd A))
  (ops : τ (@AbelianGroupOps A))
  (laws : τ (@IsAbelianGroup A ops))
  : τ (@AbelianGroupStructure A)
≔ @Struct_sigma
    (IsSetGrpd A)
    (λ _ : τ (IsSetGrpd A),
      `Σ_ ops : τ (@AbelianGroupOps A), @IsAbelianGroup A ops)
    A_set
    (@Struct_sigma
      (@AbelianGroupOps A)
      (λ data : τ (@AbelianGroupOps A), @IsAbelianGroup A data)
      ops laws);

symbol abelian_group_structure_is_set
  [A : Grpd]
  (structure : τ (@AbelianGroupStructure A))
  : τ (IsSetGrpd A)
≔ sigma_Fst structure;

symbol abelian_group_structure_ops
  [A : Grpd]
  (structure : τ (@AbelianGroupStructure A))
  : τ (@AbelianGroupOps A)
≔ sigma_Fst (sigma_Snd structure);

symbol abelian_group_structure_laws
  [A : Grpd]
  (structure : τ (@AbelianGroupStructure A))
  : τ (@IsAbelianGroup A (@abelian_group_structure_ops A structure))
≔ sigma_Snd (sigma_Snd structure);

// Readable projections of the retained abelian-group laws.
symbol abelian_group_add_assoc_law
  [A : Grpd]
  (structure : τ (@AbelianGroupStructure A))
  : τ (@AbelianGroupAddAssoc A
      (@abelian_group_structure_ops A structure))
≔ sigma_Fst (@abelian_group_structure_laws A structure);

symbol abelian_group_add_comm_law
  [A : Grpd]
  (structure : τ (@AbelianGroupStructure A))
  : τ (@AbelianGroupAddComm A
      (@abelian_group_structure_ops A structure))
≔ sigma_Fst (sigma_Snd (@abelian_group_structure_laws A structure));

symbol abelian_group_add_zero_law
  [A : Grpd]
  (structure : τ (@AbelianGroupStructure A))
  : τ (@AbelianGroupAddZero A
      (@abelian_group_structure_ops A structure))
≔ sigma_Fst
    (sigma_Snd (sigma_Snd (@abelian_group_structure_laws A structure)));

symbol abelian_group_add_inv_law
  [A : Grpd]
  (structure : τ (@AbelianGroupStructure A))
  : τ (@AbelianGroupAddInv A
      (@abelian_group_structure_ops A structure))
≔ sigma_Snd
    (sigma_Snd (sigma_Snd (@abelian_group_structure_laws A structure)));

// One abelian-group structure on every existing Hom carrier.
symbol PreadditiveHomStructures
  (C : Cat)
  : Grpd
≔ @Pi_grpd (Obj C)
    (λ X : τ (Obj C),
      @Pi_grpd (Obj C)
        (λ Y : τ (Obj C),
          @AbelianGroupStructure (Hom C X Y)));

// Composition distributes over addition in its right/input argument.
symbol PreadditiveCompAddRight
  [C : Cat]
  (hom_structure : τ (@PreadditiveHomStructures C))
  : Grpd
≔ @Pi_grpd (Obj C) (λ X : τ _,
    @Pi_grpd (Obj C) (λ Y : τ _,
      @Pi_grpd (Obj C) (λ Z : τ _,
        @Pi_grpd (Hom C Y Z) (λ g : τ _,
          @Pi_grpd (Hom C X Y) (λ f : τ _,
            @Pi_grpd (Hom C X Y) (λ h : τ _,
              @= (Hom C X Z)
                (@comp_fapp0 C X Y Z g
                  (@abelian_group_ops_add
                    (Hom C X Y)
                    (@abelian_group_structure_ops
                      (Hom C X Y) (hom_structure X Y))
                    f h))
                (@abelian_group_ops_add
                  (Hom C X Z)
                  (@abelian_group_structure_ops
                    (Hom C X Z) (hom_structure X Z))
                  (@comp_fapp0 C X Y Z g f)
                  (@comp_fapp0 C X Y Z g h))))))));

// Composition distributes over addition in its left/output argument.
symbol PreadditiveCompAddLeft
  [C : Cat]
  (hom_structure : τ (@PreadditiveHomStructures C))
  : Grpd
≔ @Pi_grpd (Obj C) (λ X : τ _,
    @Pi_grpd (Obj C) (λ Y : τ _,
      @Pi_grpd (Obj C) (λ Z : τ _,
        @Pi_grpd (Hom C Y Z) (λ g : τ _,
          @Pi_grpd (Hom C Y Z) (λ h : τ _,
            @Pi_grpd (Hom C X Y) (λ f : τ _,
              @= (Hom C X Z)
                (@comp_fapp0 C X Y Z
                  (@abelian_group_ops_add
                    (Hom C Y Z)
                    (@abelian_group_structure_ops
                      (Hom C Y Z) (hom_structure Y Z))
                    g h)
                  f)
                (@abelian_group_ops_add
                  (Hom C X Z)
                  (@abelian_group_structure_ops
                    (Hom C X Z) (hom_structure X Z))
                  (@comp_fapp0 C X Y Z g f)
                  (@comp_fapp0 C X Y Z h f))))))));

symbol PreadditiveCompositionBilinear
  [C : Cat]
  (hom_structure : τ (@PreadditiveHomStructures C))
  : Grpd
≔ @Product_grpd
    (@PreadditiveCompAddRight C hom_structure)
    (@PreadditiveCompAddLeft C hom_structure);

// Generic preadditive evidence on one existing category.
symbol PreadditiveCategory
  (C : Cat)
  : Grpd
≔ `Σ_ hom_structure : τ (@PreadditiveHomStructures C),
    @PreadditiveCompositionBilinear C hom_structure;

symbol preadditive_category_intro
  [C : Cat]
  (hom_structure : τ (@PreadditiveHomStructures C))
  (bilinear : τ (@PreadditiveCompositionBilinear C hom_structure))
  : τ (@PreadditiveCategory C)
≔ @Struct_sigma
    (@PreadditiveHomStructures C)
    (λ data : τ (@PreadditiveHomStructures C),
      @PreadditiveCompositionBilinear C data)
    hom_structure bilinear;

symbol preadditive_hom_structure
  [C : Cat]
  (structure : τ (@PreadditiveCategory C))
  (X Y : τ (Obj C))
  : τ (@AbelianGroupStructure (Hom C X Y))
≔ (sigma_Fst structure) X Y;

symbol preadditive_hom_is_set
  [C : Cat]
  (structure : τ (@PreadditiveCategory C))
  (X Y : τ (Obj C))
  : τ (IsSetGrpd (Hom C X Y))
≔ @abelian_group_structure_is_set
    (Hom C X Y)
    (@preadditive_hom_structure C structure X Y);

symbol preadditive_hom_ops
  [C : Cat]
  (structure : τ (@PreadditiveCategory C))
  (X Y : τ (Obj C))
  : τ (@AbelianGroupOps (Hom C X Y))
≔ @abelian_group_structure_ops
    (Hom C X Y)
    (@preadditive_hom_structure C structure X Y);

symbol preadditive_hom_zero
  [C : Cat]
  (structure : τ (@PreadditiveCategory C))
  (X Y : τ (Obj C))
  : τ (Hom C X Y)
≔ @abelian_group_ops_zero
    (Hom C X Y)
    (@preadditive_hom_ops C structure X Y);

symbol preadditive_hom_add
  [C : Cat]
  (structure : τ (@PreadditiveCategory C))
  [X Y : τ (Obj C)]
  (f g : τ (Hom C X Y))
  : τ (Hom C X Y)
≔ @abelian_group_ops_add
    (Hom C X Y)
    (@preadditive_hom_ops C structure X Y)
    f g;

symbol preadditive_hom_neg
  [C : Cat]
  (structure : τ (@PreadditiveCategory C))
  [X Y : τ (Obj C)]
  (f : τ (Hom C X Y))
  : τ (Hom C X Y)
≔ @abelian_group_ops_neg
    (Hom C X Y)
    (@preadditive_hom_ops C structure X Y)
    f;

symbol preadditive_bilinear
  [C : Cat]
  (structure : τ (@PreadditiveCategory C))
  : τ (@PreadditiveCompositionBilinear C (sigma_Fst structure))
≔ sigma_Snd structure;

symbol preadditive_comp_add_right_law
  [C : Cat]
  (structure : τ (@PreadditiveCategory C))
  : τ (@PreadditiveCompAddRight C (sigma_Fst structure))
≔ sigma_Fst (@preadditive_bilinear C structure);

symbol preadditive_comp_add_left_law
  [C : Cat]
  (structure : τ (@PreadditiveCategory C))
  : τ (@PreadditiveCompAddLeft C (sigma_Fst structure))
≔ sigma_Snd (@preadditive_bilinear C structure);
