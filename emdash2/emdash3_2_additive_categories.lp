/*
  Additive categories derived from preadditive Cartesian categories.

  AdditiveCategory is exactly existing PreadditiveCategory evidence paired
  with an existing selected CartesianCategory. The theorem layer derives
  zero-composition, initiality of the selected terminal object, coproduct
  injections, and copairing. No parallel coproduct classifier or category
  grammar is introduced.
*/

require open emdash.emdash3_2_preadditive_categories;
require open emdash.emdash3_2_cartesian_categories;

// Left additive unit follows from commutativity and the selected right unit.
symbol abelian_group_add_zero_left_path
  [A : Grpd]
  (S : τ (@AbelianGroupStructure A))
  (x : τ A)
  : τ (@= A
      (@abelian_group_ops_add A
        (@abelian_group_structure_ops A S)
        (@abelian_group_ops_zero A
          (@abelian_group_structure_ops A S)) x)
      x)
≔ @eq_trans A _ _ _
    ((@abelian_group_add_comm_law A S)
      (@abelian_group_ops_zero A
        (@abelian_group_structure_ops A S)) x)
    ((@abelian_group_add_zero_law A S) x);

// Left additive inverse follows from commutativity and the right inverse.
symbol abelian_group_add_inv_left_path
  [A : Grpd]
  (S : τ (@AbelianGroupStructure A))
  (x : τ A)
  : τ (@= A
      (@abelian_group_ops_add A
        (@abelian_group_structure_ops A S)
        (@abelian_group_ops_neg A
          (@abelian_group_structure_ops A S) x) x)
      (@abelian_group_ops_zero A
        (@abelian_group_structure_ops A S)))
≔ @eq_trans A _ _ _
    ((@abelian_group_add_comm_law A S)
      (@abelian_group_ops_neg A
        (@abelian_group_structure_ops A S) x) x)
    ((@abelian_group_add_inv_law A S) x);

// Cancelling one copy from an additive idempotent leaves zero.
protected symbol abelian_group_add_idempotent_reduction_path
  [A : Grpd]
  (S : τ (@AbelianGroupStructure A))
  (a : τ A)
  : τ (@= A
      (@abelian_group_ops_add A
        (@abelian_group_structure_ops A S)
        (@abelian_group_ops_add A
          (@abelian_group_structure_ops A S) a a)
        (@abelian_group_ops_neg A
          (@abelian_group_structure_ops A S) a))
      a)
≔ @eq_trans A _ _ _
    ((@abelian_group_add_assoc_law A S) a a
      (@abelian_group_ops_neg A
        (@abelian_group_structure_ops A S) a))
    (@eq_trans A _ _ _
      (@eq_ap A A
        (λ z : τ A,
          @abelian_group_ops_add A
            (@abelian_group_structure_ops A S) a z)
        _ _ ((@abelian_group_add_inv_law A S) a))
      ((@abelian_group_add_zero_law A S) a));

symbol abelian_group_add_idempotent_is_zero_path
  [A : Grpd]
  (S : τ (@AbelianGroupStructure A))
  (a : τ A)
  (idempotent : τ (@= A
      (@abelian_group_ops_add A
        (@abelian_group_structure_ops A S) a a)
      a))
  : τ (@= A a
      (@abelian_group_ops_zero A
        (@abelian_group_structure_ops A S)))
≔ @eq_trans A a _ _
    (@eq_sym A _ a
      (@abelian_group_add_idempotent_reduction_path A S a))
    (@eq_trans A _ _ _
      (@eq_ap A A
        (λ z : τ A,
          @abelian_group_ops_add A
            (@abelian_group_structure_ops A S) z
            (@abelian_group_ops_neg A
              (@abelian_group_structure_ops A S) a))
        _ _ idempotent)
      ((@abelian_group_add_inv_law A S) a));

// Postcomposition preserves the selected zero arrow.
symbol preadditive_comp_zero_right_path
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [X Y Z : τ (Obj C)]
  (g : τ (Hom C Y Z))
  : τ (@= (Hom C X Z)
      (@comp_fapp0 C X Y Z g
        (@preadditive_hom_zero C S X Y))
      (@preadditive_hom_zero C S X Z))
≔ @abelian_group_add_idempotent_is_zero_path
    (Hom C X Z)
    (@preadditive_hom_structure C S X Z)
    (@comp_fapp0 C X Y Z g
      (@preadditive_hom_zero C S X Y))
    (@eq_trans (Hom C X Z) _ _ _
      (@eq_sym (Hom C X Z) _ _
        ((@preadditive_comp_add_right_law C S)
          X Y Z g
          (@preadditive_hom_zero C S X Y)
          (@preadditive_hom_zero C S X Y)))
      (@eq_ap
        (Hom C X Y) (Hom C X Z)
        (λ f : τ (Hom C X Y), @comp_fapp0 C X Y Z g f)
        _ _
        ((@abelian_group_add_zero_law
          (Hom C X Y)
          (@preadditive_hom_structure C S X Y))
          (@preadditive_hom_zero C S X Y))));

// Precomposition preserves the selected zero arrow.
symbol preadditive_comp_zero_left_path
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [X Y Z : τ (Obj C)]
  (f : τ (Hom C X Y))
  : τ (@= (Hom C X Z)
      (@comp_fapp0 C X Y Z
        (@preadditive_hom_zero C S Y Z) f)
      (@preadditive_hom_zero C S X Z))
≔ @abelian_group_add_idempotent_is_zero_path
    (Hom C X Z)
    (@preadditive_hom_structure C S X Z)
    (@comp_fapp0 C X Y Z
      (@preadditive_hom_zero C S Y Z) f)
    (@eq_trans (Hom C X Z) _ _ _
      (@eq_sym (Hom C X Z) _ _
        ((@preadditive_comp_add_left_law C S)
          X Y Z
          (@preadditive_hom_zero C S Y Z)
          (@preadditive_hom_zero C S Y Z) f))
      (@eq_ap
        (Hom C Y Z) (Hom C X Z)
        (λ g : τ (Hom C Y Z), @comp_fapp0 C X Y Z g f)
        _ _
        ((@abelian_group_add_zero_law
          (Hom C Y Z)
          (@preadditive_hom_structure C S Y Z))
          (@preadditive_hom_zero C S Y Z))));

// At a terminal object, identity and the additive zero endomorphism agree.
symbol preadditive_terminal_identity_zero_path
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  : τ (@= (Hom C t t)
      (@id C t)
      (@preadditive_hom_zero C S t t))
≔ @eq_trans (Hom C t t)
    (@id C t)
    (@terminal_arrow_fapp0 C t T t)
    (@preadditive_hom_zero C S t t)
    (@eq_sym (Hom C t t)
      (@terminal_arrow_fapp0 C t T t) (@id C t)
      (@terminal_arrow_at_terminal_path C t T))
    (@eq_sym (Hom C t t)
      (@preadditive_hom_zero C S t t)
      (@terminal_arrow_fapp0 C t T t)
      (@terminal_unique_path C t T t
        (@preadditive_hom_zero C S t t)));

// Every arrow out of a terminal object is the additive zero arrow.
symbol preadditive_terminal_to_zero_path
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [t A : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (f : τ (Hom C t A))
  : τ (@= (Hom C t A) f (@preadditive_hom_zero C S t A))
≔ @eq_trans (Hom C t A)
    f
    (@comp_fapp0 C t t A f (@id C t))
    (@preadditive_hom_zero C S t A)
    (@eq_refl (Hom C t A) f)
    (@eq_trans (Hom C t A) _ _ _
      (@eq_ap
        (Hom C t t) (Hom C t A)
        (λ e : τ (Hom C t t), @comp_fapp0 C t t A f e)
        (@id C t) (@preadditive_hom_zero C S t t)
        (@preadditive_terminal_identity_zero_path C S t T))
      (@preadditive_comp_zero_right_path C S t t A f));

// Hence a terminal object in a preadditive category is also initial.
symbol preadditive_terminal_initial_hom_contr
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (A : τ (Obj C))
  : τ (IsContr (Hom C t A))
≔ @Struct_sigma
    (Hom C t A)
    (λ centre : τ (Hom C t A),
      @Pi_grpd (Hom C t A) (λ f : τ _, @= (Hom C t A) centre f))
    (@preadditive_hom_zero C S t A)
    (λ f : τ (Hom C t A),
      @eq_sym (Hom C t A) f (@preadditive_hom_zero C S t A)
        (@preadditive_terminal_to_zero_path C S t A T f));

// Additive structure is precisely preadditive plus selected Cartesian data.
symbol AdditiveCategory
  [C : Cat]
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  : Grpd
≔ @Product_grpd
    (@PreadditiveCategory C)
    (@CartesianCategory C P t);

symbol additive_category_intro
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (S : τ (@PreadditiveCategory C))
  (K : τ (@CartesianCategory C P t))
  : τ (@AdditiveCategory C P t)
≔ @Product_pair_grpd _ _ S K;

symbol additive_preadditive
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C P t))
  : τ (@PreadditiveCategory C)
≔ sigma_Fst A;

symbol additive_cartesian
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C P t))
  : τ (@CartesianCategory C P t)
≔ sigma_Snd A;

symbol additive_binary_products
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C P t))
  : τ (@BinaryProducts C P)
≔ @cartesian_binary_products C P t (@additive_cartesian C P t A);

symbol additive_terminal_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C P t))
  : τ (@TerminalObject C t)
≔ @cartesian_terminal_object C P t (@additive_cartesian C P t A);

symbol additive_initial_hom_contr
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C P t))
  (X : τ (Obj C))
  : τ (IsContr (Hom C t X))
≔ @preadditive_terminal_initial_hom_contr C
    (@additive_preadditive C P t A) t
    (@additive_terminal_object C P t A) X;

// First biproduct injection iota_1 = <id,0>.
symbol additive_inj1_fapp0
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C P t))
  (X Y : τ (Obj C))
  : τ (Hom C X
      (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)))
≔ @binary_products_pair_fapp0 C P
    (@additive_binary_products C P t A)
    X X Y
    (@id C X)
    (@preadditive_hom_zero C
      (@additive_preadditive C P t A) X Y);

// Second biproduct injection iota_2 = <0,id>.
symbol additive_inj2_fapp0
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C P t))
  (X Y : τ (Obj C))
  : τ (Hom C Y
      (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)))
≔ @binary_products_pair_fapp0 C P
    (@additive_binary_products C P t A)
    Y X Y
    (@preadditive_hom_zero C
      (@additive_preadditive C P t A) Y X)
    (@id C Y);

// Copairing [f,g] = f o pi_1 + g o pi_2.
symbol additive_copair_fapp0
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C P t))
  [X Y Z : τ (Obj C)]
  (f : τ (Hom C X Z))
  (g : τ (Hom C Y Z))
  : τ (Hom C
      (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) Z)
≔ @preadditive_hom_add C
    (@additive_preadditive C P t A)
    (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) Z
    (@comp_fapp0 C
      (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) X Z
      f
      (@binary_products_proj1_fapp0 C P
        (@additive_binary_products C P t A) X Y))
    (@comp_fapp0 C
      (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) Y Z
      g
      (@binary_products_proj2_fapp0 C P
        (@additive_binary_products C P t A) X Y));

// Congruence for the selected Hom addition.
symbol additive_add_congr_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C P t))
  [X Y : τ (Obj C)]
  (f f' g g' : τ (Hom C X Y))
  (p : τ (@= (Hom C X Y) f f'))
  (q : τ (@= (Hom C X Y) g g'))
  : τ (@= (Hom C X Y)
      (@preadditive_hom_add C
        (@additive_preadditive C P t A) X Y f g)
      (@preadditive_hom_add C
        (@additive_preadditive C P t A) X Y f' g'))
≔ @eq_trans (Hom C X Y) _ _ _
    (@eq_ap (Hom C X Y) (Hom C X Y)
      (λ h : τ (Hom C X Y),
        @preadditive_hom_add C
          (@additive_preadditive C P t A) X Y h g)
      f f' p)
    (@eq_ap (Hom C X Y) (Hom C X Y)
      (λ h : τ (Hom C X Y),
        @preadditive_hom_add C
          (@additive_preadditive C P t A) X Y f' h)
      g g' q);

// Congruence for product pairing.
symbol additive_pair_congr_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C P t))
  [W X Y : τ (Obj C)]
  (f f' : τ (Hom C W X))
  (g g' : τ (Hom C W Y))
  (p : τ (@= (Hom C W X) f f'))
  (q : τ (@= (Hom C W Y) g g'))
  : τ (@= (Hom C W
      (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)))
      (@binary_products_pair_fapp0 C P
        (@additive_binary_products C P t A) W X Y f g)
      (@binary_products_pair_fapp0 C P
        (@additive_binary_products C P t A) W X Y f' g'))
≔ @eq_trans _ _ _ _
    (@eq_ap (Hom C W X)
      (Hom C W
        (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)))
      (λ h : τ (Hom C W X),
        @binary_products_pair_fapp0 C P
          (@additive_binary_products C P t A) W X Y h g)
      f f' p)
    (@eq_ap (Hom C W Y)
      (Hom C W
        (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)))
      (λ h : τ (Hom C W Y),
        @binary_products_pair_fapp0 C P
          (@additive_binary_products C P t A) W X Y f' h)
      g g' q);

// First coproduct beta: [f,g] o iota_1 = f.
symbol additive_copair_inj1_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C P t))
  [X Y Z : τ (Obj C)]
  (f : τ (Hom C X Z))
  (g : τ (Hom C Y Z))
  : τ (@= (Hom C X Z)
      (@comp_fapp0 C X
        (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) Z
        (@additive_copair_fapp0 C P t A X Y Z f g)
        (@additive_inj1_fapp0 C P t A X Y))
      f)
≔ @eq_trans (Hom C X Z) _ _ _
    ((@preadditive_comp_add_left_law C
      (@additive_preadditive C P t A))
      X
      (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y))
      Z
      (@comp_fapp0 C
        (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) X Z
        f
        (@binary_products_proj1_fapp0 C P
          (@additive_binary_products C P t A) X Y))
      (@comp_fapp0 C
        (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) Y Z
        g
        (@binary_products_proj2_fapp0 C P
          (@additive_binary_products C P t A) X Y))
      (@additive_inj1_fapp0 C P t A X Y))
    (@eq_trans (Hom C X Z) _ _ _
      (@additive_add_congr_path C P t A
        X Z _ _ _ _
        (@eq_trans (Hom C X Z) _ _ f
          (@eq_sym (Hom C X Z) _ _
            (@comp_assoc C X
              (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y))
              X Z f
              (@binary_products_proj1_fapp0 C P
                (@additive_binary_products C P t A) X Y)
              (@additive_inj1_fapp0 C P t A X Y)))
          (@eq_refl (Hom C X Z) f))
        (@eq_trans (Hom C X Z) _ _
          (@preadditive_hom_zero C
            (@additive_preadditive C P t A) X Z)
          (@eq_sym (Hom C X Z) _ _
            (@comp_assoc C X
              (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y))
              Y Z g
              (@binary_products_proj2_fapp0 C P
                (@additive_binary_products C P t A) X Y)
              (@additive_inj1_fapp0 C P t A X Y)))
          (@preadditive_comp_zero_right_path C
            (@additive_preadditive C P t A) X Y Z g)))
      ((@abelian_group_add_zero_law
        (Hom C X Z)
        (@preadditive_hom_structure C
          (@additive_preadditive C P t A) X Z)) f));

// Second coproduct beta: [f,g] o iota_2 = g.
symbol additive_copair_inj2_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C P t))
  [X Y Z : τ (Obj C)]
  (f : τ (Hom C X Z))
  (g : τ (Hom C Y Z))
  : τ (@= (Hom C Y Z)
      (@comp_fapp0 C Y
        (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) Z
        (@additive_copair_fapp0 C P t A X Y Z f g)
        (@additive_inj2_fapp0 C P t A X Y))
      g)
≔ @eq_trans (Hom C Y Z) _ _ _
    ((@preadditive_comp_add_left_law C
      (@additive_preadditive C P t A))
      Y
      (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y))
      Z
      (@comp_fapp0 C
        (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) X Z
        f
        (@binary_products_proj1_fapp0 C P
          (@additive_binary_products C P t A) X Y))
      (@comp_fapp0 C
        (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) Y Z
        g
        (@binary_products_proj2_fapp0 C P
          (@additive_binary_products C P t A) X Y))
      (@additive_inj2_fapp0 C P t A X Y))
    (@eq_trans (Hom C Y Z) _ _ _
      (@additive_add_congr_path C P t A
        Y Z _ _ _ _
        (@eq_trans (Hom C Y Z) _ _
          (@preadditive_hom_zero C
            (@additive_preadditive C P t A) Y Z)
          (@eq_sym (Hom C Y Z) _ _
            (@comp_assoc C Y
              (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y))
              X Z f
              (@binary_products_proj1_fapp0 C P
                (@additive_binary_products C P t A) X Y)
              (@additive_inj2_fapp0 C P t A X Y)))
          (@preadditive_comp_zero_right_path C
            (@additive_preadditive C P t A) Y X Z f))
        (@eq_trans (Hom C Y Z) _ _ g
          (@eq_sym (Hom C Y Z) _ _
            (@comp_assoc C Y
              (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y))
              Y Z g
              (@binary_products_proj2_fapp0 C P
                (@additive_binary_products C P t A) X Y)
              (@additive_inj2_fapp0 C P t A X Y)))
          (@eq_refl (Hom C Y Z) g)))
      (@abelian_group_add_zero_left_path
        (Hom C Y Z)
        (@preadditive_hom_structure C
          (@additive_preadditive C P t A) Y Z) g));

// The canonical diagonal sum iota_1 o pi_1 + iota_2 o pi_2.
symbol additive_biproduct_identity_sum
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C P t))
  (X Y : τ (Obj C))
  : τ (Hom C
      (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y))
      (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)))
≔ @preadditive_hom_add C
    (@additive_preadditive C P t A) _ _
    (@comp_fapp0 C _ X _
      (@additive_inj1_fapp0 C P t A X Y)
      (@binary_products_proj1_fapp0 C P
        (@additive_binary_products C P t A) X Y))
    (@comp_fapp0 C _ Y _
      (@additive_inj2_fapp0 C P t A X Y)
      (@binary_products_proj2_fapp0 C P
        (@additive_binary_products C P t A) X Y));

// First projection of the diagonal sum is pi_1.
symbol additive_biproduct_identity_proj1_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C P t))
  (X Y : τ (Obj C))
  : τ (@= (Hom C
      (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) X)
      (@comp_fapp0 C _ _ X
        (@binary_products_proj1_fapp0 C P
          (@additive_binary_products C P t A) X Y)
        (@additive_biproduct_identity_sum C P t A X Y))
      (@binary_products_proj1_fapp0 C P
        (@additive_binary_products C P t A) X Y))
≔ @eq_trans _ _ _ _
    ((@preadditive_comp_add_right_law C
      (@additive_preadditive C P t A))
      (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y))
      (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) X
      (@binary_products_proj1_fapp0 C P
        (@additive_binary_products C P t A) X Y)
      (@comp_fapp0 C
        (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) X
        (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y))
        (@additive_inj1_fapp0 C P t A X Y)
        (@binary_products_proj1_fapp0 C P
          (@additive_binary_products C P t A) X Y))
      (@comp_fapp0 C
        (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) Y
        (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y))
        (@additive_inj2_fapp0 C P t A X Y)
        (@binary_products_proj2_fapp0 C P
          (@additive_binary_products C P t A) X Y)))
    (@eq_trans _ _ _ _
      (@additive_add_congr_path C P t A
        (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) X
        (@comp_fapp0 C _ _ X
          (@binary_products_proj1_fapp0 C P
            (@additive_binary_products C P t A) X Y)
          (@comp_fapp0 C _ X _
            (@additive_inj1_fapp0 C P t A X Y)
            (@binary_products_proj1_fapp0 C P
              (@additive_binary_products C P t A) X Y)))
        (@binary_products_proj1_fapp0 C P
          (@additive_binary_products C P t A) X Y)
        (@comp_fapp0 C _ _ X
          (@binary_products_proj1_fapp0 C P
            (@additive_binary_products C P t A) X Y)
          (@comp_fapp0 C _ Y _
            (@additive_inj2_fapp0 C P t A X Y)
            (@binary_products_proj2_fapp0 C P
              (@additive_binary_products C P t A) X Y)))
        (@preadditive_hom_zero C
          (@additive_preadditive C P t A) _ X)
        (@eq_trans _ _ _ _
          (@comp_assoc C _ X _ X
            (@binary_products_proj1_fapp0 C P
              (@additive_binary_products C P t A) X Y)
            (@additive_inj1_fapp0 C P t A X Y)
            (@binary_products_proj1_fapp0 C P
              (@additive_binary_products C P t A) X Y))
          (@eq_refl _
            (@binary_products_proj1_fapp0 C P
              (@additive_binary_products C P t A) X Y)))
        (@eq_trans _ _ _ _
          (@comp_assoc C _ Y _ X
            (@binary_products_proj1_fapp0 C P
              (@additive_binary_products C P t A) X Y)
            (@additive_inj2_fapp0 C P t A X Y)
            (@binary_products_proj2_fapp0 C P
              (@additive_binary_products C P t A) X Y))
          (@preadditive_comp_zero_left_path C
            (@additive_preadditive C P t A) _ Y X
            (@binary_products_proj2_fapp0 C P
              (@additive_binary_products C P t A) X Y))))
      ((@abelian_group_add_zero_law _
        (@preadditive_hom_structure C
          (@additive_preadditive C P t A) _ X))
        (@binary_products_proj1_fapp0 C P
          (@additive_binary_products C P t A) X Y)));

// Second projection of the diagonal sum is pi_2.
symbol additive_biproduct_identity_proj2_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C P t))
  (X Y : τ (Obj C))
  : τ (@= (Hom C
      (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) Y)
      (@comp_fapp0 C _ _ Y
        (@binary_products_proj2_fapp0 C P
          (@additive_binary_products C P t A) X Y)
        (@additive_biproduct_identity_sum C P t A X Y))
      (@binary_products_proj2_fapp0 C P
        (@additive_binary_products C P t A) X Y))
≔ @eq_trans _ _ _ _
    ((@preadditive_comp_add_right_law C
      (@additive_preadditive C P t A))
      (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y))
      (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) Y
      (@binary_products_proj2_fapp0 C P
        (@additive_binary_products C P t A) X Y)
      (@comp_fapp0 C
        (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) X
        (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y))
        (@additive_inj1_fapp0 C P t A X Y)
        (@binary_products_proj1_fapp0 C P
          (@additive_binary_products C P t A) X Y))
      (@comp_fapp0 C
        (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) Y
        (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y))
        (@additive_inj2_fapp0 C P t A X Y)
        (@binary_products_proj2_fapp0 C P
          (@additive_binary_products C P t A) X Y)))
    (@eq_trans _ _ _ _
      (@additive_add_congr_path C P t A
        (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) Y
        (@comp_fapp0 C _ _ Y
          (@binary_products_proj2_fapp0 C P
            (@additive_binary_products C P t A) X Y)
          (@comp_fapp0 C _ X _
            (@additive_inj1_fapp0 C P t A X Y)
            (@binary_products_proj1_fapp0 C P
              (@additive_binary_products C P t A) X Y)))
        (@preadditive_hom_zero C
          (@additive_preadditive C P t A) _ Y)
        (@comp_fapp0 C _ _ Y
          (@binary_products_proj2_fapp0 C P
            (@additive_binary_products C P t A) X Y)
          (@comp_fapp0 C _ Y _
            (@additive_inj2_fapp0 C P t A X Y)
            (@binary_products_proj2_fapp0 C P
              (@additive_binary_products C P t A) X Y)))
        (@binary_products_proj2_fapp0 C P
          (@additive_binary_products C P t A) X Y)
        (@eq_trans _ _ _ _
          (@comp_assoc C _ X _ Y
            (@binary_products_proj2_fapp0 C P
              (@additive_binary_products C P t A) X Y)
            (@additive_inj1_fapp0 C P t A X Y)
            (@binary_products_proj1_fapp0 C P
              (@additive_binary_products C P t A) X Y))
          (@preadditive_comp_zero_left_path C
            (@additive_preadditive C P t A) _ X Y
            (@binary_products_proj1_fapp0 C P
              (@additive_binary_products C P t A) X Y)))
        (@eq_trans _ _ _ _
          (@comp_assoc C _ Y _ Y
            (@binary_products_proj2_fapp0 C P
              (@additive_binary_products C P t A) X Y)
            (@additive_inj2_fapp0 C P t A X Y)
            (@binary_products_proj2_fapp0 C P
              (@additive_binary_products C P t A) X Y))
          (@eq_refl _
            (@binary_products_proj2_fapp0 C P
              (@additive_binary_products C P t A) X Y))))
      (@abelian_group_add_zero_left_path _
        (@preadditive_hom_structure C
          (@additive_preadditive C P t A) _ Y)
        (@binary_products_proj2_fapp0 C P
          (@additive_binary_products C P t A) X Y)));

// Biproduct matrix identity: iota_1 pi_1 + iota_2 pi_2 = id.
symbol additive_biproduct_identity_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C P t))
  (X Y : τ (Obj C))
  : τ (@= (Hom C
      (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y))
      (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)))
      (@additive_biproduct_identity_sum C P t A X Y)
      (@id C
        (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y))))
≔ @eq_trans _ _ _ _
    (@binary_products_pair_unique_path C P
      (@additive_binary_products C P t A)
      _ X Y
      (@additive_biproduct_identity_sum C P t A X Y))
    (@eq_trans _ _ _ _
      (@additive_pair_congr_path C P t A
        _ X Y _ _ _ _
        (@additive_biproduct_identity_proj1_path C P t A X Y)
        (@additive_biproduct_identity_proj2_path C P t A X Y))
      (@binary_products_pair_eta_path C P
        (@additive_binary_products C P t A) X Y));

// Coproduct eta: [h iota_1,h iota_2] = h.
symbol additive_copair_eta_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C P t))
  [X Y Z : τ (Obj C)]
  (h : τ (Hom C
      (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) Z))
  : τ (@= (Hom C
      (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) Z)
      (@additive_copair_fapp0 C P t A X Y Z
        (@comp_fapp0 C X _ Z h (@additive_inj1_fapp0 C P t A X Y))
        (@comp_fapp0 C Y _ Z h (@additive_inj2_fapp0 C P t A X Y)))
      h)
≔ @eq_trans _ _ _ _
    (@additive_add_congr_path C P t A _ Z _ _ _ _
      (@eq_sym _ _ _
        (@comp_assoc C _ X _ Z h
          (@additive_inj1_fapp0 C P t A X Y)
          (@binary_products_proj1_fapp0 C P
            (@additive_binary_products C P t A) X Y)))
      (@eq_sym _ _ _
        (@comp_assoc C _ Y _ Z h
          (@additive_inj2_fapp0 C P t A X Y)
          (@binary_products_proj2_fapp0 C P
            (@additive_binary_products C P t A) X Y))))
    (@eq_trans _ _ _ _
      (@eq_sym _ _ _
        ((@preadditive_comp_add_right_law C
          (@additive_preadditive C P t A))
          (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y))
          (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y))
          Z h
          (@comp_fapp0 C
            (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) X
            (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y))
            (@additive_inj1_fapp0 C P t A X Y)
            (@binary_products_proj1_fapp0 C P
              (@additive_binary_products C P t A) X Y))
          (@comp_fapp0 C
            (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) Y
            (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y))
            (@additive_inj2_fapp0 C P t A X Y)
            (@binary_products_proj2_fapp0 C P
              (@additive_binary_products C P t A) X Y))))
      (@eq_trans _ _ _ h
        (@eq_ap _ _
          (λ e : τ (Hom C _ _), @comp_fapp0 C _ _ Z h e)
          (@additive_biproduct_identity_sum C P t A X Y)
          (@id C _)
          (@additive_biproduct_identity_path C P t A X Y))
        (@eq_refl _ h)));
