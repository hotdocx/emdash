/*
  Reusable pre-Abelian bimorphism lemmas.

  A zero selected kernel embedding implies monicity, and a zero selected
  cokernel projection implies epicity. Named difference cones keep the
  universal-factor proof rigid and inspectable. Composition preserves both
  cancellation properties. No rule or additional arrow grammar is introduced.
*/

require open emdash.emdash3_2_abelian_fiber_pushout_stability;

symbol kernel_zero_difference_cone
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [A B T : τ (Obj C)]
  (m : τ (Hom C A B))
  (u v : τ (Hom C T A))
  (p : τ (@= (Hom C T B)
    (@comp_fapp0 C T A B m u)
    (@comp_fapp0 C T A B m v)))
  : τ (@WeakKernelAnnihilator C S A B m T)
≔ @Struct_sigma (Hom C T A)
    (λ h : τ (Hom C T A),
      @= (Hom C T B)
        (@comp_fapp0 C T A B m h)
        (@preadditive_hom_zero C S T B))
    (@preadditive_hom_add C S T A u
      (@preadditive_hom_neg C S T A v))
    (@preadditive_difference_postcomp_zero_path C S T A B m u v p);

symbol kernel_zero_difference_lift
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [A B T : τ (Obj C)]
  (m : τ (Hom C A B))
  (K : τ (@ComputationalKernel C S A B m))
  (u v : τ (Hom C T A))
  (p : τ (@= (Hom C T B)
    (@comp_fapp0 C T A B m u)
    (@comp_fapp0 C T A B m v)))
  : τ (Hom C T (@computational_kernel_object C S A B m K))
≔ @computational_kernel_lift C S A B m K T
    (@kernel_zero_difference_cone C S A B T m u v p);

symbol kernel_zero_difference_path
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [A B T : τ (Obj C)]
  (m : τ (Hom C A B))
  (K : τ (@ComputationalKernel C S A B m))
  (zero : τ (@= (Hom C
    (@computational_kernel_object C S A B m K) A)
    (@computational_kernel_morphism C S A B m K)
    (@preadditive_hom_zero C S
      (@computational_kernel_object C S A B m K) A)))
  (u v : τ (Hom C T A))
  (p : τ (@= (Hom C T B)
    (@comp_fapp0 C T A B m u)
    (@comp_fapp0 C T A B m v)))
  : τ (@= (Hom C T A)
      (@preadditive_hom_add C S T A u
        (@preadditive_hom_neg C S T A v))
      (@preadditive_hom_zero C S T A))
≔ @eq_trans (Hom C T A)
    (@preadditive_hom_add C S T A u
      (@preadditive_hom_neg C S T A v))
    (@comp_fapp0 C T
      (@computational_kernel_object C S A B m K) A
      (@computational_kernel_morphism C S A B m K)
      (@kernel_zero_difference_lift C S A B T m K u v p))
    (@preadditive_hom_zero C S T A)
    (@eq_sym _ _ _
      (@computational_kernel_lift_path C S A B m K T
        (@kernel_zero_difference_cone C S A B T m u v p)))
    (@eq_trans (Hom C T A) _ _ _
      (@eq_ap
        (Hom C (@computational_kernel_object C S A B m K) A)
        (Hom C T A)
        (λ h : τ (Hom C (@computational_kernel_object C S A B m K) A),
          @comp_fapp0 C T
            (@computational_kernel_object C S A B m K) A h
            (@kernel_zero_difference_lift C S A B T m K u v p))
        _ _ zero)
      (@preadditive_comp_zero_left_path C S T
        (@computational_kernel_object C S A B m K) A
        (@kernel_zero_difference_lift C S A B T m K u v p)));

symbol computational_kernel_zero_to_monic
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [A B : τ (Obj C)]
  (m : τ (Hom C A B))
  (K : τ (@ComputationalKernel C S A B m))
  (zero : τ (@= (Hom C
    (@computational_kernel_object C S A B m K) A)
    (@computational_kernel_morphism C S A B m K)
    (@preadditive_hom_zero C S
      (@computational_kernel_object C S A B m K) A)))
  : τ (@IsMonic C A B m)
≔ λ T : τ (Obj C), λ u : τ (Hom C T A), λ v : τ (Hom C T A),
    λ p : τ (@= (Hom C T B)
      (@comp_fapp0 C T A B m u)
      (@comp_fapp0 C T A B m v)),
      @abelian_group_sub_zero_to_eq_path
        (Hom C T A) (@preadditive_hom_structure C S T A) u v
        (@kernel_zero_difference_path C S A B T m K zero u v p);

symbol cokernel_zero_difference_cone
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [A B T : τ (Obj C)]
  (e : τ (Hom C A B))
  (u v : τ (Hom C B T))
  (p : τ (@= (Hom C A T)
    (@comp_fapp0 C A B T u e)
    (@comp_fapp0 C A B T v e)))
  : τ (@CokernelCoannihilator C S A B e T)
≔ @Struct_sigma (Hom C B T)
    (λ h : τ (Hom C B T),
      @= (Hom C A T)
        (@comp_fapp0 C A B T h e)
        (@preadditive_hom_zero C S A T))
    (@preadditive_hom_add C S B T u
      (@preadditive_hom_neg C S B T v))
    (@preadditive_comp_difference_zero_path C S A B T u v e p);

symbol cokernel_zero_difference_colift
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [A B T : τ (Obj C)]
  (e : τ (Hom C A B))
  (Q : τ (@ComputationalCokernel C S A B e))
  (u v : τ (Hom C B T))
  (p : τ (@= (Hom C A T)
    (@comp_fapp0 C A B T u e)
    (@comp_fapp0 C A B T v e)))
  : τ (Hom C (@computational_cokernel_object C S A B e Q) T)
≔ @computational_cokernel_colift C S A B e Q T
    (@cokernel_zero_difference_cone C S A B T e u v p);

symbol cokernel_zero_difference_path
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [A B T : τ (Obj C)]
  (e : τ (Hom C A B))
  (Q : τ (@ComputationalCokernel C S A B e))
  (zero : τ (@= (Hom C B
    (@computational_cokernel_object C S A B e Q))
    (@computational_cokernel_morphism C S A B e Q)
    (@preadditive_hom_zero C S B
      (@computational_cokernel_object C S A B e Q))))
  (u v : τ (Hom C B T))
  (p : τ (@= (Hom C A T)
    (@comp_fapp0 C A B T u e)
    (@comp_fapp0 C A B T v e)))
  : τ (@= (Hom C B T)
      (@preadditive_hom_add C S B T u
        (@preadditive_hom_neg C S B T v))
      (@preadditive_hom_zero C S B T))
≔ @eq_trans (Hom C B T)
    (@preadditive_hom_add C S B T u
      (@preadditive_hom_neg C S B T v))
    (@comp_fapp0 C B
      (@computational_cokernel_object C S A B e Q) T
      (@cokernel_zero_difference_colift C S A B T e Q u v p)
      (@computational_cokernel_morphism C S A B e Q))
    (@preadditive_hom_zero C S B T)
    (@eq_sym _ _ _
      (@computational_cokernel_colift_path C S A B e Q T
        (@cokernel_zero_difference_cone C S A B T e u v p)))
    (@eq_trans (Hom C B T) _ _ _
      (@eq_ap
        (Hom C B (@computational_cokernel_object C S A B e Q))
        (Hom C B T)
        (λ q : τ (Hom C B
          (@computational_cokernel_object C S A B e Q)),
          @comp_fapp0 C B
            (@computational_cokernel_object C S A B e Q) T
            (@cokernel_zero_difference_colift C S A B T e Q u v p) q)
        _ _ zero)
      (@preadditive_comp_zero_right_path C S B
        (@computational_cokernel_object C S A B e Q) T
        (@cokernel_zero_difference_colift C S A B T e Q u v p)));

symbol computational_cokernel_zero_to_epic
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [A B : τ (Obj C)]
  (e : τ (Hom C A B))
  (Q : τ (@ComputationalCokernel C S A B e))
  (zero : τ (@= (Hom C B
    (@computational_cokernel_object C S A B e Q))
    (@computational_cokernel_morphism C S A B e Q)
    (@preadditive_hom_zero C S B
      (@computational_cokernel_object C S A B e Q))))
  : τ (@IsEpic C A B e)
≔ λ T : τ (Obj C), λ u : τ (Hom C B T), λ v : τ (Hom C B T),
    λ p : τ (@= (Hom C A T)
      (@comp_fapp0 C A B T u e)
      (@comp_fapp0 C A B T v e)),
      @abelian_group_sub_zero_to_eq_path
        (Hom C B T) (@preadditive_hom_structure C S B T) u v
        (@cokernel_zero_difference_path C S A B T e Q zero u v p);

symbol is_monic_comp
  [C : Cat]
  [A B D : τ (Obj C)]
  (f : τ (Hom C A B))
  (g : τ (Hom C B D))
  (f_monic : τ (@IsMonic C A B f))
  (g_monic : τ (@IsMonic C B D g))
  : τ (@IsMonic C A D (@comp_fapp0 C A B D g f))
≔ λ T : τ (Obj C), λ u : τ (Hom C T A), λ v : τ (Hom C T A),
    λ p : τ (@= (Hom C T D)
      (@comp_fapp0 C T A D (@comp_fapp0 C A B D g f) u)
      (@comp_fapp0 C T A D (@comp_fapp0 C A B D g f) v)),
      f_monic T u v
        (g_monic T
          (@comp_fapp0 C T A B f u)
          (@comp_fapp0 C T A B f v)
          (@eq_trans (Hom C T D) _ _ _
            (@comp_assoc C T A B D g f u)
            (@eq_trans (Hom C T D) _ _ _ p
              (@eq_sym _ _ _ (@comp_assoc C T A B D g f v)))));

symbol is_epic_comp
  [C : Cat]
  [A B D : τ (Obj C)]
  (f : τ (Hom C A B))
  (g : τ (Hom C B D))
  (f_epic : τ (@IsEpic C A B f))
  (g_epic : τ (@IsEpic C B D g))
  : τ (@IsEpic C A D (@comp_fapp0 C A B D g f))
≔ λ T : τ (Obj C), λ u : τ (Hom C D T), λ v : τ (Hom C D T),
    λ p : τ (@= (Hom C A T)
      (@comp_fapp0 C A D T u (@comp_fapp0 C A B D g f))
      (@comp_fapp0 C A D T v (@comp_fapp0 C A B D g f))),
      g_epic T u v
        (f_epic T
          (@comp_fapp0 C B D T u g)
          (@comp_fapp0 C B D T v g)
          (@eq_trans (Hom C A T) _ _ _
            (@comp_assoc C A B D T u g f)
            (@eq_trans (Hom C A T) _ _ _ p
              (@eq_sym _ _ _ (@comp_assoc C A B D T v g f)))));

// A map annihilating the left leg also annihilates the pulled-back right leg.
symbol fiber_product_right_annihilation_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C P t))
  [K Q A I : τ (Obj C)]
  (k : τ (Hom C K Q))
  (p : τ (Hom C A Q))
  (F : τ (@ComputationalFiberProduct C P t Add K Q A k p))
  (chi : τ (Hom C Q I))
  (annihilation : τ (@= (Hom C K I)
    (@comp_fapp0 C K Q I chi k)
    (@preadditive_hom_zero C
      (@additive_preadditive C P t Add) K I)))
  : τ (@= (Hom C
      (@computational_fiber_product_object C P t Add K Q A k p F) I)
      (@comp_fapp0 C
        (@computational_fiber_product_object C P t Add K Q A k p F)
        Q I chi
        (@comp_fapp0 C
          (@computational_fiber_product_object C P t Add K Q A k p F)
          A Q p
          (@computational_fiber_product_proj2 C P t Add K Q A k p F)))
      (@preadditive_hom_zero C
        (@additive_preadditive C P t Add)
        (@computational_fiber_product_object C P t Add K Q A k p F) I))
≔ @eq_trans _ _ _ _
    (@eq_ap
      (Hom C
        (@computational_fiber_product_object C P t Add K Q A k p F) Q)
      (Hom C
        (@computational_fiber_product_object C P t Add K Q A k p F) I)
      (λ h : τ (Hom C
        (@computational_fiber_product_object C P t Add K Q A k p F) Q),
        @comp_fapp0 C
          (@computational_fiber_product_object C P t Add K Q A k p F)
          Q I chi h)
      _ _
      (@eq_sym _ _ _
        (@computational_fiber_product_compatibility_path C P t Add
          K Q A k p F)))
    (@eq_trans _ _ _ _
      (@comp_assoc C
        (@computational_fiber_product_object C P t Add K Q A k p F)
        K Q I chi k
        (@computational_fiber_product_proj1 C P t Add K Q A k p F))
      (@eq_trans _ _ _ _
        (@eq_ap (Hom C K I)
          (Hom C
            (@computational_fiber_product_object C P t Add K Q A k p F) I)
          (λ h : τ (Hom C K I),
            @comp_fapp0 C
              (@computational_fiber_product_object C P t Add K Q A k p F)
              K I h
              (@computational_fiber_product_proj1 C P t Add K Q A k p F))
          _ _ annihilation)
        (@preadditive_comp_zero_left_path C
          (@additive_preadditive C P t Add)
          (@computational_fiber_product_object C P t Add K Q A k p F)
          K I
          (@computational_fiber_product_proj1 C P t Add K Q A k p F))));

symbol preadditive_postcompose_zero_path
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [X Y Z : τ (Obj C)]
  (g : τ (Hom C Y Z))
  (f : τ (Hom C X Y))
  (p : τ (@= (Hom C X Y) f (@preadditive_hom_zero C S X Y)))
  : τ (@= (Hom C X Z)
      (@comp_fapp0 C X Y Z g f)
      (@preadditive_hom_zero C S X Z))
≔ @eq_trans (Hom C X Z) _ _ _
    (@eq_ap (Hom C X Y) (Hom C X Z)
      (λ h : τ (Hom C X Y), @comp_fapp0 C X Y Z g h)
      _ _ p)
    (@preadditive_comp_zero_right_path C S X Y Z g);

symbol preadditive_precompose_zero_path
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [X Y Z : τ (Obj C)]
  (g : τ (Hom C Y Z))
  (f : τ (Hom C X Y))
  (p : τ (@= (Hom C Y Z) g (@preadditive_hom_zero C S Y Z)))
  : τ (@= (Hom C X Z)
      (@comp_fapp0 C X Y Z g f)
      (@preadditive_hom_zero C S X Z))
≔ @eq_trans (Hom C X Z) _ _ _
    (@eq_ap (Hom C Y Z) (Hom C X Z)
      (λ h : τ (Hom C Y Z), @comp_fapp0 C X Y Z h f)
      _ _ p)
    (@preadditive_comp_zero_left_path C S X Y Z f);

// A factorized arrow vanishes after a test arrow whenever its middle factor
// does. This packages only associativity, path action, and zero composition.
symbol preadditive_factorization_right_annihilation_path
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [T A Q I B : τ (Obj C)]
  (r : τ (Hom C T A))
  (p : τ (Hom C A Q))
  (chi : τ (Hom C Q I))
  (i : τ (Hom C I B))
  (f : τ (Hom C A B))
  (factorization : τ (@= (Hom C A B)
    (@comp_fapp0 C A I B i
      (@comp_fapp0 C A Q I chi p)) f))
  (annihilation : τ (@= (Hom C T I)
    (@comp_fapp0 C T Q I chi
      (@comp_fapp0 C T A Q p r))
    (@preadditive_hom_zero C S T I)))
  : τ (@= (Hom C T B)
      (@comp_fapp0 C T A B f r)
      (@preadditive_hom_zero C S T B))
≔ @eq_trans (Hom C T B) _ _ _
    (@eq_ap (Hom C A B) (Hom C T B)
      (λ h : τ (Hom C A B), @comp_fapp0 C T A B h r)
      _ _ (@eq_sym _ _ _ factorization))
    (@eq_trans (Hom C T B) _ _ _
      (@eq_sym _ _ _
        (@comp_assoc C T A I B i
          (@comp_fapp0 C A Q I chi p) r))
      (@eq_trans (Hom C T B) _ _ _
        (@eq_ap (Hom C T I) (Hom C T B)
          (λ h : τ (Hom C T I), @comp_fapp0 C T I B i h)
          _ _
          (@eq_sym _ _ _ (@comp_assoc C T A Q I chi p r)))
        (@preadditive_postcompose_zero_path C S T I B i
          (@comp_fapp0 C T Q I chi
            (@comp_fapp0 C T A Q p r))
          annihilation)));

// In a pushout, an arrow coannihilated by the second span leg remains
// coannihilated after the first leg and its selected injection.
symbol pushout_left_annihilation_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C P t))
  [X Y Z T : τ (Obj C)]
  (alpha : τ (Hom C Y X))
  (gamma : τ (Hom C Y Z))
  (Q : τ (@ComputationalPushout C P t Add X Y Z alpha gamma))
  (h : τ (Hom C T Y))
  (annihilation : τ (@= (Hom C T Z)
    (@comp_fapp0 C T Y Z gamma h)
    (@preadditive_hom_zero C
      (@additive_preadditive C P t Add) T Z)))
  : τ (@= (Hom C T
      (@computational_pushout_object C P t Add X Y Z alpha gamma Q))
      (@comp_fapp0 C T X
        (@computational_pushout_object C P t Add X Y Z alpha gamma Q)
        (@computational_pushout_inj1 C P t Add X Y Z alpha gamma Q)
        (@comp_fapp0 C T Y X alpha h))
      (@preadditive_hom_zero C
        (@additive_preadditive C P t Add) T
        (@computational_pushout_object C P t Add X Y Z alpha gamma Q)))
≔ @eq_trans _ _ _ _
    (@comp_assoc C T Y X
      (@computational_pushout_object C P t Add X Y Z alpha gamma Q)
      (@computational_pushout_inj1 C P t Add X Y Z alpha gamma Q)
      alpha h)
    (@eq_trans _ _ _ _
      (@eq_ap (Hom C Y
          (@computational_pushout_object C P t Add X Y Z alpha gamma Q))
        (Hom C T
          (@computational_pushout_object C P t Add X Y Z alpha gamma Q))
        (λ q : τ (Hom C Y
            (@computational_pushout_object C P t Add X Y Z alpha gamma Q)),
          @comp_fapp0 C T Y
            (@computational_pushout_object C P t Add X Y Z alpha gamma Q)
            q h)
        _ _
        (@computational_pushout_compatibility_path C P t Add
          X Y Z alpha gamma Q))
      (@eq_trans _ _ _ _
        (@eq_sym _ _ _
          (@comp_assoc C T Y Z
            (@computational_pushout_object C P t Add X Y Z alpha gamma Q)
            (@computational_pushout_inj2 C P t Add X Y Z alpha gamma Q)
            gamma h))
        (@preadditive_postcompose_zero_path C
          (@additive_preadditive C P t Add)
          T Z
          (@computational_pushout_object C P t Add X Y Z alpha gamma Q)
          (@computational_pushout_inj2 C P t Add X Y Z alpha gamma Q)
          (@comp_fapp0 C T Y Z gamma h)
          annihilation)));

// A factorized arrow is coannihilated by a test arrow whenever the test arrow
// coannihilates the factorization through its middle comparison.
symbol preadditive_factorization_left_annihilation_path
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [A Q I B T : τ (Obj C)]
  (p : τ (Hom C A Q))
  (chi : τ (Hom C Q I))
  (i : τ (Hom C I B))
  (f : τ (Hom C A B))
  (s : τ (Hom C B T))
  (factorization : τ (@= (Hom C A B)
    (@comp_fapp0 C A I B i
      (@comp_fapp0 C A Q I chi p)) f))
  (annihilation : τ (@= (Hom C Q T)
    (@comp_fapp0 C Q B T s
      (@comp_fapp0 C Q I B i chi))
    (@preadditive_hom_zero C S Q T)))
  : τ (@= (Hom C A T)
      (@comp_fapp0 C A B T s f)
      (@preadditive_hom_zero C S A T))
≔ @eq_trans (Hom C A T) _ _ _
    (@eq_sym _ _ _
      (@eq_ap (Hom C A B) (Hom C A T)
        (λ h : τ (Hom C A B), @comp_fapp0 C A B T s h)
        _ _ factorization))
    (@eq_trans (Hom C A T) _ _ _
      (@eq_ap (Hom C A B) (Hom C A T)
        (λ h : τ (Hom C A B), @comp_fapp0 C A B T s h)
        _ _ (@comp_assoc C A Q I B i chi p))
      (@eq_trans (Hom C A T) _ _ _
        (@comp_assoc C A Q B T s
          (@comp_fapp0 C Q I B i chi) p)
        (@preadditive_precompose_zero_path C S A Q T
          (@comp_fapp0 C Q B T s
            (@comp_fapp0 C Q I B i chi))
          p annihilation)));
