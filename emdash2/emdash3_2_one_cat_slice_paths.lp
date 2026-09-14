/* Equality reflection at the actual ordinary native slice Hom.
   All uses of Sigma elimination retain the native classifier in the motive. */
require open emdash.emdash3_2_presheaves;
require open emdash.emdash3_2_eq1_evidence_property;

// Explicit structural/model obligation: the opaque profile has no constructor here.
// A slice of an ordinary category is ordinary.
constant symbol one_cat_slice_category [C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) (X : τ (Obj C))
  : τ (IsNCat (cat_succ cat_zero) (@Slice_cat C X));

// Dependent constructor congruence with a proposition-valued fibre.
symbol prop_fibre_image_path [A Z : Grpd] (P : τ A → Grpd)
  (c : Π a : τ A, τ (P a) → τ Z)
  (hP : Π a : τ A, τ (IsPropGrpd (P a)))
  [a b : τ A] (u : τ (P a)) (v : τ (P b)) (p : τ (@= A a b))
  : τ (@= Z (c a u) (c b v))
≔ (@ind_eq A b a (@eq_sym A a b p)
    (λ b0 : τ A, @Pi_grpd (P b0) (λ v0 : τ (P b0), @= Z (c a u) (c b0 v0)))
    (λ v0 : τ (P a), @eq_ap (P a) Z (c a) u v0
      (@is_contr_center (@= (P a) u v0) (hP a u v0)))) v;

// Literal endpoint presentation; arbitrary arrows are eliminated, not eta-rewritten.
symbol one_cat_slice_literal_path [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) (U x y : τ (Obj C))
  (a : τ (Hom C x U)) (b : τ (Hom C y U))
  (h g : τ (Hom (@Slice_cat C U) (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) x a) (@Struct_sigma (Obj C) (λ
    z : τ (Obj C), Hom C z U) y b))) (p : τ (@= (Hom C (@slice_object_domain C U (@Struct_sigma (Obj C) (λ z : τ
    (Obj C), Hom C z U) x a)) (@slice_object_domain C U (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) y b)))
    (@slice_arrow_underlying C U (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) x a) (@Struct_sigma (Obj C) (λ
    z : τ (Obj C), Hom C z U) y b) h) (@slice_arrow_underlying C U (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z
    U) x a) (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) y b) g)))
  : τ (@= (Hom (@Slice_cat C U) (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) x a) (@Struct_sigma (Obj C) (λ z
    : τ (Obj C), Hom C z U) y b)) h g)
≔ (@sigma_ind (Hom C x y) (λ f : τ (Hom C x y), (Hom (Hom_cat C x U) (@comp_fapp0 C x y U b f) a))
    (λ h0 : τ (Hom (@Slice_cat C U) (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) x a) (@Struct_sigma (Obj C)
      (λ z : τ (Obj C), Hom C z U) y b)), @Pi_grpd (Hom (@Slice_cat C U) (@Struct_sigma (Obj C) (λ z : τ (Obj C),
      Hom C z U) x a) (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) y b)) (λ g0 : τ (Hom (@Slice_cat C U)
      (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) x a) (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) y
      b)),
      @Pi_grpd (@= (Hom C (@slice_object_domain C U (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) x a))
        (@slice_object_domain C U (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) y b)))
        (@slice_arrow_underlying C U (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) x a) (@Struct_sigma (Obj C)
        (λ z : τ (Obj C), Hom C z U) y b) h0) (@slice_arrow_underlying C U (@Struct_sigma (Obj C) (λ z : τ (Obj C),
        Hom C z U) x a) (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) y b) g0)) (λ _ : τ (@= (Hom C
        (@slice_object_domain C U (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) x a)) (@slice_object_domain C
        U (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) y b))) (@slice_arrow_underlying C U (@Struct_sigma
        (Obj C) (λ z : τ (Obj C), Hom C z U) x a) (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) y b) h0)
        (@slice_arrow_underlying C U (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) x a) (@Struct_sigma (Obj C)
        (λ z : τ (Obj C), Hom C z U) y b) g0)), (@= (Hom (@Slice_cat C U) (@Struct_sigma (Obj C) (λ z : τ (Obj C),
        Hom C z U) x a) (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) y b)) h0 g0))))
    (λ f : τ (Hom C x y), λ alpha : τ (Hom (Hom_cat C x U) (@comp_fapp0 C x y U b f) a), λ g0 : τ (Hom (@Slice_cat C
      U) (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) x a) (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z
      U) y b)),
      (@sigma_ind (Hom C x y) (λ f : τ (Hom C x y), (Hom (Hom_cat C x U) (@comp_fapp0 C x y U b f) a))
        (λ g1 : τ (Hom (@Slice_cat C U) (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) x a) (@Struct_sigma (Obj
          C) (λ z : τ (Obj C), Hom C z U) y b)), @Pi_grpd (@= (Hom C (@slice_object_domain C U (@Struct_sigma (Obj
          C) (λ z : τ (Obj C), Hom C z U) x a)) (@slice_object_domain C U (@Struct_sigma (Obj C) (λ z : τ (Obj C),
          Hom C z U) y b))) (@slice_arrow_underlying C U (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) x a)
          (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) y b) (@sigma_arrow (Op_cat C) (@yoneda_psh C U) y x b
          a f alpha)) (@slice_arrow_underlying C U (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) x a)
          (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) y b) g1))
          (λ _ : τ (@= (Hom C (@slice_object_domain C U (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) x a))
            (@slice_object_domain C U (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) y b)))
            (@slice_arrow_underlying C U (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) x a) (@Struct_sigma
            (Obj C) (λ z : τ (Obj C), Hom C z U) y b) (@sigma_arrow (Op_cat C) (@yoneda_psh C U) y x b a f alpha))
            (@slice_arrow_underlying C U (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) x a) (@Struct_sigma
            (Obj C) (λ z : τ (Obj C), Hom C z U) y b) g1)), (@= (Hom (@Slice_cat C U) (@Struct_sigma (Obj C) (λ z :
            τ (Obj C), Hom C z U) x a) (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) y b)) (@sigma_arrow
            (Op_cat C) (@yoneda_psh C U) y x b a f alpha) g1)))
        (λ k : τ (Hom C x y), λ beta : τ (Hom (Hom_cat C x U) (@comp_fapp0 C x y U b k) a), λ e : τ (@= (Hom C x y)
          f k),
          @prop_fibre_image_path (Hom C x y) (Hom (@Slice_cat C U) (@Struct_sigma (Obj C) (λ z : τ (Obj C),
            Hom C z U) x a) (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) y b)) (λ f : τ (Hom C x y), (Hom
            (Hom_cat C x U) (@comp_fapp0 C x y U b f) a))
            (λ j : τ (Hom C x y), λ c : τ (Hom (Hom_cat C x U) (@comp_fapp0 C x y U b j) a), (@sigma_arrow (Op_cat
              C) (@yoneda_psh C U) y x b a j c))
            (λ j : τ (Hom C x y), @discrete_hom_is_prop (Hom_cat C x U) (C1 x U)
              (@comp_fapp0 C x y U b j) a)
            f k alpha beta e) g0)) h) g p;

// Equality reflection for arbitrary original slice endpoints.
symbol one_cat_slice_arrow_path [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) (U : τ (Obj C))
  (q r : τ (Obj (@Slice_cat C U))) (h g : τ (Hom (@Slice_cat C U) q r)) (p : τ (@= (Hom C (@slice_object_domain C U
    q) (@slice_object_domain C U r)) (@slice_arrow_underlying C U q r h) (@slice_arrow_underlying C U q r g)))
  : τ (@= (Hom (@Slice_cat C U) q r) h g)
≔ (@sigma_ind (Obj C) (λ z : τ (Obj C), Hom C z U)
    (λ q0 : τ (Obj (@Slice_cat C U)), @Pi_grpd (Obj (@Slice_cat C U)) (λ r0 : τ (Obj (@Slice_cat C U)), (@Pi_grpd
      (Hom (@Slice_cat C U) q0 r0) (λ h : τ (Hom (@Slice_cat C U) q0 r0), @Pi_grpd (Hom (@Slice_cat C U) q0 r0) (λ g
      : τ (Hom (@Slice_cat C U) q0 r0), @Pi_grpd (@= (Hom C (@slice_object_domain C U q0) (@slice_object_domain C U
      r0)) (@slice_arrow_underlying C U q0 r0 h) (@slice_arrow_underlying C U q0 r0 g)) (λ _ : τ (@= (Hom C
      (@slice_object_domain C U q0) (@slice_object_domain C U r0)) (@slice_arrow_underlying C U q0 r0 h)
      (@slice_arrow_underlying C U q0 r0 g)), (@= (Hom (@Slice_cat C U) q0 r0) h g)))))))
    (λ x : τ (Obj C), λ a : τ (Hom C x U), λ r0 : τ (Obj (@Slice_cat C U)),
      @sigma_ind (Obj C) (λ z : τ (Obj C), Hom C z U)
        (λ r1 : τ (Obj (@Slice_cat C U)), (@Pi_grpd (Hom (@Slice_cat C U) (@Struct_sigma (Obj C) (λ z : τ (Obj C),
          Hom C z U) x a) r1) (λ h : τ (Hom (@Slice_cat C U) (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) x
          a) r1), @Pi_grpd (Hom (@Slice_cat C U) (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) x a) r1) (λ g :
          τ (Hom (@Slice_cat C U) (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) x a) r1), @Pi_grpd (@= (Hom C
          (@slice_object_domain C U (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) x a)) (@slice_object_domain
          C U r1)) (@slice_arrow_underlying C U (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) x a) r1 h)
          (@slice_arrow_underlying C U (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) x a) r1 g)) (λ _ : τ (@=
          (Hom C (@slice_object_domain C U (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) x a))
          (@slice_object_domain C U r1)) (@slice_arrow_underlying C U (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C
          z U) x a) r1 h) (@slice_arrow_underlying C U (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) x a) r1
          g)), (@= (Hom (@Slice_cat C U) (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z U) x a) r1) h g))))))
        (λ y : τ (Obj C), λ b : τ (Hom C y U), @one_cat_slice_literal_path C C1 U x y a b)
        r0) q) r h g p;
