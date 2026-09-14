/* The native slice postcomposition action retains domain arrows.
   Derive the arbitrary-input observation from existing constructor betas. */
require open emdash.emdash3_2_pullbacks;

symbol slice_sigma_underlying_literal_path [C : Cat] [X Y x y : τ (Obj C)]
  (f : τ (Hom C X Y)) (a : τ (Hom C x X)) (b : τ (Hom C y X))
  (h : τ (Hom C x y))
  (alpha : τ (Hom (Hom_cat C x X) (@comp_fapp0 C x y X b h) a))
  : τ (@= (Hom C x y)
      (@slice_arrow_underlying C Y
        (@slice_sigma_obj C X Y f (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z X) x a))
        (@slice_sigma_obj C X Y f (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z X) y b))
        (@fapp1_fapp0 (@Slice_cat C X) (@Slice_cat C Y) (@slice_sigma_func C X Y f)
          (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z X) x a)
          (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z X) y b)
          (@sigma_arrow (Op_cat C) (@yoneda_psh C X) y x b a h alpha))) h)
≔ @eq_refl (Hom C x y) h;

symbol slice_sigma_underlying_path [C : Cat] [X Y : τ (Obj C)]
  (f : τ (Hom C X Y)) (q r : τ (Obj (@Slice_cat C X))) (h : τ (Hom (@Slice_cat C X) q r))
  : τ (@= (Hom C (@slice_object_domain C X q) (@slice_object_domain C X r)) (@slice_arrow_underlying C Y
    (@slice_sigma_obj C X Y f q) (@slice_sigma_obj C X Y f r) (@fapp1_fapp0 (@Slice_cat C X) (@Slice_cat C Y)
    (@slice_sigma_func C X Y f) q r h)) (@slice_arrow_underlying C X q r h))
≔ (@sigma_ind (Obj C) (λ z : τ (Obj C), Hom C z X)
    (λ q0 : τ (Obj (@Slice_cat C X)), @Pi_grpd (Obj (@Slice_cat C X)) (λ r0 : τ (Obj (@Slice_cat C X)), (@Pi_grpd
      (Hom (@Slice_cat C X) q0 r0) (λ h : τ (Hom (@Slice_cat C X) q0 r0), (@= (Hom C (@slice_object_domain C X q0)
      (@slice_object_domain C X r0)) (@slice_arrow_underlying C Y (@slice_sigma_obj C X Y f q0) (@slice_sigma_obj C
      X Y f r0) (@fapp1_fapp0 (@Slice_cat C X) (@Slice_cat C Y) (@slice_sigma_func C X Y f) q0 r0 h))
      (@slice_arrow_underlying C X q0 r0 h))))))
    (λ x : τ (Obj C), λ a : τ (Hom C x X), λ r0 : τ (Obj (@Slice_cat C X)),
      @sigma_ind (Obj C) (λ z : τ (Obj C), Hom C z X)
        (λ r1 : τ (Obj (@Slice_cat C X)), (@Pi_grpd (Hom (@Slice_cat C X) (@Struct_sigma (Obj C) (λ z : τ (Obj C),
          Hom C z X) x a) r1) (λ h : τ (Hom (@Slice_cat C X) (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z X) x
          a) r1), (@= (Hom C (@slice_object_domain C X (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z X) x a))
          (@slice_object_domain C X r1)) (@slice_arrow_underlying C Y (@slice_sigma_obj C X Y f (@Struct_sigma (Obj
          C) (λ z : τ (Obj C), Hom C z X) x a)) (@slice_sigma_obj C X Y f r1) (@fapp1_fapp0 (@Slice_cat C X)
          (@Slice_cat C Y) (@slice_sigma_func C X Y f) (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z X) x a) r1
          h)) (@slice_arrow_underlying C X (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z X) x a) r1 h)))))
        (λ y : τ (Obj C), λ b : τ (Hom C y X), λ h0 : τ (Hom (@Slice_cat C X) (@Struct_sigma (Obj C) (λ z : τ (Obj
          C), Hom C z X) x a) (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z X) y b)),
          @sigma_ind (Hom C x y) (λ k : τ (Hom C x y), (Hom (Hom_cat C x X) (@comp_fapp0 C x y X b k) a))
            (λ h1 : τ (Hom (@Slice_cat C X) (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z X) x a) (@Struct_sigma
              (Obj C) (λ z : τ (Obj C), Hom C z X) y b)), (@= (Hom C (@slice_object_domain C X (@Struct_sigma (Obj
              C) (λ z : τ (Obj C), Hom C z X) x a)) (@slice_object_domain C X (@Struct_sigma (Obj C) (λ z : τ (Obj
              C), Hom C z X) y b))) (@slice_arrow_underlying C Y (@slice_sigma_obj C X Y f (@Struct_sigma (Obj C) (λ
              z : τ (Obj C), Hom C z X) x a)) (@slice_sigma_obj C X Y f (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom
              C z X) y b)) (@fapp1_fapp0 (@Slice_cat C X) (@Slice_cat C Y) (@slice_sigma_func C X Y f)
              (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z X) x a) (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom
              C z X) y b) h1)) (@slice_arrow_underlying C X (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z X) x a)
              (@Struct_sigma (Obj C) (λ z : τ (Obj C), Hom C z X) y b) h1)))
            (λ k : τ (Hom C x y), λ alpha : τ (Hom (Hom_cat C x X) (@comp_fapp0 C x y X b k) a),
              @slice_sigma_underlying_literal_path C X Y x y f a b k alpha) h0) r0) q) r h;
