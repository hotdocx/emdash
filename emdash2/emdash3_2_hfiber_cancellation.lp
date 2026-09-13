/* Generic fibre uniqueness from cancellation, with a retained centre.
   These two existing proofs have no selected kernel/cokernel dependency. */
require open emdash.emdash3_2_eq1_evidence_property;

// Over a set-valued target, a fibre path is determined by its domain path.
symbol hfiber_set_target_path
  [A B : Grpd] (Bset : τ (IsSetGrpd B))
  [f : τ A → τ B] [b : τ B]
  (u v : τ (@HFiber A B f b))
  (p : τ (@= A (sigma_Fst u) (sigma_Fst v)))
  : τ (@= (@HFiber A B f b) u v)
≔ @sigma_path_decode A (λ a : τ A, @= B (f a) b) u v
    (@Struct_sigma (@= A (sigma_Fst u) (sigma_Fst v))
      (λ q : τ (@= A (sigma_Fst u) (sigma_Fst v)),
        @PathOver A (λ a : τ A, @= B (f a) b)
          (sigma_Fst u) (sigma_Fst v) q (sigma_Snd u) (sigma_Snd v))
      p
      (@prop_family_pathover A (λ a : τ A, @= B (f a) b)
        (λ a : τ A, Bset (f a) b)
        (sigma_Fst u) (sigma_Fst v) p (sigma_Snd u) (sigma_Snd v)));

// An injective function's inhabited fibre contracts at its supplied point.
symbol hfiber_contr_from_cancellation
  [A B : Grpd] (Bset : τ (IsSetGrpd B))
  (f : τ A → τ B)
  (cancel : Π x : τ A, Π y : τ A, τ (@= B (f x) (f y)) → τ (@= A x y))
  (b : τ B) (centre : τ (@HFiber A B f b))
  : τ (IsContr (@HFiber A B f b))
≔ @Struct_sigma (@HFiber A B f b)
    (λ w : τ (@HFiber A B f b),
      @Pi_grpd (@HFiber A B f b) (λ u : τ (@HFiber A B f b),
        @= (@HFiber A B f b) w u))
    centre
    (λ u : τ (@HFiber A B f b),
      @hfiber_set_target_path A B Bset f b centre u
        (cancel (sigma_Fst centre) (sigma_Fst u)
          (@eq_trans B (f (sigma_Fst centre)) b (f (sigma_Fst u))
            (sigma_Snd centre) (@eq_sym B (f (sigma_Fst u)) b (sigma_Snd u)))));
