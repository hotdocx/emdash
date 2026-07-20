/*
  Reviewer milestone: optional path-action refinements for open maps.

  A selected nondependent presentation carries next-dimensional agreement
  with the capped action of canonical `path_map_func`, and selections compose
  computationally. The direct dependent action remains `eq_apd`. Neither
  refinement data nor direct dependent action adds an arbitrary-constructor J
  beta or a fibrancy capability.
*/

require open emdash.emdash3_2;

assert [A B : Grpd]
  (f : τ A → τ B)
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @path_action_refinement_apply A B f (@path_action_refinement_canonical A B f) x y p
  ≡ @fapp1_fapp0
      (Path_cat A)
      (Path_cat B)
      (@path_map_func A B f)
      x y p;

assert [A : Grpd]
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @path_action_refinement_apply A A (λ z : τ A, z)
    (@path_action_refinement_id A) x y p
  ≡ p;

assert [A : Grpd]
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @fapp1_fapp0
    (Path_cat A)
    (Path_cat A)
    (@path_map_func A A (@id Grpd_cat A))
    x y p
  ≡ p;

assert [A B C : Grpd]
  [f : τ A → τ B]
  [g : τ B → τ C]
  (u : τ (@PathActionRefinement A B f))
  (v : τ (@PathActionRefinement B C g))
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @path_action_refinement_apply
    A C (λ z : τ A, g (f z))
    (@path_action_refinement_comp A B C f g u v)
    x y p
  ≡ @path_action_refinement_apply B C g v (f x) (f y)
      (@path_action_refinement_apply A B f u x y p);

assert [A B C : Grpd]
  [f : τ A → τ B]
  [g : τ B → τ C]
  (u : τ (@PathActionRefinement A B f))
  (v : τ (@PathActionRefinement B C g))
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @path_action_refinement_agrees
    A C (λ z : τ A, g (f z))
    (@path_action_refinement_comp A B C f g u v)
    x y p
  : τ (@= (@= C (g (f x)) (g (f y)))
      (@path_action_refinement_apply B C g v (f x) (f y)
        (@path_action_refinement_apply A B f u x y p))
      (@fapp1_fapp0
        (Path_cat A)
        (Path_cat C)
        (@path_map_func A C (λ z : τ A, g (f z)))
        x y p));

// Composite canonical action is related to nested action propositionally.
assert [A B C : Grpd]
  (f : τ A → τ B)
  (g : τ B → τ C)
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @eq_ap_comp A B C f g x y p
  : τ (@= (@= C (g (f x)) (g (f y)))
      (@fapp1_fapp0
        (Path_cat B)
        (Path_cat C)
        (@path_map_func B C g)
        (f x) (f y)
        (@fapp1_fapp0
          (Path_cat A)
          (Path_cat B)
          (@path_map_func A B f)
          x y p))
      (@fapp1_fapp0
        (Path_cat A)
        (Path_cat C)
        (@path_map_func A C (λ z : τ A, g (f z)))
        x y p));

assertnot [A B C : Grpd]
  (f : τ A → τ B)
  (g : τ B → τ C)
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @fapp1_fapp0
    (Path_cat A)
    (Path_cat C)
    (@path_map_func A C (λ z : τ A, g (f z)))
    x y p
  ≡ @fapp1_fapp0
      (Path_cat B)
      (Path_cat C)
      (@path_map_func B C g)
      (f x) (f y)
      (@fapp1_fapp0
        (Path_cat A)
        (Path_cat B)
        (@path_map_func A B f)
        x y p);

assert [A B : Grpd]
  [f : τ (PathRecord_grpd A) → τ (PathRecord_grpd B)]
  (u : τ (@PathActionRefinement (PathRecord_grpd A) (PathRecord_grpd B) f))
  [r s : τ (PathRecord_grpd A)]
  (p : τ (@PathRecordPathView A r s)) ⊢
  @path_record_action A B f u r s p
  : τ (@PathRecordPathView B (f r) (f s));

assert [A B : Grpd]
  (f : τ (PathRecord_grpd A) → τ (PathRecord_grpd B))
  (r : τ (PathRecord_grpd A)) ⊢
  @path_record_action A B f
    (@path_action_refinement_canonical (PathRecord_grpd A) (PathRecord_grpd B) f)
    r r (@PathRecordPathRefl A r)
  ≡ @PathRecordPathRefl B (f r);

assert [A : Grpd]
  [r s : τ (PathRecord_grpd A)]
  (p : τ (@PathRecordPathView A r s)) ⊢
  @path_record_action
    A A
    (λ t : τ (PathRecord_grpd A), t)
    (@path_action_refinement_id (PathRecord_grpd A))
    r s p
  ≡ p;

assert [A B : Grpd]
  [f : τ (PathRecord_grpd A) → τ (PathRecord_grpd B)]
  (u : τ (@PathActionRefinement (PathRecord_grpd A) (PathRecord_grpd B) f))
  [r s : τ (PathRecord_grpd A)]
  (p : τ (@PathRecordPathView A r s)) ⊢
  @path_record_action_agrees A B f u r s p
  : τ (@= (@PathRecordPathView B (f r) (f s))
      (@path_record_action A B f u r s p)
      (@fapp1_fapp0
        (Path_cat (PathRecord_grpd A))
        (Path_cat (PathRecord_grpd B))
        (@path_map_func (PathRecord_grpd A) (PathRecord_grpd B) f)
        r s p));

assert [A : Grpd]
  [r s : τ (PathRecord_grpd A)]
  (p : τ (@PathRecordPathView A r s)) ⊢
  @path_record_witness_action A r s p
  : τ (@PathOver
      (PathRecord_grpd A)
      (λ t : τ (PathRecord_grpd A),
        @= A (path_record_src t) (path_record_dst t))
      r s p (path_record_witness r) (path_record_witness s));

assert [A : Grpd]
  [r s : τ (PathRecord_grpd A)]
  (p : τ (@PathRecordPathView A r s)) ⊢
  @path_record_witness_action A r s p
  ≡ @eq_apd
      (PathRecord_grpd A)
      (λ t : τ (PathRecord_grpd A),
        @= A (path_record_src t) (path_record_dst t))
      (λ t : τ (PathRecord_grpd A), path_record_witness t)
      r s p;

// Coherence is not runtime equality for an arbitrary refinement.
assertnot [A B : Grpd]
  [f : τ A → τ B]
  (u : τ (@PathActionRefinement A B f))
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @path_action_refinement_apply A B f u x y p
  ≡ @fapp1_fapp0
      (Path_cat A)
      (Path_cat B)
      (@path_map_func A B f)
      x y p;

// Refinement packages retain their coherence evidence and have no eta.
assertnot [A B : Grpd]
  [f : τ A → τ B]
  (u : τ (@PathActionRefinement A B f)) ⊢
  u
  ≡ @path_action_refinement_intro A B f
      (@path_action_refinement_map A B f u)
      (sigma_Snd u);

// Action does not grant arbitrary-constructor dependent-J computation.
assertnot [A B : Grpd]
  [f : τ (PathRecord_grpd A) → τ (PathRecord_grpd B)]
  (u : τ (@PathActionRefinement (PathRecord_grpd A) (PathRecord_grpd B) f))
  (r : τ (PathRecord_grpd A))
  (p : τ (@PathRecordPathView A r r))
  (P : τ (PathRecord_grpd B) → Grpd)
  (branch : τ (P (f r))) ⊢
  @ind_eq
    (PathRecord_grpd B)
    (f r) (f r)
    (@path_record_action A B f u r r p)
    P branch
  ≡ branch;
