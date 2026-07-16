/*
  Reviewer milestone: registered open maps and dependent sections act on
  shaped PathRecord paths through the existing semantic path owners.

  A selected action carries next-dimensional agreement with `eq_ap` or
  `eq_apd`; selected actions compose computationally. This does not add an
  arbitrary-constructor J beta or a fibrancy capability.
*/

require open emdash.emdash3_2;

assert [A B : Grpd]
  (f : τ A → τ B)
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @obs_action_apply A B f (@obs_action_from_function A B f) x y p
  ≡ @eq_ap A B f x y p;

assert [A : Grpd]
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @obs_action_apply A A (λ z : τ A, z)
    (@obs_action_id A) x y p
  ≡ p;

assert [A B C : Grpd]
  [f : τ A → τ B]
  [g : τ B → τ C]
  (u : τ (@ObsAction A B f))
  (v : τ (@ObsAction B C g))
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @obs_action_apply
    A C (λ z : τ A, g (f z))
    (@obs_action_comp A B C f g u v)
    x y p
  ≡ @obs_action_apply B C g v (f x) (f y)
      (@obs_action_apply A B f u x y p);

assert [A B C : Grpd]
  [f : τ A → τ B]
  [g : τ B → τ C]
  (u : τ (@ObsAction A B f))
  (v : τ (@ObsAction B C g))
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @obs_action_agrees
    A C (λ z : τ A, g (f z))
    (@obs_action_comp A B C f g u v)
    x y p
  : τ (@= (@= C (g (f x)) (g (f y)))
      (@obs_action_apply B C g v (f x) (f y)
        (@obs_action_apply A B f u x y p))
      (@eq_ap A C (λ z : τ A, g (f z)) x y p));

assert [A : Grpd]
  [P : τ A → Grpd]
  (s : Π x : τ A, τ (P x))
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @obs_daction_apply A P s (@obs_daction_from_section A P s) x y p
  ≡ @eq_apd A P s x y p;

assert [A B : Grpd]
  [f : τ (PathRecord_grpd A) → τ (PathRecord_grpd B)]
  (u : τ (@ObsAction (PathRecord_grpd A) (PathRecord_grpd B) f))
  [r s : τ (PathRecord_grpd A)]
  (p : τ (@PathRecordPathView A r s)) ⊢
  @path_record_action A B f u r s p
  : τ (@PathRecordPathView B (f r) (f s));

assert [A B : Grpd]
  (f : τ (PathRecord_grpd A) → τ (PathRecord_grpd B))
  (r : τ (PathRecord_grpd A)) ⊢
  @path_record_action A B f
    (@obs_action_from_function (PathRecord_grpd A) (PathRecord_grpd B) f)
    r r (@PathRecordPathRefl A r)
  ≡ @PathRecordPathRefl B (f r);

assert [A : Grpd]
  [r s : τ (PathRecord_grpd A)]
  (p : τ (@PathRecordPathView A r s)) ⊢
  @path_record_action
    A A
    (λ t : τ (PathRecord_grpd A), t)
    (@obs_action_id (PathRecord_grpd A))
    r s p
  ≡ p;

assert [A B : Grpd]
  [f : τ (PathRecord_grpd A) → τ (PathRecord_grpd B)]
  (u : τ (@ObsAction (PathRecord_grpd A) (PathRecord_grpd B) f))
  [r s : τ (PathRecord_grpd A)]
  (p : τ (@PathRecordPathView A r s)) ⊢
  @path_record_action_agrees A B f u r s p
  : τ (@= (@PathRecordPathView B (f r) (f s))
      (@path_record_action A B f u r s p)
      (@eq_ap (PathRecord_grpd A) (PathRecord_grpd B) f r s p));

assert [A : Grpd]
  [r s : τ (PathRecord_grpd A)]
  (p : τ (@PathRecordPathView A r s)) ⊢
  @path_record_witness_action A r s p
  : τ (@PathOver
      (PathRecord_grpd A)
      (λ t : τ (PathRecord_grpd A),
        @= A (path_record_src t) (path_record_dst t))
      r s p (path_record_witness r) (path_record_witness s));

// Coherence is not runtime equality for an arbitrary registered action.
assertnot [A B : Grpd]
  [f : τ A → τ B]
  (u : τ (@ObsAction A B f))
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @obs_action_apply A B f u x y p
  ≡ @eq_ap A B f x y p;

// Registered packages retain their coherence evidence and have no eta.
assertnot [A B : Grpd]
  [f : τ A → τ B]
  (u : τ (@ObsAction A B f)) ⊢
  u
  ≡ @obs_action_intro A B f
      (@obs_action_map A B f u)
      (sigma_Snd u);

// Action does not grant arbitrary-constructor dependent-J computation.
assertnot [A B : Grpd]
  [f : τ (PathRecord_grpd A) → τ (PathRecord_grpd B)]
  (u : τ (@ObsAction (PathRecord_grpd A) (PathRecord_grpd B) f))
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
