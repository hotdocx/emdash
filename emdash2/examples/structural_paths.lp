/*
  Reviewer milestone: structural Sigma and dependent-record path round trips.

  Sigma keeps its existing J/componentwise encode and decode maps; their two
  arbitrary composites are propositional, with constructor-reflexive
  computation and no global runtime eta. PathRecord equality already is its
  nested structural view, so its named maps and round trips are transparent
  and preserve stable shaped reflexivity.
*/

require open emdash.emdash3_2;

assert [A : Grpd]
  [P : τ A → Grpd]
  [u v : @τΣ_ A P]
  (p : τ (@= (@Σ_ A P) u v)) ⊢
  @sigma_path_decode_encode A P u v p
  : τ (
      @sigma_path_decode A P u v (@sigma_path_encode A P u v p)
      = p);

assert [A : Grpd]
  [P : τ A → Grpd]
  [u v : @τΣ_ A P]
  (w : τ (@SigmaPathView A P u v)) ⊢
  @sigma_path_encode_decode A P u v w
  : τ (
      @sigma_path_encode A P u v (@sigma_path_decode A P u v w)
      = w);

assert [A : Grpd]
  [P : τ A → Grpd]
  (x : τ A)
  (a : τ (P x)) ⊢
  @sigma_path_encode_decode_refl A P (@Struct_sigma A P x a)
  ≡ @eq_refl
      (@SigmaPathView
        A P
        (@Struct_sigma A P x a)
        (@Struct_sigma A P x a))
      (@sigma_path_refl A P (@Struct_sigma A P x a));

assertnot [A : Grpd]
  [P : τ A → Grpd]
  (u : @τΣ_ A P) ⊢
  @sigma_path_encode A P u u
    (@sigma_path_decode A P u u (@sigma_path_refl A P u))
  ≡ @sigma_path_refl A P u;

assert [A : Grpd]
  [r s : τ (PathRecord_grpd A)]
  (p : τ (r = s)) ⊢
  @path_record_path_encode A r s p
  ≡ p;

assert [A : Grpd]
  [r s : τ (PathRecord_grpd A)]
  (w : τ (@PathRecordPathView A r s)) ⊢
  @path_record_path_decode A r s w
  ≡ w;

assert [A : Grpd]
  (r : τ (PathRecord_grpd A)) ⊢
  @path_record_path_encode
    A r r (@eq_refl (PathRecord_grpd A) r)
  ≡ @PathRecordPathRefl A r;

assert [A : Grpd]
  [r s : τ (PathRecord_grpd A)]
  (p : τ (r = s)) ⊢
  @path_record_path_decode_encode A r s p
  ≡ @eq_refl (@= (PathRecord_grpd A) r s) p;

assert [A : Grpd]
  [r s : τ (PathRecord_grpd A)]
  (w : τ (@PathRecordPathView A r s)) ⊢
  @path_record_path_tail
    A r s
    (@path_record_path_encode A r s
      (@path_record_path_decode A r s w))
  ≡ @path_record_path_tail A r s w;

assert [A : Grpd]
  [r s : τ (PathRecord_grpd (PathRecord_grpd A))]
  (w : τ (@PathRecordPathView (PathRecord_grpd A) r s)) ⊢
  @path_record_path_encode_decode (PathRecord_grpd A) r s w
  ≡ @eq_refl (@PathRecordPathView (PathRecord_grpd A) r s) w;
