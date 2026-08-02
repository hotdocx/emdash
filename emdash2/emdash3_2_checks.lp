/*
  m- / emdash3.2 diagnostic/assertion checks.

  The implementation lives in the active v3.2 source modules; this module
  owns executable diagnostic and regression `assert` commands. Assertions
  remain grouped by the architecture they exercise, while the generated
  reviewer-facing area map lives in reports/REPORT_EMDASH_CHECK_CATALOG.md.

  Do not use source line numbers as durable identifiers. Prefer a mathematical
  area comment, the checked head, and normalized/type-aware search.
*/

flag "eta_equality" on;
flag "print_implicits" on;
flag "print_contexts" on;
flag "print_domains" on;
flag "print_meta_args" on;
require open emdash.emdash3_2 emdash.emdash3_2_nat_arithmetic emdash.emdash3_2_finite_families emdash.emdash3_2_presheaves emdash.emdash3_2_sieves emdash.emdash3_2_sites emdash.emdash3_2_commutative_algebra emdash.emdash3_2_commutative_algebra_category emdash.emdash3_2_commutative_algebra_product emdash.emdash3_2_commutative_algebra_f2 emdash.emdash3_2_commutative_algebra_finite emdash.emdash3_2_commutative_algebra_polynomial emdash.emdash3_2_commutative_algebra_localization emdash.emdash3_2_commutative_algebra_localization_unit emdash.emdash3_2_commutative_algebra_localization_zero emdash.emdash3_2_commutative_algebra_localization_idempotent emdash.emdash3_2_commutative_algebra_localization_comparison emdash.emdash3_2_commutative_algebra_localization_overlap emdash.emdash3_2_commutative_algebra_presheaves emdash.emdash3_2_commutative_algebra_locality emdash.emdash3_2_commutative_algebra_matching emdash.emdash3_2_commutative_algebra_glue emdash.emdash3_2_commutative_algebra_affine_glue emdash.emdash3_2_commutative_algebra_zariski emdash.emdash3_2_commutative_algebra_zariski_topology emdash.emdash3_2_commutative_algebra_localization_split emdash.emdash3_2_commutative_algebra_affine_spec;
require open emdash.emdash3_2_walking_end_hit;
require open emdash.emdash3_2_eq1_evidence_property;
require open emdash.emdash3_2_eq1_hom_action;

// Elementary decoded H0 classifiers, constructors, and dependent eliminators.
assert ⊢ τ Empty_grpd ≡ empty;

assert ⊢ τ Unit_grpd ≡ unit;

assert ⊢ tt : τ Unit_grpd;

assert ⊢ τ Bool_grpd ≡ bool;

assert ⊢ false : τ Bool_grpd;

assert ⊢ true : τ Bool_grpd;

assert ⊢ nat : TYPE;

assert ⊢ Nat_grpd : Grpd;

assert ⊢ τ Nat_grpd ≡ nat;

assert ⊢ zero : τ Nat_grpd;

assert (n : nat) ⊢ succ n : τ Nat_grpd;

assert
  (P : τ Empty_grpd → Grpd)
  (x : τ Empty_grpd)
  ⊢ empty_elim P x : τ (P x);

assert
  (P : τ Bool_grpd → Grpd)
  (u_false : τ (P false))
  (u_true : τ (P true))
  ⊢ bool_elim P u_false u_true false ≡ u_false;

assert
  (P : τ Bool_grpd → Grpd)
  (u_false : τ (P false))
  (u_true : τ (P true))
  ⊢ bool_elim P u_false u_true true ≡ u_true;

assert
  (P : τ Nat_grpd → Grpd)
  (u_zero : τ (P zero))
  (u_succ : Π n : τ Nat_grpd, τ (P n) → τ (P (succ n)))
  ⊢ nat_elim P u_zero u_succ zero ≡ u_zero;

assert
  (P : τ Nat_grpd → Grpd)
  (u_zero : τ (P zero))
  (u_succ : Π n : τ Nat_grpd, τ (P n) → τ (P (succ n)))
  (n : τ Nat_grpd)
  ⊢ nat_elim P u_zero u_succ (succ n)
    ≡ u_succ n (nat_elim P u_zero u_succ n);

// catalog-area: Nat observational equality
// Visible zero/successor pairs expose Unit, Empty, or predecessor equality.
assert ⊢ @= Nat_grpd zero zero ≡ Unit_grpd;

assert (n : τ Nat_grpd) ⊢
  @= Nat_grpd zero (succ n)
  ≡ Empty_grpd;

assert (n : τ Nat_grpd) ⊢
  @= Nat_grpd (succ n) zero
  ≡ Empty_grpd;

assert (n m : τ Nat_grpd) ⊢
  @= Nat_grpd (succ n) (succ m)
  ≡ @= Nat_grpd n m;

assert (n m : τ Nat_grpd) ⊢
  @= Nat_grpd (succ (succ n)) (succ (succ m))
  ≡ @= Nat_grpd n m;

// Zero and successor reflexivity retain their generic proof heads even when
// the classifier reduces to Unit or predecessor equality.
assert ⊢ @eq_refl Nat_grpd zero : τ Unit_grpd;

assert (n : τ Nat_grpd) ⊢
  @eq_refl Nat_grpd (succ n)
  : τ (@= Nat_grpd n n);

assert ⊢ tt : τ (@= Nat_grpd zero zero);

assert (n : τ Nat_grpd) ⊢
  @eq_refl Nat_grpd n
  : τ (@= Nat_grpd (succ n) (succ n));

assertnot ⊢ @eq_refl Nat_grpd zero ≡ tt;

assertnot ⊢
  @eq_refl Unit_grpd (@eq_refl Nat_grpd zero)
  : τ (@= Unit_grpd (@eq_refl Nat_grpd zero) tt);

// Recursive classifier reduction does not install a proof-time equation
// between outer successor reflexivity and predecessor reflexivity.
assertnot (n : τ Nat_grpd) ⊢
  @eq_refl
    (@= Nat_grpd n n)
    (@eq_refl Nat_grpd (succ n))
  : τ (@=
      (@= Nat_grpd n n)
      (@eq_refl Nat_grpd (succ n))
      (@eq_refl Nat_grpd n));

// Generic J remains the literal-reflexivity owner at zero and successor.
assert
  (P : Π n : τ Nat_grpd, τ (@= Nat_grpd n zero) → Grpd)
  (u : τ (P zero (@eq_refl Nat_grpd zero))) ⊢
  @ind_eqr Nat_grpd zero P u zero (@eq_refl Nat_grpd zero)
  ≡ u;

assert (n : τ Nat_grpd)
  (P : Π m : τ Nat_grpd, τ (@= Nat_grpd m (succ n)) → Grpd)
  (u : τ (P (succ n) (@eq_refl Nat_grpd (succ n)))) ⊢
  @ind_eqr
    Nat_grpd (succ n) P u (succ n) (@eq_refl Nat_grpd (succ n))
  ≡ u;

assertnot ⊢
  @ind_eqr
    Nat_grpd zero
    (λ n : τ Nat_grpd,
      λ _ : τ (@= Nat_grpd n zero), Unit_grpd)
    tt zero tt
  ≡ tt;

// Predecessor reflexivity is a literal `eq_refl`, but its endpoint does not
// match the outer successor endpoint guarded by the generic J beta.
assertnot (n : τ Nat_grpd) ⊢
  @ind_eqr
    Nat_grpd (succ n)
    (λ m : τ Nat_grpd,
      λ _ : τ (@= Nat_grpd m (succ n)), Unit_grpd)
    tt (succ n) (@eq_refl Nat_grpd n)
  ≡ tt;

// Endpoint-guarded literal-reflexivity consumers compute at the outer zero/
// successor proofs, but do not identify predecessor reflexivity with the
// outer successor proof.
assert ⊢
  @path_sym Nat_grpd zero zero (@eq_refl Nat_grpd zero)
  ≡ @eq_refl Nat_grpd zero;

assert (n : τ Nat_grpd) ⊢
  @path_sym Nat_grpd
    (succ n) (succ n) (@eq_refl Nat_grpd (succ n))
  ≡ @eq_refl Nat_grpd (succ n);

assert ⊢
  @path_to_hom
    (Path_cat Nat_grpd) zero zero (@eq_refl Nat_grpd zero)
  ≡ @id (Path_cat Nat_grpd) zero;

assert (n : τ Nat_grpd) ⊢
  @path_to_hom
    (Path_cat Nat_grpd)
    (succ n) (succ n) (@eq_refl Nat_grpd (succ n))
  ≡ @id (Path_cat Nat_grpd) (succ n);

assertnot ⊢
  @path_sym Nat_grpd zero zero tt
  ≡ tt;

assertnot (n : τ Nat_grpd) ⊢
  (λ p : τ (@= Nat_grpd (succ n) (succ n)), p)
    (@path_sym Nat_grpd (succ n) (succ n) (@eq_refl Nat_grpd n))
  ≡
  (λ p : τ (@= Nat_grpd (succ n) (succ n)), p)
    (@eq_refl Nat_grpd n);

assert (m : τ Nat_grpd)
  (p : τ (@= Nat_grpd zero m)) ⊢
  @comp_fapp0
    (Path_cat Nat_grpd) zero zero m p (@eq_refl Nat_grpd zero)
  ≡ p;

assert (m : τ Nat_grpd)
  (p : τ (@= Nat_grpd m zero)) ⊢
  @comp_fapp0
    (Path_cat Nat_grpd) m zero zero (@eq_refl Nat_grpd zero) p
  ≡ p;

assert (n m : τ Nat_grpd)
  (p : τ (@= Nat_grpd (succ n) m)) ⊢
  @comp_fapp0
    (Path_cat Nat_grpd)
    (succ n) (succ n) m p (@eq_refl Nat_grpd (succ n))
  ≡ p;

assert (n m : τ Nat_grpd)
  (p : τ (@= Nat_grpd m (succ n))) ⊢
  @comp_fapp0
    (Path_cat Nat_grpd)
    m (succ n) (succ n) (@eq_refl Nat_grpd (succ n)) p
  ≡ p;

assert ⊢
  @idtoiso_cat
    (Path_cat Nat_grpd) zero zero (@eq_refl Nat_grpd zero)
  ≡ @iso_evidence_refl (Path_cat Nat_grpd) zero;

assert (n : τ Nat_grpd) ⊢
  @idtoiso_cat
    (Path_cat Nat_grpd)
    (succ n) (succ n) (@eq_refl Nat_grpd (succ n))
  ≡ @iso_evidence_refl (Path_cat Nat_grpd) (succ n);

assert ⊢
  @object_path_equiv
    (Path_cat Nat_grpd) zero zero (@eq_refl Nat_grpd zero)
  ≡ @omega_equiv_refl (Path_cat Nat_grpd) zero;

assert (n : τ Nat_grpd) ⊢
  @object_path_equiv
    (Path_cat Nat_grpd)
    (succ n) (succ n) (@eq_refl Nat_grpd (succ n))
  ≡ @omega_equiv_refl (Path_cat Nat_grpd) (succ n);

assertnot ⊢
  @object_path_equiv (Path_cat Nat_grpd) zero zero tt
  ≡ @omega_equiv_refl (Path_cat Nat_grpd) zero;

assertnot (n : τ Nat_grpd) ⊢
  @object_path_equiv
    (Path_cat Nat_grpd) (succ n) (succ n) (@eq_refl Nat_grpd n)
  ≡ @omega_equiv_refl (Path_cat Nat_grpd) (succ n);

// Open Nat endpoints retain primitive equality/reflexivity. These controls do
// not establish Nat canonicity, normalization, or metatheoretic no-confusion.
assertnot (n : τ Nat_grpd) ⊢
  @= Nat_grpd n n
  ≡ Unit_grpd;

assertnot (n : τ Nat_grpd) ⊢
  @eq_refl Nat_grpd n
  : τ Unit_grpd;

// catalog-area: Nat successor path induction

assert [n : τ Nat_grpd]
  (P : Π m : τ Nat_grpd,
    τ (@= Nat_grpd (succ m) (succ n)) → Grpd)
  (u : τ (P n (@eq_refl Nat_grpd n)))
  [m : τ Nat_grpd]
  (p : τ (@= Nat_grpd (succ m) (succ n))) ⊢
  @nat_succ_ind_eqr n P u m p
  : τ (P m p);

// The facade has exactly the generic predecessor-J body.
assert [n : τ Nat_grpd]
  (P : Π m : τ Nat_grpd,
    τ (@= Nat_grpd (succ m) (succ n)) → Grpd)
  (u : τ (P n (@eq_refl Nat_grpd n)))
  [m : τ Nat_grpd]
  (p : τ (@= Nat_grpd (succ m) (succ n))) ⊢
  @nat_succ_ind_eqr n P u m p
  ≡ @ind_eqr
      Nat_grpd
      n
      (λ k : τ Nat_grpd, λ q : τ (@= Nat_grpd k n), P k q)
      u
      m
      p;

// Component reflexivity exposes the existing generic J beta.
assert [n : τ Nat_grpd]
  (P : Π m : τ Nat_grpd,
    τ (@= Nat_grpd (succ m) (succ n)) → Grpd)
  (u : τ (P n (@eq_refl Nat_grpd n))) ⊢
  @nat_succ_ind_eqr
    n P u n (@eq_refl Nat_grpd n)
  ≡ u;

// Arbitrary exposed successor paths are accepted without being collapsed.
assert [m n : τ Nat_grpd]
  (p : τ (@= Nat_grpd m n)) ⊢
  @nat_succ_ind_eqr
    n
    (λ k : τ Nat_grpd,
      λ _ : τ (@= Nat_grpd (succ k) (succ n)), Unit_grpd)
    tt
    m
    p
  : τ Unit_grpd;

// Reindexing the facade at `succ n` gives the next recursive beta.
assert (n : τ Nat_grpd) ⊢
  @nat_succ_ind_eqr
    (succ n)
    (λ k : τ Nat_grpd,
      λ _ : τ (@= Nat_grpd (succ k) (succ (succ n))), Unit_grpd)
    tt
    (succ n)
    (@eq_refl Nat_grpd (succ n))
  ≡ tt;

// Outer successor reflexivity does not acquire a new beta.
assertnot (n : τ Nat_grpd) ⊢
  @nat_succ_ind_eqr
    n
    (λ k : τ Nat_grpd,
      λ _ : τ (@= Nat_grpd (succ k) (succ n)), Unit_grpd)
    tt
    n
    (@eq_refl Nat_grpd (succ n))
  ≡ tt;

// The guarded generic J owner still rejects component reflexivity at outer endpoints.
assertnot (n : τ Nat_grpd) ⊢
  @ind_eqr
    Nat_grpd
    (succ n)
    (λ k : τ Nat_grpd,
      λ _ : τ (@= Nat_grpd k (succ n)), Unit_grpd)
    tt
    (succ n)
    (@eq_refl Nat_grpd n)
  ≡ tt;

// No proof-irrelevant open-path collapse is introduced by the facade.
assertnot [m n : τ Nat_grpd]
  (p : τ (@= Nat_grpd m n)) ⊢
  @nat_succ_ind_eqr
    n
    (λ k : τ Nat_grpd,
      λ _ : τ (@= Nat_grpd (succ k) (succ n)), Unit_grpd)
    tt
    m
    p
  ≡ tt;

// catalog-area: auto

// catalog-area: Equality J subject-reduction guards
// Sharing a reduced classifier does not authorize foreign reflexivity to
// trigger J. The category and endpoint are runtime discriminators.
assertnot ⊢
  @ind_eqr
    Unit_grpd tt
    (λ u : τ Unit_grpd,
      λ _ : τ (@= Unit_grpd u tt), Unit_grpd)
    tt tt (@eq_refl Bool_grpd false)
  ≡ tt;

assertnot ⊢
  @ind_eqr
    Bool_grpd false
    (λ b : τ Bool_grpd,
      λ _ : τ (@= Bool_grpd b false), Unit_grpd)
    tt false (@eq_refl Unit_grpd tt)
  ≡ tt;

assertnot ⊢
  @ind_eqr
    Bool_grpd true
    (λ b : τ Bool_grpd,
      λ _ : τ (@= Bool_grpd b true), Unit_grpd)
    tt true (@eq_refl Bool_grpd false)
  ≡ tt;

assertnot ⊢
  @ind_eqr
    Nat_grpd zero
    (λ n : τ Nat_grpd,
      λ _ : τ (@= Nat_grpd n zero), Unit_grpd)
    tt zero (@eq_refl Unit_grpd tt)
  ≡ tt;

// catalog-area: auto

// catalog-area: Unit observational equality
// The single visible constructor pair exposes the Unit classifier.
assert ⊢ @= Unit_grpd tt tt ≡ Unit_grpd;

// Generic reflexivity and native `tt` inhabit the reduced classifier but
// remain distinct runtime and proof-time presentations.
assert ⊢ @eq_refl Unit_grpd tt : τ Unit_grpd;

assert ⊢ tt : τ (@= Unit_grpd tt tt);

assertnot ⊢ @eq_refl Unit_grpd tt ≡ tt;

assertnot ⊢
  @eq_refl Unit_grpd (@eq_refl Unit_grpd tt)
  : τ (@= Unit_grpd (@eq_refl Unit_grpd tt) tt);

// Generic J remains the sole literal-reflexivity beta.
assert
  (P : Π u : τ Unit_grpd, τ (@= Unit_grpd u tt) → Grpd)
  (v : τ (P tt (@eq_refl Unit_grpd tt))) ⊢
  @ind_eqr Unit_grpd tt P v tt (@eq_refl Unit_grpd tt)
  ≡ v;

assertnot ⊢
  @ind_eqr
    Unit_grpd tt
    (λ u : τ Unit_grpd,
      λ _ : τ (@= Unit_grpd u tt), Unit_grpd)
    tt tt tt
  ≡ tt;

// Existing generic literal-reflexivity consumers keep computing.
assert ⊢
  @path_sym Unit_grpd tt tt (@eq_refl Unit_grpd tt)
  ≡ @eq_refl Unit_grpd tt;

assert ⊢
  @path_to_hom
    (Path_cat Unit_grpd) tt tt (@eq_refl Unit_grpd tt)
  ≡ @id (Path_cat Unit_grpd) tt;

assertnot ⊢ @path_sym Unit_grpd tt tt tt ≡ tt;

assertnot ⊢
  @path_to_hom (Path_cat Unit_grpd) tt tt tt
  ≡ @id (Path_cat Unit_grpd) tt;

assert (u : τ Unit_grpd)
  (p : τ (@= Unit_grpd tt u)) ⊢
  @comp_fapp0
    (Path_cat Unit_grpd) tt tt u p (@eq_refl Unit_grpd tt)
  ≡ p;

assert (u : τ Unit_grpd)
  (p : τ (@= Unit_grpd u tt)) ⊢
  @comp_fapp0
    (Path_cat Unit_grpd) u tt tt (@eq_refl Unit_grpd tt) p
  ≡ p;

assert ⊢
  @idtoiso_cat
    (Path_cat Unit_grpd) tt tt (@eq_refl Unit_grpd tt)
  ≡ @iso_evidence_refl (Path_cat Unit_grpd) tt;

assert ⊢
  @object_path_equiv
    (Path_cat Unit_grpd) tt tt (@eq_refl Unit_grpd tt)
  ≡ @omega_equiv_refl (Path_cat Unit_grpd) tt;

assertnot ⊢
  @idtoiso_cat (Path_cat Unit_grpd) tt tt tt
  ≡ @iso_evidence_refl (Path_cat Unit_grpd) tt;

assertnot ⊢
  @object_path_equiv (Path_cat Unit_grpd) tt tt tt
  ≡ @omega_equiv_refl (Path_cat Unit_grpd) tt;

// Open Unit values retain primitive equality and reflexivity typing. These
// are local conversion controls, not Unit canonicity or non-derivability.
assertnot (u : τ Unit_grpd) ⊢
  @= Unit_grpd u u
  ≡ Unit_grpd;

assertnot (u : τ Unit_grpd) ⊢
  @eq_refl Unit_grpd u
  : τ Unit_grpd;

// catalog-area: auto

// Local constructor anti-collapse control only; this is not a Boolean
// canonicity, normalization, or observational no-confusion theorem.
assertnot ⊢ false ≡ true;

// catalog-area: Boolean observational equality
// Visible Boolean constructor pairs expose the Unit/Empty path matrix.
assert ⊢ @= Bool_grpd false false ≡ Unit_grpd;

assert ⊢ @= Bool_grpd false true ≡ Empty_grpd;

assert ⊢ @= Bool_grpd true false ≡ Empty_grpd;

assert ⊢ @= Bool_grpd true true ≡ Unit_grpd;

// Classifier reduction types both generic reflexivity and the native unit
// constructor, but generic `eq_refl` retains its runtime provenance.
assert ⊢ @eq_refl Bool_grpd false : τ Unit_grpd;

assert ⊢ @eq_refl Bool_grpd true : τ Unit_grpd;

assert ⊢ tt : τ (@= Bool_grpd false false);

assert ⊢ tt : τ (@= Bool_grpd true true);

assertnot ⊢ @eq_refl Bool_grpd false ≡ tt;

assertnot ⊢ @eq_refl Bool_grpd true ≡ tt;

// No proof-time equation identifies the two proof presentations either. The
// negative typed-reflexivity probe is a local trust-boundary control.
assertnot ⊢
  @eq_refl Unit_grpd (@eq_refl Bool_grpd false)
  : τ (@= Unit_grpd (@eq_refl Bool_grpd false) tt);

// Generic J continues to own literal reflexivity without a Boolean-specific
// consumer registration.
assert
  (P : Π b : τ Bool_grpd, τ (@= Bool_grpd b false) → Grpd)
  (u : τ (P false (@eq_refl Bool_grpd false))) ⊢
  @ind_eqr
    Bool_grpd false P u false (@eq_refl Bool_grpd false)
  ≡ u;

assert
  (P : Π b : τ Bool_grpd, τ (@= Bool_grpd b true) → Grpd)
  (u : τ (P true (@eq_refl Bool_grpd true))) ⊢
  @ind_eqr
    Bool_grpd true P u true (@eq_refl Bool_grpd true)
  ≡ u;

// A raw `tt` proof is deliberately not promoted to a second J beta. This is
// a local runtime boundary, not a Boolean canonicity or non-derivability claim.
assertnot ⊢
  @ind_eqr
    Bool_grpd false
    (λ b : τ Bool_grpd,
      λ _ : τ (@= Bool_grpd b false), Unit_grpd)
    tt false tt
  ≡ tt;

assertnot ⊢
  @ind_eqr
    Bool_grpd true
    (λ b : τ Bool_grpd,
      λ _ : τ (@= Bool_grpd b true), Unit_grpd)
    tt true tt
  ≡ tt;

// The existing generic literal-reflexivity consumers keep computing.
assert ⊢
  @path_sym Bool_grpd false false (@eq_refl Bool_grpd false)
  ≡ @eq_refl Bool_grpd false;

assert ⊢
  @path_sym Bool_grpd true true (@eq_refl Bool_grpd true)
  ≡ @eq_refl Bool_grpd true;

assert ⊢
  @path_to_hom
    (Path_cat Bool_grpd)
    false false (@eq_refl Bool_grpd false)
  ≡ @id (Path_cat Bool_grpd) false;

assert ⊢
  @path_to_hom
    (Path_cat Bool_grpd)
    true true (@eq_refl Bool_grpd true)
  ≡ @id (Path_cat Bool_grpd) true;

// Raw `tt` paths are not silently registered with the generic consumers.
assertnot ⊢
  @path_sym Bool_grpd false false tt
  ≡ tt;

assertnot ⊢
  @path_to_hom (Path_cat Bool_grpd) false false tt
  ≡ @id (Path_cat Bool_grpd) false;

// Both shared path-category units retain their generic owner at each visible
// constructor.
assert (b : τ Bool_grpd)
  (p : τ (@= Bool_grpd false b)) ⊢
  @comp_fapp0
    (Path_cat Bool_grpd) false false b p (@eq_refl Bool_grpd false)
  ≡ p;

assert (b : τ Bool_grpd)
  (p : τ (@= Bool_grpd b false)) ⊢
  @comp_fapp0
    (Path_cat Bool_grpd) b false false (@eq_refl Bool_grpd false) p
  ≡ p;

assert (b : τ Bool_grpd)
  (p : τ (@= Bool_grpd true b)) ⊢
  @comp_fapp0
    (Path_cat Bool_grpd) true true b p (@eq_refl Bool_grpd true)
  ≡ p;

assert (b : τ Bool_grpd)
  (p : τ (@= Bool_grpd b true)) ⊢
  @comp_fapp0
    (Path_cat Bool_grpd) b true true (@eq_refl Bool_grpd true) p
  ≡ p;

// The ordinary-isomorphism and native equality-valued encoders retain reflexivity beta.
assert ⊢
  @idtoiso_cat
    (Path_cat Bool_grpd) false false (@eq_refl Bool_grpd false)
  ≡ @iso_evidence_refl (Path_cat Bool_grpd) false;

assert ⊢
  @idtoiso_cat
    (Path_cat Bool_grpd) true true (@eq_refl Bool_grpd true)
  ≡ @iso_evidence_refl (Path_cat Bool_grpd) true;

assert ⊢
  @object_path_equiv
    (Path_cat Bool_grpd) false false (@eq_refl Bool_grpd false)
  ≡ @omega_equiv_refl (Path_cat Bool_grpd) false;

assert ⊢
  @object_path_equiv
    (Path_cat Bool_grpd) true true (@eq_refl Bool_grpd true)
  ≡ @omega_equiv_refl (Path_cat Bool_grpd) true;

assertnot ⊢
  @idtoiso_cat (Path_cat Bool_grpd) false false tt
  ≡ @iso_evidence_refl (Path_cat Bool_grpd) false;

assertnot ⊢
  @object_path_equiv (Path_cat Bool_grpd) false false tt
  ≡ @omega_equiv_refl (Path_cat Bool_grpd) false;

// Open Boolean values retain the generic classifier and reflexivity typing.
assertnot (b : τ Bool_grpd) ⊢
  @= Bool_grpd b b
  ≡ Unit_grpd;

assertnot (b : τ Bool_grpd) ⊢
  @eq_refl Bool_grpd b
  : τ Unit_grpd;

// catalog-area: auto

// Named finite dependent record: decoding, projections, and generated-J beta.
assert [A : Grpd] ⊢
  τ (PathRecord_grpd A)
  ≡ PathRecordData A;

assert [A : Grpd]
  (src dst : τ A)
  (witness : τ (src = dst)) ⊢
  @Struct_path_record A src dst witness
  : τ (PathRecord_grpd A);

assert [A : Grpd]
  (src dst : τ A)
  (witness : τ (src = dst)) ⊢
  path_record_src (@Struct_path_record A src dst witness)
  ≡ src;

assert [A : Grpd]
  (src dst : τ A)
  (witness : τ (src = dst)) ⊢
  path_record_dst (@Struct_path_record A src dst witness)
  ≡ dst;

assert [A : Grpd]
  (src dst : τ A)
  (witness : τ (src = dst)) ⊢
  path_record_witness (@Struct_path_record A src dst witness)
  ≡ witness;

assert [A : Grpd]
  (r : τ (PathRecord_grpd A)) ⊢
  path_record_witness r
  : τ (path_record_src r = path_record_dst r);

assert [A : Grpd]
  (Q : τ (PathRecord_grpd A) → Grpd)
  (c : Π (src dst : τ A),
       Π witness : τ (src = dst),
       τ (Q (@Struct_path_record A src dst witness)))
  (r : τ (PathRecord_grpd A)) ⊢
  path_record_ind Q c r
  : τ (Q r);

assert [A : Grpd]
  (Q : τ (PathRecord_grpd A) → Grpd)
  (c : Π (src dst : τ A),
       Π witness : τ (src = dst),
       τ (Q (@Struct_path_record A src dst witness)))
  (src dst : τ A)
  (witness : τ (src = dst)) ⊢
  path_record_ind Q c (@Struct_path_record A src dst witness)
  ≡ c src dst witness;

// No runtime record eta is selected for the convention.
assertnot [A : Grpd]
  (r : τ (PathRecord_grpd A)) ⊢
  r
  ≡ @Struct_path_record A
      (path_record_src r)
      (path_record_dst r)
      (path_record_witness r);

/*
  Candidate C: shaped reflexivity and reflexive J for the genuinely dependent
  PathRecord former. The record is viewed as a source plus a nested-Sigma tail.
*/
assert [A : Grpd]
  (r s : τ (PathRecord_grpd A)) ⊢
  @= (PathRecord_grpd A) r s
  ≡ @PathRecordPathView A r s;

assert [A : Grpd]
  (r : τ (PathRecord_grpd A)) ⊢
  @PathRecordPathRefl A r
  : τ (@PathRecordPathView A r r);

assert [A : Grpd]
  (r : τ (PathRecord_grpd A)) ⊢
  @eq_refl (PathRecord_grpd A) r
  ≡ @PathRecordPathRefl A r;

assert [A : Grpd]
  (r : τ (PathRecord_grpd A)) ⊢
  @path_record_path_src A r r
    (@eq_refl (PathRecord_grpd A) r)
  ≡ @eq_refl A (path_record_src r);

assert [A : Grpd]
  (r : τ (PathRecord_grpd A)) ⊢
  @path_record_path_tail A r r
    (@eq_refl (PathRecord_grpd A) r)
  ≡ @pathover_refl
      A
      (λ src : τ A, PathRecordTail_grpd src)
      (path_record_src r)
      (path_record_tail r);

// Generic-J-first and shaped-reflexivity-first orders join.
assert [A : Grpd]
  (r : τ (PathRecord_grpd A))
  (Q : Π s : τ (PathRecord_grpd A),
       τ (s = r) → Grpd)
  (u : τ (Q r (@eq_refl (PathRecord_grpd A) r))) ⊢
  @ind_eqr
    (PathRecord_grpd A)
    r
    Q
    u
    r
    (@eq_refl (PathRecord_grpd A) r)
  ≡ u;

// Shared category units register both literal and already-shaped spellings.
assert [A : Grpd]
  (r s : τ (PathRecord_grpd A))
  (p : τ (r = s)) ⊢
  @comp_fapp0
    (Path_cat (PathRecord_grpd A))
    r r s p (@eq_refl (PathRecord_grpd A) r)
  ≡ p;

assert [A : Grpd]
  (r s : τ (PathRecord_grpd A))
  (p : τ (r = s)) ⊢
  @comp_fapp0
    (Path_cat (PathRecord_grpd A))
    r r s p (@PathRecordPathRefl A r)
  ≡ p;

assert [A : Grpd]
  (r s : τ (PathRecord_grpd A))
  (p : τ (r = s)) ⊢
  @comp_fapp0
    (Path_cat (PathRecord_grpd A))
    r s s (@eq_refl (PathRecord_grpd A) s) p
  ≡ p;

assert [A : Grpd]
  (r s : τ (PathRecord_grpd A))
  (p : τ (r = s)) ⊢
  @comp_fapp0
    (Path_cat (PathRecord_grpd A))
    r s s (@PathRecordPathRefl A s) p
  ≡ p;

// PathSym registers literal and already-shaped record reflexivity.
assert [A : Grpd]
  (r : τ (PathRecord_grpd A)) ⊢
  @path_sym
    (PathRecord_grpd A)
    r r
    (@eq_refl (PathRecord_grpd A) r)
  ≡ @PathRecordPathRefl A r;

assert [A : Grpd]
  (r : τ (PathRecord_grpd A)) ⊢
  @fapp1_fapp0
    (Op_cat (Path_cat (PathRecord_grpd A)))
    (Path_cat (PathRecord_grpd A))
    (Path_sym_func (PathRecord_grpd A))
    r r
    (@PathRecordPathRefl A r)
  ≡ @PathRecordPathRefl A r;

// Core inclusion registers both projection orders at a concrete category
// whose object classifier is PathRecord_grpd(A).
assert [A : Grpd]
  (r : τ (PathRecord_grpd A)) ⊢
  @path_to_hom
    (Path_cat (PathRecord_grpd A))
    r r
    (@eq_refl (PathRecord_grpd A) r)
  ≡ @PathRecordPathRefl A r;

assert [A : Grpd]
  (r : τ (PathRecord_grpd A)) ⊢
  @path_to_hom
    (Path_cat (PathRecord_grpd A))
    r r
    (@PathRecordPathRefl A r)
  ≡ @PathRecordPathRefl A r;

// The ordinary-isomorphism and native equality-valued encoders register the shaped head.
assert [A : Grpd]
  (r : τ (PathRecord_grpd A)) ⊢
  @idtoiso_cat
    (Path_cat (PathRecord_grpd A))
    r r
    (@eq_refl (PathRecord_grpd A) r)
  ≡ @iso_evidence_refl (Path_cat (PathRecord_grpd A)) r;

assert [A : Grpd]
  (r : τ (PathRecord_grpd A)) ⊢
  @idtoiso_cat
    (Path_cat (PathRecord_grpd A))
    r r
    (@PathRecordPathRefl A r)
  ≡ @iso_evidence_refl (Path_cat (PathRecord_grpd A)) r;

assert [A : Grpd]
  (r : τ (PathRecord_grpd A)) ⊢
  @object_path_equiv
    (Path_cat (PathRecord_grpd A))
    r r
    (@eq_refl (PathRecord_grpd A) r)
  ≡ @omega_equiv_refl (Path_cat (PathRecord_grpd A)) r;

assert [A : Grpd]
  (r : τ (PathRecord_grpd A)) ⊢
  @object_path_equiv
    (Path_cat (PathRecord_grpd A))
    r r
    (@PathRecordPathRefl A r)
  ≡ @omega_equiv_refl (Path_cat (PathRecord_grpd A)) r;

/*
  Candidate C warning classification: post/precomposition unit diamonds.

  Each owner is checked with its shaped action still visible and with that
  action already projected to PathRecordPathRefl. These are the two reduction
  orders reported against the generic hom-action calculus.
*/
assert [A : Grpd]
  (w x y : τ (PathRecord_grpd A))
  (p : τ (x = y))
  (g : τ (w = y)) ⊢
  @comp_fapp0 (Path_cat (PathRecord_grpd A)) w x x
    (@fapp1_fapp0
      (Op_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      (Path_sym_func (PathRecord_grpd A))
      x x (@PathRecordPathRefl A x))
    (@hom_postcomp_fapp0
      (Path_cat (PathRecord_grpd A))
      (Op_cat (Path_cat (PathRecord_grpd A)))
      (Path_sym_func (PathRecord_grpd A))
      w y x p g)
  ≡ @hom_postcomp_fapp0
      (Path_cat (PathRecord_grpd A))
      (Op_cat (Path_cat (PathRecord_grpd A)))
      (Path_sym_func (PathRecord_grpd A))
      w y x p g;

assert [A : Grpd]
  (w x y : τ (PathRecord_grpd A))
  (p : τ (x = y))
  (g : τ (w = y)) ⊢
  @comp_fapp0 (Path_cat (PathRecord_grpd A)) w x x
    (@PathRecordPathRefl A x)
    (@hom_postcomp_fapp0
      (Path_cat (PathRecord_grpd A))
      (Op_cat (Path_cat (PathRecord_grpd A)))
      (Path_sym_func (PathRecord_grpd A))
      w y x p g)
  ≡ @hom_postcomp_fapp0
      (Path_cat (PathRecord_grpd A))
      (Op_cat (Path_cat (PathRecord_grpd A)))
      (Path_sym_func (PathRecord_grpd A))
      w y x p g;

assert [A : Grpd]
  (x y z : τ (PathRecord_grpd A))
  (p : τ (x = y))
  (q : τ (x = z)) ⊢
  @comp_fapp0 (Path_cat (PathRecord_grpd A)) y y z
    (@hom_precomp_along_fapp0
      (Op_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      (Path_sym_func (PathRecord_grpd A))
      z y x p q)
    (@fapp1_fapp0
      (Op_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      (Path_sym_func (PathRecord_grpd A))
      y y (@PathRecordPathRefl A y))
  ≡ @hom_precomp_along_fapp0
      (Op_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      (Path_sym_func (PathRecord_grpd A))
      z y x p q;

assert [A : Grpd]
  (x y z : τ (PathRecord_grpd A))
  (p : τ (x = y))
  (q : τ (x = z)) ⊢
  @comp_fapp0 (Path_cat (PathRecord_grpd A)) y y z
    (@hom_precomp_along_fapp0
      (Op_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      (Path_sym_func (PathRecord_grpd A))
      z y x p q)
    (@PathRecordPathRefl A y)
  ≡ @hom_precomp_along_fapp0
      (Op_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      (Path_sym_func (PathRecord_grpd A))
      z y x p q;

assert [A : Grpd]
  (w x y : τ (PathRecord_grpd A))
  (p : τ (x = y))
  (g : τ (w = x)) ⊢
  @comp_fapp0 (Path_cat (PathRecord_grpd A)) w y y
    (@fapp1_fapp0
      (Core_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      (Core_incl_func (Path_cat (PathRecord_grpd A)))
      y y (@PathRecordPathRefl A y))
    (@hom_postcomp_fapp0
      (Path_cat (PathRecord_grpd A))
      (Core_cat (Path_cat (PathRecord_grpd A)))
      (Core_incl_func (Path_cat (PathRecord_grpd A)))
      w x y p g)
  ≡ @hom_postcomp_fapp0
      (Path_cat (PathRecord_grpd A))
      (Core_cat (Path_cat (PathRecord_grpd A)))
      (Core_incl_func (Path_cat (PathRecord_grpd A)))
      w x y p g;

assert [A : Grpd]
  (w x y : τ (PathRecord_grpd A))
  (p : τ (x = y))
  (g : τ (w = x)) ⊢
  @comp_fapp0 (Path_cat (PathRecord_grpd A)) w y y
    (@PathRecordPathRefl A y)
    (@hom_postcomp_fapp0
      (Path_cat (PathRecord_grpd A))
      (Core_cat (Path_cat (PathRecord_grpd A)))
      (Core_incl_func (Path_cat (PathRecord_grpd A)))
      w x y p g)
  ≡ @hom_postcomp_fapp0
      (Path_cat (PathRecord_grpd A))
      (Core_cat (Path_cat (PathRecord_grpd A)))
      (Core_incl_func (Path_cat (PathRecord_grpd A)))
      w x y p g;

assert [A : Grpd]
  (x y z : τ (PathRecord_grpd A))
  (p : τ (x = y))
  (g : τ (y = z)) ⊢
  @comp_fapp0 (Path_cat (PathRecord_grpd A)) x x z
    (@hom_precomp_along_fapp0
      (Core_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      (Core_incl_func (Path_cat (PathRecord_grpd A)))
      z x y p g)
    (@fapp1_fapp0
      (Core_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      (Core_incl_func (Path_cat (PathRecord_grpd A)))
      x x (@PathRecordPathRefl A x))
  ≡ @hom_precomp_along_fapp0
      (Core_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      (Core_incl_func (Path_cat (PathRecord_grpd A)))
      z x y p g;

assert [A : Grpd]
  (x y z : τ (PathRecord_grpd A))
  (p : τ (x = y))
  (g : τ (y = z)) ⊢
  @comp_fapp0 (Path_cat (PathRecord_grpd A)) x x z
    (@hom_precomp_along_fapp0
      (Core_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      (Core_incl_func (Path_cat (PathRecord_grpd A)))
      z x y p g)
    (@PathRecordPathRefl A x)
  ≡ @hom_precomp_along_fapp0
      (Core_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      (Core_incl_func (Path_cat (PathRecord_grpd A)))
      z x y p g;

/*
  The four naturality overlap families have the same unit-diamond shape.
  Again, each pair retains the action head and then exposes its shaped result.
*/
assert [A : Grpd]
  (F : τ (Functor
      (Op_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))))
  (x y : τ (PathRecord_grpd A))
  (p : τ (y = x))
  (eta : τ (Transf F (Path_sym_func (PathRecord_grpd A)))) ⊢
  @comp_fapp0 (Path_cat (PathRecord_grpd A))
    (@fapp0
      (Op_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A)) F x)
    y y
    (@fapp1_fapp0
      (Op_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      (Path_sym_func (PathRecord_grpd A))
      y y (@PathRecordPathRefl A y))
    (@tapp1_fapp0
      (Op_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      F (Path_sym_func (PathRecord_grpd A)) x y eta p)
  ≡ @tapp1_fapp0
      (Op_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      F (Path_sym_func (PathRecord_grpd A)) x y eta p;

assert [A : Grpd]
  (F : τ (Functor
      (Op_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))))
  (x y : τ (PathRecord_grpd A))
  (p : τ (y = x))
  (eta : τ (Transf F (Path_sym_func (PathRecord_grpd A)))) ⊢
  @comp_fapp0 (Path_cat (PathRecord_grpd A))
    (@fapp0
      (Op_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A)) F x)
    y y
    (@PathRecordPathRefl A y)
    (@tapp1_fapp0
      (Op_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      F (Path_sym_func (PathRecord_grpd A)) x y eta p)
  ≡ @tapp1_fapp0
      (Op_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      F (Path_sym_func (PathRecord_grpd A)) x y eta p;

assert [A : Grpd]
  (G : τ (Functor
      (Op_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))))
  (x y : τ (PathRecord_grpd A))
  (p : τ (y = x))
  (eta : τ (Transf (Path_sym_func (PathRecord_grpd A)) G)) ⊢
  @comp_fapp0 (Path_cat (PathRecord_grpd A))
    x x
    (@fapp0
      (Op_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A)) G y)
    (@tapp1_fapp0
      (Op_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      (Path_sym_func (PathRecord_grpd A)) G x y eta p)
    (@fapp1_fapp0
      (Op_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      (Path_sym_func (PathRecord_grpd A))
      x x (@PathRecordPathRefl A x))
  ≡ @tapp1_fapp0
      (Op_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      (Path_sym_func (PathRecord_grpd A)) G x y eta p;

assert [A : Grpd]
  (G : τ (Functor
      (Op_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))))
  (x y : τ (PathRecord_grpd A))
  (p : τ (y = x))
  (eta : τ (Transf (Path_sym_func (PathRecord_grpd A)) G)) ⊢
  @comp_fapp0 (Path_cat (PathRecord_grpd A))
    x x
    (@fapp0
      (Op_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A)) G y)
    (@tapp1_fapp0
      (Op_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      (Path_sym_func (PathRecord_grpd A)) G x y eta p)
    (@PathRecordPathRefl A x)
  ≡ @tapp1_fapp0
      (Op_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      (Path_sym_func (PathRecord_grpd A)) G x y eta p;

assert [A : Grpd]
  (F : τ (Functor
      (Core_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))))
  (x y : τ (PathRecord_grpd A))
  (p : τ (x = y))
  (eta : τ (Transf F (Core_incl_func (Path_cat (PathRecord_grpd A))))) ⊢
  @comp_fapp0 (Path_cat (PathRecord_grpd A))
    (@fapp0
      (Core_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A)) F x)
    y y
    (@fapp1_fapp0
      (Core_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      (Core_incl_func (Path_cat (PathRecord_grpd A)))
      y y (@PathRecordPathRefl A y))
    (@tapp1_fapp0
      (Core_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      F (Core_incl_func (Path_cat (PathRecord_grpd A))) x y eta p)
  ≡ @tapp1_fapp0
      (Core_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      F (Core_incl_func (Path_cat (PathRecord_grpd A))) x y eta p;

assert [A : Grpd]
  (F : τ (Functor
      (Core_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))))
  (x y : τ (PathRecord_grpd A))
  (p : τ (x = y))
  (eta : τ (Transf F (Core_incl_func (Path_cat (PathRecord_grpd A))))) ⊢
  @comp_fapp0 (Path_cat (PathRecord_grpd A))
    (@fapp0
      (Core_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A)) F x)
    y y
    (@PathRecordPathRefl A y)
    (@tapp1_fapp0
      (Core_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      F (Core_incl_func (Path_cat (PathRecord_grpd A))) x y eta p)
  ≡ @tapp1_fapp0
      (Core_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      F (Core_incl_func (Path_cat (PathRecord_grpd A))) x y eta p;

assert [A : Grpd]
  (G : τ (Functor
      (Core_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))))
  (x y : τ (PathRecord_grpd A))
  (p : τ (x = y))
  (eta : τ (Transf (Core_incl_func (Path_cat (PathRecord_grpd A))) G)) ⊢
  @comp_fapp0 (Path_cat (PathRecord_grpd A))
    x x
    (@fapp0
      (Core_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A)) G y)
    (@tapp1_fapp0
      (Core_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      (Core_incl_func (Path_cat (PathRecord_grpd A))) G x y eta p)
    (@fapp1_fapp0
      (Core_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      (Core_incl_func (Path_cat (PathRecord_grpd A)))
      x x (@PathRecordPathRefl A x))
  ≡ @tapp1_fapp0
      (Core_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      (Core_incl_func (Path_cat (PathRecord_grpd A))) G x y eta p;

assert [A : Grpd]
  (G : τ (Functor
      (Core_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))))
  (x y : τ (PathRecord_grpd A))
  (p : τ (x = y))
  (eta : τ (Transf (Core_incl_func (Path_cat (PathRecord_grpd A))) G)) ⊢
  @comp_fapp0 (Path_cat (PathRecord_grpd A))
    x x
    (@fapp0
      (Core_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A)) G y)
    (@tapp1_fapp0
      (Core_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      (Core_incl_func (Path_cat (PathRecord_grpd A))) G x y eta p)
    (@PathRecordPathRefl A x)
  ≡ @tapp1_fapp0
      (Core_cat (Path_cat (PathRecord_grpd A)))
      (Path_cat (PathRecord_grpd A))
      (Core_incl_func (Path_cat (PathRecord_grpd A))) G x y eta p;

// Both displayed-target overlap reports contain the same ill-typed Core
// action: an ordinary PathRecord value cannot be an object of Catd_cat(K).
assertnot [A : Grpd] [K : Cat]
  (r : τ (PathRecord_grpd A)) ⊢
  @fapp1_fapp0
    (Core_cat (Catd_cat K))
    (Catd_cat K)
    (Core_incl_func (Catd_cat K))
    r r (@PathRecordPathRefl A r)
  : τ Unit_grpd;

// Nested former: the outer source reflexivity exposes the inner shaped head.
assert [A : Grpd]
  (r : τ (PathRecord_grpd (PathRecord_grpd A))) ⊢
  @path_record_path_src (PathRecord_grpd A) r r
    (@eq_refl (PathRecord_grpd (PathRecord_grpd A)) r)
  ≡ @PathRecordPathRefl A (path_record_src r);

assert [A : Grpd]
  (r : τ (PathRecord_grpd (PathRecord_grpd A)))
  (P : τ (PathRecord_grpd (PathRecord_grpd A)) → Grpd)
  (u : τ (P r)) ⊢
  @ind_eq
    (PathRecord_grpd (PathRecord_grpd A))
    r r
    (@eq_refl (PathRecord_grpd (PathRecord_grpd A)) r)
    P u
  ≡ u;

// The stable head is intentionally not the raw nested-Sigma constructor.
assertnot [A : Grpd]
  (r : τ (PathRecord_grpd A)) ⊢
  @eq_refl (PathRecord_grpd A) r
  ≡ @sigma_path_refl
      A
      (λ src : τ A, PathRecordTail_grpd src)
      (path_record_as_sigma r);

// No arbitrary structured-constructor J beta or symmetry action is claimed.
assertnot [A : Grpd]
  (r : τ (PathRecord_grpd A))
  (P : τ (PathRecord_grpd A) → Grpd)
  (u : τ (P r)) ⊢
  @ind_eq
    (PathRecord_grpd A)
    r r
    (@sigma_path_refl
      A
      (λ src : τ A, PathRecordTail_grpd src)
      (path_record_as_sigma r))
    P u
  ≡ u;

assertnot [A : Grpd]
  (r : τ (PathRecord_grpd A)) ⊢
  @path_sym
    (PathRecord_grpd A)
    r r
    (@sigma_path_refl
      A
      (λ src : τ A, PathRecordTail_grpd src)
      (path_record_as_sigma r))
  ≡ @sigma_path_refl
      A
      (λ src : τ A, PathRecordTail_grpd src)
      (path_record_as_sigma r);

// Homotopy truncation levels and recursive property computation.
assert ⊢ TruncLevel : TYPE;

assert ⊢ trunc_minus_two : TruncLevel;

assert (n : TruncLevel) ⊢ trunc_succ n : TruncLevel;

assert ⊢
  trunc_minus_one
  ≡ trunc_succ trunc_minus_two;

assert ⊢
  trunc_zero
  ≡ trunc_succ (trunc_succ trunc_minus_two);

assert ⊢
  trunc_one
  ≡ trunc_succ (trunc_succ (trunc_succ trunc_minus_two));

// The explicit -2 origin is not definitionally shifted away.
assertnot ⊢ trunc_minus_two ≡ trunc_minus_one;

assert (n : TruncLevel) (A : Grpd) ⊢
  IsTruncGrpd n A
  : Grpd;

assert [A : Grpd] ⊢
  IsTruncGrpd trunc_minus_two A
  ≡ IsContr A;

assert [A : Grpd] (n : TruncLevel) ⊢
  IsTruncGrpd (trunc_succ n) A
  ≡ @Pi_grpd A
      (λ x : τ A,
        @Pi_grpd A
          (λ y : τ A,
            IsTruncGrpd n (@= A x y)));

assert [A : Grpd] ⊢
  IsPropGrpd A
  ≡ @Pi_grpd A
      (λ x : τ A,
        @Pi_grpd A
          (λ y : τ A,
            IsContr (@= A x y)));

assert [A : Grpd] ⊢
  IsSetGrpd A
  ≡ @Pi_grpd A
      (λ x : τ A,
        @Pi_grpd A
          (λ y : τ A,
            IsPropGrpd (@= A x y)));

assert [A : Grpd] ⊢
  IsGroupoidGrpd A
  ≡ @Pi_grpd A
      (λ x : τ A,
        @Pi_grpd A
          (λ y : τ A,
            IsSetGrpd (@= A x y)));

// The definitional successor equation is the active equality-lowering step.
assert [A : Grpd]
  (n : TruncLevel)
  (h : τ (IsTruncGrpd (trunc_succ n) A))
  (x y : τ A) ⊢
  h x y
  : τ (IsTruncGrpd n (@= A x y));

assert [A : Grpd]
  (h : τ (IsTruncGrpd trunc_minus_two A)) ⊢
  h
  : τ (IsContr A);

// catalog-area: Truncation monotonicity
assert [A : Grpd]
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @eq_sym_trans_self A x y p
  : τ (@=
      (@= A y y)
      (@eq_trans A y x y (@eq_sym A x y p) p)
      (@eq_refl A y));

assert [A : Grpd]
  (x : τ A) ⊢
  @eq_sym_trans_self A x x (@eq_refl A x)
  ≡ @eq_refl (@= A x x) (@eq_refl A x);

assert [A : Grpd]
  (c : τ (IsContr A))
  (x y : τ A) ⊢
  @contractible_path_center A c x y
  : τ (@= A x y);

assert [A : Grpd]
  (c : τ (IsContr A))
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @contractible_path_contract A c x y p
  : τ (@=
      (@= A x y)
      (@contractible_path_center A c x y)
      p);

assert [A : Grpd]
  (c : τ (IsContr A)) ⊢
  @is_contr_is_prop A c
  : τ (IsPropGrpd A);

assert (n : TruncLevel) ⊢
  TruncMonotonicity n
  : Grpd;

assert (n : TruncLevel)
  [A : Grpd]
  (h : τ (IsTruncGrpd n A)) ⊢
  @is_trunc_grpd_succ n A h
  : τ (IsTruncGrpd (trunc_succ n) A);

assert [A : Grpd]
  (h : τ (IsContr A)) ⊢
  @is_trunc_grpd_succ trunc_minus_two A h
  ≡ @is_contr_is_prop A h;

assert (n : TruncLevel)
  [A : Grpd]
  (h : τ (IsTruncGrpd (trunc_succ n) A))
  (x y : τ A) ⊢
  @is_trunc_grpd_succ (trunc_succ n) A h x y
  ≡ @is_trunc_grpd_succ n (@= A x y) (h x y);

assert [A : Grpd]
  (h : τ (IsContr A)) ⊢
  @is_trunc_grpd_succ trunc_minus_two A h
  : τ (IsPropGrpd A);

assert [A : Grpd]
  (h : τ (IsPropGrpd A)) ⊢
  @is_trunc_grpd_succ trunc_minus_one A h
  : τ (IsSetGrpd A);

assert [A : Grpd]
  (h : τ (IsSetGrpd A)) ⊢
  @is_trunc_grpd_succ trunc_zero A h
  : τ (IsGroupoidGrpd A);

// The selected centre path for open contractibility data is not proof-erased.
assertnot [A : Grpd]
  (c : τ (IsContr A))
  (x : τ A) ⊢
  @contractible_path_center A c x x
  ≡ @eq_refl A x;

// catalog-area: auto

// catalog-area: Truncation evidence property-valuedness
assert [A : Grpd]
  (c d : τ (IsContr A)) ⊢
  @is_contr_evidence_transport A c d
  : τ (@Pi_grpd A
      (λ x : τ A, @= A (is_contr_center c) x));

assert [A : Grpd]
  (c d : τ (IsContr A)) ⊢
  @is_contr_evidence_pathover A c d
  : τ (@PathOver
      A
      (λ centre : τ A,
        @Pi_grpd A (λ x : τ A, @= A centre x))
      (is_contr_center c)
      (is_contr_center d)
      (is_contr_path c (is_contr_center d))
      (λ x : τ A, is_contr_path c x)
      (λ x : τ A, is_contr_path d x));

assert [A : Grpd]
  (c d : τ (IsContr A)) ⊢
  @is_contr_evidence_path A c d
  : τ (@= (IsContr A) c d);

assert [A : Grpd]
  (c : τ (IsContr A)) ⊢
  @is_contr_evidence_is_contr A c
  : τ (IsContr (IsContr A));

assert [A : Grpd] ⊢
  @is_contr_evidence_is_prop A
  : τ (IsPropGrpd (IsContr A));

assert [A : Grpd]
  [B : τ A → Grpd]
  (h : Π x : τ A, τ (IsContr (B x))) ⊢
  @is_contr_pi A B h
  : τ (IsContr (@Pi_grpd A B));

assert [A : Grpd]
  [B : τ A → Grpd]
  (h : Π x : τ A, τ (IsPropGrpd (B x))) ⊢
  @is_prop_pi A B h
  : τ (IsPropGrpd (@Pi_grpd A B));

assert (n : TruncLevel) ⊢
  TruncEvidenceProp n
  : Grpd;

assert (n : TruncLevel)
  (ih : τ (TruncEvidenceProp n))
  (A : Grpd) ⊢
  @trunc_evidence_prop_succ n ih A
  : τ (IsPropGrpd (IsTruncGrpd (trunc_succ n) A));

assert (n : TruncLevel)
  [A : Grpd] ⊢
  @is_trunc_grpd_evidence_is_prop n A
  : τ (IsPropGrpd (IsTruncGrpd n A));

assert [A : Grpd] ⊢
  @is_trunc_grpd_evidence_is_prop trunc_minus_two A
  ≡ @is_contr_evidence_is_prop A;

assert (n : TruncLevel)
  [A : Grpd] ⊢
  @is_trunc_grpd_evidence_is_prop (trunc_succ n) A
  ≡ @trunc_evidence_prop_succ
      n
      (@is_trunc_grpd_evidence_is_prop n)
      A;

assert [A : Grpd] ⊢
  @is_trunc_grpd_evidence_is_prop trunc_minus_two A
  : τ (IsPropGrpd (IsContr A));

assert [A : Grpd] ⊢
  @is_trunc_grpd_evidence_is_prop trunc_minus_one A
  : τ (IsPropGrpd (IsPropGrpd A));

assert [A : Grpd] ⊢
  @is_trunc_grpd_evidence_is_prop trunc_zero A
  : τ (IsPropGrpd (IsSetGrpd A));

assert (n : TruncLevel)
  [A : Grpd]
  (h k : τ (IsTruncGrpd n A)) ⊢
  is_contr_center
    (@is_trunc_grpd_evidence_is_prop n A h k)
  : τ (@= (IsTruncGrpd n A) h k);

// Equality of open contractibility witnesses remains propositional.
assertnot [A : Grpd]
  (c : τ (IsContr A)) ⊢
  @is_contr_evidence_path A c c
  ≡ @eq_refl (IsContr A) c;

// The evidence-property theorem does not erase two open witnesses.
assertnot (n : TruncLevel)
  [A : Grpd]
  (h k : τ (IsTruncGrpd n A)) ⊢
  h ≡ k;

// catalog-area: auto

// catalog-area: Dependent Pi truncation closure
assert (n : TruncLevel) ⊢
  PiTruncClosure n
  : Grpd;

assert (n : TruncLevel)
  (rec : τ (PiTruncClosure n))
  (A : Grpd)
  (B : τ A → Grpd)
  (h : Π x : τ A, τ (IsTruncGrpd (trunc_succ n) (B x))) ⊢
  @trunc_pi_succ n rec A B h
  : τ (IsTruncGrpd (trunc_succ n) (@Pi_grpd A B));

assert (n : TruncLevel)
  [A : Grpd]
  [B : τ A → Grpd]
  (h : Π x : τ A, τ (IsTruncGrpd n (B x))) ⊢
  @is_trunc_pi n A B h
  : τ (IsTruncGrpd n (@Pi_grpd A B));

assert [A : Grpd]
  [B : τ A → Grpd]
  (h : Π x : τ A, τ (IsContr (B x))) ⊢
  @is_trunc_pi trunc_minus_two A B h
  ≡ @is_contr_pi A B h;

assert (n : TruncLevel)
  [A : Grpd]
  [B : τ A → Grpd]
  (h : Π x : τ A, τ (IsTruncGrpd (trunc_succ n) (B x))) ⊢
  @is_trunc_pi (trunc_succ n) A B h
  ≡ @trunc_pi_succ
      n
      (@is_trunc_pi n)
      A
      B
      h;

assert [A : Grpd]
  [B : τ A → Grpd]
  (h : Π x : τ A, τ (IsPropGrpd (B x))) ⊢
  @is_trunc_pi trunc_minus_one A B h
  : τ (IsPropGrpd (@Pi_grpd A B));

assert [A : Grpd]
  [B : τ A → Grpd]
  (h : Π x : τ A, τ (IsSetGrpd (B x))) ⊢
  @is_trunc_pi trunc_zero A B h
  : τ (IsSetGrpd (@Pi_grpd A B));

assert [A : Grpd]
  [B : τ A → Grpd]
  (h : Π x : τ A, τ (IsGroupoidGrpd (B x))) ⊢
  @is_trunc_pi trunc_one A B h
  : τ (IsGroupoidGrpd (@Pi_grpd A B));

assert [A : Grpd]
  [B : τ A → Grpd]
  (h : Π x : τ A, τ (IsPropGrpd (B x))) ⊢
  @is_prop_pi A B h
  ≡ @is_trunc_pi trunc_minus_one A B h;

assert (n : TruncLevel)
  [A : Grpd]
  [B : τ A → Grpd]
  (h : Π x : τ A, τ (IsTruncGrpd (trunc_succ n) (B x)))
  (f g : τ (@Pi_grpd A B)) ⊢
  @is_trunc_pi (trunc_succ n) A B h f g
  : τ (IsTruncGrpd n (@= (@Pi_grpd A B) f g));

// Open pointwise evidence remains visible to the stable recursive owner.
assertnot (n : TruncLevel)
  [A : Grpd]
  [B : τ A → Grpd]
  (h k : Π x : τ A, τ (IsTruncGrpd n (B x))) ⊢
  @is_trunc_pi n A B h
  ≡ @is_trunc_pi n A B k;

// catalog-area: auto

// catalog-area: Dependent Sigma truncation closure
assert (n : TruncLevel) ⊢
  SigmaTruncClosure n
  : Grpd;

assert [A : Grpd]
  [B : τ A → Grpd]
  (hA : τ (IsContr A))
  (hB : Π x : τ A, τ (IsContr (B x))) ⊢
  @is_contr_sigma A B hA hB
  : τ (IsContr (@Σ_ A B));

assert (n : TruncLevel)
  (rec : τ (SigmaTruncClosure n))
  (A : Grpd)
  (B : τ A → Grpd)
  (hA : τ (IsTruncGrpd (trunc_succ n) A))
  (hB : Π x : τ A, τ (IsTruncGrpd (trunc_succ n) (B x))) ⊢
  @trunc_sigma_succ n rec A B hA hB
  : τ (IsTruncGrpd (trunc_succ n) (@Σ_ A B));

assert (n : TruncLevel)
  [A : Grpd]
  [B : τ A → Grpd]
  (hA : τ (IsTruncGrpd n A))
  (hB : Π x : τ A, τ (IsTruncGrpd n (B x))) ⊢
  @is_trunc_sigma n A B hA hB
  : τ (IsTruncGrpd n (@Σ_ A B));

assert [A : Grpd]
  [B : τ A → Grpd]
  (hA : τ (IsContr A))
  (hB : Π x : τ A, τ (IsContr (B x))) ⊢
  @is_trunc_sigma trunc_minus_two A B hA hB
  ≡ @is_contr_sigma A B hA hB;

assert (n : TruncLevel)
  [A : Grpd]
  [B : τ A → Grpd]
  (hA : τ (IsTruncGrpd (trunc_succ n) A))
  (hB : Π x : τ A, τ (IsTruncGrpd (trunc_succ n) (B x))) ⊢
  @is_trunc_sigma (trunc_succ n) A B hA hB
  ≡ @trunc_sigma_succ
      n
      (@is_trunc_sigma n)
      A
      B
      hA
      hB;

assert [A : Grpd]
  [B : τ A → Grpd]
  (hA : τ (IsPropGrpd A))
  (hB : Π x : τ A, τ (IsPropGrpd (B x))) ⊢
  @is_trunc_sigma trunc_minus_one A B hA hB
  : τ (IsPropGrpd (@Σ_ A B));

assert [A : Grpd]
  [B : τ A → Grpd]
  (hA : τ (IsSetGrpd A))
  (hB : Π x : τ A, τ (IsSetGrpd (B x))) ⊢
  @is_trunc_sigma trunc_zero A B hA hB
  : τ (IsSetGrpd (@Σ_ A B));

assert [A : Grpd]
  [B : τ A → Grpd]
  (hA : τ (IsGroupoidGrpd A))
  (hB : Π x : τ A, τ (IsGroupoidGrpd (B x))) ⊢
  @is_trunc_sigma trunc_one A B hA hB
  : τ (IsGroupoidGrpd (@Σ_ A B));

assert (n : TruncLevel)
  [A : Grpd]
  [B : τ A → Grpd]
  (hA : τ (IsTruncGrpd (trunc_succ n) A))
  (hB : Π x : τ A, τ (IsTruncGrpd (trunc_succ n) (B x)))
  (u v : @τΣ_ A B) ⊢
  @is_trunc_sigma (trunc_succ n) A B hA hB u v
  : τ (IsTruncGrpd n (@= (@Σ_ A B) u v));

// Both base and fibre evidence remain visible to the stable theorem owner.
assertnot (n : TruncLevel)
  [A : Grpd]
  [B : τ A → Grpd]
  (hA kA : τ (IsTruncGrpd n A))
  (hB : Π x : τ A, τ (IsTruncGrpd n (B x))) ⊢
  @is_trunc_sigma n A B hA hB
  ≡ @is_trunc_sigma n A B kA hB;

assertnot (n : TruncLevel)
  [A : Grpd]
  [B : τ A → Grpd]
  (hA : τ (IsTruncGrpd n A))
  (hB kB : Π x : τ A, τ (IsTruncGrpd n (B x))) ⊢
  @is_trunc_sigma n A B hA hB
  ≡ @is_trunc_sigma n A B hA kB;

// catalog-area: auto

// Packaged universes of n-truncated classifiers.
assert (n : TruncLevel) ⊢
  τ (TruncGrpdU n)
  ≡ TruncGrpdData n;

assert (n : TruncLevel)
  (carrier : Grpd)
  (evidence : τ (IsTruncGrpd n carrier)) ⊢
  @Struct_trunc_grpd n carrier evidence
  : τ (TruncGrpdU n);

assert (n : TruncLevel)
  (carrier : Grpd)
  (evidence : τ (IsTruncGrpd n carrier)) ⊢
  trunc_grpd_carrier (@Struct_trunc_grpd n carrier evidence)
  ≡ carrier;

assert (n : TruncLevel)
  (carrier : Grpd)
  (evidence : τ (IsTruncGrpd n carrier)) ⊢
  trunc_grpd_evidence (@Struct_trunc_grpd n carrier evidence)
  ≡ evidence;

assert (n : TruncLevel)
  (X : τ (TruncGrpdU n)) ⊢
  trunc_grpd_evidence X
  : τ (IsTruncGrpd n (trunc_grpd_carrier X));

assert ⊢
  PropU_grpd
  ≡ TruncGrpdU trunc_minus_one;

assert ⊢
  SetU_grpd
  ≡ TruncGrpdU trunc_zero;

assert ⊢
  GroupoidU_grpd
  ≡ TruncGrpdU trunc_one;

assert (carrier : Grpd)
  (evidence : τ (IsPropGrpd carrier)) ⊢
  @trunc_grpd_carrier trunc_minus_one
    (@Struct_trunc_grpd trunc_minus_one carrier evidence)
  ≡ carrier;

assert (carrier : Grpd)
  (evidence : τ (IsSetGrpd carrier)) ⊢
  @trunc_grpd_carrier trunc_zero
    (@Struct_trunc_grpd trunc_zero carrier evidence)
  ≡ carrier;

assert (carrier : Grpd)
  (evidence : τ (IsGroupoidGrpd carrier)) ⊢
  @trunc_grpd_carrier trunc_one
    (@Struct_trunc_grpd trunc_one carrier evidence)
  ≡ carrier;

// No runtime package eta is selected.
assertnot (n : TruncLevel)
  (X : τ (TruncGrpdU n)) ⊢
  X
  ≡ @Struct_trunc_grpd n
      (trunc_grpd_carrier X)
      (trunc_grpd_evidence X);

// Evidence fields are not erased by conversion.
assertnot (n : TruncLevel)
  (carrier : Grpd)
  (evidence0 evidence1 : τ (IsTruncGrpd n carrier)) ⊢
  @Struct_trunc_grpd n carrier evidence0
  ≡ @Struct_trunc_grpd n carrier evidence1;

// Element evidence is not falsely typed as evidence that the package universe
// itself is n-truncated; no same-level universe theorem is installed.
assertnot (n : TruncLevel)
  (X : τ (TruncGrpdU n)) ⊢
  trunc_grpd_evidence X
  : τ (IsTruncGrpd n (TruncGrpdU n));

// catalog-area: Truncated-universe carrier/evidence paths
assert (n : TruncLevel)
  (Q : τ (TruncGrpdU n) → Grpd)
  (c : Π carrier : Grpd,
       Π evidence : τ (IsTruncGrpd n carrier),
       τ (Q (@Struct_trunc_grpd n carrier evidence)))
  (X : τ (TruncGrpdU n)) ⊢
  @trunc_grpd_ind n Q c X
  : τ (Q X);

assert (n : TruncLevel)
  (Q : τ (TruncGrpdU n) → Grpd)
  (c : Π carrier : Grpd,
       Π evidence : τ (IsTruncGrpd n carrier),
       τ (Q (@Struct_trunc_grpd n carrier evidence)))
  (A : Grpd)
  (h : τ (IsTruncGrpd n A)) ⊢
  @trunc_grpd_ind n Q c (@Struct_trunc_grpd n A h)
  ≡ c A h;

assert (n : TruncLevel)
  (X Y : τ (TruncGrpdU n)) ⊢
  TruncGrpdPathView n X Y
  : Grpd;

assert (n : TruncLevel)
  (X : τ (TruncGrpdU n)) ⊢
  @trunc_grpd_path_refl n X
  : τ (TruncGrpdPathView n X X);

assert (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (w : τ (TruncGrpdPathView n X Y)) ⊢
  @trunc_grpd_path_decode n X Y w
  : τ (@= (TruncGrpdU n) X Y);

assert (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= (TruncGrpdU n) X Y)) ⊢
  @trunc_grpd_path_encode n X Y p
  : τ (TruncGrpdPathView n X Y);

assert (n : TruncLevel)
  (X : τ (TruncGrpdU n)) ⊢
  @trunc_grpd_path_decode_refl n X
  : τ (@=
      (@= (TruncGrpdU n) X X)
      (@trunc_grpd_path_decode
        n X X (@trunc_grpd_path_refl n X))
      (@eq_refl (TruncGrpdU n) X));

assert (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= (TruncGrpdU n) X Y)) ⊢
  @trunc_grpd_path_decode_encode n X Y p
  : τ (@=
      (@= (TruncGrpdU n) X Y)
      (@trunc_grpd_path_decode
        n X Y (@trunc_grpd_path_encode n X Y p))
      p);

assert (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= Grpd_grpd
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y))) ⊢
  @trunc_grpd_evidence_pathover n X Y p
  : τ (@PathOver
      Grpd_grpd
      (λ A : Grpd, IsTruncGrpd n A)
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y)
      p
      (trunc_grpd_evidence X)
      (trunc_grpd_evidence Y));

assert (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= Grpd_grpd
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y))) ⊢
  @trunc_grpd_path_from_carrier n X Y p
  : τ (@= (TruncGrpdU n) X Y);

assert (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= Grpd_grpd
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y))) ⊢
  @trunc_grpd_carrier_path_from_carrier n X Y p
  : τ (@=
      (@= Grpd_grpd
        (trunc_grpd_carrier X)
        (trunc_grpd_carrier Y))
      (@trunc_grpd_carrier_path
        n X Y (@trunc_grpd_path_from_carrier n X Y p))
      p);

assert (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= (TruncGrpdU n) X Y)) ⊢
  @trunc_grpd_path_from_carrier_carrier_path n X Y p
  : τ (@=
      (@= (TruncGrpdU n) X Y)
      (@trunc_grpd_path_from_carrier
        n X Y (@trunc_grpd_carrier_path n X Y p))
      p);

assert (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)] ⊢
  @trunc_grpd_carrier_path_type_equiv n X Y
  : τ (TypeEquiv
      (@= (TruncGrpdU n) X Y)
      (@= Grpd_grpd
        (trunc_grpd_carrier X)
        (trunc_grpd_carrier Y)));

assert (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= (TruncGrpdU n) X Y)) ⊢
  type_equiv_to (@trunc_grpd_carrier_path_type_equiv n X Y) p
  ≡ @trunc_grpd_carrier_path n X Y p;

assert (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= Grpd_grpd
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y))) ⊢
  type_equiv_from (@trunc_grpd_carrier_path_type_equiv n X Y) p
  ≡ @trunc_grpd_path_from_carrier n X Y p;

// The propositional round trips are not runtime cancellation rules.
assertnot (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= Grpd_grpd
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y))) ⊢
  @trunc_grpd_carrier_path
    n X Y (@trunc_grpd_path_from_carrier n X Y p)
  ≡ p;

assertnot (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= (TruncGrpdU n) X Y)) ⊢
  @trunc_grpd_path_from_carrier
    n X Y (@trunc_grpd_carrier_path n X Y p)
  ≡ p;

// Encoding/decoding an open package path also remains propositional.
assertnot (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= (TruncGrpdU n) X Y)) ⊢
  @trunc_grpd_path_decode
    n X Y (@trunc_grpd_path_encode n X Y p)
  ≡ p;

// catalog-area: Truncated-universe restricted univalence
assert [A B : Grpd] ⊢
  @grpd_univalence_type_equiv A B
  : τ (TypeEquiv (@= Grpd_grpd A B) (TypeEquiv A B));

assert [A B : Grpd]
  (p : τ (@= Grpd_grpd A B)) ⊢
  type_equiv_to (@grpd_univalence_type_equiv A B) p
  ≡ @idtoequiv_grpd A B p;

assert [A B : Grpd]
  (e : τ (TypeEquiv A B)) ⊢
  type_equiv_from (@grpd_univalence_type_equiv A B) e
  ≡ @grpd_equiv_path A B e;

assert (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)] ⊢
  @trunc_grpd_univalence_type_equiv n X Y
  : τ (TypeEquiv
      (@= (TruncGrpdU n) X Y)
      (TypeEquiv
        (trunc_grpd_carrier X)
        (trunc_grpd_carrier Y)));

assert (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= (TruncGrpdU n) X Y)) ⊢
  type_equiv_to (@trunc_grpd_univalence_type_equiv n X Y) p
  ≡ @idtoequiv_grpd
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y)
      (@trunc_grpd_carrier_path n X Y p);

assert (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (e : τ (TypeEquiv
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y))) ⊢
  type_equiv_from (@trunc_grpd_univalence_type_equiv n X Y) e
  ≡ @trunc_grpd_path_from_carrier
      n X Y
      (@grpd_equiv_path
        (trunc_grpd_carrier X)
        (trunc_grpd_carrier Y)
        e);

assert (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= (TruncGrpdU n) X Y)) ⊢
  @trunc_grpd_idtoequiv n X Y p
  : τ (TypeEquiv
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y));

assert (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (e : τ (TypeEquiv
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y))) ⊢
  @trunc_grpd_equiv_path n X Y e
  : τ (@= (TruncGrpdU n) X Y);

assert (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= (TruncGrpdU n) X Y)) ⊢
  @trunc_grpd_equiv_path_idtoequiv n X Y p
  : τ (@=
      (@= (TruncGrpdU n) X Y)
      (@trunc_grpd_equiv_path
        n X Y (@trunc_grpd_idtoequiv n X Y p))
      p);

assert (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (e : τ (TypeEquiv
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y))) ⊢
  @trunc_grpd_idtoequiv_equiv_path n X Y e
  : τ (@=
      (TypeEquiv
        (trunc_grpd_carrier X)
        (trunc_grpd_carrier Y))
      (@trunc_grpd_idtoequiv
        n X Y (@trunc_grpd_equiv_path n X Y e))
      e);

assert (n : TruncLevel)
  (X : τ (TruncGrpdU n)) ⊢
  @trunc_grpd_idtoequiv
    n X X (@eq_refl (TruncGrpdU n) X)
  ≡ @type_equiv_refl (trunc_grpd_carrier X);

assert (n : TruncLevel)
  (X : τ (TruncGrpdU n)) ⊢
  @trunc_grpd_equiv_path_refl n X
  : τ (@=
      (@= (TruncGrpdU n) X X)
      (@trunc_grpd_equiv_path
        n X X (@type_equiv_refl (trunc_grpd_carrier X)))
      (@eq_refl (TruncGrpdU n) X));

// Restricted univalence round trips remain propositional.
assertnot (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= (TruncGrpdU n) X Y)) ⊢
  @trunc_grpd_equiv_path
    n X Y (@trunc_grpd_idtoequiv n X Y p)
  ≡ p;

assertnot (n : TruncLevel)
  [X Y : τ (TruncGrpdU n)]
  (e : τ (TypeEquiv
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y))) ⊢
  @trunc_grpd_idtoequiv
    n X Y (@trunc_grpd_equiv_path n X Y e)
  ≡ e;

// Even reflexive carrier equivalence decodes only propositionally.
assertnot (n : TruncLevel)
  (X : τ (TruncGrpdU n)) ⊢
  @trunc_grpd_equiv_path
    n X X (@type_equiv_refl (trunc_grpd_carrier X))
  ≡ @eq_refl (TruncGrpdU n) X;

// catalog-area: Truncated-universe expected level
assert [A B : Grpd]
  (hA : τ (IsContr A))
  (hB : τ (IsContr B))
  (f : τ A → τ B) ⊢
  @contractible_map_by_inverse A B hA hB f
  : τ (@EquivByInverse
      A B f (λ _ : τ B, is_contr_center hA));

assert [A B : Grpd]
  (hA : τ (IsContr A))
  (hB : τ (IsContr B))
  (f : τ A → τ B) ⊢
  @contractible_map_is_equiv A B hA hB f
  : τ (@IsEquivMap A B f);

assert [A B : Grpd]
  (f : τ A → τ B) ⊢
  @is_equiv_map_evidence_is_prop A B f
  : τ (IsPropGrpd (@IsEquivMap A B f));

assert [A B : Grpd]
  (hA : τ (IsContr A))
  (hB : τ (IsContr B))
  (f : τ A → τ B) ⊢
  @is_equiv_map_evidence_is_contr A B hA hB f
  : τ (IsContr (@IsEquivMap A B f));

assert [A B : Grpd]
  (hA : τ (IsContr A))
  (hB : τ (IsContr B)) ⊢
  @contractible_type_equiv A B hA hB
  : τ (IsContr (TypeEquiv A B));

assert (n : TruncLevel)
  [A : Grpd]
  (h : τ (IsPropGrpd A)) ⊢
  @prop_is_trunc_succ n A h
  : τ (IsTruncGrpd (trunc_succ n) A);

assert [A : Grpd]
  (h : τ (IsPropGrpd A)) ⊢
  @prop_is_trunc_succ trunc_minus_two A h
  ≡ h;

assert (n : TruncLevel)
  [A B : Grpd]
  (hB : τ (IsTruncGrpd (trunc_succ n) B)) ⊢
  @trunc_type_equiv_succ n A B hB
  : τ (IsTruncGrpd (trunc_succ n) (TypeEquiv A B));

assert (n : TruncLevel) ⊢
  TypeEquivTruncClosure n
  : Grpd;

assert (n : TruncLevel) ⊢
  @is_trunc_type_equiv n
  : τ (TypeEquivTruncClosure n);

assert [A B : Grpd]
  (hA : τ (IsContr A))
  (hB : τ (IsContr B)) ⊢
  @is_trunc_type_equiv trunc_minus_two A B hA hB
  ≡ @contractible_type_equiv A B hA hB;

assert (n : TruncLevel)
  [A B : Grpd]
  (hA : τ (IsTruncGrpd (trunc_succ n) A))
  (hB : τ (IsTruncGrpd (trunc_succ n) B)) ⊢
  @is_trunc_type_equiv (trunc_succ n) A B hA hB
  ≡ @trunc_type_equiv_succ n A B hB;

// Source evidence is intentionally not a successor-level discriminator.
assert (n : TruncLevel)
  [A B : Grpd]
  (hA kA : τ (IsTruncGrpd (trunc_succ n) A))
  (hB : τ (IsTruncGrpd (trunc_succ n) B)) ⊢
  @is_trunc_type_equiv (trunc_succ n) A B hA hB
  ≡ @is_trunc_type_equiv (trunc_succ n) A B kA hB;

assert (n : TruncLevel) ⊢
  @is_trunc_grpd_universe n
  : τ (IsTruncGrpd
      (trunc_succ n)
      (TruncGrpdU n));

assert ⊢
  @is_trunc_grpd_universe trunc_minus_two
  : τ (IsPropGrpd (TruncGrpdU trunc_minus_two));

assert ⊢
  @is_trunc_grpd_universe trunc_minus_one
  : τ (IsSetGrpd PropU_grpd);

assert ⊢
  @is_trunc_grpd_universe trunc_zero
  : τ (IsGroupoidGrpd SetU_grpd);

// Contractible source evidence remains explicit in the base construction.
assertnot [A B : Grpd]
  (hA kA : τ (IsContr A))
  (hB : τ (IsContr B))
  (f : τ A → τ B) ⊢
  @contractible_map_is_equiv A B hA hB f
  ≡ @contractible_map_is_equiv A B kA hB f;

// Target evidence remains explicit data in the successor helper.
assertnot (n : TruncLevel)
  [A B : Grpd]
  (hA : τ (IsTruncGrpd (trunc_succ n) A))
  (hB kB : τ (IsTruncGrpd (trunc_succ n) B)) ⊢
  @is_trunc_type_equiv (trunc_succ n) A B hA hB
  ≡ @is_trunc_type_equiv (trunc_succ n) A B hA kB;

// The theorem does not install a same-level universe claim.
assertnot (n : TruncLevel) ⊢
  @is_trunc_grpd_universe n
  : τ (IsTruncGrpd n (TruncGrpdU n));

// catalog-area: auto

assert [A : Grpd] ⊢ Obj (Path_cat A) ≡ A;

assert [A : Grpd] (x y : τ A) ⊢ Hom_cat (Path_cat A) x y ≡ Path_cat (x = y);

assert [A : Grpd] (x : τ A) ⊢ @id (Path_cat A) x ≡ eq_refl x;

// E0 keeps the shared generic category-composition head. J-derived
// transitivity agrees propositionally, not by runtime conversion.
assert [A : Grpd]
  [x y : τ A]
  (p : τ (x = y))
  [z : τ A]
  (q : τ (y = z)) ⊢
  @path_comp_eq_trans A x y p z q
  : τ (
      @comp_fapp0 (Path_cat A) x y z q p
      = @eq_trans A x y z p q);

assert [A : Grpd] (y z : τ A) (q : τ (y = z)) ⊢
  @path_comp_eq_trans A y y (eq_refl y) z q
  ≡ eq_refl q;

assertnot [A : Grpd]
  [x y : τ A]
  (p : τ (x = y))
  [z : τ A]
  (q : τ (y = z)) ⊢
  @comp_fapp0 (Path_cat A) x y z q p
  ≡ @eq_trans A x y z p q;

// Both unit orders join whether generic `id` or its `eq_refl` projection is
// exposed first.
assert [A : Grpd] (x y : τ A) (p : τ (x = y)) ⊢
  @comp_fapp0 (Path_cat A) x x y p (@id (Path_cat A) x)
  ≡ p;

assert [A : Grpd] (x y : τ A) (p : τ (x = y)) ⊢
  @comp_fapp0 (Path_cat A) x x y p (eq_refl x)
  ≡ p;

assert [A : Grpd] (x y : τ A) (p : τ (x = y)) ⊢
  @comp_fapp0 (Path_cat A) x y y (@id (Path_cat A) y) p
  ≡ p;

assert [A : Grpd] (x y : τ A) (p : τ (x = y)) ⊢
  @comp_fapp0 (Path_cat A) x y y (eq_refl y) p
  ≡ p;

// Generic associativity remains a proof-time equation; typed reflexivity
// exercises that owner on arbitrary path-category arrows.
assert [A : Grpd]
  (w x y z : τ A)
  (p : τ (w = x))
  (q : τ (x = y))
  (r : τ (y = z)) ⊢
  eq_refl
    (@comp_fapp0
      (Path_cat A)
      w y z r
      (@comp_fapp0 (Path_cat A) w x y q p))
  : τ (
      @comp_fapp0
        (Path_cat A)
        w y z r
        (@comp_fapp0 (Path_cat A) w x y q p)
      = @comp_fapp0
          (Path_cat A)
          w x z
          (@comp_fapp0 (Path_cat A) x y z r q)
          p);

// Opposite path categories retain reversed hom endpoints and do not collapse
// definitionally back to the original category.
assert [A : Grpd] (x y : τ A) ⊢
  Hom_cat (Op_cat (Path_cat A)) x y
  ≡ Path_cat (y = x);

assertnot [A : Grpd] ⊢
  Op_cat (Path_cat A)
  ≡ Path_cat A;

// Oriented action heads retain distinct runtime normal forms. Their existing
// proof-time comparisons with shared category composition supply both units
// without four additional constructor-specific runtime bridges.
symbol path_postcomp_comp_check
  [A : Grpd]
  [w x y : τ A]
  (h : τ (x = y))
  (g : τ (w = x))
  : τ (
      @hom_postcomp_fapp0
        (Path_cat A) (Path_cat A) (@id Cat_cat (Path_cat A))
        w x y h g
      = @comp_fapp0 (Path_cat A) w x y h g)
≔ eq_refl
    (@hom_postcomp_fapp0
      (Path_cat A) (Path_cat A) (@id Cat_cat (Path_cat A))
      w x y h g);

symbol path_precomp_comp_check
  [A : Grpd]
  [z w x : τ A]
  (h : τ (w = x))
  (g : τ (x = z))
  : τ (
      @hom_precomp_along_fapp0
        (Path_cat A) (Path_cat A) (@id Cat_cat (Path_cat A))
        z w x h g
      = @comp_fapp0 (Path_cat A) w x z g h)
≔ eq_refl
    (@hom_precomp_along_fapp0
      (Path_cat A) (Path_cat A) (@id Cat_cat (Path_cat A))
      z w x h g);

assert [A : Grpd] (x y : τ A) (p : τ (x = y)) ⊢
  @path_postcomp_comp_check A x x y p (eq_refl x)
  : τ (
      @hom_postcomp_fapp0
        (Path_cat A) (Path_cat A) (@id Cat_cat (Path_cat A))
        x x y p (eq_refl x)
      = p);

assert [A : Grpd] (x y : τ A) (p : τ (x = y)) ⊢
  @path_postcomp_comp_check A x y y (eq_refl y) p
  : τ (
      @hom_postcomp_fapp0
        (Path_cat A) (Path_cat A) (@id Cat_cat (Path_cat A))
        x y y (eq_refl y) p
      = p);

assert [A : Grpd] (x y : τ A) (p : τ (x = y)) ⊢
  @path_precomp_comp_check A y x x (eq_refl x) p
  : τ (
      @hom_precomp_along_fapp0
        (Path_cat A) (Path_cat A) (@id Cat_cat (Path_cat A))
        y x x (eq_refl x) p
      = p);

assert [A : Grpd] (x y : τ A) (p : τ (x = y)) ⊢
  @path_precomp_comp_check A y x y p (eq_refl y)
  : τ (
      @hom_precomp_along_fapp0
        (Path_cat A) (Path_cat A) (@id Cat_cat (Path_cat A))
        y x y p (eq_refl y)
      = p);

assertnot [A : Grpd] (x y : τ A) (p : τ (x = y)) ⊢
  @hom_postcomp_fapp0
    (Path_cat A) (Path_cat A) (@id Cat_cat (Path_cat A))
    x x y p (eq_refl x)
  ≡ p;

assertnot [A : Grpd] (x y : τ A) (p : τ (x = y)) ⊢
  @hom_postcomp_fapp0
    (Path_cat A) (Path_cat A) (@id Cat_cat (Path_cat A))
    x y y (eq_refl y) p
  ≡ p;

assertnot [A : Grpd] (x y : τ A) (p : τ (x = y)) ⊢
  @hom_precomp_along_fapp0
    (Path_cat A) (Path_cat A) (@id Cat_cat (Path_cat A))
    y x x (eq_refl x) p
  ≡ p;

assertnot [A : Grpd] (x y : τ A) (p : τ (x = y)) ⊢
  @hom_precomp_along_fapp0
    (Path_cat A) (Path_cat A) (@id Cat_cat (Path_cat A))
    y x y p (eq_refl y)
  ≡ p;

// The oriented postcomposition and shared category-composition heads remain
// distinct runtime normal forms; their existing proof-time comparison joins
// them for typing.
assert [A : Grpd]
  (x y z : τ A)
  (p : τ (x = y))
  (q : τ (y = z)) ⊢
  @eq_refl (x = z)
    (@hom_postcomp_fapp0
      (Path_cat A) (Path_cat A) (@id Cat_cat (Path_cat A))
      x y z q p)
  : τ (
      @hom_postcomp_fapp0
        (Path_cat A) (Path_cat A) (@id Cat_cat (Path_cat A))
        x y z q p
      = @comp_fapp0 (Path_cat A) x y z q p);

// E1: path symmetry is the arrow action of one functor from the genuine
// opposite path category. Generic functoriality owns its strict identity and
// anti-composition computation.
assert [A : Grpd] (x : τ A) ⊢
  @fapp0
    (Op_cat (Path_cat A))
    (Path_cat A)
    (Path_sym_func A)
    x
  ≡ x;

assert [A : Grpd] (x : τ A) ⊢
  @path_sym A x x (eq_refl x)
  ≡ eq_refl x;

// Identity-first and action-first reduction orders join: generic functor
// identity sees the literal source identity, while Path_cat may expose refl
// first for the focused PathSym projection bridge.
assert [A : Grpd] (x : τ A) ⊢
  @fapp1_fapp0
    (Op_cat (Path_cat A))
    (Path_cat A)
    (Path_sym_func A)
    x x
    (@id (Op_cat (Path_cat A)) x)
  ≡ eq_refl x;

assert [A : Grpd]
  [x y : τ A]
  (p : τ (x = y))
  [z : τ A]
  (q : τ (y = z)) ⊢
  @comp_fapp0
    (Path_cat A)
    z y x
    (@path_sym A x y p)
    (@path_sym A y z q)
  ≡ @path_sym A x z
      (@comp_fapp0 (Path_cat A) x y z q p);

// The composition-first intermediate also joins after opposite composition
// reverses its factors; no constructor-specific path_sym(comp) rule is used.
assert [A : Grpd]
  [x y : τ A]
  (p : τ (x = y))
  [z : τ A]
  (q : τ (y = z)) ⊢
  @fapp1_fapp0
    (Op_cat (Path_cat A))
    (Path_cat A)
    (Path_sym_func A)
    z x
    (@comp_fapp0 (Op_cat (Path_cat A)) z y x p q)
  ≡ @path_sym A x z
      (@comp_fapp0 (Path_cat A) x y z q p);

assertnot [A : Grpd]
  [x y : τ A]
  (p : τ (x = y)) ⊢
  @path_sym A x y p
  ≡ @eq_sym A x y p;

assert [A : Grpd]
  [x y : τ A]
  (p : τ (x = y)) ⊢
  @path_sym_agrees_eq_sym A x y p
  : τ (@path_sym A x y p = @eq_sym A x y p);

assert [A : Grpd] (x : τ A) ⊢
  @path_sym_agrees_eq_sym A x x (eq_refl x)
  ≡ eq_refl (eq_refl x);

assert [A : Grpd]
  [x y : τ A]
  (p : τ (x = y)) ⊢
  @path_sym_invol A x y p
  : τ (
      @path_sym A y x (@path_sym A x y p)
      = p);

assertnot [A : Grpd]
  [x y : τ A]
  (p : τ (x = y)) ⊢
  @path_sym A y x (@path_sym A x y p)
  ≡ p;

assert [A : Grpd] (x : τ A) ⊢
  @path_sym_invol A x x (eq_refl x)
  ≡ eq_refl (eq_refl x);

assert [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (x = y)) ⊢
  @path_sym_core_incl_agreement C x y p
  : τ (@=
      (Hom C x y)
      (@path_to_hom (Op_cat C) y x
        (@path_sym (Obj C) x y p))
      (@path_to_hom C x y p));

assert [C : Cat] (x : τ (Obj C)) ⊢
  @path_sym_core_incl_agreement C x x (eq_refl x)
  ≡ eq_refl (@id C x);

/*
  Classification and resolution of the twelve E1 owner warnings.

  Six mapped-DefIso reports exposed over-specified endpoint guards and vanish
  after the generic owner is minimized. The post/pre and naturality families
  are typed unit diamonds. Each pair checks the action-first spelling and the
  spelling with the PathSym reflexivity projection already exposed. The two
  Product projection reports are rejected below as untyped rigid-head cases.
*/
assert [A : Grpd]
  (w x y : τ A)
  (p : τ (x = y))
  (g : τ (w = y)) ⊢
  @comp_fapp0 (Path_cat A) w x x
    (@path_sym A x x (eq_refl x))
    (@hom_postcomp_fapp0
      (Path_cat A) (Op_cat (Path_cat A)) (Path_sym_func A)
      w y x p g)
  ≡ @hom_postcomp_fapp0
      (Path_cat A) (Op_cat (Path_cat A)) (Path_sym_func A)
      w y x p g;

assert [A : Grpd]
  (w x y : τ A)
  (p : τ (x = y))
  (g : τ (w = y)) ⊢
  @comp_fapp0 (Path_cat A) w x x
    (eq_refl x)
    (@hom_postcomp_fapp0
      (Path_cat A) (Op_cat (Path_cat A)) (Path_sym_func A)
      w y x p g)
  ≡ @hom_postcomp_fapp0
      (Path_cat A) (Op_cat (Path_cat A)) (Path_sym_func A)
      w y x p g;

assert [A : Grpd]
  (x y z : τ A)
  (p : τ (x = y))
  (q : τ (x = z)) ⊢
  @comp_fapp0 (Path_cat A) y y z
    (@hom_precomp_along_fapp0
      (Op_cat (Path_cat A)) (Path_cat A) (Path_sym_func A)
      z y x p q)
    (@path_sym A y y (eq_refl y))
  ≡ @hom_precomp_along_fapp0
      (Op_cat (Path_cat A)) (Path_cat A) (Path_sym_func A)
      z y x p q;

assert [A : Grpd]
  (x y z : τ A)
  (p : τ (x = y))
  (q : τ (x = z)) ⊢
  @comp_fapp0 (Path_cat A) y y z
    (@hom_precomp_along_fapp0
      (Op_cat (Path_cat A)) (Path_cat A) (Path_sym_func A)
      z y x p q)
    (eq_refl y)
  ≡ @hom_precomp_along_fapp0
      (Op_cat (Path_cat A)) (Path_cat A) (Path_sym_func A)
      z y x p q;

// Mapped-DefIso cancellation is checked before and after all PathSym object
// projections. Both spellings failed with explicit endpoint guards and now
// join through the minimized generic owner, without a path-specific rule.
assert [A : Grpd]
  (x y : τ A)
  (i : τ (@DefIso (Op_cat (Path_cat A)) x y)) ⊢
  @hom_postcomp_fapp0
    (Path_cat A) (Path_cat A) (@id Cat_cat (Path_cat A))
    (@fapp0 (Op_cat (Path_cat A)) (Path_cat A) (Path_sym_func A) x)
    (@fapp0 (Op_cat (Path_cat A)) (Path_cat A) (Path_sym_func A) y)
    (@fapp0 (Op_cat (Path_cat A)) (Path_cat A) (Path_sym_func A) x)
    (@fapp1_fapp0
      (Op_cat (Path_cat A)) (Path_cat A) (Path_sym_func A)
      y x (@defiso_from (Op_cat (Path_cat A)) x y i))
    (@fapp1_fapp0
      (Op_cat (Path_cat A)) (Path_cat A) (Path_sym_func A)
      x y (@defiso_to (Op_cat (Path_cat A)) x y i))
  ≡ eq_refl x;

assert [A : Grpd]
  (x y : τ A)
  (i : τ (@DefIso (Op_cat (Path_cat A)) x y)) ⊢
  @hom_postcomp_fapp0
    (Path_cat A) (Path_cat A) (@id Cat_cat (Path_cat A))
    x y x
    (@fapp1_fapp0
      (Op_cat (Path_cat A)) (Path_cat A) (Path_sym_func A)
      y x (@defiso_from (Op_cat (Path_cat A)) x y i))
    (@fapp1_fapp0
      (Op_cat (Path_cat A)) (Path_cat A) (Path_sym_func A)
      x y (@defiso_to (Op_cat (Path_cat A)) x y i))
  ≡ eq_refl x;

assert [A : Grpd]
  (x y : τ A)
  (i : τ (@DefIso (Op_cat (Path_cat A)) x y)) ⊢
  @hom_postcomp_fapp0
    (Path_cat A) (Path_cat A) (@id Cat_cat (Path_cat A))
    (@fapp0 (Op_cat (Path_cat A)) (Path_cat A) (Path_sym_func A) y)
    (@fapp0 (Op_cat (Path_cat A)) (Path_cat A) (Path_sym_func A) x)
    (@fapp0 (Op_cat (Path_cat A)) (Path_cat A) (Path_sym_func A) y)
    (@fapp1_fapp0
      (Op_cat (Path_cat A)) (Path_cat A) (Path_sym_func A)
      x y (@defiso_to (Op_cat (Path_cat A)) x y i))
    (@fapp1_fapp0
      (Op_cat (Path_cat A)) (Path_cat A) (Path_sym_func A)
      y x (@defiso_from (Op_cat (Path_cat A)) x y i))
  ≡ eq_refl y;

assert [A : Grpd]
  (x y : τ A)
  (i : τ (@DefIso (Op_cat (Path_cat A)) x y)) ⊢
  @hom_postcomp_fapp0
    (Path_cat A) (Path_cat A) (@id Cat_cat (Path_cat A))
    y x y
    (@fapp1_fapp0
      (Op_cat (Path_cat A)) (Path_cat A) (Path_sym_func A)
      x y (@defiso_to (Op_cat (Path_cat A)) x y i))
    (@fapp1_fapp0
      (Op_cat (Path_cat A)) (Path_cat A) (Path_sym_func A)
      y x (@defiso_from (Op_cat (Path_cat A)) x y i))
  ≡ eq_refl y;

// Product-projection overlaps are untyped: PathSym's rigid target is a path
// category, never a product-category head. Keep explicit negative typing
// controls for both projection owners.
assertnot [A : Grpd] [B C : Cat] (x : τ A) ⊢
  sigma_Fst
    (@fapp0
      (Op_cat (Path_cat A)) (Product_cat B C) (Path_sym_func A) x)
  : τ (Obj B);

assertnot [A : Grpd] [B C : Cat] (x : τ A) ⊢
  sigma_Snd
    (@fapp0
      (Op_cat (Path_cat A)) (Product_cat B C) (Path_sym_func A) x)
  : τ (Obj C);

assert [A : Grpd]
  (F : τ (Functor (Op_cat (Path_cat A)) (Path_cat A)))
  (x y : τ A)
  (p : τ (y = x))
  (eta : τ (Transf F (Path_sym_func A))) ⊢
  @comp_fapp0 (Path_cat A)
    (@fapp0 (Op_cat (Path_cat A)) (Path_cat A) F x) y y
    (@path_sym A y y (eq_refl y))
    (@tapp1_fapp0
      (Op_cat (Path_cat A)) (Path_cat A)
      F (Path_sym_func A) x y eta p)
  ≡ @tapp1_fapp0
      (Op_cat (Path_cat A)) (Path_cat A)
      F (Path_sym_func A) x y eta p;

assert [A : Grpd]
  (F : τ (Functor (Op_cat (Path_cat A)) (Path_cat A)))
  (x y : τ A)
  (p : τ (y = x))
  (eta : τ (Transf F (Path_sym_func A))) ⊢
  @comp_fapp0 (Path_cat A)
    (@fapp0 (Op_cat (Path_cat A)) (Path_cat A) F x) y y
    (eq_refl y)
    (@tapp1_fapp0
      (Op_cat (Path_cat A)) (Path_cat A)
      F (Path_sym_func A) x y eta p)
  ≡ @tapp1_fapp0
      (Op_cat (Path_cat A)) (Path_cat A)
      F (Path_sym_func A) x y eta p;

assert [A : Grpd]
  (G : τ (Functor (Op_cat (Path_cat A)) (Path_cat A)))
  (x y : τ A)
  (p : τ (y = x))
  (eta : τ (Transf (Path_sym_func A) G)) ⊢
  @comp_fapp0 (Path_cat A)
    x x (@fapp0 (Op_cat (Path_cat A)) (Path_cat A) G y)
    (@tapp1_fapp0
      (Op_cat (Path_cat A)) (Path_cat A)
      (Path_sym_func A) G x y eta p)
    (@path_sym A x x (eq_refl x))
  ≡ @tapp1_fapp0
      (Op_cat (Path_cat A)) (Path_cat A)
      (Path_sym_func A) G x y eta p;

assert [A : Grpd]
  (G : τ (Functor (Op_cat (Path_cat A)) (Path_cat A)))
  (x y : τ A)
  (p : τ (y = x))
  (eta : τ (Transf (Path_sym_func A) G)) ⊢
  @comp_fapp0 (Path_cat A)
    x x (@fapp0 (Op_cat (Path_cat A)) (Path_cat A) G y)
    (@tapp1_fapp0
      (Op_cat (Path_cat A)) (Path_cat A)
      (Path_sym_func A) G x y eta p)
    (eq_refl x)
  ≡ @tapp1_fapp0
      (Op_cat (Path_cat A)) (Path_cat A)
      (Path_sym_func A) G x y eta p;

// Ordinary categorical isomorphism evidence.
assert [C : Cat] (x : τ (Obj C)) ⊢
  @iso_evidence_to C x x (@iso_evidence_refl C x)
  ≡ @id C x;

assert [C : Cat] (x : τ (Obj C)) ⊢
  @iso_evidence_from C x x (@iso_evidence_refl C x)
  ≡ @id C x;

assert [C : Cat] (x : τ (Obj C)) ⊢
  @iso_evidence_left C x x (@iso_evidence_refl C x)
  ≡ eq_refl (@id C x);

assert [C : Cat] (x : τ (Obj C)) ⊢
  @iso_evidence_right C x x (@iso_evidence_refl C x)
  ≡ eq_refl (@id C x);

assert [C : Cat] [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y)) ⊢
  @iso_evidence_to C y x (@iso_evidence_sym C x y i)
  ≡ @iso_evidence_from C x y i;

assert [C : Cat] [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y)) ⊢
  @iso_evidence_from C y x (@iso_evidence_sym C x y i)
  ≡ @iso_evidence_to C x y i;

assert [C : Cat] [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y)) ⊢
  @iso_evidence_left C x y i
  : τ (
      @comp_fapp0 C x y x
        (@iso_evidence_from C x y i)
        (@iso_evidence_to C x y i)
      =
      @id C x);

assert [C : Cat] [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y)) ⊢
  @iso_evidence_right C x y i
  : τ (
      @comp_fapp0 C y x y
        (@iso_evidence_to C x y i)
        (@iso_evidence_from C x y i)
      =
      @id C y);

// Categorical univalence skeleton: 1-categorical staging and omega layer.
assert [C : Cat] (x : τ (Obj C)) ⊢
  @idtoiso_cat C x x (eq_refl x)
  ≡ @iso_evidence_refl C x;

assert [C : Cat] (x : τ (Obj C)) ⊢
  @iso_evidence_to C x x (@idtoiso_cat C x x (eq_refl x))
  ≡ @id C x;

// Equality-valued fixed-arrow staging record: construction and projections.
assert [C : Cat] (x y : τ (Obj C)) (f : τ (Hom C x y))
  (l r : τ (Hom C y x))
  (alpha : τ (@= (Hom C x x)
    (@comp_fapp0 C x y x l f) (@id C x)))
  (beta : τ (@= (Hom C y y)
    (@comp_fapp0 C y x y f r) (@id C y))) ⊢
  @omega_equiv_along_left_inv C x y f
    (@omega_equiv_along_intro C x y f l r alpha beta)
  ≡ l;

assert [C : Cat] (x y : τ (Obj C)) (f : τ (Hom C x y))
  (l r : τ (Hom C y x))
  (alpha : τ (@= (Hom C x x)
    (@comp_fapp0 C x y x l f) (@id C x)))
  (beta : τ (@= (Hom C y y)
    (@comp_fapp0 C y x y f r) (@id C y))) ⊢
  @omega_equiv_along_right_inv C x y f
    (@omega_equiv_along_intro C x y f l r alpha beta)
  ≡ r;

assert [C : Cat] (x y : τ (Obj C)) (f : τ (Hom C x y))
  (l r : τ (Hom C y x))
  (alpha : τ (@= (Hom C x x)
    (@comp_fapp0 C x y x l f) (@id C x)))
  (beta : τ (@= (Hom C y y)
    (@comp_fapp0 C y x y f r) (@id C y))) ⊢
  @omega_equiv_along_left_law C x y f
    (@omega_equiv_along_intro C x y f l r alpha beta)
  ≡ alpha;

assert [C : Cat] (x y : τ (Obj C)) (f : τ (Hom C x y))
  (l r : τ (Hom C y x))
  (alpha : τ (@= (Hom C x x)
    (@comp_fapp0 C x y x l f) (@id C x)))
  (beta : τ (@= (Hom C y y)
    (@comp_fapp0 C y x y f r) (@id C y))) ⊢
  @omega_equiv_along_right_law C x y f
    (@omega_equiv_along_intro C x y f l r alpha beta)
  ≡ beta;

// Reflexive evidence exposes both identity inverses and both reflexive laws.
assert [C : Cat] (x : τ (Obj C)) ⊢
  @omega_equiv_along_left_inv C x x (@id C x)
    (@omega_equiv_along_refl C x)
  ≡ @id C x;

assert [C : Cat] (x : τ (Obj C)) ⊢
  @omega_equiv_along_right_inv C x x (@id C x)
    (@omega_equiv_along_refl C x)
  ≡ @id C x;

assert [C : Cat] (x : τ (Obj C)) ⊢
  @omega_equiv_along_left_law C x x (@id C x)
    (@omega_equiv_along_refl C x)
  ≡ @eq_refl (Hom C x x) (@id C x);

assert [C : Cat] (x : τ (Obj C)) ⊢
  @omega_equiv_along_right_law C x x (@id C x)
    (@omega_equiv_along_refl C x)
  ≡ @eq_refl (Hom C x x) (@id C x);

// The public indexed eliminator computes on introduced evidence.
assert [C : Cat] (x y : τ (Obj C)) (f : τ (Hom C x y))
  (l r : τ (Hom C y x))
  (alpha : τ (@= (Hom C x x)
    (@comp_fapp0 C x y x l f) (@id C x)))
  (beta : τ (@= (Hom C y y)
    (@comp_fapp0 C y x y f r) (@id C y))) ⊢
  @omega_equiv_along_ind C x y
    (λ g : τ (Hom C x y),
     λ _ : τ (@OmegaEquivAlong C x y g), Unit_grpd)
    (λ g : τ (Hom C x y),
     λ l' : τ (Hom C y x),
     λ r' : τ (Hom C y x),
     λ _ : τ (@= (Hom C x x)
       (@comp_fapp0 C x y x l' g) (@id C x)),
     λ _ : τ (@= (Hom C y y)
       (@comp_fapp0 C y x y g r') (@id C y)),
     tt)
    f
    (@omega_equiv_along_intro C x y f l r alpha beta)
  ≡ tt;

// A named Cat arrow carries evidence without a first-class repackaging step.
assert [A B : Cat] (F : τ (Functor A B))
  (u : τ (@OmegaEquivAlong Cat_cat A B F)) ⊢
  @omega_equiv_along_left_inv Cat_cat A B F u
  : τ (Functor B A);

// Separate inverse choices remain observably separate.
assertnot [C : Cat] (x y : τ (Obj C)) (f : τ (Hom C x y))
  (l r : τ (Hom C y x))
  (alpha : τ (@= (Hom C x x)
    (@comp_fapp0 C x y x l f) (@id C x)))
  (beta : τ (@= (Hom C y y)
    (@comp_fapp0 C y x y f r) (@id C y))) ⊢
  @omega_equiv_along_left_inv C x y f
    (@omega_equiv_along_intro C x y f l r alpha beta)
  ≡ @omega_equiv_along_right_inv C x y f
    (@omega_equiv_along_intro C x y f l r alpha beta);

// No runtime evidence eta is selected.
assertnot [C : Cat] (x y : τ (Obj C)) (f : τ (Hom C x y))
  (u : τ (@OmegaEquivAlong C x y f)) ⊢
  @omega_equiv_along_intro C x y f
    (@omega_equiv_along_left_inv C x y f u)
    (@omega_equiv_along_right_inv C x y f u)
    (@omega_equiv_along_left_law C x y f u)
    (@omega_equiv_along_right_law C x y f u)
  ≡ u;

// Supplied equality evidence remains observable and is not proof-erased.
assertnot [C : Cat] (x : τ (Obj C))
  (alpha beta : τ (@= (Hom C x x) (@id C x) (@id C x))) ⊢
  @omega_equiv_along_left_law C x x (@id C x)
    (@omega_equiv_along_intro C x x (@id C x)
      (@id C x) (@id C x) alpha beta)
  ≡ @eq_refl (Hom C x x) (@id C x);


// EVOGJ Phase-2 facade, comparison-view, and adapter diagnostics.
assert [C : Cat] (x y : τ (Obj C)) (f : τ (Hom C x y))
  (u : τ (@OmegaEquivAlong C x y f)) ⊢
  @omega_equiv_to C x y
    (@omega_equiv_pack C x y f u)
  ≡ f;

assert [C : Cat] (x y : τ (Obj C)) (f : τ (Hom C x y))
  (u : τ (@OmegaEquivAlong C x y f)) ⊢
  @omega_equiv_evidence C x y
    (@omega_equiv_pack C x y f u)
  ≡ u;

assert [C : Cat] (x y : τ (Obj C)) (f : τ (Hom C x y))
  (u : τ (@OmegaEquivAlong C x y f)) ⊢
  @omega_equiv_ind C x y
    (λ _ : τ (@OmegaEquiv C x y), Unit_grpd)
    (λ g : τ (Hom C x y),
     λ _ : τ (@OmegaEquivAlong C x y g), tt)
    (@omega_equiv_pack C x y f u)
  ≡ tt;

assert [C : Cat] (x : τ (Obj C)) ⊢
  @omega_equiv_to C x x (@omega_equiv_refl C x)
  ≡ @id C x;

assert [C : Cat] (x : τ (Obj C)) ⊢
  @omega_equiv_evidence C x x (@omega_equiv_refl C x)
  ≡ @omega_equiv_along_refl C x;

assert [C : Cat] (x y : τ (Obj C)) (f : τ (Hom C x y))
  (u : τ (@OmegaEquivAlong C x y f)) ⊢
  @omega_equiv_eta C x y
    (@omega_equiv_pack C x y f u)
  ≡ @eq_refl
      (@OmegaEquiv C x y)
      (@omega_equiv_pack C x y f u);

assert [C : Cat] (x y : τ (Obj C)) (f : τ (Hom C x y))
  (u : τ (@OmegaEquivAlong C x y f)) ⊢
  @omega_sigma_to_facade C x y
    (@Struct_sigma
      (Hom C x y)
      (λ g : τ (Hom C x y), @OmegaEquivAlong C x y g)
      f u)
  ≡ @omega_equiv_pack C x y f u;

assert [C : Cat] (x y : τ (Obj C)) (f : τ (Hom C x y))
  (u : τ (@OmegaEquivAlong C x y f)) ⊢
  @omega_facade_to_sigma C x y
    (@omega_equiv_pack C x y f u)
  ≡ @Struct_sigma
      (Hom C x y)
      (λ g : τ (Hom C x y), @OmegaEquivAlong C x y g)
      f u;

assert [C : Cat] (x y : τ (Obj C)) (f : τ (Hom C x y))
  (u : τ (@OmegaEquivAlong C x y f)) ⊢
  @omega_sigma_roundtrip C x y
    (@Struct_sigma
      (Hom C x y)
      (λ g : τ (Hom C x y), @OmegaEquivAlong C x y g)
      f u)
  ≡ @eq_refl
      (@OmegaEquivSigma C x y)
      (@Struct_sigma
        (Hom C x y)
        (λ g : τ (Hom C x y), @OmegaEquivAlong C x y g)
        f u);

assert [C : Cat] (x y : τ (Obj C)) (f : τ (Hom C x y))
  (u : τ (@OmegaEquivAlong C x y f)) ⊢
  @omega_facade_roundtrip C x y
    (@omega_equiv_pack C x y f u)
  ≡ @eq_refl
      (@OmegaEquiv C x y)
      (@omega_equiv_pack C x y f u);

assert [C : Cat] (x y : τ (Obj C))
  (p : τ (@= (Obj C) x y)) ⊢
  @omega_equiv_to C x y
    (@object_path_equiv C x y p)
  ≡ @path_to_hom C x y p;

assert [C : Cat] (x y : τ (Obj C))
  (p : τ (@= (Obj C) x y)) ⊢
  @omega_equiv_evidence C x y
    (@object_path_equiv C x y p)
  ≡ @object_path_equiv_along C x y p;

assert [C : Cat] (x y : τ (Obj C))
  (p : τ (@= (Obj C) x y)) ⊢
  @omega_equiv_along_left_inv
    C x y
    (@path_to_hom C x y p)
    (@object_path_equiv_along C x y p)
  ≡ @path_to_hom C y x (@path_sym (Obj C) x y p);

assert [C : Cat] (x y : τ (Obj C))
  (p : τ (@= (Obj C) x y)) ⊢
  @omega_equiv_along_right_inv
    C x y
    (@path_to_hom C x y p)
    (@object_path_equiv_along C x y p)
  ≡ @path_to_hom C y x (@path_sym (Obj C) x y p);

assert [C : Cat] (x y : τ (Obj C))
  (p : τ (@= (Obj C) x y)) ⊢
  @omega_equiv_along_left_law
    C x y
    (@path_to_hom C x y p)
    (@object_path_equiv_along C x y p)
  ≡ @object_path_equiv_left_law C x y p;

assert [C : Cat] (x y : τ (Obj C))
  (p : τ (@= (Obj C) x y)) ⊢
  @omega_equiv_along_right_law
    C x y
    (@path_to_hom C x y p)
    (@object_path_equiv_along C x y p)
  ≡ @object_path_equiv_right_law C x y p;

assert [C : Cat] (x : τ (Obj C)) ⊢
  @object_path_equiv_left_law C x x (@eq_refl (Obj C) x)
  ≡ @eq_refl (Hom C x x) (@id C x);

assert [C : Cat] (x : τ (Obj C)) ⊢
  @object_path_equiv_right_law C x x (@eq_refl (Obj C) x)
  ≡ @eq_refl (Hom C x x) (@id C x);

// Ordinary isomorphism evidence has a direct one-way native equality-valued lift.
assert [C : Cat]
  [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y)) ⊢
  @iso_evidence_omega_equiv C x y i
  : τ (@OmegaEquiv C x y);

assert [C : Cat]
  [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y)) ⊢
  @omega_equiv_to C x y
    (@iso_evidence_omega_equiv C x y i)
  ≡ @iso_evidence_to C x y i;

assert [C : Cat]
  [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y)) ⊢
  @omega_equiv_along_left_inv
    C x y
    (@iso_evidence_to C x y i)
    (@omega_equiv_evidence C x y
      (@iso_evidence_omega_equiv C x y i))
  ≡ @iso_evidence_from C x y i;

assert [C : Cat]
  [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y)) ⊢
  @omega_equiv_along_right_law
    C x y
    (@iso_evidence_to C x y i)
    (@omega_equiv_evidence C x y
      (@iso_evidence_omega_equiv C x y i))
  ≡ @iso_evidence_right C x y i;

// The stable cast is not a package decoder: explicit native reflexivity keeps
// provenance distinct from the raw equality constructor.
assertnot [C : Cat]
  (x : τ (Obj C)) ⊢
  @omega_cast_to_object_path C x x
    (@iso_evidence_omega_equiv C x x
      (@iso_evidence_refl C x))
  ≡ @eq_refl (Obj C) x;

// The stable facade is intentionally not runtime-transparent Sigma data.
assertnot [C : Cat] (x y : τ (Obj C)) ⊢
  @OmegaEquiv C x y
  ≡ @OmegaEquivSigma C x y;

// Eta is propositional, not a runtime package collapse.
assertnot [C : Cat] (x y : τ (Obj C))
  (e : τ (@OmegaEquiv C x y)) ⊢
  @omega_equiv_pack
    C x y
    (@omega_equiv_to C x y e)
    (@omega_equiv_evidence C x y e)
  ≡ e;

// No generic equality/equivalence classifier comparison is promoted here.
assertnot [C : Cat] (x y : τ (Obj C)) ⊢
  @= (Obj C) x y
  ≡ @OmegaEquiv C x y;

// Elimination computes only when the facade constructor is exposed.
assertnot [C : Cat] (x y : τ (Obj C))
  (e : τ (@OmegaEquiv C x y)) ⊢
  @omega_equiv_ind C x y
    (λ _ : τ (@OmegaEquiv C x y), Unit_grpd)
    (λ g : τ (Hom C x y),
     λ _ : τ (@OmegaEquivAlong C x y g), tt)
    e
  ≡ tt;

// EVOGJ Phase-3 literal-path and canonical-groupoidality diagnostics.
assert [A : Grpd] (x y : τ A)
  (p : τ (@= A x y)) ⊢
  p : τ (@OmegaEquiv (Path_cat A) x y);

assert [A : Grpd] (x y : τ A)
  (e : τ (@OmegaEquiv (Path_cat A) x y)) ⊢
  e : τ (@= A x y);

// The shaped join is proof-time only.
assertnot [A : Grpd] (x y : τ A) ⊢
  @OmegaEquiv (Path_cat A) x y
  ≡ @= A x y;

assert [A : Grpd] (x y : τ A)
  (p : τ (@= A x y)) ⊢
  @omega_equiv_to (Path_cat A) x y
    (@path_equiv A x y p)
  ≡ p;

assert [A : Grpd] (x y : τ A)
  (p : τ (@= A x y)) ⊢
  @omega_equiv_evidence (Path_cat A) x y
    (@path_equiv A x y p)
  ≡ @path_equiv_along A x y p;

assert [A : Grpd] (x y : τ A)
  (p : τ (@= A x y)) ⊢
  @omega_equiv_along_left_inv
    (Path_cat A) x y p
    (@path_equiv_along A x y p)
  ≡ @path_sym A x y p;

assert [A : Grpd] (x y : τ A)
  (p : τ (@= A x y)) ⊢
  @omega_equiv_along_right_inv
    (Path_cat A) x y p
    (@path_equiv_along A x y p)
  ≡ @path_sym A x y p;

assert [A : Grpd] (x y : τ A)
  (p : τ (@= A x y)) ⊢
  @omega_equiv_along_left_law
    (Path_cat A) x y p
    (@path_equiv_along A x y p)
  ≡ @path_equiv_left_law A x y p;

assert [A : Grpd] (x y : τ A)
  (p : τ (@= A x y)) ⊢
  @omega_equiv_along_right_law
    (Path_cat A) x y p
    (@path_equiv_along A x y p)
  ≡ @path_equiv_right_law A x y p;

assert [A : Grpd] (x : τ A) ⊢
  @path_equiv_left_law A x x (@eq_refl A x)
  ≡ @eq_refl
      (Hom (Path_cat A) x x)
      (@id (Path_cat A) x);

assert [A : Grpd] (x : τ A) ⊢
  @path_equiv_right_law A x x (@eq_refl A x)
  ≡ @eq_refl
      (Hom (Path_cat A) x x)
      (@id (Path_cat A) x);

// The facade eliminator consumes the explicit path package and returns its
// selected literal path.
assert [A : Grpd] (x y : τ A)
  (p : τ (@= A x y)) ⊢
  @omega_equiv_ind
    (Path_cat A) x y
    (λ _ : τ (@OmegaEquiv (Path_cat A) x y), @= A x y)
    (λ f : τ (Hom (Path_cat A) x y),
     λ _ : τ (@OmegaEquivAlong (Path_cat A) x y f), f)
    (@path_equiv A x y p)
  ≡ p;

// The left cancellation path can itself be reified and observed one hom
// dimension higher through the general object-path adapter.
assert [A : Grpd] (x y : τ A)
  (p : τ (@= A x y)) ⊢
  @omega_equiv_to
    (Hom_cat (Path_cat A) x x)
    (@comp_fapp0
      (Path_cat A) x y x
      (@path_sym A x y p)
      p)
    (@id (Path_cat A) x)
    (@object_path_equiv
      (Hom_cat (Path_cat A) x x)
      (@comp_fapp0
        (Path_cat A) x y x
        (@path_sym A x y p)
        p)
      (@id (Path_cat A) x)
      (@path_equiv_left_law A x y p))
  ≡ @path_to_hom
      (Hom_cat (Path_cat A) x x)
      (@comp_fapp0
        (Path_cat A) x y x
        (@path_sym A x y p)
        p)
      (@id (Path_cat A) x)
      (@path_equiv_left_law A x y p);

// Typed reflexivity exercises the Core-inclusion proof-time comparison.
assert [A : Grpd] ⊢
  @eq_refl
    (Hom Cat_cat (Path_cat A) (Path_cat A))
    (@Core_incl_func (Path_cat A))
  : τ (@=
      (Hom Cat_cat (Path_cat A) (Path_cat A))
      (@Core_incl_func (Path_cat A))
      (@id Cat_cat (Path_cat A)));

assert [A : Grpd] ⊢
  @path_cat_is_groupoidal A
  : τ (@IsGroupoidalCat (Path_cat A));

assert [A : Grpd] ⊢
  @omega_equiv_along_left_inv
    Cat_cat
    (Core_cat (Path_cat A))
    (Path_cat A)
    (Core_incl_func (Path_cat A))
    (@path_cat_is_groupoidal A)
  ≡ @id Cat_cat (Path_cat A);

assert [A : Grpd] ⊢
  @omega_equiv_along_right_inv
    Cat_cat
    (Core_cat (Path_cat A))
    (Path_cat A)
    (Core_incl_func (Path_cat A))
    (@path_cat_is_groupoidal A)
  ≡ @id Cat_cat (Path_cat A);

assert [A : Grpd] ⊢
  @omega_equiv_along_left_law
    Cat_cat
    (Core_cat (Path_cat A))
    (Path_cat A)
    (Core_incl_func (Path_cat A))
    (@path_cat_is_groupoidal A)
  ≡ @eq_refl
      (Hom Cat_cat (Path_cat A) (Path_cat A))
      (@id Cat_cat (Path_cat A));

// No raw-path observer or package erasure is selected.
assertnot [A : Grpd] (x y : τ A)
  (p : τ (@= A x y)) ⊢
  @omega_equiv_to (Path_cat A) x y p
  ≡ p;

assertnot [A : Grpd] (x y : τ A)
  (p : τ (@= A x y)) ⊢
  @path_equiv A x y p
  ≡ p;

// Core inclusion and identity compare only at proof time.
assertnot [A : Grpd] ⊢
  @Core_incl_func (Path_cat A)
  ≡ @id Cat_cat (Path_cat A);

// The literal path join does not promote generic all-category univalence.
assertnot [C : Cat] (x y : τ (Obj C)) ⊢
  @= (Obj C) x y
  ≡ @OmegaEquiv C x y;

// A facade reflexivity package accepted as a literal path is not primitive
// equality reflexivity, so raw J does not acquire a new beta rule.
assertnot [A : Grpd] (x : τ A) ⊢
  @ind_eqr
    A
    x
    (λ z : τ A, λ _ : τ (@= A z x), Unit_grpd)
    tt
    x
    (@omega_equiv_refl (Path_cat A) x)
  ≡ tt;

// EVOGJ Phase-4 Grpd_cat function-path boundary and explicit bridges.
assert [A B : Grpd] ⊢
  Hom_cat Grpd_cat A B
  ≡ Path_cat (@Function_grpd A B);

assertnot [A : Grpd] ⊢
  @id Grpd_cat A
  ≡ λ a : τ A, a;

assert [A : Grpd] ⊢
  @grpd_id_function A
  ≡ λ a : τ A, a;

// Typed reflexivity exercises the proof-time identity comparison.
assert [A : Grpd] ⊢
  @eq_refl (@Function_grpd A A) (@id Grpd_cat A)
  : τ (@= (@Function_grpd A A)
      (@id Grpd_cat A)
      (@grpd_id_function A));

// G2 adds only capped application, not a whole-term composition rewrite.
// With eta_equality enabled, that pointwise computation is nevertheless
// observable as conversion with the corresponding lambda.
assert [A B C : Grpd]
  (f : τ A → τ B)
  (g : τ B → τ C) ⊢
  @comp_fapp0 Grpd_cat A B C g f
  ≡ λ a : τ A, g (f a);

assert [A B C : Grpd]
  (f : τ A → τ B)
  (g : τ B → τ C) ⊢
  @grpd_comp_function A B C g f
  ≡ λ a : τ A, g (f a);

// Typed reflexivity exercises the proof-time composition comparison.
assert [A B C : Grpd]
  (f : τ A → τ B)
  (g : τ B → τ C) ⊢
  @eq_refl (@Function_grpd A C)
    (@comp_fapp0 Grpd_cat A B C g f)
  : τ (@= (@Function_grpd A C)
      (@comp_fapp0 Grpd_cat A B C g f)
      (@grpd_comp_function A B C g f));

assert [A B : Grpd] (e : τ (TypeEquiv A B)) ⊢
  @omega_equiv_to Grpd_cat A B
    (@type_equiv_to_omega A B e)
  ≡ @type_equiv_to A B e;

assert [A B : Grpd] (e : τ (TypeEquiv A B)) ⊢
  @omega_equiv_evidence Grpd_cat A B
    (@type_equiv_to_omega A B e)
  ≡ @omega_equiv_along_intro
      Grpd_cat A B
      (@type_equiv_to A B e)
      (λ b : τ B, @type_equiv_from A B e b)
      (λ b : τ B, @type_equiv_from A B e b)
      (@type_equiv_omega_left_law A B e)
      (@type_equiv_omega_right_law A B e);

assert [A B : Grpd] (e : τ (TypeEquiv A B)) ⊢
  @omega_equiv_along_left_inv
    Grpd_cat A B (@type_equiv_to A B e)
    (@omega_equiv_evidence Grpd_cat A B
      (@type_equiv_to_omega A B e))
  ≡ λ b : τ B, @type_equiv_from A B e b;

assert [A B : Grpd] (e : τ (TypeEquiv A B)) ⊢
  @omega_equiv_along_right_inv
    Grpd_cat A B (@type_equiv_to A B e)
    (@omega_equiv_evidence Grpd_cat A B
      (@type_equiv_to_omega A B e))
  ≡ λ b : τ B, @type_equiv_from A B e b;

assert [A B : Grpd] (e : τ (TypeEquiv A B)) ⊢
  @omega_equiv_along_left_law
    Grpd_cat A B (@type_equiv_to A B e)
    (@omega_equiv_evidence Grpd_cat A B
      (@type_equiv_to_omega A B e))
  ≡ @type_equiv_omega_left_law A B e;

assert [A B : Grpd] (e : τ (TypeEquiv A B)) ⊢
  @omega_equiv_along_right_law
    Grpd_cat A B (@type_equiv_to A B e)
    (@omega_equiv_evidence Grpd_cat A B
      (@type_equiv_to_omega A B e))
  ≡ @type_equiv_omega_right_law A B e;

assert [A B : Grpd]
  (f : τ (@Function_grpd A B))
  (u : τ (@OmegaEquivAlong Grpd_cat A B f)) ⊢
  @type_equiv_to A B
    (@omega_along_to_type_equiv A B f u)
  ≡ f;

assert [A B : Grpd]
  (f : τ (@Function_grpd A B))
  (u : τ (@OmegaEquivAlong Grpd_cat A B f)) ⊢
  @type_equiv_is_equiv A B
    (@omega_along_to_type_equiv A B f u)
  ≡ @omega_grpd_is_equiv A B f u;

assert [A B : Grpd]
  (f : τ (@Function_grpd A B))
  (u : τ (@OmegaEquivAlong Grpd_cat A B f))
  (b : τ B) ⊢
  @type_equiv_from A B
    (@omega_along_to_type_equiv A B f u)
    b
  ≡ (@omega_equiv_along_left_inv Grpd_cat A B f u) b;

assert [A B : Grpd]
  (f : τ (@Function_grpd A B))
  (u : τ (@OmegaEquivAlong Grpd_cat A B f))
  (b : τ B) ⊢
  @type_equiv_right A B
    (@omega_along_to_type_equiv A B f u)
    b
  ≡ @omega_grpd_left_right_point A B f u b;

assert [A B : Grpd]
  (f : τ (@Function_grpd A B))
  (u : τ (@OmegaEquivAlong Grpd_cat A B f)) ⊢
  @type_equiv_to A B
    (@omega_to_type_equiv A B
      (@omega_equiv_pack Grpd_cat A B f u))
  ≡ f;

assert [A B : Grpd] (e : τ (TypeEquiv A B)) ⊢
  @type_equiv_to A B
    (@omega_to_type_equiv A B
      (@type_equiv_to_omega A B e))
  ≡ @type_equiv_to A B e;

// Phase 6 retargets rigid groupoid-universe equality to the equality-valued facade.
assert [A B : Grpd] ⊢
  @= Grpd_grpd A B
  ≡ @OmegaEquiv Grpd_cat A B;

assertnot [A B : Grpd] ⊢
  @= Grpd_grpd A B
  ≡ @GrpdPathView A B;

// Neither bridge currently supplies definitional package eta.
assertnot [A B : Grpd] (e : τ (TypeEquiv A B)) ⊢
  @omega_to_type_equiv A B
    (@type_equiv_to_omega A B e)
  ≡ e;

assertnot [A B : Grpd]
  (e : τ (@OmegaEquiv Grpd_cat A B)) ⊢
  @type_equiv_to_omega A B
    (@omega_to_type_equiv A B e)
  ≡ e;

// The selected fibre centre computes, but its contraction field remains the
// pre-existing opaque `is_equiv_map_by_inverse` theorem data.
assertnot [A B : Grpd]
  (f : τ (@Function_grpd A B))
  (u : τ (@OmegaEquivAlong Grpd_cat A B f))
  (b : τ B) ⊢
  (sigma_Snd (@omega_grpd_is_equiv A B f u b))
    (sigma_Fst (@omega_grpd_is_equiv A B f u b))
  ≡ @eq_refl
      (@HFiber A B f b)
      (sigma_Fst (@omega_grpd_is_equiv A B f u b));

// catalog-area: Abstract direct univalence and reduced-former boundary

// Typed reflexivity exercises the abstract proof-time comparison in both
// directions; the classifiers remain runtime-distinct for a variable C.
assert [C : Cat] (x y : τ (Obj C))
  (p : τ (@= (Obj C) x y)) ⊢
  @eq_refl (@OmegaEquiv C x y) p
  : τ (@= (@OmegaEquiv C x y) p p);

assert [C : Cat] (x y : τ (Obj C))
  (e : τ (@OmegaEquiv C x y)) ⊢
  @eq_refl (@= (Obj C) x y) e
  : τ (@= (@= (Obj C) x y) e e);

assertnot [C : Cat] (x y : τ (Obj C)) ⊢
  @= (Obj C) x y
  ≡ @OmegaEquiv C x y;

// Some constructors retain the abstract owner until elaboration.
assert [K : Cat] (E : τ (Catd K))
  (x y : τ (Obj (@Sigma_cat K E)))
  (p : τ (@= (Obj (@Sigma_cat K E)) x y)) ⊢
  @eq_refl (@OmegaEquiv (@Sigma_cat K E) x y) p
  : τ (@= (@OmegaEquiv (@Sigma_cat K E) x y) p p);

assert [A B : Cat]
  (F G : τ (Obj (Functor_cat A B)))
  (p : τ (@= (Obj (Functor_cat A B)) F G)) ⊢
  @eq_refl (@OmegaEquiv (Functor_cat A B) F G) p
  : τ (@= (@OmegaEquiv (Functor_cat A B) F G) p p);

// The general stable carrier view supports explicit transparent casts in both
// directions without relying on transitivity of unification hints.
assert [C : Cat] (x y : τ (Obj C)) ⊢
  τ (@ObjectPathCastView C x y)
  ≡ τ (@= (Obj C) x y);

assertnot [C : Cat] (x y : τ (Obj C)) ⊢
  @ObjectPathCastView C x y
  ≡ @= (Obj C) x y;

assertnot [C : Cat] (x y : τ (Obj C)) ⊢
  @ObjectPathCastView C x y
  ≡ @OmegaEquiv C x y;

assert [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (@= (Obj C) x y)) ⊢
  @omega_cast_to_object_path C x y
    (@object_path_cast_to_omega C x y p)
  ≡ p;

assert [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (@OmegaEquiv C x y)) ⊢
  @object_path_cast_to_omega C x y
    (@omega_cast_to_object_path C x y e)
  ≡ e;

assert [A B : Grpd]
  (p : τ (@= (Obj Grpd_cat) A B)) ⊢
  @omega_cast_to_object_path Grpd_cat A B
    (@object_path_cast_to_omega Grpd_cat A B p)
  ≡ p;

assert [A B : Cat]
  (p : τ (@= (Obj Cat_cat) A B)) ⊢
  @omega_cast_to_object_path Cat_cat A B
    (@object_path_cast_to_omega Cat_cat A B p)
  ≡ p;

// Product object equality now retains a stable path classifier. Proof-time
// interchange is available, and the public casts are transparent identities;
// raw terms still do not acquire facade-observer computation.
assert [A B : Cat] ⊢
  Obj (Product_cat A B)
  ≡ Product_grpd (Obj A) (Obj B);

assert [A B : Cat]
  (x y : τ (Obj (Product_cat A B))) ⊢
  @= (Obj (Product_cat A B)) x y
  ≡ @ProductPathView (Obj A) (Obj B) x y;

assert [A B : Cat]
  (x y : τ (Obj (Product_cat A B)))
  (p : τ (@= (Obj (Product_cat A B)) x y)) ⊢
  p : τ (@OmegaEquiv (Product_cat A B) x y);

assert [A B : Cat]
  [x y : τ (Obj (Product_cat A B))]
  (p : τ (@= (Obj (Product_cat A B)) x y)) ⊢
  @product_omega_as_path A B x y
    (@product_path_as_omega A B x y p)
  ≡ p;

assert [A B : Cat]
  [x y : τ (Obj (Product_cat A B))]
  (e : τ (@OmegaEquiv (Product_cat A B) x y)) ⊢
  @product_path_as_omega A B x y
    (@product_omega_as_path A B x y e)
  ≡ e;

assertnot [A B : Cat]
  (x y : τ (Obj (Product_cat A B))) ⊢
  @= (Obj (Product_cat A B)) x y
  ≡ @OmegaEquiv (Product_cat A B) x y;

assertnot [A B : Cat]
  [x y : τ (Obj (Product_cat A B))]
  (p : τ (@= (Obj (Product_cat A B)) x y)) ⊢
  @omega_equiv_to
    (Product_cat A B) x y
    (@product_path_as_omega A B x y p)
  ≡ @path_to_hom (Product_cat A B) x y p;

assert [A B : Cat]
  (x y : τ (Obj (Product_cat A B)))
  (p : τ (@= (Obj (Product_cat A B)) x y)) ⊢
  @omega_equiv_to
    (Product_cat A B) x y
    (@object_path_equiv (Product_cat A B) x y p)
  ≡ @path_to_hom (Product_cat A B) x y p;

// Opposite object equality still erases its category head. Its compatibility
// names use the general explicit cast; raw interchange remains unavailable.
assertnot [A : Cat]
  (x y : τ (Obj (Op_cat A)))
  (p : τ (@= (Obj (Op_cat A)) x y)) ⊢
  p : τ (@OmegaEquiv (Op_cat A) x y);

assert [A : Cat]
  [x y : τ (Obj A)]
  (p : τ (@= (Obj A) x y)) ⊢
  @op_omega_as_path A x y
    (@op_path_as_omega A x y p)
  ≡ p;

assert [A : Cat]
  [x y : τ (Obj A)]
  (e : τ (@OmegaEquiv (Op_cat A) x y)) ⊢
  @op_path_as_omega A x y
    (@op_omega_as_path A x y e)
  ≡ e;

assert [A B : Cat]
  [x y : τ (Obj (Product_cat A B))]
  (p : τ (@= (Obj (Product_cat A B)) x y)) ⊢
  @op_omega_as_path (Product_cat A B) x y
    (@op_path_as_omega (Product_cat A B) x y p)
  ≡ p;

assert [A : Grpd]
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @op_omega_as_path (Path_cat A) x y
    (@op_path_as_omega (Path_cat A) x y p)
  ≡ p;

assertnot [A : Cat]
  [x y : τ (Obj A)]
  (p : τ (@= (Obj A) x y)) ⊢
  @omega_equiv_to
    (Op_cat A) x y
    (@op_path_as_omega A x y p)
  ≡ @path_to_hom (Op_cat A) x y p;

assert [A : Cat]
  (x y : τ (Obj (Op_cat A)))
  (p : τ (@= (Obj (Op_cat A)) x y)) ⊢
  @omega_equiv_to
    (Op_cat A) x y
    (@object_path_equiv (Op_cat A) x y p)
  ≡ @path_to_hom (Op_cat A) x y p;

// Proof-time interchange does not add observers to a raw abstract path.
assertnot [C : Cat] (x y : τ (Obj C))
  (p : τ (@= (Obj C) x y)) ⊢
  @omega_equiv_to C x y p
  ≡ @path_to_hom C x y p;

// catalog-area: Internal groupoidality and structured J
assert [C : Cat]
  (g : τ (@IsGroupoidalCat C))
  (x y : τ (Obj C)) ⊢
  @groupoidal_core_homwise C g x y
  : τ (@OmegaEquivAlong
      Cat_cat
      (Path_cat (@= (Obj C) x y))
      (Hom_cat C x y)
      (@core_incl_hom_func C x y));

assert [C : Cat]
  (g : τ (@IsGroupoidalCat C))
  (x y : τ (Obj C)) ⊢
  @groupoidal_arrow_to_path_func C g x y
  : τ (Functor
      (Hom_cat C x y)
      (Path_cat (@= (Obj C) x y)));

assert [C : Cat]
  (g : τ (@IsGroupoidalCat C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @groupoidal_arrow_to_path C g x y f
  : τ (@= (Obj C) x y);

assert [C : Cat]
  (g : τ (@IsGroupoidalCat C))
  (x y : τ (Obj C)) ⊢
  @groupoidal_arrow_section C g x y
  : τ (@=
      (Hom Cat_cat (Hom_cat C x y) (Hom_cat C x y))
      (@comp_fapp0
        Cat_cat
        (Hom_cat C x y)
        (Path_cat (@= (Obj C) x y))
        (Hom_cat C x y)
        (@core_incl_hom_func C x y)
        (@groupoidal_arrow_to_path_func C g x y))
      (@id Cat_cat (Hom_cat C x y)));

assert [C : Cat]
  (g : τ (@IsGroupoidalCat C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @groupoidal_path_to_arrow_retract C g x y f
  : τ (@=
      (Hom C x y)
      (@fapp0
        (Path_cat (@= (Obj C) x y))
        (Hom_cat C x y)
        (@core_incl_hom_func C x y)
        (@groupoidal_arrow_to_path C g x y f))
      f);

// Ordinary functor action preserves native fixed-arrow equality-valued evidence, with
// computational inverse projections inherited from the explicit package.
assert [A B : Cat]
  (F : τ (Functor A B))
  [x y : τ (Obj A)]
  [f : τ (Hom A x y)]
  (u : τ (@OmegaEquivAlong A x y f)) ⊢
  @omega_equiv_along_fapp1_fapp0 A B F x y f u
  : τ (@OmegaEquivAlong
      B
      (@fapp0 A B F x)
      (@fapp0 A B F y)
      (@fapp1_fapp0 A B F x y f));

assert [A B : Cat]
  (F : τ (Functor A B))
  [x y : τ (Obj A)]
  [f : τ (Hom A x y)]
  (u : τ (@OmegaEquivAlong A x y f)) ⊢
  @omega_equiv_along_left_inv
    B
    (@fapp0 A B F x)
    (@fapp0 A B F y)
    (@fapp1_fapp0 A B F x y f)
    (@omega_equiv_along_fapp1_fapp0 A B F x y f u)
  ≡ @fapp1_fapp0 A B F y x
      (@omega_equiv_along_left_inv A x y f u);

assert [A B : Cat]
  (F : τ (Functor A B))
  [x y : τ (Obj A)]
  [f : τ (Hom A x y)]
  (u : τ (@OmegaEquivAlong A x y f)) ⊢
  @omega_equiv_along_right_inv
    B
    (@fapp0 A B F x)
    (@fapp0 A B F y)
    (@fapp1_fapp0 A B F x y f)
    (@omega_equiv_along_fapp1_fapp0 A B F x y f u)
  ≡ @fapp1_fapp0 A B F y x
      (@omega_equiv_along_right_inv A x y f u);

// Internal groupoidality reconstructs explicit native equivalence evidence
// for every directed arrow, rather than assuming an opaque decoder.
assert [C : Cat]
  (g : τ (@IsGroupoidalCat C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @groupoidal_arrow_equiv_along C g x y f
  : τ (@OmegaEquivAlong C x y f);

assert [C : Cat]
  (g : τ (@IsGroupoidalCat C)) ⊢
  @groupoidal_all_arrows_equiv C g
  : τ (@AllArrowsEquiv C);

assert [C : Cat]
  (g : τ (@IsGroupoidalCat C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @groupoidal_all_arrows_equiv C g x y f
  ≡ @groupoidal_arrow_equiv_along C g x y f;

assert [C : Cat]
  (g : τ (@IsGroupoidalCat C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @omega_equiv_along_left_inv C x y f
    (@groupoidal_arrow_equiv_along C g x y f)
  ≡ @groupoidal_arrow_inverse C g x y f;

assert [C : Cat]
  (g : τ (@IsGroupoidalCat C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @groupoidal_arrow_left_law C g x y f
  : τ (@=
      (Hom C x x)
      (@comp_fapp0 C x y x
        (@groupoidal_arrow_inverse C g x y f)
        f)
      (@id C x));

assert [C : Cat]
  (g : τ (@IsGroupoidalCat C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @groupoidal_arrow_right_law C g x y f
  : τ (@=
      (Hom C y y)
      (@comp_fapp0 C y x y
        f
        (@groupoidal_arrow_inverse C g x y f))
      (@id C y));

// The existing displayed action along a groupoidal arrow is therefore an
// equivalence of fibres, with its inverse given by action on the chosen arrow.
assert [C : Cat]
  (g : τ (@IsGroupoidalCat C))
  (D : τ (Catd C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @groupoidal_fibre_transport_equiv C g D x y f
  : τ (@OmegaEquivAlong
      Cat_cat
      (Fibre_cat D x)
      (Fibre_cat D y)
      (@fapp1_fapp0 C Cat_cat D x y f));

assert [C : Cat]
  (g : τ (@IsGroupoidalCat C))
  (D : τ (Catd C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @omega_equiv_along_left_inv
    Cat_cat
    (Fibre_cat D x)
    (Fibre_cat D y)
    (@fapp1_fapp0 C Cat_cat D x y f)
    (@groupoidal_fibre_transport_equiv C g D x y f)
  ≡ @fapp1_fapp0 C Cat_cat D y x
      (@groupoidal_arrow_inverse C g x y f);

// Existing discrete evidence, and therefore every packaged zero-category,
// gives a nonliteral internally groupoidal consumer.
assert [C : Cat]
  (d : τ (IsDiscreteCat C)) ⊢
  @discrete_cat_is_groupoidal C d
  : τ (@IsGroupoidalCat C);

assert (X : τ ZeroCat) ⊢
  @zero_cat_is_groupoidal X
  : τ (@IsGroupoidalCat (@ncat_carrier cat_zero X));

// The generic homwise consumer specializes to a literal path category, but
// its general half-adjoint inverse is not the direct path-package computation.
assert [A : Grpd]
  [x y : τ A] ⊢
  @groupoidal_core_homwise
    (Path_cat A)
    (@path_cat_is_groupoidal A)
    x
    y
  : τ (@OmegaEquivAlong
      Cat_cat
      (Hom_cat (Core_cat (Path_cat A)) x y)
      (Hom_cat (Path_cat A) x y)
      (@fapp1_func
        (Core_cat (Path_cat A))
        (Path_cat A)
        (@Core_incl_func (Path_cat A))
        x
        y));

assertnot [A : Grpd]
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @groupoidal_arrow_to_path
    (Path_cat A)
    (@path_cat_is_groupoidal A)
    x
    y
    p
  ≡ p;

// A structured motive uses the existing directed `path_ind_sec`; no second
// groupoidal eliminator or raw-fibrancy capability is introduced.
assert [C : Cat]
  (g : τ (@IsGroupoidalCat C))
  (D : τ (Catd C))
  (x : τ (Obj C))
  (u : τ (Obj (Fibre_cat D x))) ⊢
  @path_ind_sec
    C
    x
    (@Sigma_proj1_pullback_catd C (@Rep_catd C x) D)
    u
  ≡ @fib_cov_transf C D x u;

// At a literal path source, the existing displayed action agrees with
// primitive right-J transport through ordinary path induction.
assert [A : Grpd]
  (D : τ (Catd (Path_cat A)))
  [x y : τ A]
  (u : τ (Obj (Fibre_cat D x)))
  (p : τ (@= A x y)) ⊢
  @path_cat_structured_transport_agrees_ind_eqr A D x y u p
  : τ (@=
      (Obj (Fibre_cat D y))
      (@path_cat_structured_transport A D x y u p)
      (@path_cat_ind_eqr_transport A D x y u p));

assert [A : Grpd]
  (D : τ (Catd (Path_cat A)))
  [x y : τ A]
  (u : τ (Obj (Fibre_cat D x)))
  (p : τ (@= A x y)) ⊢
  @path_cat_path_ind_app_agrees_structured A D x y u p
  : τ (@=
      (Obj (Fibre_cat D y))
      (@path_cat_path_ind_app A D x y u p)
      (@path_cat_structured_transport A D x y u p));

assert [A : Grpd]
  (D : τ (Catd (Path_cat A)))
  [x y : τ A]
  (u : τ (Obj (Fibre_cat D x)))
  (p : τ (@= A x y)) ⊢
  @path_cat_path_ind_app_agrees_ind_eqr A D x y u p
  : τ (@=
      (Obj (Fibre_cat D y))
      (@path_cat_path_ind_app A D x y u p)
      (@path_cat_ind_eqr_transport A D x y u p));

// Primitive J computes at reflexivity. The structured presentation and the
// existing section application remain propositionally, not definitionally,
// equal there because their proof-time joins do not select runtime folds.
assert [A : Grpd]
  (D : τ (Catd (Path_cat A)))
  (x : τ A)
  (u : τ (Obj (Fibre_cat D x))) ⊢
  @path_cat_ind_eqr_transport A D x x u (@eq_refl A x)
  ≡ u;

assertnot [A : Grpd]
  (D : τ (Catd (Path_cat A)))
  (x : τ A)
  (u : τ (Obj (Fibre_cat D x))) ⊢
  @path_cat_structured_transport A D x x u (@eq_refl A x)
  ≡ u;

assertnot [A : Grpd]
  (D : τ (Catd (Path_cat A)))
  (x : τ A)
  (u : τ (Obj (Fibre_cat D x))) ⊢
  @path_cat_path_ind_app A D x x u (@eq_refl A x)
  ≡ u;

// The path-category identity join is proof-time only.
assert [A : Grpd]
  (D : τ (Catd (Path_cat A)))
  (x : τ A) ⊢
  @eq_refl
    (Hom Cat_cat (Fibre_cat D x) (Fibre_cat D x))
    (@fapp1_fapp0
      (Path_cat A) Cat_cat D x x (@eq_refl A x))
  : τ (@=
      (Hom Cat_cat (Fibre_cat D x) (Fibre_cat D x))
      (@fapp1_fapp0
        (Path_cat A) Cat_cat D x x (@eq_refl A x))
      (@id Cat_cat (Fibre_cat D x)));

assertnot [A : Grpd]
  (D : τ (Catd (Path_cat A)))
  (x : τ A) ⊢
  @fapp1_fapp0
    (Path_cat A) Cat_cat D x x (@eq_refl A x)
  ≡ @id Cat_cat (Fibre_cat D x);

// The reflexive uncurried component join is likewise proof-time only.
assert [A : Grpd]
  (D : τ (Catd (Path_cat A)))
  (x : τ A)
  (u : τ (Obj (Fibre_cat D x))) ⊢
  @eq_refl
    (Hom Cat_cat Terminal_cat (Fibre_cat D x))
    (@tapp0_fapp0
      (@PathOut_cat (Path_cat A) x)
      Cat_cat
      (@Const_catd (@PathOut_cat (Path_cat A) x) Terminal_cat)
      (@Sigma_proj1_pullback_catd
        (Path_cat A)
        (@Rep_catd (Path_cat A) x)
        D)
      (@pathout_obj (Path_cat A) x x (@eq_refl A x))
      (@fib_cov_transf (Path_cat A) D x u))
  : τ (@=
      (Hom Cat_cat Terminal_cat (Fibre_cat D x))
      (@tapp0_fapp0
        (@PathOut_cat (Path_cat A) x)
        Cat_cat
        (@Const_catd (@PathOut_cat (Path_cat A) x) Terminal_cat)
        (@Sigma_proj1_pullback_catd
          (Path_cat A)
          (@Rep_catd (Path_cat A) x)
          D)
        (@pathout_obj (Path_cat A) x x (@eq_refl A x))
        (@fib_cov_transf (Path_cat A) D x u))
      (@Obj_func (Fibre_cat D x) u));

assertnot [A : Grpd]
  (D : τ (Catd (Path_cat A)))
  (x : τ A)
  (u : τ (Obj (Fibre_cat D x))) ⊢
  @tapp0_fapp0
      (@PathOut_cat (Path_cat A) x)
      Cat_cat
      (@Const_catd (@PathOut_cat (Path_cat A) x) Terminal_cat)
      (@Sigma_proj1_pullback_catd
        (Path_cat A)
        (@Rep_catd (Path_cat A) x)
        D)
      (@pathout_obj (Path_cat A) x x (@eq_refl A x))
      (@fib_cov_transf (Path_cat A) D x u)
  ≡ @Obj_func (Fibre_cat D x) u;

// Phase 9 discrete-category core and homwise adequacy.
// catalog-area: Discrete category core-inclusion adequacy
assert [C : Cat] ⊢
  IsDiscreteCat C
  ≡ @Product_grpd
      (IsSetGrpd (Obj C))
      (@IsGroupoidalCat C);

assert [C : Cat]
  (obj_set : τ (IsSetGrpd (Obj C)))
  (core_equiv : τ (@IsGroupoidalCat C)) ⊢
  @discrete_cat_intro C obj_set core_equiv
  : τ (IsDiscreteCat C);

assert [C : Cat]
  (obj_set : τ (IsSetGrpd (Obj C)))
  (core_equiv : τ (@IsGroupoidalCat C)) ⊢
  @is_discrete_cat_obj_set C
    (@discrete_cat_intro C obj_set core_equiv)
  ≡ obj_set;

assert [C : Cat]
  (obj_set : τ (IsSetGrpd (Obj C)))
  (core_equiv : τ (@IsGroupoidalCat C)) ⊢
  @is_discrete_cat_core_equiv C
    (@discrete_cat_intro C obj_set core_equiv)
  ≡ core_equiv;

assert [C : Cat]
  [x y : τ (Obj C)] ⊢
  @core_incl_hom_func C x y
  : τ (Functor
      (Path_cat (@= (Obj C) x y))
      (Hom_cat C x y));

assert [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (@= (Obj C) x y)) ⊢
  @fapp0
    (Path_cat (@= (Obj C) x y))
    (Hom_cat C x y)
    (@core_incl_hom_func C x y)
    p
  ≡ @path_to_hom C x y p;

assert [C : Cat]
  (d : τ (IsDiscreteCat C))
  (x y : τ (Obj C)) ⊢
  @discrete_core_homwise C d x y
  : τ (@OmegaEquivAlong
      Cat_cat
      (Path_cat (@= (Obj C) x y))
      (Hom_cat C x y)
      (@core_incl_hom_func C x y));

assert [C : Cat]
  (d : τ (IsDiscreteCat C))
  (x y : τ (Obj C)) ⊢
  @discrete_core_homwise C d x y
  ≡ @groupoidal_core_homwise
      C (is_discrete_cat_core_equiv d) x y;

assert [C : Cat]
  (d : τ (IsDiscreteCat C))
  (x y : τ (Obj C)) ⊢
  @discrete_core_hom_inv_func C d x y
  : τ (Functor
      (Hom_cat C x y)
      (Path_cat (@= (Obj C) x y)));

assert [C : Cat]
  (d : τ (IsDiscreteCat C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @hom_to_path C d x y f
  : τ (@= (Obj C) x y);

assert [C : Cat]
  (d : τ (IsDiscreteCat C))
  (x y : τ (Obj C)) ⊢
  @discrete_core_hom_left_law C d x y
  : τ (@=
      (Hom Cat_cat
        (Path_cat (@= (Obj C) x y))
        (Path_cat (@= (Obj C) x y)))
      (@comp_cat_fapp0
        (Path_cat (@= (Obj C) x y))
        (Hom_cat C x y)
        (Path_cat (@= (Obj C) x y))
        (@discrete_core_hom_inv_func C d x y)
        (@core_incl_hom_func C x y))
      (@id Cat_cat (Path_cat (@= (Obj C) x y))));

assert [C : Cat]
  (d : τ (IsDiscreteCat C))
  [x y : τ (Obj C)]
  (p : τ (@= (Obj C) x y)) ⊢
  @hom_to_path_path_to_hom C d x y p
  : τ (@=
      (@= (Obj C) x y)
      (@hom_to_path C d x y (@path_to_hom C x y p))
      p);

assert [C : Cat]
  (d : τ (IsDiscreteCat C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @path_to_hom_hom_to_path_path C d x y f
  ≡ @groupoidal_path_to_arrow_retract
      C (is_discrete_cat_core_equiv d) x y f;

assert [C : Cat]
  (d : τ (IsDiscreteCat C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @path_to_hom_hom_to_path C d x y f
  : τ (Hom
      (Hom_cat C x y)
      (@path_to_hom C x y (@hom_to_path C d x y f))
      f);

// Set-truncation alone is not the selected two-field discrete-category data.
assertnot [C : Cat]
  (obj_set : τ (IsSetGrpd (Obj C))) ⊢
  obj_set
  : τ (IsDiscreteCat C);

// The two round trips are propositional, not runtime cancellation.
assertnot [C : Cat]
  (d : τ (IsDiscreteCat C))
  [x y : τ (Obj C)]
  (p : τ (@= (Obj C) x y)) ⊢
  @hom_to_path C d x y (@path_to_hom C x y p)
  ≡ p;

assertnot [C : Cat]
  (d : τ (IsDiscreteCat C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @path_to_hom C x y (@hom_to_path C d x y f)
  ≡ f;

// No runtime eta or proof-field erasure is selected for the evidence package.
assertnot [C : Cat]
  (d : τ (IsDiscreteCat C)) ⊢
  d
  ≡ @discrete_cat_intro C
      (is_discrete_cat_obj_set d)
      (is_discrete_cat_core_equiv d);

// catalog-area: Directed categorical dimension
assert (n : TruncLevel) [C : Cat] ⊢
  IsObjTruncCat n C
  ≡ IsTruncGrpd n (Obj C);

assert [C : Cat]
  (n : TruncLevel)
  (h : τ (IsObjTruncCat (trunc_succ n) C))
  (x y : τ (Obj C)) ⊢
  h x y
  : τ (IsTruncGrpd n (@= (Obj C) x y));

assert ⊢ cat_zero : CatDim;

assert (n : CatDim) ⊢ cat_succ n : CatDim;

assert (n : CatDim) ⊢
  cat_dim_trunc_level n
  : TruncLevel;

assert ⊢
  cat_dim_trunc_level cat_zero
  ≡ trunc_zero;

assert (n : CatDim) ⊢
  cat_dim_trunc_level (cat_succ n)
  ≡ trunc_succ (cat_dim_trunc_level n);

assert ⊢
  cat_dim_trunc_level (cat_succ cat_zero)
  ≡ trunc_one;

assert ⊢
  cat_dim_trunc_level (cat_succ (cat_succ cat_zero))
  ≡ trunc_succ trunc_one;

assert [C : Cat] ⊢
  IsNCat cat_zero C
  ≡ IsDiscreteCat C;

assert (n : CatDim) [C : Cat] ⊢
  IsNCat (cat_succ n) C
  ≡ @Pi_grpd (Obj C)
      (λ x : τ (Obj C),
        @Pi_grpd (Obj C)
          (λ y : τ (Obj C),
            IsNCat n (Hom_cat C x y)));

assert (n : CatDim) ⊢
  τ (NCat n)
  ≡ NCatData n;

assert (n : CatDim)
  (carrier : Cat)
  (evidence : τ (IsNCat n carrier)) ⊢
  @Struct_ncat n carrier evidence
  : τ (NCat n);

assert (n : CatDim)
  (carrier : Cat)
  (evidence : τ (IsNCat n carrier)) ⊢
  @ncat_carrier n (@Struct_ncat n carrier evidence)
  ≡ carrier;

assert (n : CatDim)
  (carrier : Cat)
  (evidence : τ (IsNCat n carrier)) ⊢
  @ncat_evidence n (@Struct_ncat n carrier evidence)
  ≡ evidence;

assert (n : CatDim)
  (X : τ (NCat n)) ⊢
  @ncat_evidence n X
  : τ (IsNCat n (@ncat_carrier n X));

assert ⊢
  ZeroCat
  ≡ NCat cat_zero;

assert ⊢
  OneCat
  ≡ NCat (cat_succ cat_zero);

assert (X : τ ZeroCat) ⊢
  @ncat_evidence cat_zero X
  : τ (IsDiscreteCat (@ncat_carrier cat_zero X));

assert (X : τ OneCat)
  (x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))) ⊢
  @one_cat_hom_discrete X x y
  : τ (IsDiscreteCat
      (Hom_cat (@ncat_carrier (cat_succ cat_zero) X) x y));

assert (X : τ OneCat)
  (x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))) ⊢
  @one_cat_hom_discrete X x y
  ≡ @ncat_evidence (cat_succ cat_zero) X x y;

assert (X : τ OneCat)
  (x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X)))
  (f g : τ (Hom (@ncat_carrier (cat_succ cat_zero) X) x y)) ⊢
  @one_cat_hom_core_homwise X x y f g
  : τ (@OmegaEquivAlong
      Cat_cat
      (Path_cat (@=
        (Hom (@ncat_carrier (cat_succ cat_zero) X) x y)
        f
        g))
      (Hom_cat
        (Hom_cat (@ncat_carrier (cat_succ cat_zero) X) x y)
        f
        g)
      (@core_incl_hom_func
        (Hom_cat (@ncat_carrier (cat_succ cat_zero) X) x y)
        f
        g));

assert (X : τ OneCat)
  (x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X)))
  (f g : τ (Hom (@ncat_carrier (cat_succ cat_zero) X) x y)) ⊢
  @one_cat_hom_core_homwise X x y f g
  ≡ @discrete_core_homwise
      (Hom_cat (@ncat_carrier (cat_succ cat_zero) X) x y)
      (@one_cat_hom_discrete X x y)
      f
      g;

// catalog-area: Directed categorical dimension

// Object truncation is independent of directed dimension.
assertnot [C : Cat] ⊢
  IsObjTruncCat trunc_zero C
  ≡ IsNCat cat_zero C;

assertnot [C : Cat]
  (h : τ (IsNCat cat_zero C)) ⊢
  h
  : τ (IsObjTruncCat trunc_zero C);

// The index bridge alone does not construct the object-truncation theorem.
assertnot (n : CatDim)
  [C : Cat]
  (h : τ (IsNCat n C)) ⊢
  h
  : τ (IsObjTruncCat (cat_dim_trunc_level n) C);

// Distinct dimension codes do not collapse their package classifiers.
assertnot ⊢
  ZeroCat
  ≡ OneCat;

// No runtime package eta or proof-field erasure is selected.
assertnot (n : CatDim)
  (X : τ (NCat n)) ⊢
  X
  ≡ @Struct_ncat n
      (@ncat_carrier n X)
      (@ncat_evidence n X);

assertnot (n : CatDim)
  (carrier : Cat)
  (evidence0 evidence1 : τ (IsNCat n carrier)) ⊢
  @Struct_ncat n carrier evidence0
  ≡ @Struct_ncat n carrier evidence1;

// Representation-independent truncation raising retained by the native finite-dimension proof.
assert (n : CatDim)
  [A : Grpd]
  (h : τ (IsPropGrpd A)) ⊢
  @prop_is_trunc_cat_dim n A h
  : τ (IsTruncGrpd (cat_dim_trunc_level n) A);

assert [A : Grpd]
  (h : τ (IsPropGrpd A)) ⊢
  @prop_is_trunc_cat_dim cat_zero A h
  ≡ @prop_is_trunc_succ trunc_minus_one A h;

assert (n : CatDim)
  [A : Grpd]
  (h : τ (IsPropGrpd A)) ⊢
  @prop_is_trunc_cat_dim (cat_succ n) A h
  ≡ @prop_is_trunc_succ (cat_dim_trunc_level n) A h;

// catalog-area: Ordinary Product isomorphism evidence

assert [A B : Cat]
  [x0 x1 : τ (Obj A)]
  [y0 y1 : τ (Obj B)]
  (iA : τ (IsoEvidence A x0 x1))
  (iB : τ (IsoEvidence B y0 y1)) ⊢
  @iso_evidence_product A B x0 x1 y0 y1 iA iB
  : τ (IsoEvidence
      (Product_cat A B)
      (Struct_sigma x0 y0)
      (Struct_sigma x1 y1));

assert [A B : Cat]
  [x0 x1 : τ (Obj A)]
  [y0 y1 : τ (Obj B)]
  (iA : τ (IsoEvidence A x0 x1))
  (iB : τ (IsoEvidence B y0 y1)) ⊢
  @iso_evidence_to
    (Product_cat A B)
    (Struct_sigma x0 y0)
    (Struct_sigma x1 y1)
    (@iso_evidence_product A B x0 x1 y0 y1 iA iB)
  ≡ @Struct_sigma
      (Obj (Hom_cat A x0 x1))
      (λ _ : τ (Obj (Hom_cat A x0 x1)), Obj (Hom_cat B y0 y1))
      (@iso_evidence_to A x0 x1 iA)
      (@iso_evidence_to B y0 y1 iB);

assert [A B : Cat]
  [x0 x1 : τ (Obj A)]
  [y0 y1 : τ (Obj B)]
  (iA : τ (IsoEvidence A x0 x1))
  (iB : τ (IsoEvidence B y0 y1)) ⊢
  @iso_evidence_from
    (Product_cat A B)
    (Struct_sigma x0 y0)
    (Struct_sigma x1 y1)
    (@iso_evidence_product A B x0 x1 y0 y1 iA iB)
  ≡ @Struct_sigma
      (Obj (Hom_cat A x1 x0))
      (λ _ : τ (Obj (Hom_cat A x1 x0)), Obj (Hom_cat B y1 y0))
      (@iso_evidence_from A x0 x1 iA)
      (@iso_evidence_from B y0 y1 iB);

assert [A B : Cat]
  [x0 x1 : τ (Obj A)]
  [y0 y1 : τ (Obj B)]
  (pA : τ (x0 = x1))
  (pB : τ (@PathOver (Obj A) (λ _ : τ (Obj A), Obj B) x0 x1 pA y0 y1)) ⊢
  @idtoiso_cat
    (Product_cat A B)
    (Struct_sigma x0 y0)
    (Struct_sigma x1 y1)
    (@Struct_sigma
      (@= (Obj A) x0 x1)
      (λ p : τ (@= (Obj A) x0 x1),
        @PathOver (Obj A) (λ _ : τ (Obj A), Obj B) x0 x1 p y0 y1)
      pA
      pB)
  ≡ @iso_evidence_product
      A
      B
      x0
      x1
      y0
      y1
      (@idtoiso_cat A x0 x1 pA)
      (@idtoiso_cat
        B
        y0
        y1
        (@const_pathover_path
          (Obj A)
          (Obj B)
          x0
          x1
          y0
          y1
          pA
          pB));

assert [A B : Cat]
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  @idtoiso_cat
    (Product_cat A B)
    (Struct_sigma x y)
    (Struct_sigma x y)
    (@Struct_sigma
      (@= (Obj A) x x)
      (λ p : τ (@= (Obj A) x x),
        @PathOver (Obj A) (λ _ : τ (Obj A), Obj B) x x p y y)
      (eq_refl x)
      (@pathover_refl (Obj A) (λ _ : τ (Obj A), Obj B) x y))
  ≡ @iso_evidence_product
      A B x x y y
      (@iso_evidence_refl A x)
      (@iso_evidence_refl B y);

assertnot [A B : Cat]
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  @iso_evidence_product
    A B x x y y
    (@iso_evidence_refl A x)
    (@iso_evidence_refl B y)
  ≡ @iso_evidence_refl
      (Product_cat A B)
      (Struct_sigma x y);

// catalog-area: auto

assert [a b : Grpd] (f : τ a → τ b) (x : τ a) ⊢
  @eq_ap a b f x x (eq_refl x)
  ≡ eq_refl (f x);

assert [a : Grpd] (x : τ a) ⊢
  @eq_sym a x x (eq_refl x)
  ≡ eq_refl x;

// Groupoid path-over and dependent path action.
assert [A : Grpd]
  (P : τ A → Grpd)
  (x : τ A)
  (u v : τ (P x)) ⊢
  @PathOver A P x x (eq_refl x) u v
  ≡ u = v;

assert [A : Grpd]
  [P : τ A → Grpd]
  (f : Π x : τ A, τ (P x))
  (x : τ A) ⊢
  @eq_apd A P f x x (eq_refl x)
  ≡ eq_refl (f x);

assert [A : Grpd]
  (y : τ A)
  (P : Π x : τ A, τ (x = y) → Grpd)
  (u : τ (P y (eq_refl y))) ⊢
  @ind_eqr A y P u y (eq_refl y)
  ≡ u;

assert [A : Grpd]
  (x : τ A)
  (P : τ A → Grpd)
  (u : τ (P x)) ⊢
  @ind_eq A x x (eq_refl x) P u
  ≡ u;

assert [A : Grpd]
  [P : τ A → Grpd]
  (Q : @τΣ_ A P → Grpd)
  (c : Π x : τ A, Π u : τ (P x), τ (Q (@Struct_sigma A P x u)))
  (x : τ A)
  (u : τ (P x)) ⊢
  @sigma_ind A P Q c (@Struct_sigma A P x u)
  ≡ c x u;

assert [A : Grpd]
  [P : τ A → Grpd]
  (u : @τΣ_ A P) ⊢
  sigma_path_base (sigma_path_refl u)
  ≡ eq_refl (sigma_Fst u);

assert [A : Grpd]
  [P : τ A → Grpd]
  (u : @τΣ_ A P) ⊢
  sigma_path_fibre (sigma_path_refl u)
  ≡ @pathover_refl A P (sigma_Fst u) (sigma_Snd u);

assert [A : Grpd]
  [P : τ A → Grpd]
  (u : @τΣ_ A P) ⊢
  @sigma_path_encode A P u u (eq_refl u)
  ≡ sigma_path_refl u;

assert [A : Grpd]
  [P : τ A → Grpd]
  (x : τ A)
  (a b : τ (P x))
  (q : τ (a = b)) ⊢
  @sigma_path_intro A P x x a b (eq_refl x) q
  ≡ @eq_ap
      (P x)
      (@Σ_ A P)
      (λ z : τ (P x), @Struct_sigma A P x z)
      a
      b
      q;

assert [A : Grpd]
  [P : τ A → Grpd]
  (x : τ A)
  (a : τ (P x)) ⊢
  sigma_path_decode (sigma_path_refl (@Struct_sigma A P x a))
  ≡ @eq_refl (@Σ_ A P) (@Struct_sigma A P x a);

assert [A : Grpd]
  [P : τ A → Grpd]
  (u : @τΣ_ A P) ⊢
  eq_refl (@eq_refl (@Σ_ A P) u)
  : τ (@eq_refl (@Σ_ A P) u = sigma_path_refl u);

assert [A : Grpd]
  [P : τ A → Grpd]
  (u : @τΣ_ A P) ⊢
  eq_refl (@eq_refl (@Σ_ A P) u)
  : τ (sigma_path_refl u = @eq_refl (@Σ_ A P) u);

// Arbitrary Sigma path-characterization round trips.
assert [A : Grpd]
  [P : τ A → Grpd]
  (u : @τΣ_ A P) ⊢
  @sigma_path_decode_refl A P u
  : τ (
      @sigma_path_decode A P u u (@sigma_path_refl A P u)
      = @eq_refl (@Σ_ A P) u);

assert [A : Grpd]
  [P : τ A → Grpd]
  (x : τ A)
  (a : τ (P x)) ⊢
  @sigma_path_decode_refl A P (@Struct_sigma A P x a)
  ≡ @eq_refl
      (@= (@Σ_ A P)
        (@Struct_sigma A P x a)
        (@Struct_sigma A P x a))
      (@eq_refl (@Σ_ A P) (@Struct_sigma A P x a));

assert [A : Grpd]
  [P : τ A → Grpd]
  [u v : @τΣ_ A P]
  (p : τ (@= (@Σ_ A P) u v)) ⊢
  @sigma_path_decode_encode A P u v p
  : τ (
      @sigma_path_decode A P u v (@sigma_path_encode A P u v p)
      = p);

// The arbitrary Sigma round trip is a theorem, not a global runtime eta.
assertnot [A : Grpd]
  [P : τ A → Grpd]
  [u v : @τΣ_ A P]
  (p : τ (@= (@Σ_ A P) u v)) ⊢
  @sigma_path_decode A P u v (@sigma_path_encode A P u v p)
  ≡ p;

assert [A : Grpd]
  [P : τ A → Grpd]
  (x : τ A)
  (a : τ (P x)) ⊢
  @sigma_path_decode_encode
    A P
    (@Struct_sigma A P x a)
    (@Struct_sigma A P x a)
    (@eq_refl (@Σ_ A P) (@Struct_sigma A P x a))
  ≡ @eq_refl
      (@= (@Σ_ A P)
        (@Struct_sigma A P x a)
        (@Struct_sigma A P x a))
      (@eq_refl (@Σ_ A P) (@Struct_sigma A P x a));

assert [A : Grpd]
  [P : τ A → Grpd]
  (u : @τΣ_ A P) ⊢
  @sigma_path_encode_decode_refl A P u
  : τ (
      @sigma_path_encode A P u u
        (@sigma_path_decode A P u u (@sigma_path_refl A P u))
      = @sigma_path_refl A P u);

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

assert [A : Grpd]
  [P : τ A → Grpd]
  (u : @τΣ_ A P) ⊢
  @sigma_path_encode_decode_eq_refl A P u
  : τ (
      @sigma_path_encode A P u u
        (@sigma_path_decode A P u u (@eq_refl (@Σ_ A P) u))
      = @eq_refl (@Σ_ A P) u);

assert [A : Grpd]
  [P : τ A → Grpd]
  (x : τ A)
  (a : τ (P x)) ⊢
  @sigma_path_encode_decode_eq_refl A P (@Struct_sigma A P x a)
  ≡ @eq_refl
      (@= (@Σ_ A P)
        (@Struct_sigma A P x a)
        (@Struct_sigma A P x a))
      (@eq_refl (@Σ_ A P) (@Struct_sigma A P x a));

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
  @sigma_path_encode_decode
    A P
    (@Struct_sigma A P x a)
    (@Struct_sigma A P x a)
    (@eq_refl (@Σ_ A P) (@Struct_sigma A P x a))
  ≡ @eq_refl
      (@= (@Σ_ A P)
        (@Struct_sigma A P x a)
        (@Struct_sigma A P x a))
      (@eq_refl (@Σ_ A P) (@Struct_sigma A P x a));

// Generic J supplies the arbitrary theorem propositionally; it does not gain
// a runtime beta on the canonical structured Sigma path constructor.
assertnot [A : Grpd]
  [P : τ A → Grpd]
  (u : @τΣ_ A P) ⊢
  @sigma_path_encode A P u u
    (@sigma_path_decode A P u u (@sigma_path_refl A P u))
  ≡ @sigma_path_refl A P u;

// PathRecord equality is already its structural view, so its named maps and
// both round trips are transparent and retain shaped reflexivity.
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
  (r : τ (PathRecord_grpd A)) ⊢
  @path_record_path_decode A r r (@PathRecordPathRefl A r)
  ≡ @eq_refl (PathRecord_grpd A) r;

assert [A : Grpd]
  [r s : τ (PathRecord_grpd A)]
  (p : τ (r = s)) ⊢
  @path_record_path_decode_encode A r s p
  ≡ @eq_refl (@= (PathRecord_grpd A) r s) p;

assert [A : Grpd]
  [r s : τ (PathRecord_grpd A)]
  (w : τ (@PathRecordPathView A r s)) ⊢
  @path_record_path_encode_decode A r s w
  ≡ @eq_refl (@PathRecordPathView A r s) w;

// The dependent tail observer is unchanged by the transparent round trip.
assert [A : Grpd]
  [r s : τ (PathRecord_grpd A)]
  (w : τ (@PathRecordPathView A r s)) ⊢
  @path_record_path_tail
    A r s
    (@path_record_path_encode A r s
      (@path_record_path_decode A r s w))
  ≡ @path_record_path_tail A r s w;

// One nested former checks that the round-trip surface iterates.
assert [A : Grpd]
  [r s : τ (PathRecord_grpd (PathRecord_grpd A))]
  (p : τ (r = s)) ⊢
  @path_record_path_decode_encode (PathRecord_grpd A) r s p
  ≡ @eq_refl (@= (PathRecord_grpd (PathRecord_grpd A)) r s) p;

assert [A : Grpd]
  [r s : τ (PathRecord_grpd (PathRecord_grpd A))]
  (w : τ (@PathRecordPathView (PathRecord_grpd A) r s)) ⊢
  @path_record_path_encode_decode (PathRecord_grpd A) r s w
  ≡ @eq_refl (@PathRecordPathView (PathRecord_grpd A) r s) w;

// Dependent witness transport is owned directly by canonical eq_apd.
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

// catalog-area: Equality-valued half-adjointification
// Separate left/right inverse homotopies admit a derived adjusted counit
// whose triangle is computational on reflexive identity data.
assert [A B : Grpd]
  (f : τ A → τ B)
  (l : τ B → τ A)
  (eta : Π x : τ A, τ (@= A (l (f x)) x))
  (epsilon : Π b : τ B, τ (@= B (f (l b)) b))
  (x : τ A) ⊢
  @half_adjoint_triangle A B f l eta epsilon x
  : τ (@=
      (@= B (f (l (f x))) (f x))
      (@eq_ap A B f (l (f x)) x (eta x))
      (@half_adjoint_counit A B f l eta epsilon (f x)));

assert [A : Grpd]
  (x : τ A) ⊢
  @half_adjoint_counit
    A A
    (λ z : τ A, z)
    (λ z : τ A, z)
    (λ z : τ A, @eq_refl A z)
    (λ z : τ A, @eq_refl A z)
    x
  ≡ @eq_refl A x;

assert [A : Grpd]
  (x : τ A) ⊢
  @half_adjoint_triangle
    A A
    (λ z : τ A, z)
    (λ z : τ A, z)
    (λ z : τ A, @eq_refl A z)
    (λ z : τ A, @eq_refl A z)
    x
  ≡ @eq_refl (@= A x x) (@eq_refl A x);

// catalog-area: Native equality-valued evidence property
// The native record has a transparent two-fibre view. Literal path-category
// evidence is contractible, while its contraction path remains propositional
// rather than a global runtime proof-erasure rule.
assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f)) ⊢
  @omega_equiv_along_from_view_view C x y f u
  : τ (@=
      (@OmegaEquivAlong C x y f)
      (@omega_equiv_along_from_view C x y f
        (@omega_equiv_along_view C x y f u))
      u);

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (hleft : τ (IsContr (@OmegaEquivLeftView C x y f)))
  (hright : τ (IsContr (@OmegaEquivRightView C x y f))) ⊢
  @omega_equiv_along_evidence_is_contr_from_view
    C x y f
    (@omega_equiv_along_view_is_contr
      C x y f hleft hright)
  : τ (IsContr (@OmegaEquivAlong C x y f));

assert [A : Grpd]
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @path_equiv_evidence_is_contr A y x p
  : τ (IsContr (@OmegaEquivAlong (Path_cat A) x y p));

assert [A : Grpd]
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @path_equiv_evidence_is_prop A x y p
  : τ (IsPropGrpd (@OmegaEquivAlong (Path_cat A) x y p));

assert [A : Grpd]
  (x : τ A) ⊢
  is_contr_center (@path_refl_equiv_evidence_is_contr A x)
  ≡ @path_equiv_along A x x (@eq_refl A x);

assertnot [A : Grpd]
  (x : τ A) ⊢
  is_contr_path
    (@path_refl_equiv_evidence_is_contr A x)
    (@path_equiv_along A x x (@eq_refl A x))
  ≡ @eq_refl
      (@OmegaEquivAlong (Path_cat A) x x (@eq_refl A x))
      (@path_equiv_along A x x (@eq_refl A x));

// A groupoidal category with set-valued objects has proposition-valued homs
// by a fully transparent retract argument.
assert [C : Cat]
  (g : τ (@IsGroupoidalCat C))
  (obj_set : τ (IsSetGrpd (Obj C)))
  (x y : τ (Obj C)) ⊢
  @groupoidal_hom_is_prop C g obj_set x y
  : τ (IsPropGrpd (Hom C x y));

assert [C : Cat]
  (d : τ (IsDiscreteCat C))
  (x y : τ (Obj C)) ⊢
  @discrete_hom_is_prop C d x y
  : τ (IsPropGrpd (Hom C x y));

// Ordinary cross-inverse uniqueness is explicit categorical path algebra.
assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (l r : τ (Hom C y x))
  (alpha : τ (@=
    (Hom C x x)
    (@comp_fapp0 C x y x l f)
    (@id C x)))
  (beta : τ (@=
    (Hom C y y)
    (@comp_fapp0 C y x y f r)
    (@id C y))) ⊢
  @omega_equiv_candidate_left_to_right
    C x y f l r alpha beta
  : τ (@= (Hom C y x) l r);

// The composition-map argument contracts native fixed-arrow evidence in an
// arbitrary category. No local truncation premise is needed.
assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f)) ⊢
  @omega_equiv_along_evidence_is_contr C x y f u
  : τ (IsContr (@OmegaEquivAlong C x y f));

assert [C : Cat]
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @omega_equiv_along_evidence_is_prop C x y f
  : τ (IsPropGrpd (@OmegaEquivAlong C x y f));

// The earlier local-set proof remains a useful independent specialization.
assert [C : Cat]
  (h : τ (@IsLocallySetCat C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @locally_set_equiv_evidence_is_prop C h x y f
  : τ (IsPropGrpd (@OmegaEquivAlong C x y f));

assert [C : Cat]
  (h : τ (IsNCat (cat_succ cat_zero) C)) ⊢
  @one_cat_is_locally_set C h
  : τ (@IsLocallySetCat C);

// The transparent Sigma and stable facade transfer set truncation by
// explicit retractions; no contractible-fibre theorem is invoked.
assert [C : Cat]
  [x y : τ (Obj C)]
  (h : τ (IsSetGrpd (@OmegaEquivSigma C x y))) ⊢
  @omega_equiv_facade_is_set C x y h
  : τ (IsSetGrpd (@OmegaEquiv C x y));

assert [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (@= (Obj C) x y)) ⊢
  @object_path_cast_roundtrip C x y p
  ≡ @eq_refl (@= (Obj C) x y) p;

// Dimension one is now unconditional: discrete hom categories supply the
// local-set hypothesis and the direct equality-valued Sigma supplies object-path sets.
assert [C : Cat]
  (h : τ (IsNCat (cat_succ cat_zero) C)) ⊢
  @one_cat_omega_sigma_is_set C h
  : Π x : τ (Obj C), Π y : τ (Obj C),
      τ (IsSetGrpd (@OmegaEquivSigma C x y));

assert [C : Cat]
  (h : τ (IsNCat (cat_succ cat_zero) C)) ⊢
  @one_cat_obj_trunc C h
  : τ (IsObjTruncCat
      (cat_dim_trunc_level (cat_succ cat_zero)) C);

// Explicit retractions preserve every truncation level by transparent
// TruncLevel induction.
assert (n : TruncLevel) (X Y : Grpd)
  (r : τ X → τ Y)
  (s : τ Y → τ X)
  (epsilon : Π y : τ Y, τ (@= Y (r (s y)) y))
  (hX : τ (IsTruncGrpd n X)) ⊢
  @is_trunc_retract n X Y r s epsilon hX
  : τ (IsTruncGrpd n Y);

// Finite directed dimension now bounds object truncation unconditionally.
assert (n : CatDim) (C : Cat)
  (h : τ (IsNCat n C)) ⊢
  @ncat_obj_trunc n C h
  : τ (IsObjTruncCat (cat_dim_trunc_level n) C);

assert (C : Cat) (h : τ (IsNCat cat_zero C)) ⊢
  @ncat_obj_trunc cat_zero C h
  ≡ @is_discrete_cat_obj_set C h;

// The successor equation exposes exactly the hom induction, Sigma closure,
// evidence-property weakening, and the two explicit retractions.
assert (n : CatDim) (C : Cat)
  (h : τ (IsNCat (cat_succ n) C))
  (x y : τ (Obj C)) ⊢
  (@ncat_obj_trunc (cat_succ n) C h) x y
  ≡ @object_path_is_trunc_from_omega
      (cat_dim_trunc_level n)
      C x y
      (@omega_equiv_facade_is_trunc
        (cat_dim_trunc_level n)
        C x y
        (@is_trunc_sigma
          (cat_dim_trunc_level n)
          (Hom C x y)
          (λ f : τ (Hom C x y), @OmegaEquivAlong C x y f)
          (@ncat_obj_trunc n (Hom_cat C x y) (h x y))
          (λ f : τ (Hom C x y),
            @prop_is_trunc_cat_dim
              n
              (@OmegaEquivAlong C x y f)
              (@omega_equiv_along_evidence_is_prop C x y f))));

// catalog-area: Native equality-valued next-hom action
// A category-level equality-valued omega-equivalence acts by a transparent
// equality-valued omega-equivalence on every next hom category.
assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  omega_equiv_along_fapp1 u x y
  : τ (@OmegaEquivAlong
      Cat_cat
      (Hom_cat A x y)
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (@fapp1_func A B F x y));

// Both inverse projections compute to the same half-adjointified inverse.
assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  @omega_equiv_along_left_inv
    Cat_cat
    (Hom_cat A x y)
    (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
    (@fapp1_func A B F x y)
    (omega_equiv_along_fapp1 u x y)
  ≡ @omega_equiv_along_right_inv
    Cat_cat
    (Hom_cat A x y)
    (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
    (@fapp1_func A B F x y)
    (omega_equiv_along_fapp1 u x y);

// The left cancellation projection has its native equality-valued type.
assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  @omega_equiv_along_left_law
    Cat_cat
    (Hom_cat A x y)
    (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
    (@fapp1_func A B F x y)
    (omega_equiv_along_fapp1 u x y)
  : τ (@=
      (Hom Cat_cat (Hom_cat A x y) (Hom_cat A x y))
      (@comp_fapp0
        Cat_cat
        (Hom_cat A x y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (Hom_cat A x y)
        (@omega_equiv_along_left_inv
          Cat_cat
          (Hom_cat A x y)
          (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
          (@fapp1_func A B F x y)
          (omega_equiv_along_fapp1 u x y))
        (@fapp1_func A B F x y))
      (@id Cat_cat (Hom_cat A x y)));

// The right cancellation projection has its native equality-valued type.
assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  @omega_equiv_along_right_law
    Cat_cat
    (Hom_cat A x y)
    (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
    (@fapp1_func A B F x y)
    (omega_equiv_along_fapp1 u x y)
  : τ (@=
      (Hom Cat_cat
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y)))
      (@comp_fapp0
        Cat_cat
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (Hom_cat A x y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (@fapp1_func A B F x y)
        (@omega_equiv_along_right_inv
          Cat_cat
          (Hom_cat A x y)
          (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
          (@fapp1_func A B F x y)
          (omega_equiv_along_fapp1 u x y)))
      (@id Cat_cat
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))));

// Reflexive input computes through the protected proof chain to identity.
assert [A : Cat] (x y : τ (Obj A)) ⊢
  @omega_equiv_along_left_inv
    Cat_cat
    (Hom_cat A x y)
    (Hom_cat A x y)
    (@fapp1_func A A (@id_func A) x y)
    (omega_equiv_along_fapp1
      (@omega_equiv_along_refl Cat_cat A)
      x y)
  ≡ @id_func (Hom_cat A x y);
// catalog-area: auto

assert [A : Grpd]
  [B : τ A → Grpd]
  (f : Π x : τ A, τ (B x))
  (x : τ A) ⊢
  @eq_refl (@Pi_grpd A B) f x x (eq_refl x)
  ≡ eq_refl (f x);

assert [A : Grpd]
  [B : τ A → Grpd]
  (f : Π x : τ A, τ (B x))
  (x0 x1 : τ A)
  (p : τ (x0 = x1)) ⊢
  @eq_refl (@Pi_grpd A B) f x0 x1 p
  ≡ @eq_apd A B f x0 x1 p;

assert [A : Grpd]
  [B : τ A → Grpd]
  (f : Π x : τ A, τ (B x))
  (x0 x1 : τ A)
  (p : τ (x0 = x1)) ⊢
  pi_path_refl f x0 x1 p
  ≡ @eq_apd A B f x0 x1 p;

assert [A : Grpd]
  [B : τ A → Grpd]
  (f : Π x : τ A, τ (B x)) ⊢
  @eq_refl (@Pi_grpd A B) f
  ≡ @eq_apd A B f;

assert [A : Grpd]
  [B : τ A → Grpd] ⊢
  @eq_refl (@Pi_grpd A B)
  ≡ @eq_apd A B;

assert [A : Grpd]
  [B : τ A → Grpd]
  (f : Π x : τ A, τ (B x)) ⊢
  pi_path_refl f
  ≡ @eq_refl (@Pi_grpd A B) f;

assert [A : Grpd]
  [B : τ A → Grpd]
  (f : Π x : τ A, τ (B x)) ⊢
  @pi_path_encode A B f f (eq_refl f)
  ≡ pi_path_refl f;

assert [A : Grpd]
  [B : τ A → Grpd]
  (f g : Π x : τ A, τ (B x)) ⊢
  @= (@Pi_grpd A B) f g
  ≡ @PiPathView A B f g;

assert [A : Grpd]
  [B : τ A → Grpd]
  (f g : Π x : τ A, τ (B x))
  (w : τ (@PiPathView A B f g)) ⊢
  w
  : τ (@= (@Pi_grpd A B) f g);

assert [A : Grpd]
  [B : τ A → Grpd]
  (f : Π x : τ A, τ (B x))
  (M : τ (@Pi_grpd A B) → Grpd)
  (u : τ (M f)) ⊢
  @ind_eq
    (@Pi_grpd A B)
    f
    f
    (@eq_refl (@Pi_grpd A B) f)
    M
    u
  ≡ u;

// Ordinary Pi happly/funext surface over the related-input path view.
assert [A : Grpd]
  [B : τ A → Grpd]
  (f g : Π x : τ A, τ (B x)) ⊢
  @PiPointwisePath A B f g
  ≡ @Pi_grpd A (λ x : τ A, f x = g x);

assert [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (p : τ (f = g))
  (x : τ A) ⊢
  @PiHapply A B f g p x
  ≡ p x x (@eq_refl A x);

// Application-first reduction joins the active shaped Pi reflexivity rule.
assert [A : Grpd]
  [B : τ A → Grpd]
  (f : Π x : τ A, τ (B x))
  (x : τ A) ⊢
  @PiHapply A B f f (@eq_refl (@Pi_grpd A B) f) x
  ≡ @eq_refl (B x) (f x);

assert [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (h : τ (@PiPointwisePath A B f g))
  (x0 x1 : τ A)
  (p : τ (x0 = x1)) ⊢
  @PiFunext A B f g h x0 x1 p
  ≡ @ind_eqr A x1
      (λ x0 : τ A, λ p : τ (x0 = x1),
        @PathOver A B x0 x1 p (f x0) (g x1))
      (h x1)
      x0
      p;

assert [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (h : τ (@PiPointwisePath A B f g))
  (x : τ A) ⊢
  @PiHapply A B f g (@PiFunext A B f g h) x
  ≡ h x;

// Typed reflexivity, rather than conversion assertion, exercises the selected
// proof-time reflexive eta equation.
assert [A : Grpd]
  [B : τ A → Grpd]
  (f : Π x : τ A, τ (B x)) ⊢
  @eq_refl
    (@= (@Pi_grpd A B) f f)
    (@eq_refl (@Pi_grpd A B) f)
  : τ (
      @PiFunext A B f f
        (@PiHapply A B f f (@eq_refl (@Pi_grpd A B) f))
      = @eq_refl (@Pi_grpd A B) f);

// After applying the two stable heads, the shaped-reflexivity and funext
// action paths join by runtime computation without the proof-time equation.
assert [A : Grpd]
  [B : τ A → Grpd]
  (f : Π x : τ A, τ (B x))
  (x0 x1 : τ A)
  (p : τ (x0 = x1)) ⊢
  @PiFunext A B f f
    (@PiHapply A B f f (@eq_refl (@Pi_grpd A B) f))
    x0 x1 p
  ≡ @eq_refl (@Pi_grpd A B) f x0 x1 p;

assert [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (p : τ (f = g)) ⊢
  @pi_funext_eta A B f g p
  : τ (@PiFunext A B f g (@PiHapply A B f g p) = p);

assert [A : Grpd]
  [B : τ A → Grpd]
  (f : Π x : τ A, τ (B x)) ⊢
  @pi_funext_eta A B f f (@eq_refl (@Pi_grpd A B) f)
  ≡ @eq_refl
      (@= (@Pi_grpd A B) f f)
      (@eq_refl (@Pi_grpd A B) f);

// The stable reflexive coherence is proof-time only, not runtime conversion.
assertnot [A : Grpd]
  [B : τ A → Grpd]
  (f : Π x : τ A, τ (B x)) ⊢
  @PiFunext A B f f
    (@PiHapply A B f f (@eq_refl (@Pi_grpd A B) f))
  ≡ @eq_refl (@Pi_grpd A B) f;

assert [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (p : τ (f = g)) ⊢
  @PiHapplyMap A B f g p
  ≡ @PiHapply A B f g p;

assert [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (h : τ (@PiPointwisePath A B f g)) ⊢
  @PiFunextMap A B f g h
  ≡ @PiFunext A B f g h;

assert [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (h : τ (@PiPointwisePath A B f g)) ⊢
  @pi_happly_beta A B f g h
  : τ (
      @PiHapply A B f g (@PiFunext A B f g h)
      = h);

assert [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (h : τ (@PiPointwisePath A B f g))
  (x : τ A) ⊢
  @pi_happly_beta A B f g h x x (@eq_refl A x)
  ≡ @eq_refl (@= (B x) (f x) (g x)) (h x);

// Whole-function forward beta is propositional; only its point action reduces.
assertnot [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (h : τ (@PiPointwisePath A B f g)) ⊢
  @PiHapply A B f g (@PiFunext A B f g h)
  ≡ h;

// Arbitrary structured Pi paths do not acquire an additional J beta.
assertnot [A : Grpd]
  [B : τ A → Grpd]
  (f : Π x : τ A, τ (B x))
  (h : τ (@PiPointwisePath A B f f))
  (M : τ (@Pi_grpd A B) → Grpd)
  (u : τ (M f)) ⊢
  @ind_eqr
    (@Pi_grpd A B)
    f
    (λ k : τ (@Pi_grpd A B), λ _ : τ (k = f), M k)
    u
    f
    (@PiFunext A B f f h)
  ≡ u;

// A supplied quasi-inverse selects the expected centre of each homotopy fibre.
assert [A B : Grpd]
  [f : τ A → τ B]
  [g : τ B → τ A]
  (q : τ (@EquivByInverse A B f g))
  (b : τ B) ⊢
  @is_contr_center
    (@HFiber A B f b)
    (@is_equiv_fiber
      A B f
      (@is_equiv_map_by_inverse A B f g q)
      b)
  ≡ @Struct_sigma
      A
      (λ a : τ A, @= B (f a) b)
      (g b)
      ((sigma_Snd q) b);

assert [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)] ⊢
  @pi_happly_by_inverse A B f g
  : τ (@EquivByInverse
      (@= (@Pi_grpd A B) f g)
      (@PiPointwisePath A B f g)
      (@PiHapplyMap A B f g)
      (@PiFunextMap A B f g));

assert [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (p : τ (f = g)) ⊢
  (sigma_Fst (@pi_happly_by_inverse A B f g)) p
  ≡ @pi_funext_eta A B f g p;

assert [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (h : τ (@PiPointwisePath A B f g)) ⊢
  (sigma_Snd (@pi_happly_by_inverse A B f g)) h
  ≡ @pi_happly_beta A B f g h;

assert [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)] ⊢
  @pi_happly_is_equiv A B f g
  : τ (@IsEquivMap
      (@= (@Pi_grpd A B) f g)
      (@PiPointwisePath A B f g)
      (@PiHapplyMap A B f g));

assert [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (h : τ (@PiPointwisePath A B f g)) ⊢
  @is_equiv_fiber
    (@= (@Pi_grpd A B) f g)
    (@PiPointwisePath A B f g)
    (@PiHapplyMap A B f g)
    (@pi_happly_is_equiv A B f g)
    h
  : τ (IsContr
      (@HFiber
        (@= (@Pi_grpd A B) f g)
        (@PiPointwisePath A B f g)
        (@PiHapplyMap A B f g)
        h));

assert [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)] ⊢
  @pi_happly_type_equiv A B f g
  : τ (TypeEquiv
      (@= (@Pi_grpd A B) f g)
      (@PiPointwisePath A B f g));

assert [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (p : τ (f = g)) ⊢
  type_equiv_to (@pi_happly_type_equiv A B f g) p
  ≡ @PiHapply A B f g p;

assert [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (h : τ (@PiPointwisePath A B f g)) ⊢
  type_equiv_from (@pi_happly_type_equiv A B f g) h
  ≡ @PiFunext A B f g h;

assert [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (h : τ (@PiPointwisePath A B f g)) ⊢
  type_equiv_right (@pi_happly_type_equiv A B f g) h
  ≡ @pi_happly_beta A B f g h;

assert [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (p : τ (f = g)) ⊢
  type_equiv_left (@pi_happly_type_equiv A B f g) p
  : τ (
      @PiFunext A B f g (@PiHapply A B f g p)
      = p);

// The opaque fibre contraction does not duplicate the separately derived eta.
assertnot [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (p : τ (f = g)) ⊢
  type_equiv_left (@pi_happly_type_equiv A B f g) p
  ≡ @pi_funext_eta A B f g p;

// Arbitrary reverse-composite eta remains propositional, not runtime.
assertnot [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (p : τ (f = g)) ⊢
  @PiFunext A B f g (@PiHapply A B f g p)
  ≡ p;

// Ordinary identity, symmetry, and composition algebra for TypeEquiv.
assert [A : Grpd] ⊢
  @type_equiv_refl_is_equiv A
  : τ (@IsEquivMap A A (λ x : τ A, x));

assert [A : Grpd]
  (a : τ A) ⊢
  @is_contr_center
    (@HFiber A A (λ x : τ A, x) a)
    (@is_equiv_fiber
      A A
      (λ x : τ A, x)
      (@type_equiv_refl_is_equiv A)
      a)
  ≡ @Struct_sigma A (λ x : τ A, x = a) a (eq_refl a);

assert [A B : Grpd]
  (e : τ (TypeEquiv A B)) ⊢
  @type_equiv_sym_by_inverse A B e
  : τ (@EquivByInverse
      B A
      (λ b : τ B, type_equiv_from e b)
      (λ a : τ A, type_equiv_to e a));

assert [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (b : τ B) ⊢
  (sigma_Fst (@type_equiv_sym_by_inverse A B e)) b
  ≡ type_equiv_right e b;

assert [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (a : τ A) ⊢
  (sigma_Snd (@type_equiv_sym_by_inverse A B e)) a
  ≡ type_equiv_left e a;

assert [A B : Grpd]
  (e : τ (TypeEquiv A B)) ⊢
  @type_equiv_sym_is_equiv A B e
  : τ (@IsEquivMap
      B A
      (λ b : τ B, type_equiv_from e b));

assert [A B : Grpd]
  (e : τ (TypeEquiv A B)) ⊢
  @type_equiv_sym A B e
  : τ (TypeEquiv B A);

assert [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (b : τ B) ⊢
  type_equiv_to (@type_equiv_sym A B e) b
  ≡ type_equiv_from e b;

assert [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (a : τ A) ⊢
  type_equiv_from (@type_equiv_sym A B e) a
  ≡ type_equiv_to e a;

assert [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (a : τ A) ⊢
  type_equiv_right (@type_equiv_sym A B e) a
  ≡ type_equiv_left e a;

assert [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (b : τ B) ⊢
  type_equiv_left (@type_equiv_sym A B e) b
  : τ (type_equiv_to e (type_equiv_from e b) = b);

// The opaque contraction theorem does not turn the other inverse law into a
// second runtime projection rule.
assertnot [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (b : τ B) ⊢
  type_equiv_left (@type_equiv_sym A B e) b
  ≡ type_equiv_right e b;

assert [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (a : τ A) ⊢
  type_equiv_to (@type_equiv_sym B A (@type_equiv_sym A B e)) a
  ≡ type_equiv_to e a;

// Double symmetry agrees on maps, not by a global package eta.
assertnot [A B : Grpd]
  (e : τ (TypeEquiv A B)) ⊢
  @type_equiv_sym B A (@type_equiv_sym A B e)
  ≡ e;

assert [A B C : Grpd]
  (eBC : τ (TypeEquiv B C))
  (eAB : τ (TypeEquiv A B))
  (a : τ A) ⊢
  @type_equiv_comp_left A B C eBC eAB a
  : τ (
      type_equiv_from eAB
        (type_equiv_from eBC
          (type_equiv_to eBC (type_equiv_to eAB a)))
      = a);

assert [A B C : Grpd]
  (eBC : τ (TypeEquiv B C))
  (eAB : τ (TypeEquiv A B))
  (c : τ C) ⊢
  @type_equiv_comp_right A B C eBC eAB c
  : τ (
      type_equiv_to eBC
        (type_equiv_to eAB
          (type_equiv_from eAB (type_equiv_from eBC c)))
      = c);

assert [A B C : Grpd]
  (eBC : τ (TypeEquiv B C))
  (eAB : τ (TypeEquiv A B))
  (a : τ A) ⊢
  (sigma_Fst (@type_equiv_comp_by_inverse A B C eBC eAB)) a
  ≡ @type_equiv_comp_left A B C eBC eAB a;

assert [A B C : Grpd]
  (eBC : τ (TypeEquiv B C))
  (eAB : τ (TypeEquiv A B))
  (c : τ C) ⊢
  (sigma_Snd (@type_equiv_comp_by_inverse A B C eBC eAB)) c
  ≡ @type_equiv_comp_right A B C eBC eAB c;

assert [A B C : Grpd]
  (eBC : τ (TypeEquiv B C))
  (eAB : τ (TypeEquiv A B)) ⊢
  @type_equiv_comp_is_equiv A B C eBC eAB
  : τ (@IsEquivMap
      A C
      (λ a : τ A,
        type_equiv_to eBC (type_equiv_to eAB a)));

assert [A B C : Grpd]
  (eBC : τ (TypeEquiv B C))
  (eAB : τ (TypeEquiv A B)) ⊢
  @type_equiv_comp A B C eBC eAB
  : τ (TypeEquiv A C);

assert [A B C : Grpd]
  (eBC : τ (TypeEquiv B C))
  (eAB : τ (TypeEquiv A B))
  (a : τ A) ⊢
  type_equiv_to (@type_equiv_comp A B C eBC eAB) a
  ≡ type_equiv_to eBC (type_equiv_to eAB a);

assert [A B C : Grpd]
  (eBC : τ (TypeEquiv B C))
  (eAB : τ (TypeEquiv A B))
  (c : τ C) ⊢
  type_equiv_from (@type_equiv_comp A B C eBC eAB) c
  ≡ type_equiv_from eAB (type_equiv_from eBC c);

assert [A B C : Grpd]
  (eBC : τ (TypeEquiv B C))
  (eAB : τ (TypeEquiv A B))
  (c : τ C) ⊢
  type_equiv_right (@type_equiv_comp A B C eBC eAB) c
  ≡ @type_equiv_comp_right A B C eBC eAB c;

assert [A B C : Grpd]
  (eBC : τ (TypeEquiv B C))
  (eAB : τ (TypeEquiv A B))
  (a : τ A) ⊢
  type_equiv_left (@type_equiv_comp A B C eBC eAB) a
  : τ (
      type_equiv_from eAB
        (type_equiv_from eBC
          (type_equiv_to eBC (type_equiv_to eAB a)))
      = a);

assertnot [A B C : Grpd]
  (eBC : τ (TypeEquiv B C))
  (eAB : τ (TypeEquiv A B))
  (a : τ A) ⊢
  type_equiv_left (@type_equiv_comp A B C eBC eAB) a
  ≡ @type_equiv_comp_left A B C eBC eAB a;

assert [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (a : τ A) ⊢
  type_equiv_to
    (@type_equiv_comp A B B (@type_equiv_refl B) e)
    a
  ≡ type_equiv_to e a;

assert [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (a : τ A) ⊢
  type_equiv_to
    (@type_equiv_comp A A B e (@type_equiv_refl A))
    a
  ≡ type_equiv_to e a;

assert [A B C D : Grpd]
  (eCD : τ (TypeEquiv C D))
  (eBC : τ (TypeEquiv B C))
  (eAB : τ (TypeEquiv A B))
  (a : τ A) ⊢
  type_equiv_to
    (@type_equiv_comp A C D eCD
      (@type_equiv_comp A B C eBC eAB))
    a
  ≡ type_equiv_to
      (@type_equiv_comp A B D
        (@type_equiv_comp B C D eCD eBC)
        eAB)
      a;

// Unit laws compute on forward maps, not by package-level eta.
assertnot [A B : Grpd]
  (e : τ (TypeEquiv A B)) ⊢
  @type_equiv_comp A B B (@type_equiv_refl B) e
  ≡ e;

// Groupoid-level Pi and contractible-fibre type equivalence infrastructure.
assert [A : Grpd] [B : τ A → Grpd] ⊢
  τ (@Pi_grpd A B) ≡ Π x : τ A, τ (B x);

assert [A B : Grpd] ⊢
  τ (Function_grpd A B) ≡ (τ A → τ B);

assert [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (a : τ A) ⊢
  type_equiv_to e a
  : τ B;

assert [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (b : τ B) ⊢
  type_equiv_from e b
  : τ A;

assert [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (b : τ B) ⊢
  type_equiv_right e b
  : τ (type_equiv_to e (type_equiv_from e b) = b);

assert [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (a : τ A) ⊢
  type_equiv_left e a
  : τ (type_equiv_from e (type_equiv_to e a) = a);

assert [A : Grpd] ⊢
  type_equiv_to (@type_equiv_refl A)
  ≡ λ x : τ A, x;

assert [A : Grpd] (a : τ A) ⊢
  type_equiv_from (@type_equiv_refl A) a
  ≡ a;

assert [A : Grpd] (a : τ A) ⊢
  type_equiv_right (@type_equiv_refl A) a
  ≡ eq_refl a;

assert [A : Grpd] (a : τ A) ⊢
  type_equiv_left (@type_equiv_refl A) a
  ≡ eq_refl a;

assert [A : Grpd] (a : τ A) ⊢
  @coe_grpd A A (eq_refl A) a
  ≡ a;

assert [A : Grpd] ⊢
  @idtoequiv_grpd A A (eq_refl A)
  ≡ @type_equiv_refl A;

assert [A : Grpd] ⊢
  @grpd_equiv_path A A (@type_equiv_refl A)
  ≡ @eq_refl Grpd_grpd A;

assert [A A' B B' : Grpd] ⊢
  @ProductGrpdPathView A A' B B'
  ≡ `Σ_ pA : τ (@= Grpd_grpd A A'),
     @PathOver Grpd_grpd (λ _ : Grpd, Grpd_grpd) A A' pA B B';

assert [A A' B B' : Grpd]
  (pA : τ (@= Grpd_grpd A A'))
  (pB : τ (@PathOver Grpd_grpd (λ _ : Grpd, Grpd_grpd) A A' pA B B')) ⊢
  @product_grpd_path A A' B B' pA pB
  : τ (@= Grpd_grpd (Product_grpd A B) (Product_grpd A' B'));

assert [A A' B B' : Grpd]
  (eA : τ (TypeEquiv A A'))
  (eB : τ (TypeEquiv B B')) ⊢
  @grpd_equiv_path
      (Product_grpd A B)
      (Product_grpd A' B')
      (@product_type_equiv A A' B B' eA eB)
  ≡ @product_grpd_path
      A
      A'
      B
      B'
      (@grpd_equiv_path A A' eA)
      (@const_pathover
        Grpd_grpd
        Grpd_grpd
        A
        A'
        B
        B'
        (@grpd_equiv_path A A' eA)
        (@grpd_equiv_path B B' eB));

assert [A A' B B' : Grpd]
  (pA : τ (@= Grpd_grpd A A'))
  (pB : τ (@PathOver Grpd_grpd (λ _ : Grpd, Grpd_grpd) A A' pA B B')) ⊢
  @idtoequiv_grpd
    (Product_grpd A B)
    (Product_grpd A' B')
    (@product_grpd_path A A' B B' pA pB)
  ≡ @product_type_equiv
      A
      A'
      B
      B'
      (@idtoequiv_grpd A A' pA)
      (@idtoequiv_grpd
        B
        B'
        (@const_pathover_path
          Grpd_grpd
          Grpd_grpd
          A
          A'
          B
          B'
          pA
          pB));

assert [A B : Grpd] ⊢
  @idtoequiv_grpd
    (Product_grpd A B)
    (Product_grpd A B)
    (@product_grpd_path
      A
      A
      B
      B
      (eq_refl A)
      (@pathover_refl Grpd_grpd (λ _ : Grpd, Grpd_grpd) A B))
  ≡ @product_type_equiv
      A
      A
      B
      B
      (@type_equiv_refl A)
      (@type_equiv_refl B);

assert ⊢
  grpd_univalence_by_decoder
  : τ GrpdUnivalenceByDecoder;

// Groupoid univalence decoder round trips and transport/action coherence.
assert ⊢
  grpd_univalence_from_decoder
  : τ GrpdUnivalence;

assert [A B : Grpd] ⊢
  grpd_univalence_from_decoder A B
  : τ (@IsEquivMap
      (@= Grpd_grpd A B)
      (TypeEquiv A B)
      (λ p : τ (@= Grpd_grpd A B), @idtoequiv_grpd A B p));

assert [A B : Grpd]
  (e : τ (TypeEquiv A B)) ⊢
  @grpd_univalence_selected_path A B e
  ≡ @grpd_equiv_path A B e;

assert [A B : Grpd]
  (e : τ (TypeEquiv A B)) ⊢
  @is_contr_center
    (@HFiber
      (@= Grpd_grpd A B)
      (TypeEquiv A B)
      (λ p : τ (@= Grpd_grpd A B), @idtoequiv_grpd A B p)
      e)
    (@is_equiv_fiber
      (@= Grpd_grpd A B)
      (TypeEquiv A B)
      (λ p : τ (@= Grpd_grpd A B), @idtoequiv_grpd A B p)
      (grpd_univalence_from_decoder A B)
      e)
  ≡ @Struct_sigma
      (@= Grpd_grpd A B)
      (λ p : τ (@= Grpd_grpd A B),
        @idtoequiv_grpd A B p = e)
      (@grpd_equiv_path A B e)
      (@idtoequiv_grpd_equiv_path A B e);

assert [A B : Grpd]
  (p : τ (@= Grpd_grpd A B)) ⊢
  @grpd_equiv_path_idtoequiv A B p
  : τ (
      @grpd_equiv_path A B (@idtoequiv_grpd A B p)
      = p);

assert [A B : Grpd]
  (e : τ (TypeEquiv A B)) ⊢
  @idtoequiv_grpd_equiv_path A B e
  : τ (
      @idtoequiv_grpd A B (@grpd_equiv_path A B e)
      = e);

// Both arbitrary round trips are propositions, not broad runtime eta rules.
assertnot [A B : Grpd]
  (p : τ (@= Grpd_grpd A B)) ⊢
  @grpd_equiv_path A B (@idtoequiv_grpd A B p)
  ≡ p;

assertnot [A B : Grpd]
  (e : τ (TypeEquiv A B)) ⊢
  @idtoequiv_grpd A B (@grpd_equiv_path A B e)
  ≡ e;

assert [A B : Grpd]
  (p : τ (@= Grpd_grpd A B))
  (a : τ A) ⊢
  @coe_grpd_idtoequiv A B p a
  : τ (
      @coe_grpd A B p a
      = type_equiv_to (@idtoequiv_grpd A B p) a);

assert [A : Grpd]
  (a : τ A) ⊢
  @coe_grpd_idtoequiv A A (eq_refl A) a
  ≡ @eq_refl A a;

assert [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (a : τ A) ⊢
  @grpd_equiv_path_coe A B e a
  : τ (
      @coe_grpd A B (@grpd_equiv_path A B e) a
      = type_equiv_to e a);

// The operational decoder square is propositional until constructor-path
// transports join; the broad runtime orientation is deliberately absent.
assertnot [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (a : τ A) ⊢
  @coe_grpd A B (@grpd_equiv_path A B e) a
  ≡ type_equiv_to e a;

assert [A : Grpd]
  [B C : τ A → Grpd]
  (e : Π x : τ A, τ (TypeEquiv (B x) (C x)))
  (f : τ (@Pi_grpd A B))
  (x : τ A) ⊢
  @grpd_equiv_path_pi_action A B C e f x
  : τ (
      (@coe_grpd
        (@Pi_grpd A B)
        (@Pi_grpd A C)
        (@grpd_equiv_path
          (@Pi_grpd A B)
          (@Pi_grpd A C)
          (@pi_type_equiv_same_domain A B C e))
        f)
        x
      = type_equiv_to (e x) (f x));

assert [A A' B B' : Grpd]
  (eA : τ (TypeEquiv A A'))
  (eB : τ (TypeEquiv B B'))
  (x : τ A)
  (y : τ B) ⊢
  @grpd_equiv_path_coe
    (Product_grpd A B)
    (Product_grpd A' B')
    (@product_type_equiv A A' B B' eA eB)
    (@Product_pair_grpd A B x y)
  : τ (
      @coe_grpd
        (Product_grpd A B)
        (Product_grpd A' B')
        (@grpd_equiv_path
          (Product_grpd A B)
          (Product_grpd A' B')
          (@product_type_equiv A A' B B' eA eB))
        (@Product_pair_grpd A B x y)
      = @Product_pair_grpd A' B'
          (type_equiv_to eA x)
          (type_equiv_to eB y));

assertnot [A A' B B' : Grpd]
  (eA : τ (TypeEquiv A A'))
  (eB : τ (TypeEquiv B B'))
  (x : τ A)
  (y : τ B) ⊢
  @coe_grpd
    (Product_grpd A B)
    (Product_grpd A' B')
    (@product_grpd_path
      A A' B B'
      (@grpd_equiv_path A A' eA)
      (@const_pathover
        Grpd_grpd Grpd_grpd A A' B B'
        (@grpd_equiv_path A A' eA)
        (@grpd_equiv_path B B' eB)))
    (@Product_pair_grpd A B x y)
  ≡ @Product_pair_grpd A' B'
      (type_equiv_to eA x)
      (type_equiv_to eB y);

// An arbitrary legacy ua capability is not silently identified with the
// canonical decoder; new coherence consumers use the decoder package above.
assertnot (U : τ GrpdUnivalence)
  [A B : Grpd]
  (e : τ (TypeEquiv A B)) ⊢
  @ua_grpd U A B e
  ≡ @grpd_equiv_path A B e;

assert [A : Grpd] (a : τ A) ⊢
  type_equiv_to (@idtoequiv_grpd A A (eq_refl A)) a
  ≡ a;

assert (U : τ GrpdUnivalence) [A B : Grpd]
  (e : τ (TypeEquiv A B)) ⊢
  @ua_grpd U A B e
  : τ (@= Grpd_grpd A B);

assert (U : τ GrpdUnivalence)
  [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (a : τ A) ⊢
  @coe_grpd A B (@ua_grpd U A B e) a
  ≡ type_equiv_to e a;

// catalog-area: Groupoid-universe identity view
// The named Phase-13 fallback exposes the existing TypeEquiv classifier while
// keeping public universe equality opaque.
assert [A B : Grpd] ⊢
  @GrpdPathView A B
  ≡ TypeEquiv A B;

assert [A : Grpd] ⊢
  @grpd_path_refl A
  ≡ @type_equiv_refl A;

assert [A : Grpd] ⊢
  type_equiv_to (@grpd_path_refl A)
  ≡ λ x : τ A, x;

assert [A B : Grpd]
  (p : τ (@= Grpd_grpd A B)) ⊢
  @grpd_path_encode A B p
  : τ (@GrpdPathView A B);

assert [A B : Grpd]
  (p : τ (@= Grpd_grpd A B)) ⊢
  @grpd_path_encode A B p
  ≡ @idtoequiv_grpd A B p;

assert [A : Grpd] ⊢
  @grpd_path_encode A A (@eq_refl Grpd_grpd A)
  ≡ @grpd_path_refl A;

assert [A B : Grpd]
  (e : τ (@GrpdPathView A B)) ⊢
  @grpd_path_decode A B e
  : τ (@= Grpd_grpd A B);

assert [A B : Grpd]
  (e : τ (@GrpdPathView A B)) ⊢
  @grpd_path_decode A B e
  ≡ @grpd_equiv_path A B e;

assert [A : Grpd] ⊢
  @grpd_path_decode A A (@grpd_path_refl A)
  ≡ @eq_refl Grpd_grpd A;

assert [A B : Grpd]
  (p : τ (@= Grpd_grpd A B)) ⊢
  @grpd_path_decode_encode A B p
  : τ (
      @grpd_path_decode A B (@grpd_path_encode A B p)
      = p);

assert [A B : Grpd]
  (e : τ (@GrpdPathView A B)) ⊢
  @grpd_path_encode_decode A B e
  : τ (
      @grpd_path_encode A B (@grpd_path_decode A B e)
      = e);

assert [A B : Grpd]
  (e : τ (@GrpdPathView A B))
  (a : τ A) ⊢
  @grpd_path_decode_coe A B e a
  : τ (
      @coe_grpd A B (@grpd_path_decode A B e) a
      = type_equiv_to e a);

// Product encode/decode diamonds remain owned by the existing componentwise
// rules and are visible through the transparent named maps.
assert [A A' B B' : Grpd]
  (eA : τ (@GrpdPathView A A'))
  (eB : τ (@GrpdPathView B B')) ⊢
  @grpd_path_decode
    (Product_grpd A B)
    (Product_grpd A' B')
    (@product_type_equiv A A' B B' eA eB)
  ≡ @product_grpd_path
      A A' B B'
      (@grpd_path_decode A A' eA)
      (@const_pathover
        Grpd_grpd Grpd_grpd A A' B B'
        (@grpd_path_decode A A' eA)
        (@grpd_path_decode B B' eB));

assert [A A' B B' : Grpd]
  (pA : τ (@= Grpd_grpd A A'))
  (pB : τ (@PathOver
      Grpd_grpd (λ _ : Grpd, Grpd_grpd) A A' pA B B')) ⊢
  @grpd_path_encode
    (Product_grpd A B)
    (Product_grpd A' B')
    (@product_grpd_path A A' B B' pA pB)
  ≡ @product_type_equiv
      A A' B B'
      (@grpd_path_encode A A' pA)
      (@grpd_path_encode
        B B'
        (@const_pathover_path
          Grpd_grpd Grpd_grpd A A' B B' pA pB));

// The generic decoder square supplies Pi action under the named spelling.
assert [A : Grpd]
  [B C : τ A → Grpd]
  (e : Π x : τ A, τ (@GrpdPathView (B x) (C x)))
  (f : τ (@Pi_grpd A B))
  (x : τ A) ⊢
  @grpd_equiv_path_pi_action A B C e f x
  : τ (
      (@coe_grpd
        (@Pi_grpd A B)
        (@Pi_grpd A C)
        (@grpd_path_decode
          (@Pi_grpd A B)
          (@Pi_grpd A C)
          (@pi_type_equiv_same_domain A B C e))
        f)
        x
      = type_equiv_to (e x) (f x));

// Same-base Sigma equivalence is accepted by the view without adding a new
// decoder or transport body.
assert [A : Grpd]
  [P Q : τ A → Grpd]
  (e : Π x : τ A, τ (@GrpdPathView (P x) (Q x))) ⊢
  @grpd_path_decode
    (@Σ_ A P)
    (@Σ_ A Q)
    (@sigma_type_equiv_same_base A P Q e)
  : τ (@= Grpd_grpd (@Σ_ A P) (@Σ_ A Q));

assert ⊢
  @grpd_path_refl Grpd_grpd
  : τ (@GrpdPathView Grpd_grpd Grpd_grpd);

// Public equality and the named view remain a deliberate encode/decode
// boundary, including at the unstratified self-universe instance.
assertnot [A B : Grpd] ⊢
  @= Grpd_grpd A B
  ≡ @GrpdPathView A B;

assertnot [A B : Grpd]
  (e : τ (@GrpdPathView A B)) ⊢
  e
  : τ (@= Grpd_grpd A B);

assertnot [A B : Grpd]
  (p : τ (@= Grpd_grpd A B)) ⊢
  p
  : τ (@GrpdPathView A B);

// Both inverse laws and decoder transport remain propositional, not runtime
// cancellation or a hidden direct-equality computation rule.
assertnot [A B : Grpd]
  (p : τ (@= Grpd_grpd A B)) ⊢
  @grpd_path_decode A B (@grpd_path_encode A B p)
  ≡ p;

assertnot [A B : Grpd]
  (e : τ (@GrpdPathView A B)) ⊢
  @grpd_path_encode A B (@grpd_path_decode A B e)
  ≡ e;

assertnot [A B : Grpd]
  (e : τ (@GrpdPathView A B))
  (a : τ A) ⊢
  @coe_grpd A B (@grpd_path_decode A B e) a
  ≡ type_equiv_to e a;

assertnot ⊢
  @= Grpd_grpd Grpd_grpd Grpd_grpd
  ≡ @GrpdPathView Grpd_grpd Grpd_grpd;

// catalog-area: Truncation equivalence invariance
assert (n : TruncLevel)
  [A B : Grpd]
  (e : τ (TypeEquiv A B)) ⊢
  @is_trunc_grpd_equiv_path n A B e
  : τ (@= Grpd_grpd (IsTruncGrpd n A) (IsTruncGrpd n B));

assert (n : TruncLevel)
  [A B : Grpd]
  (e : τ (TypeEquiv A B)) ⊢
  @is_trunc_grpd_type_equiv n A B e
  : τ (TypeEquiv (IsTruncGrpd n A) (IsTruncGrpd n B));

assert (n : TruncLevel)
  [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (h : τ (IsTruncGrpd n A)) ⊢
  @is_trunc_grpd_equiv_to n A B e h
  : τ (IsTruncGrpd n B);

assert (n : TruncLevel)
  [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (h : τ (IsTruncGrpd n B)) ⊢
  @is_trunc_grpd_equiv_from n A B e h
  : τ (IsTruncGrpd n A);

assert (n : TruncLevel)
  [A : Grpd] ⊢
  @is_trunc_grpd_equiv_path n A A (@type_equiv_refl A)
  ≡ @eq_refl Grpd_grpd (IsTruncGrpd n A);

assert (n : TruncLevel)
  [A : Grpd] ⊢
  @is_trunc_grpd_type_equiv n A A (@type_equiv_refl A)
  ≡ @type_equiv_refl (IsTruncGrpd n A);

assert (n : TruncLevel)
  [A : Grpd]
  (h : τ (IsTruncGrpd n A)) ⊢
  @is_trunc_grpd_equiv_to n A A (@type_equiv_refl A) h
  ≡ h;

assert (n : TruncLevel)
  [A : Grpd]
  (h : τ (IsTruncGrpd n A)) ⊢
  @is_trunc_grpd_equiv_from n A A (@type_equiv_refl A) h
  ≡ h;

assert (n : TruncLevel)
  [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (h : τ (IsTruncGrpd n B)) ⊢
  type_equiv_right (@is_trunc_grpd_type_equiv n A B e) h
  : τ (
      @is_trunc_grpd_equiv_to n A B e
        (@is_trunc_grpd_equiv_from n A B e h)
      = h);

assert (n : TruncLevel)
  [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (h : τ (IsTruncGrpd n A)) ⊢
  type_equiv_left (@is_trunc_grpd_type_equiv n A B e) h
  : τ (
      @is_trunc_grpd_equiv_from n A B e
        (@is_trunc_grpd_equiv_to n A B e h)
      = h);

// An arbitrary self-equivalence is not silently treated as reflexivity.
assertnot (n : TruncLevel)
  [A : Grpd]
  (e : τ (TypeEquiv A A))
  (h : τ (IsTruncGrpd n A)) ⊢
  @is_trunc_grpd_equiv_to n A A e h
  ≡ h;

// catalog-area: Categorical object-truncation invariance
assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F)) ⊢
  @omega_equiv_along_obj_path A B F u
  : τ (@= Grpd_grpd (Obj A) (Obj B));

assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F)) ⊢
  @omega_equiv_along_obj_type_equiv A B F u
  : τ (TypeEquiv (Obj A) (Obj B));

assert (n : TruncLevel)
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F)) ⊢
  @is_obj_trunc_cat_equiv_type_equiv n A B F u
  : τ (TypeEquiv (IsObjTruncCat n A) (IsObjTruncCat n B));

assert (n : TruncLevel)
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (h : τ (IsObjTruncCat n A)) ⊢
  @is_obj_trunc_cat_equiv_to n A B F u h
  : τ (IsObjTruncCat n B);

assert (n : TruncLevel)
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (h : τ (IsObjTruncCat n B)) ⊢
  @is_obj_trunc_cat_equiv_from n A B F u h
  : τ (IsObjTruncCat n A);

// Stable facade casting is theorem-level and does not decode an explicit
// reflexive native package to raw eq_refl at runtime.
assertnot [A : Cat] ⊢
  @omega_equiv_along_obj_path
    A A (@id_func A) (@omega_equiv_along_refl Cat_cat A)
  ≡ @eq_refl Grpd_grpd (Obj A);

assertnot [A : Cat] ⊢
  @omega_equiv_along_obj_type_equiv
    A A (@id_func A) (@omega_equiv_along_refl Cat_cat A)
  ≡ @type_equiv_refl (Obj A);

assertnot (n : TruncLevel)
  [A : Cat] ⊢
  @is_obj_trunc_cat_equiv_type_equiv
    n A A (@id_func A) (@omega_equiv_along_refl Cat_cat A)
  ≡ @type_equiv_refl (IsObjTruncCat n A);

assertnot (n : TruncLevel)
  [A : Cat]
  (h : τ (IsObjTruncCat n A)) ⊢
  @is_obj_trunc_cat_equiv_to
    n A A (@id_func A) (@omega_equiv_along_refl Cat_cat A) h
  ≡ h;

assertnot (n : TruncLevel)
  [A : Cat]
  (h : τ (IsObjTruncCat n A)) ⊢
  @is_obj_trunc_cat_equiv_from
    n A A (@id_func A) (@omega_equiv_along_refl Cat_cat A) h
  ≡ h;

assert (n : TruncLevel)
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (h : τ (IsObjTruncCat n B)) ⊢
  type_equiv_right
    (@is_obj_trunc_cat_equiv_type_equiv n A B F u) h
  : τ (
      @is_obj_trunc_cat_equiv_to n A B F u
        (@is_obj_trunc_cat_equiv_from n A B F u h)
      = h);

assert (n : TruncLevel)
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (h : τ (IsObjTruncCat n A)) ⊢
  type_equiv_left
    (@is_obj_trunc_cat_equiv_type_equiv n A B F u) h
  : τ (
      @is_obj_trunc_cat_equiv_from n A B F u
        (@is_obj_trunc_cat_equiv_to n A B F u h)
      = h);

// Cast-induced object equivalence does not runtime expose the functor map.
assertnot [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x : τ (Obj A)) ⊢
  type_equiv_to (@omega_equiv_along_obj_type_equiv A B F u) x
  ≡ @fapp0 A B F x;

// Arbitrary fixed-map evidence is not silently treated as reflexivity.
assertnot [A : Cat]
  [F : τ (Functor A A)]
  (u : τ (@OmegaEquivAlong Cat_cat A A F)) ⊢
  @omega_equiv_along_obj_type_equiv A A F u
  ≡ @type_equiv_refl (Obj A);

assertnot (n : TruncLevel)
  [A : Cat]
  [F : τ (Functor A A)]
  (u : τ (@OmegaEquivAlong Cat_cat A A F))
  (h : τ (IsObjTruncCat n A)) ⊢
  @is_obj_trunc_cat_equiv_to n A A F u h
  ≡ h;

// catalog-area: auto

// Constructor-specific computational-univalence skeleton.
assert [A B : Grpd] ⊢
  τ (Product_grpd A B)
  ≡ @τΣ_ A (λ _ : τ A, B);

assert [A : Grpd]
  [P : τ A → Grpd]
  (u v : @τΣ_ A P) ⊢
  @= (@Σ_ A P) u v
  ≡ @SigmaPathView A P u v;

assert [A B : Grpd]
  (p q : τ (Product_grpd A B)) ⊢
  @= (Product_grpd A B) p q
  ≡ @ProductPathView A B p q;

assert [A B : Grpd]
  (p q : τ (Product_grpd A B)) ⊢
  τ (@ProductPathView A B p q)
  ≡ τ (@SigmaPathView A (λ _ : τ A, B) p q);

assertnot [A B : Grpd]
  (p q : τ (Product_grpd A B)) ⊢
  @ProductPathView A B p q
  ≡ @SigmaPathView A (λ _ : τ A, B) p q;

assert [A B : Grpd]
  [p q : τ (Product_grpd A B)]
  (w : τ (@ProductPathView A B p q)) ⊢
  @sigma_view_to_product_path A B p q
    (@product_path_to_sigma_view A B p q w)
  ≡ w;

assert [A B : Grpd]
  [p q : τ (Product_grpd A B)]
  (w : τ (@SigmaPathView A (λ _ : τ A, B) p q)) ⊢
  @product_path_to_sigma_view A B p q
    (@sigma_view_to_product_path A B p q w)
  ≡ w;

assert [A B : Grpd]
  [p q : τ (Product_grpd A B)]
  (base : τ (@= A (sigma_Fst p) (sigma_Fst q)))
  (fibre : τ (@PathOver
    A (λ _ : τ A, B)
    (sigma_Fst p) (sigma_Fst q) base
    (sigma_Snd p) (sigma_Snd q))) ⊢
  @product_path_base A B p q
    (@product_path_intro A B p q base fibre)
  ≡ base;

assert [A B : Grpd]
  [p q : τ (Product_grpd A B)]
  (base : τ (@= A (sigma_Fst p) (sigma_Fst q)))
  (fibre : τ (@PathOver
    A (λ _ : τ A, B)
    (sigma_Fst p) (sigma_Fst q) base
    (sigma_Snd p) (sigma_Snd q))) ⊢
  @product_path_fibre A B p q
    (@product_path_intro A B p q base fibre)
  ≡ fibre;

assert [A B : Grpd]
  [p q : τ (Product_grpd A B)]
  (Q : τ (@ProductPathView A B p q) → Grpd)
  (c : Π base : τ (@= A (sigma_Fst p) (sigma_Fst q)),
       Π fibre : τ (@PathOver
         A
         (λ _ : τ A, B)
         (sigma_Fst p)
         (sigma_Fst q)
         base
         (sigma_Snd p)
         (sigma_Snd q)),
       τ (Q (@product_path_intro A B p q base fibre)))
  (base : τ (@= A (sigma_Fst p) (sigma_Fst q)))
  (fibre : τ (@PathOver
    A (λ _ : τ A, B)
    (sigma_Fst p) (sigma_Fst q) base
    (sigma_Snd p) (sigma_Snd q))) ⊢
  @product_path_ind A B p q Q c
    (@product_path_intro A B p q base fibre)
  ≡ c base fibre;

assert [A B : Grpd]
  (p : τ (Product_grpd A B)) ⊢
  @product_path_base A B p p (@product_path_refl A B p)
  ≡ @eq_refl A (sigma_Fst p);

assert [A B : Grpd]
  (p : τ (Product_grpd A B)) ⊢
  @product_path_fibre A B p p (@product_path_refl A B p)
  ≡ @pathover_refl A (λ _ : τ A, B) (sigma_Fst p) (sigma_Snd p);

assertnot [A B : Grpd]
  (p : τ (Product_grpd A B)) ⊢
  @eq_refl (Product_grpd A B) p
  ≡ @product_path_refl A B p;

assert [A B : Grpd]
  (x : τ A)
  (y : τ B) ⊢
  sigma_Fst (@eq_refl (Product_grpd A B) (@Product_pair_grpd A B x y))
  ≡ eq_refl x;

assert [A B : Grpd]
  (x : τ A)
  (y : τ B) ⊢
  sigma_Snd (@eq_refl (Product_grpd A B) (@Product_pair_grpd A B x y))
  ≡ @pathover_refl A (λ _ : τ A, B) x y;

assert [A B : Grpd]
  [x : τ A]
  [u v : τ B]
  (q : τ (u = v)) ⊢
  @const_pathover A B x x u v (eq_refl x) q
  ≡ q;

assert [A B : Grpd]
  [x : τ A]
  [u v : τ B]
  (q : τ (@PathOver A (λ _ : τ A, B) x x (eq_refl x) u v)) ⊢
  @const_pathover_path A B x x u v (eq_refl x) q
  ≡ q;

assert [A B : Grpd]
  (x : τ A)
  (y : τ B)
  (M : τ (Product_grpd A B) → Grpd)
  (u : τ (M (@Product_pair_grpd A B x y))) ⊢
  @ind_eq
    (Product_grpd A B)
    (@Product_pair_grpd A B x y)
    (@Product_pair_grpd A B x y)
    (@eq_refl (Product_grpd A B) (@Product_pair_grpd A B x y))
    M
    u
  ≡ u;

assert [A A' B B' : Grpd]
  (eA : τ (TypeEquiv A A'))
  (eB : τ (TypeEquiv B B'))
  (x : τ A)
  (y : τ B) ⊢
  type_equiv_to (@product_type_equiv A A' B B' eA eB)
    (@Product_pair_grpd A B x y)
  ≡ @Product_pair_grpd A' B'
      (type_equiv_to eA x)
      (type_equiv_to eB y);

assert (U : τ GrpdUnivalence)
  [A A' B B' : Grpd]
  (eA : τ (TypeEquiv A A'))
  (eB : τ (TypeEquiv B B'))
  (x : τ A)
  (y : τ B) ⊢
  @coe_grpd
    (Product_grpd A B)
    (Product_grpd A' B')
    (@ua_grpd U
      (Product_grpd A B)
      (Product_grpd A' B')
      (@product_type_equiv A A' B B' eA eB))
    (@Product_pair_grpd A B x y)
  ≡ @Product_pair_grpd A' B'
      (type_equiv_to eA x)
      (type_equiv_to eB y);

assert [A : Grpd]
  [P Q : τ A → Grpd]
  (e : Π x : τ A, τ (TypeEquiv (P x) (Q x)))
  (x : τ A)
  (u : τ (P x)) ⊢
  type_equiv_to (@sigma_type_equiv_same_base A P Q e)
    (@Struct_sigma A P x u)
  ≡ @Struct_sigma A Q x (type_equiv_to (e x) u);

assert (U : τ GrpdUnivalence)
  [A : Grpd]
  [P Q : τ A → Grpd]
  (e : Π x : τ A, τ (TypeEquiv (P x) (Q x)))
  (x : τ A)
  (u : τ (P x)) ⊢
  @coe_grpd
    (@Σ_ A P)
    (@Σ_ A Q)
    (@ua_grpd U (@Σ_ A P) (@Σ_ A Q)
      (@sigma_type_equiv_same_base A P Q e))
    (@Struct_sigma A P x u)
  ≡ @Struct_sigma A Q x (type_equiv_to (e x) u);

assert [A : Grpd]
  [B C : τ A → Grpd]
  (e : Π x : τ A, τ (TypeEquiv (B x) (C x)))
  (f : τ (@Pi_grpd A B))
  (x : τ A) ⊢
  type_equiv_to (@pi_type_equiv_same_domain A B C e) f x
  ≡ type_equiv_to (e x) (f x);

assert (U : τ GrpdUnivalence)
  [A : Grpd]
  [B C : τ A → Grpd]
  (e : Π x : τ A, τ (TypeEquiv (B x) (C x)))
  (f : τ (@Pi_grpd A B))
  (x : τ A) ⊢
  @coe_grpd
    (@Pi_grpd A B)
    (@Pi_grpd A C)
    (@ua_grpd U (@Pi_grpd A B) (@Pi_grpd A C)
      (@pi_type_equiv_same_domain A B C e))
    f
    x
  ≡ type_equiv_to (e x) (f x);

// Core inclusion/path-to-arrow is functor-owned. Composition is checked
// through the generic fapp1_fapp0 composition rule, not a specialized rule.
assert [C : Cat] (x : τ (Obj C)) ⊢
  @path_to_hom C x x (eq_refl x)
  ≡ @id C x;

assert [C : Cat]
  [x y z : τ (Obj C)]
  (p : τ (x = y))
  (q : τ (y = z)) ⊢
  @comp_fapp0 C x y z
    (@path_to_hom C y z q)
    (@path_to_hom C x y p)
  ≡ @path_to_hom C x z
      (@comp_fapp0 (Path_cat (Obj C)) x y z q p);

assert [C : Cat] [w x y z : τ (Obj C)]
  (h : τ (Hom C y z))
  (g : τ (Hom C x y))
  (f : τ (Hom C w x)) ⊢
  @comp_assoc C w x y z h g f
  ≡ eq_refl
      (@comp_fapp0 C w y z h
        (@comp_fapp0 C w x y g f));

assert [C : Cat] [x y z : τ (Obj C)]
  (j : τ (IsoEvidence C y z))
  (i : τ (IsoEvidence C x y)) ⊢
  @iso_evidence_to C x z
    (@iso_evidence_comp C x y z j i)
  ≡ @comp_fapp0 C x y z
      (@iso_evidence_to C y z j)
      (@iso_evidence_to C x y i);

assert [C : Cat] [x y z : τ (Obj C)]
  (j : τ (IsoEvidence C y z))
  (i : τ (IsoEvidence C x y)) ⊢
  @iso_evidence_from C x z
    (@iso_evidence_comp C x y z j i)
  ≡ @comp_fapp0 C z y x
      (@iso_evidence_from C x y i)
      (@iso_evidence_from C y z j);

assert [C D : Cat] (F : τ (Functor C D))
  [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y)) ⊢
  @iso_evidence_to
    D
    (@fapp0 C D F x)
    (@fapp0 C D F y)
    (@iso_evidence_fmap C D F x y i)
  ≡ @fapp1_fapp0 C D F x y
      (@iso_evidence_to C x y i);

assert [C D : Cat] (F : τ (Functor C D))
  [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y)) ⊢
  @iso_evidence_from
    D
    (@fapp0 C D F x)
    (@fapp0 C D F y)
    (@iso_evidence_fmap C D F x y i)
  ≡ @fapp1_fapp0 C D F y x
      (@iso_evidence_from C x y i);

assert ⊢ τ (Obj Grpd_cat) ≡ Grpd;

assert ⊢ τ (Obj Cat_cat) ≡ Cat;

assert (A B : Cat) ⊢ Hom_cat Cat_cat A B ≡ Functor_cat A B;

assert [K : Cat] ⊢
  @eq_refl Cat_grpd (Catd_cat K)
  : τ (@= Cat_grpd (Catd_cat K) (Functor_cat K Cat_cat));

assert [K : Cat] ⊢
  Obj (Catd_cat K) ≡ Obj (Functor_cat K Cat_cat);

assert [K : Cat] (E D : τ (Catd K)) ⊢
  Hom_cat (Catd_cat K) E D ≡ Functord_cat E D;

assert [K : Cat] (E D : τ (Catd K)) ⊢
  Obj (@Functord_cat K E D)
    ≡ Obj (@Transf_cat K Cat_cat E D);

assert [K : Cat] [E D : τ (Catd K)] (FF GG : τ (Functord E D)) ⊢
  Hom_cat (Functord_cat E D) FF GG ≡ Transfd_cat FF GG;

assert [K : Cat] [E D : τ (Catd K)] (FF GG : τ (Functord E D)) ⊢
  Obj (@Transfd_cat K E D FF GG)
    ≡ Obj (Hom_cat (@Transf_cat K Cat_cat E D) FF GG);

assert [K : Cat] [E D : τ (Catd K)] (FF GG : τ (Functord E D)) ⊢
  @eq_refl Cat_grpd (@Transfd_cat K E D FF GG)
  : τ (@= Cat_grpd
      (@Transfd_cat K E D FF GG)
      (Hom_cat (@Transf_cat K Cat_cat E D) FF GG));

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D)) ⊢
  @id (@Functord_cat K E D) FF
    ≡ @id_transfd K E D FF;

assert [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A)) (y : τ (Obj B)) ⊢
  @fapp0 B Cat_cat (@hom_ A B F W) y ≡ Hom_cat A W (@fapp0 B A F y);

assert [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A)) (x : τ (Obj (Op_cat B))) ⊢
  @fapp0 (Op_cat B) Cat_cat (@hom_con A W B F) x ≡ Hom_cat A (@fapp0 B A F x) W;

// Primitive contravariant represented-family action.
assert [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A))
  (X Y : τ (Obj B)) ⊢
  @fapp1_func _ Cat_cat (@hom_con A W B F) X Y
    ≡ @hom_con_precomp_tele_func A B F W X Y;

assert [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A))
  (X Y : τ (Obj B)) (p : τ (Hom (Op_cat B) X Y)) ⊢
  @fapp0
    (Hom_cat (Op_cat B) X Y)
    (Functor_cat
      (Hom_cat A (@fapp0 B A F X) W)
      (Hom_cat A (@fapp0 B A F Y) W))
    (@hom_con_precomp_tele_func A B F W X Y)
    p
  ≡ @hom_precomp_along_func B A F W Y X p;

assert [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A))
  (X Y : τ (Obj B)) (p : τ (Hom (Op_cat B) X Y)) ⊢
  @fapp1_fapp0 _ Cat_cat (@hom_con A W B F) X Y p
    ≡ @hom_precomp_along_func B A F W Y X p;

assert [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A))
  (X Y : τ (Obj B)) (p : τ (Hom (Op_cat B) X Y))
  (g : τ (Hom A (@fapp0 B A F X) W)) ⊢
  @fapp0
    (Hom_cat A (@fapp0 B A F X) W)
    (Hom_cat A (@fapp0 B A F Y) W)
    (@fapp1_fapp0 _ Cat_cat (@hom_con A W B F) X Y p)
    g
  ≡ @hom_precomp_along_fapp0 B A F W Y X p g;

assert [B : Cat] (F : τ (Functor B Terminal_cat))
  (W : τ (Obj Terminal_cat)) ⊢
  @hom_con Terminal_cat W B F
    ≡ @Const_catd (Op_cat B) Terminal_cat;

assert [A B : Cat] (u W : τ (Obj A)) ⊢
  @hom_con A W B (@Const_func B A u)
    ≡ @Const_catd (Op_cat B) (Hom_cat A u W);

assert [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj (Op_cat A))) ⊢
  @fapp0 (Op_cat A) (Catd_cat B) (@hom_int A B F) W
    ≡ @hom_ A B F W;

assert [A B : Cat] (F : τ (Functor B A)) (X : τ (Obj (Op_cat A))) (Y : τ (Obj B)) ⊢
  @fapp0 B Cat_cat (@fapp0 (Op_cat A) (Catd_cat B) (@hom_int A B F) X) Y
    ≡ Hom_cat A X (fapp0 F Y);

// Generic represented-object action of `hom_int`.
assert [A B : Cat] (F : τ (Functor B A)) (y x : τ (Obj A)) ⊢
  @fapp1_func (Op_cat A) (@Catd_cat B) (@hom_int A B F) y x
    ≡ @hom_int_precomp_tele_func A B F y x;

assert [A B : Cat] (F : τ (Functor B A)) (y x : τ (Obj A))
  (p : τ (Hom (Op_cat A) y x)) ⊢
  @fapp1_fapp0 (Op_cat A) (@Catd_cat B) (@hom_int A B F) y x p
    ≡ @hom_int_precomp_func A B F y x p;

assert [A B : Cat] (F : τ (Functor B A)) (y x : τ (Obj A))
  (p : τ (Hom (Op_cat A) y x)) (b : τ (Obj B)) ⊢
  @tapp0_fapp0
    B
    Cat_cat
    (@hom_ A B F y)
    (@hom_ A B F x)
    b
    (@hom_int_precomp_func A B F y x p)
    ≡ @hom_precomp_along_func A A (@id_func A) (@fapp0 B A F b) x y p;

// Higher represented-object action: q |-> Hom_func(p,F[q]).
assert [A B : Cat] (F : τ (Functor B A)) (y x : τ (Obj A))
  (p : τ (Hom (Op_cat A) y x)) (b c : τ (Obj B)) ⊢
  @tapp1_func
    B Cat_cat
    (@hom_ A B F y) (@hom_ A B F x)
    b c
    (@hom_int_precomp_func A B F y x p)
  ≡ @comp_fapp0
      Cat_cat
      (Hom_cat B b c)
      (Product_cat
        (Hom_cat A x y)
        (Hom_cat A (@fapp0 B A F b) (@fapp0 B A F c)))
      (Functor_cat
        (Hom_cat A y (@fapp0 B A F b))
        (Hom_cat A x (@fapp0 B A F c)))
      (@Hom_tele_func A y x (@fapp0 B A F b) (@fapp0 B A F c))
      (Struct_sigma
        (@Const_func (Hom_cat B b c) (Hom_cat A x y) p)
        (@fapp1_func B A F b c));

assert [A B : Cat] (F : τ (Functor B A)) (y x : τ (Obj A))
  (p : τ (Hom (Op_cat A) y x)) (b c : τ (Obj B))
  (q : τ (Hom B b c)) ⊢
  @tapp1_fapp0
    B Cat_cat
    (@hom_ A B F y) (@hom_ A B F x)
    b c
    (@hom_int_precomp_func A B F y x p)
    q
  ≡ @Hom_func
      A y x
      (@fapp0 B A F b) (@fapp0 B A F c)
      p
      (@fapp1_fapp0 B A F b c q);

// Owner-first evaluation of the semantic composite reaches the same cap.
assert [A B : Cat] (F : τ (Functor B A)) (y x : τ (Obj A))
  (p : τ (Hom (Op_cat A) y x)) (b c : τ (Obj B))
  (q : τ (Hom B b c)) ⊢
  @fapp0
    (Hom_cat B b c)
    (Functor_cat
      (Hom_cat A y (@fapp0 B A F b))
      (Hom_cat A x (@fapp0 B A F c)))
    (@comp_fapp0
      Cat_cat
      (Hom_cat B b c)
      (Product_cat
        (Hom_cat A x y)
        (Hom_cat A (@fapp0 B A F b) (@fapp0 B A F c)))
      (Functor_cat
        (Hom_cat A y (@fapp0 B A F b))
        (Hom_cat A x (@fapp0 B A F c)))
      (@Hom_tele_func A y x (@fapp0 B A F b) (@fapp0 B A F c))
      (Struct_sigma
        (@Const_func (Hom_cat B b c) (Hom_cat A x y) p)
        (@fapp1_func B A F b c)))
    q
  ≡ @Hom_func
      A y x
      (@fapp0 B A F b) (@fapp0 B A F c)
      p
      (@fapp1_fapp0 B A F b c q);

// Projection-first evaluation reaches the direct capped join.
assert [A B : Cat] (F : τ (Functor B A)) (y x : τ (Obj A))
  (p : τ (Hom (Op_cat A) y x)) (b c : τ (Obj B))
  (q : τ (Hom B b c)) ⊢
  @fapp0
    (Hom_cat B b c)
    (Functor_cat
      (Hom_cat A y (@fapp0 B A F b))
      (Hom_cat A x (@fapp0 B A F c)))
    (@tapp1_func
      B Cat_cat
      (@hom_ A B F y) (@hom_ A B F x)
      b c
      (@hom_int_precomp_func A B F y x p))
    q
  ≡ @Hom_func
      A y x
      (@fapp0 B A F b) (@fapp0 B A F c)
      p
      (@fapp1_fapp0 B A F b c q);

assert [A B : Cat] (F : τ (Functor B A)) (y x : τ (Obj A))
  (p : τ (Hom (Op_cat A) y x)) (b c : τ (Obj B))
  (q : τ (Hom B b c))
  (h : τ (Hom A y (@fapp0 B A F b))) ⊢
  @fapp0
    (Hom_cat A y (@fapp0 B A F b))
    (Hom_cat A x (@fapp0 B A F c))
    (@fapp0
      (Hom_cat B b c)
      (Functor_cat
        (Hom_cat A y (@fapp0 B A F b))
        (Hom_cat A x (@fapp0 B A F c)))
      (@tapp1_func
        B Cat_cat
        (@hom_ A B F y) (@hom_ A B F x)
        b c
        (@hom_int_precomp_func A B F y x p))
      q)
    h
  ≡ @Hom_fapp0
      A y x
      (@fapp0 B A F b) (@fapp0 B A F c)
      p
      (@fapp1_fapp0 B A F b c q)
      h;

// Target-internalized mirror: f varies covariantly and each fibre is hom_con.
assert [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A)) ⊢
  @fapp0 A (@Catd_cat (Op_cat B)) (@hom_con_int A B F) W
    ≡ @hom_con A W B F;

assert [A B : Cat] (F : τ (Functor B A)) (W X : τ (Obj A)) ⊢
  @fapp1_func A (@Catd_cat (Op_cat B)) (@hom_con_int A B F) W X
    ≡ @hom_con_int_postcomp_tele_func A B F W X;

assert [A B : Cat] (F : τ (Functor B A)) (W X : τ (Obj A))
  (f : τ (Hom A W X)) ⊢
  @fapp1_fapp0 A (@Catd_cat (Op_cat B)) (@hom_con_int A B F) W X f
    ≡ @hom_con_int_postcomp_func A B F W X f;

assert [A B : Cat] (F : τ (Functor B A)) (W X : τ (Obj A))
  (f : τ (Hom A W X)) ⊢
  @fapp0
    (Hom_cat A W X)
    (Hom_cat
      (@Catd_cat (Op_cat B))
      (@hom_con A W B F)
      (@hom_con A X B F))
    (@hom_con_int_postcomp_tele_func A B F W X)
    f
  ≡ @hom_con_int_postcomp_func A B F W X f;

assert [A B : Cat] (F : τ (Functor B A)) (W X : τ (Obj A))
  (f : τ (Hom A W X)) (b : τ (Obj B)) ⊢
  @tapp0_fapp0
    (Op_cat B) Cat_cat
    (@hom_con A W B F) (@hom_con A X B F)
    b
    (@hom_con_int_postcomp_func A B F W X f)
  ≡ @hom_postcomp_func
      A A (@id_func A)
      (@fapp0 B A F b)
      W X f;

assert [A B : Cat] (F : τ (Functor B A)) (W X : τ (Obj A))
  (f : τ (Hom A W X)) (b c : τ (Obj B)) ⊢
  @tapp1_func
    (Op_cat B) Cat_cat
    (@hom_con A W B F) (@hom_con A X B F)
    b c
    (@hom_con_int_postcomp_func A B F W X f)
  ≡ @comp_fapp0
      Cat_cat
      (Hom_cat (Op_cat B) b c)
      (Product_cat
        (Hom_cat A (@fapp0 B A F c) (@fapp0 B A F b))
        (Hom_cat A W X))
      (Functor_cat
        (Hom_cat A (@fapp0 B A F b) W)
        (Hom_cat A (@fapp0 B A F c) X))
      (@Hom_tele_func
        A (@fapp0 B A F b) (@fapp0 B A F c) W X)
      (Struct_sigma
        (@fapp1_func B A F c b)
        (@Const_func (Hom_cat (Op_cat B) b c) (Hom_cat A W X) f));

assert [A B : Cat] (F : τ (Functor B A)) (W X : τ (Obj A))
  (f : τ (Hom A W X)) (b c : τ (Obj B))
  (q : τ (Hom (Op_cat B) b c)) ⊢
  @tapp1_fapp0
    (Op_cat B) Cat_cat
    (@hom_con A W B F) (@hom_con A X B F)
    b c
    (@hom_con_int_postcomp_func A B F W X f)
    q
  ≡ @Hom_func
      A
      (@fapp0 B A F b) (@fapp0 B A F c)
      W X
      (@fapp1_fapp0 B A F c b q)
      f;

// Owner-first evaluation of the mirror semantic composite reaches the cap.
assert [A B : Cat] (F : τ (Functor B A)) (W X : τ (Obj A))
  (f : τ (Hom A W X)) (b c : τ (Obj B))
  (q : τ (Hom (Op_cat B) b c)) ⊢
  @fapp0
    (Hom_cat (Op_cat B) b c)
    (Functor_cat
      (Hom_cat A (@fapp0 B A F b) W)
      (Hom_cat A (@fapp0 B A F c) X))
    (@comp_fapp0
      Cat_cat
      (Hom_cat (Op_cat B) b c)
      (Product_cat
        (Hom_cat A (@fapp0 B A F c) (@fapp0 B A F b))
        (Hom_cat A W X))
      (Functor_cat
        (Hom_cat A (@fapp0 B A F b) W)
        (Hom_cat A (@fapp0 B A F c) X))
      (@Hom_tele_func
        A (@fapp0 B A F b) (@fapp0 B A F c) W X)
      (Struct_sigma
        (@fapp1_func B A F c b)
        (@Const_func (Hom_cat (Op_cat B) b c) (Hom_cat A W X) f)))
    q
  ≡ @Hom_func
      A
      (@fapp0 B A F b) (@fapp0 B A F c)
      W X
      (@fapp1_fapp0 B A F c b q)
      f;

// Projection-first evaluation reaches the direct capped mirror.
assert [A B : Cat] (F : τ (Functor B A)) (W X : τ (Obj A))
  (f : τ (Hom A W X)) (b c : τ (Obj B))
  (q : τ (Hom (Op_cat B) b c)) ⊢
  @fapp0
    (Hom_cat (Op_cat B) b c)
    (Functor_cat
      (Hom_cat A (@fapp0 B A F b) W)
      (Hom_cat A (@fapp0 B A F c) X))
    (@tapp1_func
      (Op_cat B) Cat_cat
      (@hom_con A W B F) (@hom_con A X B F)
      b c
      (@hom_con_int_postcomp_func A B F W X f))
    q
  ≡ @Hom_func
      A
      (@fapp0 B A F b) (@fapp0 B A F c)
      W X
      (@fapp1_fapp0 B A F c b q)
      f;

assert [A B : Cat] (F : τ (Functor B A)) (W X : τ (Obj A))
  (f : τ (Hom A W X)) (b c : τ (Obj B))
  (q : τ (Hom (Op_cat B) b c))
  (h : τ (Hom A (@fapp0 B A F b) W)) ⊢
  @fapp0
    (Hom_cat A (@fapp0 B A F b) W)
    (Hom_cat A (@fapp0 B A F c) X)
    (@tapp1_fapp0
      (Op_cat B) Cat_cat
      (@hom_con A W B F) (@hom_con A X B F)
      b c
      (@hom_con_int_postcomp_func A B F W X f)
      q)
    h
  ≡ @Hom_fapp0
      A
      (@fapp0 B A F b) (@fapp0 B A F c)
      W X
      (@fapp1_fapp0 B A F c b q)
      f h;

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y)) ⊢
  @Rep_transport_func Z x y p
    ≡ @hom_int_precomp_func Z Z (@id_func Z) y x p;

assert [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A))
  (X Y : τ (Obj B)) (f : τ (Hom B X Y)) (g : τ (Hom A W (fapp0 F X))) ⊢
  fapp0 (@fapp1_fapp0 B Cat_cat (@hom_ A B F W) X Y f) g
    ≡ @hom_postcomp_fapp0 A B F W X Y f g;

// Hom-action functoriality joins for postcomposition.
assert [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A))
  (X : τ (Obj B)) ⊢
  @hom_postcomp_func A B F W X X (@id B X)
    ≡ @id_func (Hom_cat A W (@fapp0 B A F X));

assert [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A))
  (X : τ (Obj B)) (g : τ (Hom A W (@fapp0 B A F X))) ⊢
  @hom_postcomp_fapp0 A B F W X X (@id B X) g
    ≡ g;

assert [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A))
  (X Y Z : τ (Obj B))
  (p : τ (Hom B X Y)) (q : τ (Hom B Y Z)) ⊢
  @hom_postcomp_func A B F W X Z (@comp_fapp0 B X Y Z q p)
    ≡ @comp_cat_fapp0
        (Hom_cat A W (@fapp0 B A F X))
        (Hom_cat A W (@fapp0 B A F Y))
        (Hom_cat A W (@fapp0 B A F Z))
        (@hom_postcomp_func A B F W Y Z q)
        (@hom_postcomp_func A B F W X Y p);

assert [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A))
  (X Y Z : τ (Obj B))
  (p : τ (Hom B X Y)) (q : τ (Hom B Y Z))
  (g : τ (Hom A W (@fapp0 B A F X))) ⊢
  @hom_postcomp_fapp0 A B F W X Z (@comp_fapp0 B X Y Z q p) g
    ≡ @hom_postcomp_fapp0 A B F W Y Z q
        (@hom_postcomp_fapp0 A B F W X Y p g);

assert [A B : Cat] (F : τ (Functor B A))
  (V W : τ (Obj A)) (X Y : τ (Obj B))
  (h : τ (Hom A V W))
  (f : τ (Hom B X Y))
  (g : τ (Hom A W (@fapp0 B A F X))) ⊢
  @comp_fapp0
    A
    V
    W
    (@fapp0 B A F Y)
    (@hom_postcomp_fapp0 A B F W X Y f g)
    h
  ≡ @hom_postcomp_fapp0
      A B F V X Y f
      (@comp_fapp0 A V W (@fapp0 B A F X) g h);

assert [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A))
  (X Y : τ (Obj B)) (f : τ (Hom B X Y))
  (g : τ (Hom A W (@fapp0 B A F X))) ⊢
  @hom_postcomp_fapp1_fapp0
    A
    B
    F
    W
    X
    Y
    f
    g
    g
    (@id (Hom_cat A W (@fapp0 B A F X)) g)
  ≡ @id
      (Hom_cat A W (@fapp0 B A F Y))
      (@hom_postcomp_fapp0 A B F W X Y f g);

// DefIso utility constructors and ordinary semantic evidence extraction.
assert [C : Cat] (x : τ (Obj C)) ⊢
  @defiso_refl C x
  : τ (@DefIso C x x);

assert [C : Cat] (x : τ (Obj C)) ⊢
  @defiso_to C x x (@defiso_refl C x)
  ≡ @id C x;

assert [C : Cat] (x : τ (Obj C)) ⊢
  @defiso_from C x x (@defiso_refl C x)
  ≡ @id C x;

assert [C : Cat] [x y : τ (Obj C)] (i : τ (@DefIso C x y)) ⊢
  @defiso_to C y x (@defiso_sym C x y i)
  ≡ @defiso_from C x y i;

assert [C : Cat] [x y : τ (Obj C)] (i : τ (@DefIso C x y)) ⊢
  @defiso_from C y x (@defiso_sym C x y i)
  ≡ @defiso_to C x y i;

assert [C : Cat] [x y : τ (Obj C)] (i : τ (@DefIso C x y)) ⊢
  @defiso_iso_evidence C x y i
  : τ (@IsoEvidence C x y);

assert [C : Cat] [x y : τ (Obj C)] (i : τ (@DefIso C x y)) ⊢
  @iso_evidence_to C x y (@defiso_iso_evidence C x y i)
  ≡ @defiso_to C x y i;

assert [C : Cat] [x y : τ (Obj C)] (i : τ (@DefIso C x y)) ⊢
  @iso_evidence_from C x y (@defiso_iso_evidence C x y i)
  ≡ @defiso_from C x y i;

assert [C : Cat] [x y z : τ (Obj C)]
  (j : τ (@DefIso C y z))
  (i : τ (@DefIso C x y)) ⊢
  @defiso_to C x z (@defiso_comp C x y z j i)
  ≡ @hom_postcomp_fapp0
      C C (@id_func C) x y z
      (@defiso_to C y z j)
      (@defiso_to C x y i);

assert [C : Cat] [x y z : τ (Obj C)]
  (j : τ (@DefIso C y z))
  (i : τ (@DefIso C x y)) ⊢
  @defiso_from C x z (@defiso_comp C x y z j i)
  ≡ @hom_postcomp_fapp0
      C C (@id_func C) z y x
      (@defiso_from C x y i)
      (@defiso_from C y z j);

assert [C : Cat] [x y z : τ (Obj C)]
  (j : τ (@DefIso C y z))
  (i : τ (@DefIso C x y)) ⊢
  @hom_postcomp_fapp0
    C C (@id_func C) x z x
    (@defiso_from C x z (@defiso_comp C x y z j i))
    (@defiso_to C x z (@defiso_comp C x y z j i))
  ≡ @id C x;

assert [C D : Cat] (F : τ (Functor C D))
  [x y : τ (Obj C)]
  (i : τ (@DefIso C x y)) ⊢
  @defiso_to
    D
    (@fapp0 C D F x)
    (@fapp0 C D F y)
    (@defiso_fmap C D F x y i)
  ≡ @fapp1_fapp0 C D F x y (@defiso_to C x y i);

assert [C D : Cat] (F : τ (Functor C D))
  [x y : τ (Obj C)]
  (i : τ (@DefIso C x y)) ⊢
  @defiso_from
    D
    (@fapp0 C D F x)
    (@fapp0 C D F y)
    (@defiso_fmap C D F x y i)
  ≡ @fapp1_fapp0 C D F y x (@defiso_from C x y i);

assert [C D : Cat] (F : τ (Functor C D))
  [x y : τ (Obj C)]
  (i : τ (@DefIso C x y)) ⊢
  @hom_postcomp_fapp0
    D D (@id_func D)
    (@fapp0 C D F x)
    (@fapp0 C D F y)
    (@fapp0 C D F x)
    (@defiso_from
      D
      (@fapp0 C D F x)
      (@fapp0 C D F y)
      (@defiso_fmap C D F x y i))
    (@defiso_to
      D
      (@fapp0 C D F x)
      (@fapp0 C D F y)
      (@defiso_fmap C D F x y i))
  ≡ @id D (@fapp0 C D F x);

assert [A : Cat] (x y z : τ (Obj A))
  (p : τ (Hom A x y)) (q : τ (Hom A y z)) ⊢
  @fapp0
    (Hom_cat A y z)
    (Hom_cat A x z)
    (@hom_precomp_along_func A A (@id_func A) z x y p)
    q
    ≡ @hom_precomp_along_fapp0 A A (@id_func A) z x y p q;

// Identity-family precomposition and postcomposition remain proof-time
// compatible without selecting either one as the other's runtime normal form.
assert [A : Cat] (x y z : τ (Obj A))
  (p : τ (Hom A x y)) (q : τ (Hom A y z)) ⊢
  eq_refl (@hom_postcomp_fapp0 A A (@id Cat_cat A) x y z q p)
    : τ (
        @hom_precomp_along_fapp0 A A (@id Cat_cat A) z x y p q
        =
        @hom_postcomp_fapp0 A A (@id Cat_cat A) x y z q p);

// Inferred generic identity cuts eliminate the PathOut fibre-proof core. The
// selected runtime identity presentation joins the contravariant one through
// the proof-time pre/post bridge.
assert [A : Cat] (x y z : τ (Obj A))
  (p : τ (Hom A x y)) (q : τ (Hom A y z)) ⊢
  eq_refl
    (@id
      (Hom_cat A x z)
      (@hom_precomp_along_fapp0 A A (@id Cat_cat A) z x y p q))
  : τ (
      @comp_fapp0
        (Hom_cat A x z)
        (@comp_fapp0 A x y z q p)
        (@hom_postcomp_fapp0 A A (@id Cat_cat A) x y z q p)
        (@hom_precomp_along_fapp0 A A (@id Cat_cat A) z x y p q)
        (@id
          (Hom_cat A x z)
          (@hom_precomp_along_fapp0 A A (@id Cat_cat A) z x y p q))
        (@id
          (Hom_cat A x z)
          (@hom_postcomp_fapp0 A A (@id Cat_cat A) x y z q p))
      =
      @id
        (Hom_cat A x z)
        (@hom_precomp_along_fapp0 A A (@id Cat_cat A) z x y p q));

assert [A B : Cat] (F : τ (Functor A B)) (z : τ (Obj B))
  (w x : τ (Obj A)) (h : τ (Hom A w x))
  (g : τ (Hom B (@fapp0 A B F x) z)) ⊢
  fapp0 (@hom_precomp_along_func A B F z w x h) g
    ≡ @hom_precomp_along_fapp0 A B F z w x h g;

// This typed `eq_refl` exercises the proof-time unification bridge between
// identity-family precomposition and ordinary raw composition.
assert [A : Cat] (z w x : τ (Obj A))
  (h : τ (Hom A w x))
  (g : τ (Hom A x z)) ⊢
  eq_refl (@hom_precomp_along_fapp0 A A (@id Cat_cat A) z w x h g)
  : τ (
      @hom_precomp_along_fapp0 A A (@id Cat_cat A) z w x h g
      =
      @comp_fapp0 A w x z g h);

// Hom-action functoriality joins for precomposition.
assert [A B : Cat] (F : τ (Functor A B)) (z : τ (Obj B))
  (x : τ (Obj A)) ⊢
  @hom_precomp_along_func A B F z x x (@id A x)
    ≡ @id_func (Hom_cat B (@fapp0 A B F x) z);

assert [A B : Cat] (F : τ (Functor A B)) (z : τ (Obj B))
  (x : τ (Obj A))
  (g : τ (Hom B (@fapp0 A B F x) z)) ⊢
  @hom_precomp_along_fapp0 A B F z x x (@id A x) g
    ≡ g;

assert [A B : Cat] (F : τ (Functor A B))
  (w x : τ (Obj A))
  (h : τ (Hom A w x)) ⊢
  @hom_precomp_along_fapp0
    A
    B
    F
    (@fapp0 A B F x)
    w
    x
    h
    (@id B (@fapp0 A B F x))
  ≡ @fapp1_fapp0 A B F w x h;

assert [A : Cat] (F : τ (Functor A Cat_cat))
  (w x : τ (Obj A))
  (h : τ (Hom A w x)) ⊢
  @hom_precomp_along_fapp0
    A
    Cat_cat
    F
    (@fapp0 A Cat_cat F x)
    w
    x
    h
    (@id_func (@fapp0 A Cat_cat F x))
  ≡ @fapp1_fapp0 A Cat_cat F w x h;

assert [A K : Cat] (F : τ (Functor A (@Catd_cat K)))
  (w x : τ (Obj A))
  (h : τ (Hom A w x)) ⊢
  @hom_precomp_along_fapp0
    A
    (@Catd_cat K)
    F
    (@fapp0 A (@Catd_cat K) F x)
    w
    x
    h
    (@id_funcd K (@fapp0 A (@Catd_cat K) F x))
  ≡ @fapp1_fapp0 A (@Catd_cat K) F w x h;

symbol hom_postcomp_opfunc_general_tele_visible_check
  [A B : Cat]
  (F : τ (Functor A B))
  (z : τ (Obj B))
  (w x : τ (Obj A))
  : τ (Functor
      (Hom_cat A w x)
      (Functor_cat
        (Hom_cat B (@fapp0 A B F x) z)
        (Hom_cat B (@fapp0 A B F w) z)))
≔ @hom_postcomp_tele_func
    (Op_cat B)
    (Op_cat A)
    (@Op_func A B F)
    z x w;

symbol hom_postcomp_opfunc_general_tele_eq_refl_check
  [A B : Cat] (F : τ (Functor A B)) (z : τ (Obj B))
  (w x : τ (Obj A))
  : τ (
      @hom_postcomp_opfunc_general_tele_visible_check A B F z w x
      =
      @hom_precomp_along_tele_func A B F z w x)
≔ eq_refl (@hom_precomp_along_tele_func A B F z w x);

symbol hom_postcomp_opfunc_general_func_visible_check
  [A B : Cat]
  (F : τ (Functor A B))
  (z : τ (Obj B))
  [w x : τ (Obj A)]
  (h : τ (Hom A w x))
  : τ (Functor
      (Hom_cat B (@fapp0 A B F x) z)
      (Hom_cat B (@fapp0 A B F w) z))
≔ @hom_postcomp_func
    (Op_cat B)
    (Op_cat A)
    (@Op_func A B F)
    z x w h;

symbol hom_postcomp_opfunc_general_func_eq_refl_check
  [A B : Cat] (F : τ (Functor A B)) (z : τ (Obj B))
  (w x : τ (Obj A)) (h : τ (Hom A w x))
  : τ (
      @hom_postcomp_opfunc_general_func_visible_check A B F z w x h
      =
      @hom_precomp_along_func A B F z w x h)
≔ eq_refl (@hom_precomp_along_func A B F z w x h);

symbol hom_postcomp_opfunc_general_visible_check
  [A B : Cat]
  (F : τ (Functor A B))
  (z : τ (Obj B))
  [w x : τ (Obj A)]
  (h : τ (Hom A w x))
  (g : τ (Hom B (@fapp0 A B F x) z))
  : τ (Hom B (@fapp0 A B F w) z)
≔ @hom_postcomp_fapp0
    (Op_cat B)
    (Op_cat A)
    (@Op_func A B F)
    z x w h g;

symbol hom_postcomp_opfunc_general_eq_refl_check
  [A B : Cat] (F : τ (Functor A B)) (z : τ (Obj B))
  (w x : τ (Obj A))
  (h : τ (Hom A w x))
  (g : τ (Hom B (@fapp0 A B F x) z))
  : τ (
      @hom_postcomp_opfunc_general_visible_check A B F z w x h g
      =
      @hom_precomp_along_fapp0 A B F z w x h g)
≔ eq_refl (@hom_precomp_along_fapp0 A B F z w x h g);

symbol hom_postcomp_opfunc_general_double_op_check
  [A B : Cat]
  (F : τ (Functor (Op_cat A) (Op_cat B)))
  (z : τ (Obj B))
  [w x : τ (Obj A)]
  (h : τ (Hom A x w))
  : τ (Functor
      (Hom_cat (Op_cat B) (@fapp0 (Op_cat A) (Op_cat B) F x) z)
      (Hom_cat (Op_cat B) (@fapp0 (Op_cat A) (Op_cat B) F w) z))
≔ @hom_postcomp_func
    B
    A
    (@Op_func (Op_cat A) (Op_cat B) F)
    z x w h;

symbol hom_postcomp_opfunc_general_double_op_eq_refl_check
  [A B : Cat] (F : τ (Functor (Op_cat A) (Op_cat B))) (z : τ (Obj B))
  (w x : τ (Obj A)) (h : τ (Hom A x w))
  : τ (
      @hom_postcomp_opfunc_general_double_op_check A B F z w x h
      =
      @hom_precomp_along_func (Op_cat A) (Op_cat B) F z w x h)
≔ eq_refl (@hom_precomp_along_func (Op_cat A) (Op_cat B) F z w x h);

assert [A B : Cat] (F : τ (Functor A B)) (z : τ (Obj B))
  (w x y : τ (Obj A))
  (p : τ (Hom A w x)) (q : τ (Hom A x y)) ⊢
  @hom_precomp_along_func A B F z w y (@comp_fapp0 A w x y q p)
    ≡ @comp_cat_fapp0
        (Hom_cat B (@fapp0 A B F y) z)
        (Hom_cat B (@fapp0 A B F x) z)
        (Hom_cat B (@fapp0 A B F w) z)
        (@hom_precomp_along_func A B F z w x p)
        (@hom_precomp_along_func A B F z x y q);

assert [A B : Cat] (F : τ (Functor A B)) (z : τ (Obj B))
  (w x y : τ (Obj A))
  (p : τ (Hom A w x)) (q : τ (Hom A x y))
  (g : τ (Hom B (@fapp0 A B F y) z)) ⊢
  @hom_precomp_along_fapp0 A B F z w y (@comp_fapp0 A w x y q p) g
    ≡ @hom_precomp_along_fapp0 A B F z w x p
        (@hom_precomp_along_fapp0 A B F z x y q g);

// Generalized precomposition projection ladder.
assert [A B : Cat] (F : τ (Functor A B)) (z : τ (Obj B))
  (w x : τ (Obj A)) (h : τ (Hom A w x)) ⊢
  fapp0 (@hom_precomp_along_tele_func A B F z w x) h
    ≡ @hom_precomp_along_func A B F z w x h;

assert [A B : Cat] (F : τ (Functor A B)) (z : τ (Obj B))
  (w x : τ (Obj A)) (h : τ (Hom A w x)) ⊢
  @fapp1_fapp0
    (Op_cat A)
    Cat_cat
    (@hom_con B z A F)
    x
    w
    h
  ≡ @hom_precomp_along_func A B F z w x h;

assert [A B : Cat] (F : τ (Functor A B)) (z : τ (Obj B))
  (w x : τ (Obj A)) (h : τ (Hom A w x))
  (g k : τ (Hom B (@fapp0 A B F x) z)) ⊢
  @fapp1_func
    (Hom_cat B (@fapp0 A B F x) z)
    (Hom_cat B (@fapp0 A B F w) z)
    (@hom_precomp_along_func A B F z w x h)
    g
    k
  ≡ @hom_precomp_along_fapp1_func A B F z w x h g k;

assert [A B : Cat] (F : τ (Functor A B)) (z : τ (Obj B))
  (w x : τ (Obj A)) (h : τ (Hom A w x))
  (g k : τ (Hom B (@fapp0 A B F x) z))
  (alpha : τ (Hom (Hom_cat B (@fapp0 A B F x) z) g k)) ⊢
  @fapp1_fapp0
    (Hom_cat B (@fapp0 A B F x) z)
    (Hom_cat B (@fapp0 A B F w) z)
    (@hom_precomp_along_func A B F z w x h)
    g
    k
    alpha
  ≡ @hom_precomp_along_fapp1_fapp0 A B F z w x h g k alpha;

assert [A B : Cat] (F : τ (Functor A B)) (z : τ (Obj B))
  (w x : τ (Obj A)) (h : τ (Hom A w x))
  (g : τ (Hom B (@fapp0 A B F x) z)) ⊢
  @hom_precomp_along_fapp1_fapp0
    A
    B
    F
    z
    w
    x
    h
    g
    g
    (@id (Hom_cat B (@fapp0 A B F x) z) g)
  ≡ @id
      (Hom_cat B (@fapp0 A B F w) z)
      (@hom_precomp_along_fapp0 A B F z w x h g);

// Projection checks exercise the same proof-time bridges after generic
// telescope and functor evaluation.
symbol hom_postcomp_opfunc_projected_func_eq_refl_check
  [A B : Cat] (F : τ (Functor A B)) (z : τ (Obj B))
  (w x : τ (Obj A)) (h : τ (Hom A w x))
  : τ (
      fapp0
        (@hom_postcomp_tele_func
          (Op_cat B) (Op_cat A) (@Op_func A B F) z x w)
        h
      =
      @hom_precomp_along_func A B F z w x h)
≔ eq_refl (@hom_precomp_along_func A B F z w x h);

symbol hom_postcomp_opfunc_projected_fapp0_eq_refl_check
  [A B : Cat] (F : τ (Functor A B)) (z : τ (Obj B))
  (w x : τ (Obj A)) (h : τ (Hom A w x))
  (g : τ (Hom B (@fapp0 A B F x) z))
  : τ (
      fapp0
        (@hom_postcomp_func
          (Op_cat B) (Op_cat A) (@Op_func A B F) z x w h)
        g
      =
      @hom_precomp_along_fapp0 A B F z w x h g)
≔ eq_refl (@hom_precomp_along_fapp0 A B F z w x h g);

assert [X Y Z : Cat] (F : τ (Functor X Y)) ⊢
  fapp0 (@comp_cat_con_func_func X Y Z) F
    ≡ @comp_cat_con_func X Y Z F;

assert [X Y Z : Cat] ⊢
  @comp_cat_con_func_func X Y Z
    ≡ @hom_precomp_along_tele_func
        Cat_cat
        Cat_cat
        (@id Cat_cat Cat_cat)
        Z
        X
        Y;

assert (F : τ (Functor Cat_cat Cat_cat)) (Z W X : Cat)
  (H : τ (Functor W X)) ⊢
  eq_refl (@hom_precomp_along_func Cat_cat Cat_cat F Z W X H)
  : τ (
    @hom_precomp_along_func Cat_cat Cat_cat F Z W X H
    =
    @hom_precomp_along_func
        Cat_cat
        Cat_cat
        (@id Cat_cat Cat_cat)
        Z
        (@fapp0 Cat_cat Cat_cat F W)
        (@fapp0 Cat_cat Cat_cat F X)
        (@fapp1_fapp0 Cat_cat Cat_cat F W X H));

assert (F : τ (Functor Cat_cat Cat_cat)) (Z W X : Cat)
  (H : τ (Functor W X))
  (G K : τ (Functor (@fapp0 Cat_cat Cat_cat F X) Z)) ⊢
  @fapp1_func
    (Functor_cat (@fapp0 Cat_cat Cat_cat F X) Z)
    (Functor_cat (@fapp0 Cat_cat Cat_cat F W) Z)
    (@hom_precomp_along_func Cat_cat Cat_cat F Z W X H)
    G
    K
  ≡ @hom_precomp_along_fapp1_func Cat_cat Cat_cat F Z W X H G K;

assert (F : τ (Functor Cat_cat Cat_cat)) (Z W X : Cat)
  (H : τ (Functor W X))
  (G K : τ (Functor (@fapp0 Cat_cat Cat_cat F X) Z))
  (eta : τ (Transf G K)) ⊢
  @fapp1_fapp0
    (Functor_cat (@fapp0 Cat_cat Cat_cat F X) Z)
    (Functor_cat (@fapp0 Cat_cat Cat_cat F W) Z)
    (@hom_precomp_along_func Cat_cat Cat_cat F Z W X H)
    G
    K
    eta
  ≡ @hom_precomp_along_fapp1_fapp0 Cat_cat Cat_cat F Z W X H G K eta;

assert [K : Cat]
  (E : τ (Functor K Cat_cat))
  (Z : Cat)
  [x y : τ (Obj K)]
  (f : τ (Hom K x y))
  [G H : τ (Functor (@fapp0 K Cat_cat E y) Z)]
  (eta : τ (Transf G H)) ⊢
  @hom_precomp_along_fapp1_fapp0 K Cat_cat E Z x y f G H eta
  ≡ @comp_prod_fapp1_fapp0
      Cat_cat
      (@fapp0 K Cat_cat E x)
      (@fapp0 K Cat_cat E y)
      Z
      (@Product_pair
        (Functor_cat (@fapp0 K Cat_cat E x) (@fapp0 K Cat_cat E y))
        (Functor_cat (@fapp0 K Cat_cat E y) Z)
        (@fapp1_fapp0 K Cat_cat E x y f)
        G)
      (@Product_pair
        (Functor_cat (@fapp0 K Cat_cat E x) (@fapp0 K Cat_cat E y))
        (Functor_cat (@fapp0 K Cat_cat E y) Z)
        (@fapp1_fapp0 K Cat_cat E x y f)
        H)
      (@Product_pair
        (Hom_cat
          (Functor_cat (@fapp0 K Cat_cat E x) (@fapp0 K Cat_cat E y))
          (@fapp1_fapp0 K Cat_cat E x y f)
          (@fapp1_fapp0 K Cat_cat E x y f))
        (Hom_cat (Functor_cat (@fapp0 K Cat_cat E y) Z) G H)
        (@id
          (Functor_cat (@fapp0 K Cat_cat E x) (@fapp0 K Cat_cat E y))
          (@fapp1_fapp0 K Cat_cat E x y f))
        eta);

assert [X Y Z : Cat] (F : τ (Functor X Y)) (G H : τ (Functor Y Z))
  (eta : τ (Transf G H)) ⊢
  @fapp1_fapp0
    (Functor_cat Y Z)
    (Functor_cat X Z)
    (@comp_cat_con_func X Y Z F)
    G
    H
    eta
  ≡ @hom_precomp_along_fapp1_fapp0
      Cat_cat
      Cat_cat
      (@id Cat_cat Cat_cat)
      Z
      X
      Y
      F
      G
      H
      eta;

assert [X Y Z : Cat] (F : τ (Functor X Y)) (G H : τ (Functor Y Z))
  (eta : τ (Transf G H)) ⊢
  fapp0 (@comp_cat_con_fapp1_func X Y Z F G H) eta
    ≡ @hom_precomp_along_fapp1_fapp0
        Cat_cat
        Cat_cat
        (@id Cat_cat Cat_cat)
        Z
        X
        Y
        F
        G
        H
        eta;

assert [X Y Z : Cat] ⊢
  @comp_cat_cov_func_func X Y Z
    ≡ @hom_postcomp_tele_func
        Cat_cat
        Cat_cat
        (@id Cat_cat Cat_cat)
        X
        Y
        Z;

assert [X Y Z : Cat] (G : τ (Functor Y Z)) ⊢
  @comp_cat_cov_func X Y Z G
    ≡ @hom_postcomp_func
        Cat_cat
        Cat_cat
        (@id Cat_cat Cat_cat)
        X
        Y
        Z
        G;

assert (E : τ (Functor Cat_cat Cat_cat)) (W X Y : Cat)
  (L : τ (Functor X Y))
  (G K : τ (Functor W (@fapp0 Cat_cat Cat_cat E X))) ⊢
  @fapp1_func
    (Functor_cat W (@fapp0 Cat_cat Cat_cat E X))
    (Functor_cat W (@fapp0 Cat_cat Cat_cat E Y))
    (@hom_postcomp_func Cat_cat Cat_cat E W X Y L)
    G
    K
  ≡ @hom_postcomp_fapp1_func Cat_cat Cat_cat E W X Y L G K;

assert (E : τ (Functor Cat_cat Cat_cat)) (W X Y : Cat)
  (L : τ (Functor X Y))
  (G K : τ (Functor W (@fapp0 Cat_cat Cat_cat E X)))
  (eta : τ (Transf G K)) ⊢
  @fapp1_fapp0
    (Functor_cat W (@fapp0 Cat_cat Cat_cat E X))
    (Functor_cat W (@fapp0 Cat_cat Cat_cat E Y))
    (@hom_postcomp_func Cat_cat Cat_cat E W X Y L)
    G
    K
    eta
  ≡ @hom_postcomp_fapp1_fapp0 Cat_cat Cat_cat E W X Y L G K eta;

assert [K : Cat]
  (E : τ (Functor K Cat_cat))
  (W : Cat)
  [x y : τ (Obj K)]
  (f : τ (Hom K x y))
  [G H : τ (Functor W (@fapp0 K Cat_cat E x))]
  (eta : τ (Transf G H)) ⊢
  @hom_postcomp_fapp1_fapp0 Cat_cat K E W x y f G H eta
  ≡ @comp_prod_fapp1_fapp0
      Cat_cat
      W
      (@fapp0 K Cat_cat E x)
      (@fapp0 K Cat_cat E y)
      (@Product_pair
        (Functor_cat W (@fapp0 K Cat_cat E x))
        (Functor_cat (@fapp0 K Cat_cat E x) (@fapp0 K Cat_cat E y))
        G
        (@fapp1_fapp0 K Cat_cat E x y f))
      (@Product_pair
        (Functor_cat W (@fapp0 K Cat_cat E x))
        (Functor_cat (@fapp0 K Cat_cat E x) (@fapp0 K Cat_cat E y))
        H
        (@fapp1_fapp0 K Cat_cat E x y f))
      (@Product_pair
        (Hom_cat (Functor_cat W (@fapp0 K Cat_cat E x)) G H)
        (Hom_cat
          (Functor_cat (@fapp0 K Cat_cat E x) (@fapp0 K Cat_cat E y))
          (@fapp1_fapp0 K Cat_cat E x y f)
          (@fapp1_fapp0 K Cat_cat E x y f))
        eta
        (@id
          (Functor_cat (@fapp0 K Cat_cat E x) (@fapp0 K Cat_cat E y))
          (@fapp1_fapp0 K Cat_cat E x y f)));

assert [X Y Z : Cat] (G : τ (Functor Y Z)) (F H : τ (Functor X Y))
  (eta : τ (Transf F H)) ⊢
  @fapp1_fapp0
    (Functor_cat X Y)
    (Functor_cat X Z)
    (@comp_cat_cov_func X Y Z G)
    F
    H
    eta
  ≡ @hom_postcomp_fapp1_fapp0
      Cat_cat
      Cat_cat
      (@id Cat_cat Cat_cat)
      X
      Y
      Z
      G
      F
      H
      eta;

assert [X Y Z : Cat] (G : τ (Functor Y Z)) (F H : τ (Functor X Y))
  (eta : τ (Transf F H)) ⊢
  fapp0 (@comp_cat_cov_fapp1_func X Y Z G F H) eta
    ≡ @hom_postcomp_fapp1_fapp0
        Cat_cat
        Cat_cat
        (@id Cat_cat Cat_cat)
        X
        Y
        Z
        G
        F
        H
        eta;

// Higher action of the tele-level postcomposition stable head.
assert [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A))
  (X Y : τ (Obj B)) (f g : τ (Hom B X Y)) ⊢
  @fapp1_func
    (Hom_cat B X Y)
    (Functor_cat
      (Hom_cat A W (@fapp0 B A F X))
      (Hom_cat A W (@fapp0 B A F Y)))
    (@hom_postcomp_tele_func A B F W X Y)
    f
    g
  ≡ @hom_postcomp_tele_fapp1_func A B F W X Y f g;

assert [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A))
  (X Y : τ (Obj B)) (f g : τ (Hom B X Y))
  (alpha : τ (Hom (Hom_cat B X Y) f g)) ⊢
  @fapp1_fapp0
    (Hom_cat B X Y)
    (Functor_cat
      (Hom_cat A W (@fapp0 B A F X))
      (Hom_cat A W (@fapp0 B A F Y)))
    (@hom_postcomp_tele_func A B F W X Y)
    f
    g
    alpha
  ≡ @hom_postcomp_tele_transf A B F W X Y f g alpha;

assert [K : Cat]
  (E : τ (Functor K Cat_cat))
  (W : Cat)
  [x y : τ (Obj K)]
  [f g : τ (Hom K x y)]
  (alpha : τ (Hom (Hom_cat K x y) f g)) ⊢
  @hom_postcomp_tele_fapp1_fapp0 Cat_cat K E W x y f g alpha
  ≡ @hom_postcomp_tele_transf Cat_cat K E W x y f g alpha;

assert (W X Y : Cat) (G H : τ (Functor X Y)) ⊢
  @fapp1_func
    (Functor_cat X Y)
    (Functor_cat (Functor_cat W X) (Functor_cat W Y))
    (@comp_cat_cov_func_func W X Y)
    G
    H
  ≡ @hom_postcomp_tele_fapp1_func
      Cat_cat
      Cat_cat
      (@id_func Cat_cat)
      W
      X
      Y
      G
      H;

assert (W X Y : Cat) (G H : τ (Functor X Y)) (eta : τ (Transf G H)) ⊢
  @fapp1_fapp0
    (Functor_cat X Y)
    (Functor_cat (Functor_cat W X) (Functor_cat W Y))
    (@comp_cat_cov_func_func W X Y)
    G
    H
    eta
  ≡ @comp_cat_cov_func_func_transf W X Y G H eta;

assert (W X Y : Cat) [G H : τ (Functor X Y)]
  (eta : τ (Transf G H)) ⊢
  @comp_cat_cov_func_func_transf W X Y G H eta
  ≡ @hom_postcomp_tele_transf
      Cat_cat
      Cat_cat
      (@id Cat_cat Cat_cat)
      W
      X
      Y
      G
      H
      eta;

assert (W X Y : Cat) (G H : τ (Functor X Y)) (eta : τ (Transf G H)) ⊢
  fapp0 (@comp_cat_cov_func_func_fapp1_func W X Y G H) eta
    ≡ @comp_cat_cov_func_func_transf W X Y G H eta;

assert [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A))
  [X Y : τ (Obj B)] [f g : τ (Hom B X Y)]
  (alpha : τ (Hom (Hom_cat B X Y) f g))
  (u : τ (Hom A W (@fapp0 B A F X))) ⊢
  @tapp0_fapp0
    (Hom_cat A W (@fapp0 B A F X))
    (Hom_cat A W (@fapp0 B A F Y))
    (@hom_postcomp_func A B F W X Y f)
    (@hom_postcomp_func A B F W X Y g)
    u
    (@hom_postcomp_tele_transf A B F W X Y f g alpha)
  ≡ @comp_prod_fapp1_fapp0
      A
      W
      (@fapp0 B A F X)
      (@fapp0 B A F Y)
      (@Product_pair
        (Hom_cat A W (@fapp0 B A F X))
        (Hom_cat A (@fapp0 B A F X) (@fapp0 B A F Y))
        u
        (@fapp1_fapp0 B A F X Y f))
      (@Product_pair
        (Hom_cat A W (@fapp0 B A F X))
        (Hom_cat A (@fapp0 B A F X) (@fapp0 B A F Y))
        u
        (@fapp1_fapp0 B A F X Y g))
      (@Product_pair
        (Hom_cat (Hom_cat A W (@fapp0 B A F X)) u u)
        (Hom_cat
          (Hom_cat A (@fapp0 B A F X) (@fapp0 B A F Y))
          (@fapp1_fapp0 B A F X Y f)
          (@fapp1_fapp0 B A F X Y g))
        (@id (Hom_cat A W (@fapp0 B A F X)) u)
        (@fapp1_fapp0
          (Hom_cat B X Y)
          (Hom_cat A (@fapp0 B A F X) (@fapp0 B A F Y))
          (@fapp1_func B A F X Y)
          f
          g
          alpha));

assert [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A))
  [X Y : τ (Obj B)] [f g : τ (Hom B X Y)]
  (alpha : τ (Hom (Hom_cat B X Y) f g))
  (u v : τ (Hom A W (@fapp0 B A F X))) ⊢
  @tapp1_func
    (Hom_cat A W (@fapp0 B A F X))
    (Hom_cat A W (@fapp0 B A F Y))
    (@hom_postcomp_func A B F W X Y f)
    (@hom_postcomp_func A B F W X Y g)
    u
    v
    (@hom_postcomp_tele_transf A B F W X Y f g alpha)
  ≡ @comp_cat_fapp0
      (Hom_cat (Hom_cat A W (@fapp0 B A F X)) u v)
      (Hom_cat
        (Product_cat
          (Hom_cat A W (@fapp0 B A F X))
          (Hom_cat A (@fapp0 B A F X) (@fapp0 B A F Y)))
        (@Product_pair
          (Hom_cat A W (@fapp0 B A F X))
          (Hom_cat A (@fapp0 B A F X) (@fapp0 B A F Y))
          u
          (@fapp1_fapp0 B A F X Y f))
        (@Product_pair
          (Hom_cat A W (@fapp0 B A F X))
          (Hom_cat A (@fapp0 B A F X) (@fapp0 B A F Y))
          v
          (@fapp1_fapp0 B A F X Y g)))
      (Hom_cat
        (Hom_cat A W (@fapp0 B A F Y))
        (@comp_fapp0 A W (@fapp0 B A F X) (@fapp0 B A F Y)
          (@fapp1_fapp0 B A F X Y f) u)
        (@comp_fapp0 A W (@fapp0 B A F X) (@fapp0 B A F Y)
          (@fapp1_fapp0 B A F X Y g) v))
      (@comp_prod_fapp1_func
        A
        W
        (@fapp0 B A F X)
        (@fapp0 B A F Y)
        (@Product_pair
          (Hom_cat A W (@fapp0 B A F X))
          (Hom_cat A (@fapp0 B A F X) (@fapp0 B A F Y))
          u
          (@fapp1_fapp0 B A F X Y f))
        (@Product_pair
          (Hom_cat A W (@fapp0 B A F X))
          (Hom_cat A (@fapp0 B A F X) (@fapp0 B A F Y))
          v
          (@fapp1_fapp0 B A F X Y g)))
      (Struct_sigma
        (@id_func (Hom_cat (Hom_cat A W (@fapp0 B A F X)) u v))
        (@Const_func
          (Hom_cat (Hom_cat A W (@fapp0 B A F X)) u v)
          (Hom_cat
            (Hom_cat A (@fapp0 B A F X) (@fapp0 B A F Y))
            (@fapp1_fapp0 B A F X Y f)
            (@fapp1_fapp0 B A F X Y g))
          (@fapp1_fapp0
            (Hom_cat B X Y)
            (Hom_cat A (@fapp0 B A F X) (@fapp0 B A F Y))
            (@fapp1_func B A F X Y)
            f
            g
            alpha)));

assert [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A))
  [X Y : τ (Obj B)] [f g : τ (Hom B X Y)]
  (alpha : τ (Hom (Hom_cat B X Y) f g))
  (u v : τ (Hom A W (@fapp0 B A F X)))
  (beta : τ (Hom (Hom_cat A W (@fapp0 B A F X)) u v)) ⊢
  @tapp1_fapp0
    (Hom_cat A W (@fapp0 B A F X))
    (Hom_cat A W (@fapp0 B A F Y))
    (@hom_postcomp_func A B F W X Y f)
    (@hom_postcomp_func A B F W X Y g)
    u
    v
    (@hom_postcomp_tele_transf A B F W X Y f g alpha)
    beta
  ≡ @comp_prod_fapp1_fapp0
      A
      W
      (@fapp0 B A F X)
      (@fapp0 B A F Y)
      (@Product_pair
        (Hom_cat A W (@fapp0 B A F X))
        (Hom_cat A (@fapp0 B A F X) (@fapp0 B A F Y))
        u
        (@fapp1_fapp0 B A F X Y f))
      (@Product_pair
        (Hom_cat A W (@fapp0 B A F X))
        (Hom_cat A (@fapp0 B A F X) (@fapp0 B A F Y))
        v
        (@fapp1_fapp0 B A F X Y g))
      (@Product_pair
        (Hom_cat (Hom_cat A W (@fapp0 B A F X)) u v)
        (Hom_cat
          (Hom_cat A (@fapp0 B A F X) (@fapp0 B A F Y))
          (@fapp1_fapp0 B A F X Y f)
          (@fapp1_fapp0 B A F X Y g))
        beta
        (@fapp1_fapp0
          (Hom_cat B X Y)
          (Hom_cat A (@fapp0 B A F X) (@fapp0 B A F Y))
          (@fapp1_func B A F X Y)
          f
          g
          alpha));

// Higher action of the tele-level precomposition-along stable head.
assert [A B : Cat] (F : τ (Functor A B)) (Z : τ (Obj B))
  (W X : τ (Obj A)) (h k : τ (Hom A W X)) ⊢
  @fapp1_func
    (Hom_cat A W X)
    (Functor_cat
      (Hom_cat B (@fapp0 A B F X) Z)
      (Hom_cat B (@fapp0 A B F W) Z))
    (@hom_precomp_along_tele_func A B F Z W X)
    h
    k
  ≡ @hom_precomp_along_tele_fapp1_func A B F Z W X h k;

assert [A B : Cat] (F : τ (Functor A B)) (Z : τ (Obj B))
  (W X : τ (Obj A)) (h k : τ (Hom A W X))
  (alpha : τ (Hom (Hom_cat A W X) h k)) ⊢
  @fapp1_fapp0
    (Hom_cat A W X)
    (Functor_cat
      (Hom_cat B (@fapp0 A B F X) Z)
      (Hom_cat B (@fapp0 A B F W) Z))
    (@hom_precomp_along_tele_func A B F Z W X)
    h
    k
    alpha
  ≡ @hom_precomp_along_tele_transf A B F Z W X h k alpha;

assert [K : Cat]
  (E : τ (Functor K Cat_cat))
  (Z : Cat)
  [x y : τ (Obj K)]
  [f g : τ (Hom K x y)]
  (alpha : τ (Hom (Hom_cat K x y) f g)) ⊢
  @hom_precomp_along_tele_fapp1_fapp0 K Cat_cat E Z x y f g alpha
  ≡ @hom_precomp_along_tele_transf K Cat_cat E Z x y f g alpha;

assert [X Y Z : Cat] (F K : τ (Functor X Y)) ⊢
  @fapp1_func
    (Functor_cat X Y)
    (Functor_cat (Functor_cat Y Z) (Functor_cat X Z))
    (@comp_cat_con_func_func X Y Z)
    F
    K
  ≡ @hom_precomp_along_tele_fapp1_func
      Cat_cat
      Cat_cat
      (@id_func Cat_cat)
      Z
      X
      Y
      F
      K;

assert [X Y Z : Cat] (F K : τ (Functor X Y))
  (alpha : τ (Transf F K)) ⊢
  @fapp1_fapp0
    (Functor_cat X Y)
    (Functor_cat (Functor_cat Y Z) (Functor_cat X Z))
    (@comp_cat_con_func_func X Y Z)
    F
    K
    alpha
  ≡ @comp_cat_con_func_func_transf X Y Z F K alpha;

assert [X Y Z : Cat] [F K : τ (Functor X Y)]
  (alpha : τ (Transf F K)) ⊢
  @comp_cat_con_func_func_transf X Y Z F K alpha
  ≡ @hom_precomp_along_tele_transf
      Cat_cat
      Cat_cat
      (@id Cat_cat Cat_cat)
      Z
      X
      Y
      F
      K
      alpha;

assert [X Y Z : Cat] (F K : τ (Functor X Y))
  (alpha : τ (Transf F K)) ⊢
  fapp0 (@comp_cat_con_func_func_fapp1_func X Y Z F K) alpha
    ≡ @comp_cat_con_func_func_transf X Y Z F K alpha;

assert [A B : Cat] (F : τ (Functor A B)) (Z : τ (Obj B))
  [W X : τ (Obj A)] [h k : τ (Hom A W X)]
  (alpha : τ (Hom (Hom_cat A W X) h k))
  (g : τ (Hom B (@fapp0 A B F X) Z)) ⊢
  @tapp0_fapp0
    (Hom_cat B (@fapp0 A B F X) Z)
    (Hom_cat B (@fapp0 A B F W) Z)
    (@hom_precomp_along_func A B F Z W X h)
    (@hom_precomp_along_func A B F Z W X k)
    g
    (@hom_precomp_along_tele_transf A B F Z W X h k alpha)
  ≡ @comp_prod_fapp1_fapp0
      B
      (@fapp0 A B F W)
      (@fapp0 A B F X)
      Z
      (@Product_pair
        (Hom_cat B (@fapp0 A B F W) (@fapp0 A B F X))
        (Hom_cat B (@fapp0 A B F X) Z)
        (@fapp1_fapp0 A B F W X h)
        g)
      (@Product_pair
        (Hom_cat B (@fapp0 A B F W) (@fapp0 A B F X))
        (Hom_cat B (@fapp0 A B F X) Z)
        (@fapp1_fapp0 A B F W X k)
        g)
      (@Product_pair
        (Hom_cat
          (Hom_cat B (@fapp0 A B F W) (@fapp0 A B F X))
          (@fapp1_fapp0 A B F W X h)
          (@fapp1_fapp0 A B F W X k))
        (Hom_cat (Hom_cat B (@fapp0 A B F X) Z) g g)
        (@fapp1_fapp0
          (Hom_cat A W X)
          (Hom_cat B (@fapp0 A B F W) (@fapp0 A B F X))
          (@fapp1_func A B F W X)
          h
          k
          alpha)
        (@id (Hom_cat B (@fapp0 A B F X) Z) g));

assert [A B : Cat] (F : τ (Functor A B)) (Z : τ (Obj B))
  [W X : τ (Obj A)] [h k : τ (Hom A W X)]
  (alpha : τ (Hom (Hom_cat A W X) h k))
  (g j : τ (Hom B (@fapp0 A B F X) Z)) ⊢
  @tapp1_func
    (Hom_cat B (@fapp0 A B F X) Z)
    (Hom_cat B (@fapp0 A B F W) Z)
    (@hom_precomp_along_func A B F Z W X h)
    (@hom_precomp_along_func A B F Z W X k)
    g
    j
    (@hom_precomp_along_tele_transf A B F Z W X h k alpha)
  ≡ @comp_cat_fapp0
      (Hom_cat (Hom_cat B (@fapp0 A B F X) Z) g j)
      (Hom_cat
        (Product_cat
          (Hom_cat B (@fapp0 A B F W) (@fapp0 A B F X))
          (Hom_cat B (@fapp0 A B F X) Z))
        (@Product_pair
          (Hom_cat B (@fapp0 A B F W) (@fapp0 A B F X))
          (Hom_cat B (@fapp0 A B F X) Z)
          (@fapp1_fapp0 A B F W X h)
          g)
        (@Product_pair
          (Hom_cat B (@fapp0 A B F W) (@fapp0 A B F X))
          (Hom_cat B (@fapp0 A B F X) Z)
          (@fapp1_fapp0 A B F W X k)
          j))
      (Hom_cat
        (Hom_cat B (@fapp0 A B F W) Z)
        (@comp_fapp0 B (@fapp0 A B F W) (@fapp0 A B F X) Z
          g
          (@fapp1_fapp0 A B F W X h))
        (@comp_fapp0 B (@fapp0 A B F W) (@fapp0 A B F X) Z
          j
          (@fapp1_fapp0 A B F W X k)))
      (@comp_prod_fapp1_func
        B
        (@fapp0 A B F W)
        (@fapp0 A B F X)
        Z
        (@Product_pair
          (Hom_cat B (@fapp0 A B F W) (@fapp0 A B F X))
          (Hom_cat B (@fapp0 A B F X) Z)
          (@fapp1_fapp0 A B F W X h)
          g)
        (@Product_pair
          (Hom_cat B (@fapp0 A B F W) (@fapp0 A B F X))
          (Hom_cat B (@fapp0 A B F X) Z)
          (@fapp1_fapp0 A B F W X k)
          j))
      (Struct_sigma
        (@Const_func
          (Hom_cat (Hom_cat B (@fapp0 A B F X) Z) g j)
          (Hom_cat
            (Hom_cat B (@fapp0 A B F W) (@fapp0 A B F X))
            (@fapp1_fapp0 A B F W X h)
            (@fapp1_fapp0 A B F W X k))
          (@fapp1_fapp0
            (Hom_cat A W X)
            (Hom_cat B (@fapp0 A B F W) (@fapp0 A B F X))
            (@fapp1_func A B F W X)
            h
            k
            alpha))
        (@id_func (Hom_cat (Hom_cat B (@fapp0 A B F X) Z) g j)));

assert [A B : Cat] (F : τ (Functor A B)) (Z : τ (Obj B))
  [W X : τ (Obj A)] [h k : τ (Hom A W X)]
  (alpha : τ (Hom (Hom_cat A W X) h k))
  (g j : τ (Hom B (@fapp0 A B F X) Z))
  (beta : τ (Hom (Hom_cat B (@fapp0 A B F X) Z) g j)) ⊢
  @tapp1_fapp0
    (Hom_cat B (@fapp0 A B F X) Z)
    (Hom_cat B (@fapp0 A B F W) Z)
    (@hom_precomp_along_func A B F Z W X h)
    (@hom_precomp_along_func A B F Z W X k)
    g
    j
    (@hom_precomp_along_tele_transf A B F Z W X h k alpha)
    beta
  ≡ @comp_prod_fapp1_fapp0
      B
      (@fapp0 A B F W)
      (@fapp0 A B F X)
      Z
      (@Product_pair
        (Hom_cat B (@fapp0 A B F W) (@fapp0 A B F X))
        (Hom_cat B (@fapp0 A B F X) Z)
        (@fapp1_fapp0 A B F W X h)
        g)
      (@Product_pair
        (Hom_cat B (@fapp0 A B F W) (@fapp0 A B F X))
        (Hom_cat B (@fapp0 A B F X) Z)
        (@fapp1_fapp0 A B F W X k)
        j)
      (@Product_pair
        (Hom_cat
          (Hom_cat B (@fapp0 A B F W) (@fapp0 A B F X))
          (@fapp1_fapp0 A B F W X h)
          (@fapp1_fapp0 A B F W X k))
        (Hom_cat (Hom_cat B (@fapp0 A B F X) Z) g j)
        (@fapp1_fapp0
          (Hom_cat A W X)
          (Hom_cat B (@fapp0 A B F W) (@fapp0 A B F X))
          (@fapp1_func A B F W X)
          h
          k
          alpha)
        beta);

assert [A : Cat] (x y z : τ (Obj A))
  (p : τ (Hom A x y)) (q : τ (Hom A y z)) ⊢
  @fapp0
    (Hom_cat A x y)
    (Hom_cat A x z)
    (@hom_postcomp_func A A (@id_func A) x y z q)
    p
    ≡ @hom_postcomp_fapp0 A A (@id_func A) x y z q p;

assert [A B C : Cat] (F : τ (Functor B C)) (G : τ (Functor A B))
  (x y : τ (Obj A)) (f : τ (Hom A x y)) ⊢
  @fapp1_fapp0
    A
    C
    (@comp_cat_fapp0 A B C F G)
    x
    y
    f
    ≡ @fapp1_fapp0
        B
        C
        F
        (@fapp0 A B G x)
        (@fapp0 A B G y)
        (@fapp1_fapp0 A B G x y f);

assert [A : Cat] (x y : τ (Obj A)) (p : τ (Hom A x y)) ⊢
  @fapp1_fapp0 A A (@id_func A) x y p
    ≡ p;

// CATALIAS-02: generic `Cat_cat` identity owner, separate from public alias spelling.
assert [A : Cat] ⊢ @id_func A ≡ @id Cat_cat A;

assert [A : Cat] (x : τ (Obj A)) ⊢
  @fapp0 A A (@id Cat_cat A) x ≡ x;

assert [A : Cat] (x y : τ (Obj A)) (p : τ (Hom A x y)) ⊢
  @fapp1_fapp0 A A (@id Cat_cat A) x y p ≡ p;

assert [A B : Cat] (x : τ (Obj A)) (u : τ (Obj B)) ⊢
  @Product_projL A B (@Product_pair A B x u) ≡ x;

assert [A B : Cat] (x : τ (Obj A)) (u : τ (Obj B)) ⊢
  @Product_projR A B (@Product_pair A B x u) ≡ u;

assert [A B : Cat]
  (p q : τ (Obj (Product_cat A B))) ⊢
  @Hom_cat (Product_cat A B) p q
    ≡ @Product_cat
        (Hom_cat A (sigma_Fst p) (sigma_Fst q))
        (Hom_cat B (sigma_Snd p) (sigma_Snd q));

assert [A B : Cat] (x : τ (Obj A)) (u : τ (Obj B)) ⊢
  @id (Product_cat A B) (Struct_sigma x u)
    ≡ @Struct_sigma
        (Obj (Hom_cat A x x))
        (λ _ : τ (Obj (Hom_cat A x x)), Obj (Hom_cat B u u))
        (@id A x)
        (@id B u);

assert [A B : Cat]
  (xu : τ (Obj (Product_cat A B))) ⊢
  sigma_Fst (@id (Product_cat A B) xu)
    ≡ @id A (sigma_Fst xu);

assert [A B : Cat]
  (xu : τ (Obj (Product_cat A B))) ⊢
  sigma_Snd (@id (Product_cat A B) xu)
    ≡ @id B (sigma_Snd xu);

assert [A B : Cat]
  (x y z : τ (Obj A))
  (u v w : τ (Obj B))
  (f : τ (Hom A x y))
  (g : τ (Hom A y z))
  (alpha : τ (Hom B u v))
  (beta : τ (Hom B v w)) ⊢
  @comp_fapp0
    (Product_cat A B)
    (Struct_sigma x u)
    (Struct_sigma y v)
    (Struct_sigma z w)
    (Struct_sigma g beta)
    (Struct_sigma f alpha)
    ≡ @Struct_sigma
        (Obj (Hom_cat A x z))
        (λ _ : τ (Obj (Hom_cat A x z)), Obj (Hom_cat B u w))
        (@comp_fapp0 A x y z g f)
        (@comp_fapp0 B u v w beta alpha);

// Product/uncurried composition owner.
assert [A : Cat]
  [W X Z : τ (Obj A)]
  (f : τ (Hom A W X))
  (g : τ (Hom A X Z)) ⊢
  fapp0 (@comp_prod_func A W X Z) (Struct_sigma f g)
  ≡ @comp_fapp0 A W X Z g f;

assert [A : Cat]
  [W X Z : τ (Obj A)]
  (pg pg' : τ (Obj (Product_cat (Hom_cat A W X) (Hom_cat A X Z))))
  (alpha : τ (Hom
    (Product_cat (Hom_cat A W X) (Hom_cat A X Z))
    pg
    pg')) ⊢
  @fapp1_func
    (Product_cat (Hom_cat A W X) (Hom_cat A X Z))
    (Hom_cat A W Z)
    (@comp_prod_func A W X Z)
    pg
    pg'
  ≡ @comp_prod_fapp1_func A W X Z pg pg';

assert [A : Cat]
  [W X Z : τ (Obj A)]
  (pg pg' : τ (Obj (Product_cat (Hom_cat A W X) (Hom_cat A X Z))))
  (alpha : τ (Hom
    (Product_cat (Hom_cat A W X) (Hom_cat A X Z))
    pg
    pg')) ⊢
  @fapp1_fapp0
    (Product_cat (Hom_cat A W X) (Hom_cat A X Z))
    (Hom_cat A W Z)
    (@comp_prod_func A W X Z)
    pg
    pg'
    alpha
  ≡ @comp_prod_fapp1_fapp0 A W X Z pg pg' alpha;

assert [A B C : Cat]
  (F : τ (Functor A B))
  (G : τ (Functor B C)) ⊢
  fapp0 (@Functor_comp_pair_func A B C) (Struct_sigma F G)
  ≡ @comp_cat_fapp0 A B C G F;

assert [X Y Z : Cat]
  (FG FG' : τ (Obj (Product_cat (Functor_cat X Y) (Functor_cat Y Z))))
  (theta : τ (Hom
    (Product_cat (Functor_cat X Y) (Functor_cat Y Z))
    FG
    FG'))
  (i : τ (Obj X)) ⊢
  @tapp0_fapp0
    _
    _
    _
    _
    i
    (@comp_prod_fapp1_fapp0 Cat_cat X Y Z FG FG' theta)
  ≡ @tapp1_fapp0
      Y
      Z
      (sigma_Snd FG)
      (sigma_Snd FG')
      (@fapp0 X Y (sigma_Fst FG) i)
      (@fapp0 X Y (sigma_Fst FG') i)
      (sigma_Snd theta)
      (@tapp0_fapp0 X Y (sigma_Fst FG) (sigma_Fst FG') i (sigma_Fst theta));

assert [X Y Z : Cat]
  (FG FG' : τ (Obj (Product_cat (Functor_cat X Y) (Functor_cat Y Z))))
  (theta : τ (Hom
    (Product_cat (Functor_cat X Y) (Functor_cat Y Z))
    FG
    FG'))
  (i j : τ (Obj X)) ⊢
  @tapp1_func
    _
    _
    _
    _
    i
    j
    (@comp_prod_fapp1_fapp0 Cat_cat X Y Z FG FG' theta)
  ≡ @comp_cat_fapp0
      (Hom_cat X i j)
      (Hom_cat
        Y
        (@fapp0 X Y (sigma_Fst FG) i)
        (@fapp0 X Y (sigma_Fst FG') j))
      (Hom_cat
        Z
        (@fapp0 Y Z (sigma_Snd FG) (@fapp0 X Y (sigma_Fst FG) i))
        (@fapp0 Y Z (sigma_Snd FG') (@fapp0 X Y (sigma_Fst FG') j)))
      (@tapp1_func
        Y
        Z
        (sigma_Snd FG)
        (sigma_Snd FG')
        (@fapp0 X Y (sigma_Fst FG) i)
        (@fapp0 X Y (sigma_Fst FG') j)
        (sigma_Snd theta))
      (@tapp1_func
        X
        Y
        (sigma_Fst FG)
        (sigma_Fst FG')
        i
        j
        (sigma_Fst theta));

assert [X Y Z : Cat]
  (FG FG' : τ (Obj (Product_cat (Functor_cat X Y) (Functor_cat Y Z))))
  (theta : τ (Hom
    (Product_cat (Functor_cat X Y) (Functor_cat Y Z))
    FG
    FG'))
  (i j : τ (Obj X))
  (p : τ (Hom X i j)) ⊢
  @tapp1_fapp0
    _
    _
    _
    _
    i
    j
    (@comp_prod_fapp1_fapp0 Cat_cat X Y Z FG FG' theta)
    p
  ≡ @tapp1_fapp0
      Y
      Z
      (sigma_Snd FG)
      (sigma_Snd FG')
      (@fapp0 X Y (sigma_Fst FG) i)
      (@fapp0 X Y (sigma_Fst FG') j)
      (sigma_Snd theta)
      (@tapp1_fapp0
        X
        Y
        (sigma_Fst FG)
        (sigma_Fst FG')
        i
        j
        (sigma_Fst theta)
        p);

// General Hom_cat endpoint-action owner.
assert [A : Cat]
  (x x' y y' : τ (Obj A))
  (g : τ (Hom A x' x))
  (f : τ (Hom A y y')) ⊢
  fapp0 (@Hom_tele_func A x x' y y') (Struct_sigma g f)
  ≡ @Hom_func A x x' y y' g f;

assert [A : Cat]
  (x x' y y' : τ (Obj A))
  (g : τ (Hom A x' x))
  (f : τ (Hom A y y'))
  (h : τ (Hom A x y)) ⊢
  fapp0 (@Hom_func A x x' y y' g f) h
  ≡ @Hom_fapp0 A x x' y y' g f h;

// Both direct one-slot evaluation orders elaborate against the rigid pointwise
// two-endpoint owner.
assert [A : Cat]
  (x x' y y' : τ (Obj A))
  (g : τ (Hom A x' x))
  (f : τ (Hom A y y'))
  (h : τ (Hom A x y)) ⊢
  eq_refl (@Hom_fapp0 A x x' y y' g f h)
  : τ (
      @Hom_fapp0 A x x' y y' g f h
      =
      @hom_postcomp_fapp0 A A (@id Cat_cat A) x' y y' f
        (@hom_precomp_along_fapp0 A A (@id Cat_cat A) y x' x g h));

assert [A : Cat]
  (x x' y y' : τ (Obj A))
  (g : τ (Hom A x' x))
  (f : τ (Hom A y y'))
  (h : τ (Hom A x y)) ⊢
  eq_refl (@Hom_fapp0 A x x' y y' g f h)
  : τ (
      @Hom_fapp0 A x x' y y' g f h
      =
      @hom_precomp_along_fapp0 A A (@id Cat_cat A) y' x' x g
        (@hom_postcomp_fapp0 A A (@id Cat_cat A) x y y' f h));

// One active endpoint is proof-time compatible with the corresponding
// one-slot owner at both functor and point levels.
assert [A : Cat]
  (x y y' : τ (Obj A))
  (f : τ (Hom A y y')) ⊢
  eq_refl (@Hom_func A x x y y' (@id A x) f)
  : τ (
      @Hom_func A x x y y' (@id A x) f
      =
      @hom_postcomp_func A A (@id Cat_cat A) x y y' f);

assert [A : Cat]
  (x x' y : τ (Obj A))
  (g : τ (Hom A x' x)) ⊢
  eq_refl (@Hom_func A x x' y y g (@id A y))
  : τ (
      @Hom_func A x x' y y g (@id A y)
      =
      @hom_precomp_along_func A A (@id Cat_cat A) y x' x g);

assert [A : Cat]
  (x y y' : τ (Obj A))
  (f : τ (Hom A y y'))
  (h : τ (Hom A x y)) ⊢
  eq_refl (@Hom_fapp0 A x x y y' (@id A x) f h)
  : τ (
      @Hom_fapp0 A x x y y' (@id A x) f h
      =
      @hom_postcomp_fapp0 A A (@id Cat_cat A) x y y' f h);

assert [A : Cat]
  (x x' y : τ (Obj A))
  (g : τ (Hom A x' x))
  (h : τ (Hom A x y)) ⊢
  eq_refl (@Hom_fapp0 A x x' y y g (@id A y) h)
  : τ (
      @Hom_fapp0 A x x' y y g (@id A y) h
      =
      @hom_precomp_along_fapp0 A A (@id Cat_cat A) y x' x g h);

// One-slot identity reductions remain runtime; comparison with rigid Hom is proof-time.
assert [A : Cat]
  (x y y' : τ (Obj A))
  (f : τ (Hom A y y'))
  (h : τ (Hom A x y)) ⊢
  @hom_postcomp_fapp0 A A (@id Cat_cat A) x y y' f
    (@hom_precomp_along_fapp0 A A (@id Cat_cat A)
      y x x (@id A x) h)
  ≡ @hom_postcomp_fapp0 A A (@id Cat_cat A) x y y' f h;

assert [A : Cat]
  (x x' y : τ (Obj A))
  (g : τ (Hom A x' x))
  (h : τ (Hom A x y)) ⊢
  @hom_precomp_along_fapp0 A A (@id Cat_cat A) y x' x g
    (@hom_postcomp_fapp0 A A (@id Cat_cat A)
      x y y (@id A y) h)
  ≡ @hom_precomp_along_fapp0 A A (@id Cat_cat A) y x' x g h;

assert [A : Cat]
  (x y y' : τ (Obj A))
  (f : τ (Hom A y y')) ⊢
  @comp_fapp0
    Cat_cat
    (Hom_cat A x y)
    (Hom_cat A x y)
    (Hom_cat A x y')
    (@hom_postcomp_func A A (@id Cat_cat A) x y y' f)
    (@hom_precomp_along_func A A (@id Cat_cat A) y x x (@id A x))
  ≡ @hom_postcomp_func A A (@id Cat_cat A) x y y' f;

assert [A : Cat]
  (x x' y : τ (Obj A))
  (g : τ (Hom A x' x)) ⊢
  @comp_fapp0
    Cat_cat
    (Hom_cat A x y)
    (Hom_cat A x y)
    (Hom_cat A x' y)
    (@hom_precomp_along_func A A (@id Cat_cat A) y x' x g)
    (@hom_postcomp_func A A (@id Cat_cat A) x y y (@id A y))
  ≡ @hom_precomp_along_func A A (@id Cat_cat A) y x' x g;

assert [A : Cat]
  (x y y' : τ (Obj A))
  (f : τ (Hom A y y'))
  (h : τ (Hom A x y)) ⊢
  eq_refl (@Hom_fapp0 A x x y y' (@id A x) f h)
  : τ (
      @Hom_fapp0 A x x y y' (@id A x) f h
      =
      @comp_fapp0 A x y y' f h);

assert [A : Cat]
  (x x' y : τ (Obj A))
  (g : τ (Hom A x' x))
  (h : τ (Hom A x y)) ⊢
  eq_refl (@Hom_fapp0 A x x' y y g (@id A y) h)
  : τ (
      @Hom_fapp0 A x x' y y g (@id A y) h
      =
      @comp_fapp0 A x' x y h g);

// Rigid Hom action retains ordinary functoriality under its own stable heads.
assert [A : Cat] (x y : τ (Obj A)) ⊢
  @Hom_func A x x y y (@id A x) (@id A y)
  ≡ @id_func (Hom_cat A x y);

assert [A : Cat] (x y : τ (Obj A)) (h : τ (Hom A x y)) ⊢
  @Hom_fapp0 A x x y y (@id A x) (@id A y) h
  ≡ h;

assert [A : Cat]
  (x0 x1 x2 y0 y1 y2 : τ (Obj A))
  (g01 : τ (Hom A x1 x0))
  (g12 : τ (Hom A x2 x1))
  (f01 : τ (Hom A y0 y1))
  (f12 : τ (Hom A y1 y2)) ⊢
  @comp_fapp0
    Cat_cat
    (Hom_cat A x0 y0)
    (Hom_cat A x1 y1)
    (Hom_cat A x2 y2)
    (@Hom_func A x1 x2 y1 y2 g12 f12)
    (@Hom_func A x0 x1 y0 y1 g01 f01)
  ≡ @Hom_func
      A x0 x2 y0 y2
      (@comp_fapp0 A x2 x1 x0 g01 g12)
      (@comp_fapp0 A y0 y1 y2 f12 f01);

assert [A : Cat]
  (x0 x1 x2 y0 y1 y2 : τ (Obj A))
  (g01 : τ (Hom A x1 x0))
  (g12 : τ (Hom A x2 x1))
  (f01 : τ (Hom A y0 y1))
  (f12 : τ (Hom A y1 y2))
  (h : τ (Hom A x0 y0)) ⊢
  @Hom_fapp0 A x1 x2 y1 y2 g12 f12
    (@Hom_fapp0 A x0 x1 y0 y1 g01 f01 h)
  ≡ @Hom_fapp0
      A x0 x2 y0 y2
      (@comp_fapp0 A x2 x1 x0 g01 g12)
      (@comp_fapp0 A y0 y1 y2 f12 f01)
      h;

assert [A : Cat]
  (x x' y y' : τ (Obj A)) ⊢
  eq_refl (@Hom_tele_func A x x' y y')
  : τ (
      @Hom_tele_func A x x' y y'
      =
      @comp_fapp0
        Cat_cat
        (Product_cat (Hom_cat A x' x) (Hom_cat A y y'))
        (Product_cat
          (Functor_cat (Hom_cat A x y) (Hom_cat A x' y))
          (Functor_cat (Hom_cat A x' y) (Hom_cat A x' y')))
        (Functor_cat (Hom_cat A x y) (Hom_cat A x' y'))
        (@comp_prod_func
          Cat_cat
          (Hom_cat A x y)
          (Hom_cat A x' y)
          (Hom_cat A x' y'))
        (@Product_map_func
          (Hom_cat A x' x)
          (Functor_cat (Hom_cat A x y) (Hom_cat A x' y))
          (Hom_cat A y y')
          (Functor_cat (Hom_cat A x' y) (Hom_cat A x' y'))
          (@hom_precomp_along_tele_func A A (@id Cat_cat A) y x' x)
          (@hom_postcomp_tele_func A A (@id Cat_cat A) x' y y')));

assert [A : Cat]
  (x x' y y' : τ (Obj A)) ⊢
  eq_refl (@Hom_tele_func A x x' y y')
  : τ (
      @Hom_tele_func A x x' y y'
      =
      @comp_cat_fapp0
        (Product_cat (Hom_cat A x' x) (Hom_cat A y y'))
        (Product_cat
          (Functor_cat (Hom_cat A x y) (Hom_cat A x' y))
          (Functor_cat (Hom_cat A x' y) (Hom_cat A x' y')))
        (Functor_cat (Hom_cat A x y) (Hom_cat A x' y'))
        (@Functor_comp_pair_func
          (Hom_cat A x y)
          (Hom_cat A x' y)
          (Hom_cat A x' y'))
        (@Product_map_func
          (Hom_cat A x' x)
          (Functor_cat (Hom_cat A x y) (Hom_cat A x' y))
          (Hom_cat A y y')
          (Functor_cat (Hom_cat A x' y) (Hom_cat A x' y'))
          (@hom_precomp_along_tele_func A A (@id Cat_cat A) y x' x)
          (@hom_postcomp_tele_func A A (@id Cat_cat A) x' y y')));

assert [A : Cat]
  (x x' y y' : τ (Obj A))
  (g : τ (Hom A x' x))
  (f : τ (Hom A y y')) ⊢
  eq_refl (@Hom_func A x x' y y' g f)
  : τ (
      @Hom_func A x x' y y' g f
      =
      @comp_cat_fapp0
        (Hom_cat A x y)
        (Hom_cat A x' y)
        (Hom_cat A x' y')
        (@hom_postcomp_func A A (@id Cat_cat A) x' y y' f)
        (@hom_precomp_along_func A A (@id Cat_cat A) y x' x g));

assert [A : Cat]
  (x x' y y' : τ (Obj A))
  (g : τ (Hom A x' x))
  (f : τ (Hom A y y')) ⊢
  eq_refl (@Hom_func A x x' y y' g f)
  : τ (
      @Hom_func A x x' y y' g f
      =
      @comp_cat_fapp0
        (Hom_cat A x y)
        (Hom_cat A x y')
        (Hom_cat A x' y')
        (@hom_precomp_along_func A A (@id Cat_cat A) y' x' x g)
        (@hom_postcomp_func A A (@id Cat_cat A) x y y' f));

assert [A B I : Cat]
  (F : τ (Functor I A))
  (G : τ (Functor I B))
  (i : τ (Obj I)) ⊢
  @fapp0 I (Product_cat A B)
    (@Struct_sigma
      (Obj (Functor_cat I A))
      (λ _ : τ (Obj (Functor_cat I A)), Obj (Functor_cat I B))
      F
      G)
    i
    ≡ @Struct_sigma
        (Obj A)
        (λ _ : τ (Obj A), Obj B)
        (@fapp0 I A F i)
        (@fapp0 I B G i);

assert [A B I : Cat]
  (F : τ (Functor I A))
  (G : τ (Functor I B))
  (i j : τ (Obj I)) ⊢
  @fapp1_func I (Product_cat A B)
    (@Struct_sigma
      (Obj (Functor_cat I A))
      (λ _ : τ (Obj (Functor_cat I A)), Obj (Functor_cat I B))
      F
      G)
    i
    j
    ≡ @Struct_sigma
        (Obj (Functor_cat
          (Hom_cat I i j)
          (Hom_cat A (@fapp0 I A F i) (@fapp0 I A F j))))
        (λ _ : τ (Obj (Functor_cat
          (Hom_cat I i j)
          (Hom_cat A (@fapp0 I A F i) (@fapp0 I A F j)))),
          Obj (Functor_cat
            (Hom_cat I i j)
            (Hom_cat B (@fapp0 I B G i) (@fapp0 I B G j))))
        (@fapp1_func I A F i j)
        (@fapp1_func I B G i j);

assert [A B : Cat]
  (p q : τ (Obj (Product_cat A B))) ⊢
  @fapp1_func (Product_cat A B) A (@Product_projL_func A B) p q
    ≡ @Product_projL_func
        (Hom_cat A (sigma_Fst p) (sigma_Fst q))
        (Hom_cat B (sigma_Snd p) (sigma_Snd q));

assert [A B : Cat]
  (p q : τ (Obj (Product_cat A B)))
  (h : τ (Hom (Product_cat A B) p q)) ⊢
  @fapp1_fapp0 (Product_cat A B) A (@Product_projL_func A B) p q h
    ≡ sigma_Fst h;

assert [I A B : Cat]
  (H : τ (Functor I (Product_cat A B)))
  (i : τ (Obj I)) ⊢
  sigma_Fst (@fapp0 I (Product_cat A B) H i)
    ≡ @fapp0 I A (sigma_Fst H) i;

assert [K : Cat] (E D : τ (Catd K)) ⊢
  @eq_refl Cat_grpd (Hom_cat (Catd_cat K) E D)
  : τ (@= Cat_grpd
      (Hom_cat (Catd_cat K) E D)
      (@Transf_cat K Cat_cat E D));

assert [K : Cat] (E D : τ (Catd K)) ⊢
  @eq_refl Cat_grpd (Hom_cat (Functor_cat K Cat_cat) E D)
  : τ (@= Cat_grpd
      (Hom_cat (Functor_cat K Cat_cat) E D)
      (@Functord_cat K E D));

assert [X A B : Cat]
  (F G : τ (Functor X (Product_cat A B)))
  (eta : τ (@Transf X (Product_cat A B) F G))
  (i : τ (Obj X)) ⊢
  sigma_Fst (@tapp0_fapp0 X (Product_cat A B) F G i eta)
    ≡ @tapp0_fapp0 X A (sigma_Fst F) (sigma_Fst G) i (sigma_Fst eta);

assert [A B : Cat] (F : τ (Functor B A))
  (x y : τ (Obj A)) (p : τ (Hom A x y)) (b : τ (Obj B)) ⊢
  @tapp0_fapp0
    B
    Cat_cat
    (@hom_ A B F y)
    (@hom_ A B F x)
    b
    (@fapp1_fapp0 (Op_cat A) (@Catd_cat B) (@hom_int A B F) y x p)
    ≡ @hom_precomp_along_func A A (@id_func A) (@fapp0 B A F b) x y p;

assert [X A B : Cat]
  (F G : τ (Functor X (Product_cat A B)))
  (eta : τ (@Transf X (Product_cat A B) F G))
  (i j : τ (Obj X)) ⊢
  sigma_Fst (@tapp1_func X (Product_cat A B) F G i j eta)
    ≡ @tapp1_func X A (sigma_Fst F) (sigma_Fst G) i j (sigma_Fst eta);

assert [K A : Cat] (x y : τ (Obj A)) (p : τ (Hom A x y))
  (k : τ (Obj K)) ⊢
  @tapp0_fapp0
      K A
      (@Const_func K A x)
      (@Const_func K A y)
      k
      (@Const_transf K A x y p)
    ≡ p;

assert [K A : Cat] (x y : τ (Obj A)) (p : τ (Hom A x y))
  (k k' : τ (Obj K)) ⊢
  @tapp1_func
      K A
      (@Const_func K A x)
      (@Const_func K A y)
      k k'
      (@Const_transf K A x y p)
    ≡ @Const_func (Hom_cat K k k') (Hom_cat A x y) p;

assert [K A : Cat] (x y : τ (Obj A)) (p : τ (Hom A x y))
  (k k' : τ (Obj K)) (q : τ (Hom K k k')) ⊢
  @tapp1_fapp0
      K A
      (@Const_func K A x)
      (@Const_func K A y)
      k k'
      (@Const_transf K A x y p)
      q
    ≡ p;

assert [X Y Z : Cat] (G : τ (Functor Y Z)) (F H : τ (Functor X Y))
  (eta : τ (Transf F H)) (i : τ (Obj X)) ⊢
  @tapp0_fapp0
    X
    Z
    (@comp_cat_fapp0 X Y Z G F)
    (@comp_cat_fapp0 X Y Z G H)
    i
    (@comp_prod_fapp1_fapp0
      Cat_cat
      X
      Y
      Z
      (@Product_pair (Functor_cat X Y) (Functor_cat Y Z) F G)
      (@Product_pair (Functor_cat X Y) (Functor_cat Y Z) H G)
      (@Product_pair
        (Hom_cat (Functor_cat X Y) F H)
        (Hom_cat (Functor_cat Y Z) G G)
        eta
        (@id (Functor_cat Y Z) G)))
  ≡ @fapp1_fapp0
      Y
      Z
      G
      (@fapp0 X Y F i)
      (@fapp0 X Y H i)
      (@tapp0_fapp0 X Y F H i eta);

assert [X Y Z : Cat] (G : τ (Functor Y Z)) (F H : τ (Functor X Y))
  (eta : τ (Transf F H)) (i j : τ (Obj X)) ⊢
  @tapp1_func
    _
    _
    _
    _
    i j
    (@comp_prod_fapp1_fapp0
      Cat_cat
      X
      Y
      Z
      (@Product_pair (Functor_cat X Y) (Functor_cat Y Z) F G)
      (@Product_pair (Functor_cat X Y) (Functor_cat Y Z) H G)
      (@Product_pair
        (Hom_cat (Functor_cat X Y) F H)
        (Hom_cat (Functor_cat Y Z) G G)
        eta
        (@id (Functor_cat Y Z) G)))
  ≡ @comp_cat_fapp0
      (Hom_cat X i j)
      (Hom_cat Y
        (@fapp0 X Y F i)
        (@fapp0 X Y H j))
      (Hom_cat Z
        (@fapp0 Y Z G (@fapp0 X Y F i))
        (@fapp0 Y Z G (@fapp0 X Y H j)))
      (@fapp1_func
        Y
        Z
        G
        (@fapp0 X Y F i)
        (@fapp0 X Y H j))
      (@tapp1_func X Y F H i j eta);

assert [X Y Z : Cat] (G : τ (Functor Y Z)) (F H : τ (Functor X Y))
  (eta : τ (Transf F H)) (i j : τ (Obj X)) (p : τ (Hom X i j)) ⊢
  @tapp1_fapp0
    _
    _
    _
    _
    i j
    (@comp_prod_fapp1_fapp0
      Cat_cat
      X
      Y
      Z
      (@Product_pair (Functor_cat X Y) (Functor_cat Y Z) F G)
      (@Product_pair (Functor_cat X Y) (Functor_cat Y Z) H G)
      (@Product_pair
        (Hom_cat (Functor_cat X Y) F H)
        (Hom_cat (Functor_cat Y Z) G G)
        eta
        (@id (Functor_cat Y Z) G)))
    p
  ≡ @fapp1_fapp0
      Y
      Z
      G
      (@fapp0 X Y F i)
      (@fapp0 X Y H j)
      (@tapp1_fapp0 X Y F H i j eta p);

assert [X Y Z : Cat] (G : τ (Functor Y Z)) (F : τ (Functor X Y)) ⊢
  @comp_prod_fapp1_fapp0
    Cat_cat
    X
    Y
    Z
    (@Product_pair (Functor_cat X Y) (Functor_cat Y Z) F G)
    (@Product_pair (Functor_cat X Y) (Functor_cat Y Z) F G)
    (@Product_pair
      (Hom_cat (Functor_cat X Y) F F)
      (Hom_cat (Functor_cat Y Z) G G)
      (@id (Functor_cat X Y) F)
      (@id (Functor_cat Y Z) G))
    ≡ @id
        (Functor_cat X Z)
        (@comp_cat_fapp0 X Y Z G F);

assert [X Y Z : Cat] (F : τ (Functor X Y)) (G H : τ (Functor Y Z))
  (eta : τ (Transf G H)) (i : τ (Obj X)) ⊢
  @tapp0_fapp0
    _
    _
    _
    _
    i
    (@comp_prod_fapp1_fapp0
      Cat_cat
      X
      Y
      Z
      (@Product_pair (Functor_cat X Y) (Functor_cat Y Z) F G)
      (@Product_pair (Functor_cat X Y) (Functor_cat Y Z) F H)
      (@Product_pair
        (Hom_cat (Functor_cat X Y) F F)
        (Hom_cat (Functor_cat Y Z) G H)
        (@id (Functor_cat X Y) F)
        eta))
  ≡ @tapp0_fapp0
      Y
      Z
      G
      H
      (@fapp0 X Y F i)
      eta;

assert [X Y Z : Cat] (F : τ (Functor X Y)) (G H : τ (Functor Y Z))
  (eta : τ (Transf G H)) (i j : τ (Obj X)) ⊢
  @tapp1_func
    _
    _
    _
    _
    i j
    (@comp_prod_fapp1_fapp0
      Cat_cat
      X
      Y
      Z
      (@Product_pair (Functor_cat X Y) (Functor_cat Y Z) F G)
      (@Product_pair (Functor_cat X Y) (Functor_cat Y Z) F H)
      (@Product_pair
        (Hom_cat (Functor_cat X Y) F F)
        (Hom_cat (Functor_cat Y Z) G H)
        (@id (Functor_cat X Y) F)
        eta))
  ≡ @comp_cat_fapp0
      (Hom_cat X i j)
      (Hom_cat Y
        (@fapp0 X Y F i)
        (@fapp0 X Y F j))
      (Hom_cat Z
        (@fapp0 Y Z G (@fapp0 X Y F i))
        (@fapp0 Y Z H (@fapp0 X Y F j)))
      (@tapp1_func
        Y
        Z
        G
        H
        (@fapp0 X Y F i)
        (@fapp0 X Y F j)
        eta)
      (@fapp1_func X Y F i j);

assert [X Y Z : Cat] (F : τ (Functor X Y)) (G H : τ (Functor Y Z))
  (eta : τ (Transf G H)) (i j : τ (Obj X)) (p : τ (Hom X i j)) ⊢
  @tapp1_fapp0
    _
    _
    _
    _
    i j
    (@comp_prod_fapp1_fapp0
      Cat_cat
      X
      Y
      Z
      (@Product_pair (Functor_cat X Y) (Functor_cat Y Z) F G)
      (@Product_pair (Functor_cat X Y) (Functor_cat Y Z) F H)
      (@Product_pair
        (Hom_cat (Functor_cat X Y) F F)
        (Hom_cat (Functor_cat Y Z) G H)
        (@id (Functor_cat X Y) F)
        eta))
    p
  ≡ @tapp1_fapp0
      Y
      Z
      G
      H
      (@fapp0 X Y F i)
      (@fapp0 X Y F j)
      eta
      (@fapp1_fapp0 X Y F i j p);

assert [X Y Z : Cat] (F : τ (Functor X Y)) (G : τ (Functor Y Z)) ⊢
  @comp_prod_fapp1_fapp0
    Cat_cat
    X
    Y
    Z
    (@Product_pair (Functor_cat X Y) (Functor_cat Y Z) F G)
    (@Product_pair (Functor_cat X Y) (Functor_cat Y Z) F G)
    (@Product_pair
      (Hom_cat (Functor_cat X Y) F F)
      (Hom_cat (Functor_cat Y Z) G G)
      (@id (Functor_cat X Y) F)
      (@id (Functor_cat Y Z) G))
    ≡ @id
        (Functor_cat X Z)
        (@comp_cat_fapp0 X Y Z G F);

assert [X A B : Cat]
  (F G : τ (Functor X (Product_cat A B)))
  (eta : τ (@Transf X (Product_cat A B) F G))
  (i j : τ (Obj X))
  (p : τ (Hom X i j)) ⊢
  sigma_Fst (@tapp1_fapp0 X (Product_cat A B) F G i j eta p)
    ≡ @tapp1_fapp0 X A (sigma_Fst F) (sigma_Fst G) i j (sigma_Fst eta) p;

assert [A A' B : Cat] (G : τ (Functor A A'))
  (x : τ (Obj A)) (y : τ (Obj B)) ⊢
  sigma_Fst
    (fapp0 (@Product_cat_fapp1_tapp0_func A A' B G) (Struct_sigma x y))
    ≡ fapp0 G x;

assert [A A' B : Cat] (G : τ (Functor A A'))
  (x : τ (Obj A)) (y : τ (Obj B)) ⊢
  sigma_Snd
    (fapp0 (@Product_cat_fapp1_tapp0_func A A' B G) (Struct_sigma x y))
    ≡ y;

assert [A A' B : Cat] (G : τ (Functor A A'))
  (x x' : τ (Obj A)) (y y' : τ (Obj B))
  (p : τ (Hom A x x')) (q : τ (Hom B y y')) ⊢
  sigma_Fst
    (@fapp1_fapp0
      (Product_cat A B)
      (Product_cat A' B)
      (@Product_cat_fapp1_tapp0_func A A' B G)
      (Struct_sigma x y)
      (Struct_sigma x' y')
      (Struct_sigma p q))
    ≡ @fapp1_fapp0 A A' G x x' p;

assert [A A' B : Cat] (G : τ (Functor A A'))
  (x x' : τ (Obj A)) (y y' : τ (Obj B))
  (p : τ (Hom A x x')) (q : τ (Hom B y y')) ⊢
  sigma_Snd
    (@fapp1_fapp0
      (Product_cat A B)
      (Product_cat A' B)
      (@Product_cat_fapp1_tapp0_func A A' B G)
      (Struct_sigma x y)
      (Struct_sigma x' y')
      (Struct_sigma p q))
    ≡ q;

assert [A A' B : Cat] (G : τ (Functor A A')) ⊢
  @fapp0
    (Functor_cat A A')
    (Functor_cat (Product_cat A B) (Product_cat A' B))
    (@Product_mapL_func_func A A' B)
    G
    ≡ @Product_cat_fapp1_tapp0_func A A' B G;

// Transparent fibrewise product: no Product_catd owner is introduced.
symbol Product_catd_transparent_check [K : Cat]
  (B C : τ (Catd K))
  : τ (Catd K)
≔ @comp_cat_fapp0
    K
    (Product_cat Cat_cat Cat_cat)
    Cat_cat
    (@uncurry_func Cat_cat Cat_cat Cat_cat Product_cat_func)
    (Struct_sigma B C);

// The existing semantic composite computes its pointwise fibre.
assert [K : Cat]
  (B C : τ (Catd K))
  (k : τ (Obj K)) ⊢
  Fibre_cat (@Product_catd_transparent_check K B C) k
    ≡ Product_cat (Fibre_cat B k) (Fibre_cat C k);

// The two existing-owner projections expose componentwise base-arrow
// transport while retaining Product_map_func as the iterable result.
assert [K : Cat]
  (B C : τ (Catd K))
  (x y : τ (Obj K))
  (p : τ (Hom K x y)) ⊢
  catd_transport_func
    (@Product_catd_transparent_check K B C)
    p
    ≡ @Product_map_func
        (Fibre_cat B x)
        (Fibre_cat B y)
        (Fibre_cat C x)
        (Fibre_cat C y)
        (catd_transport_func B p)
        (catd_transport_func C p);

// The shared base arrow is a real discriminator: two unrelated parallel
// arrows do not trigger the narrow product projection.
assertnot [K : Cat]
  (B C : τ (Catd K))
  (x y : τ (Obj K))
  (p q : τ (Hom K x y)) ⊢
  @tapp1_fapp0
      Cat_cat
      Cat_cat
      (@Product_cat_fapp0_func (Fibre_cat B x))
      (@Product_cat_fapp0_func (Fibre_cat B y))
      (Fibre_cat C x)
      (Fibre_cat C y)
      (@Product_cat_fapp1_fapp0_functord
        (Fibre_cat B x)
        (Fibre_cat B y)
        (catd_transport_func B p))
      (catd_transport_func C q)
    ≡ @Product_map_func
        (Fibre_cat B x)
        (Fibre_cat B y)
        (Fibre_cat C x)
        (Fibre_cat C y)
        (catd_transport_func B p)
        (catd_transport_func C q);

// An opaque family is not identified with the transparent product.
assertnot [K : Cat]
  (E B C : τ (Catd K)) ⊢
  E ≡ @Product_catd_transparent_check K B C;

// Displayed functor categories do not globally collapse to products.
assertnot [K : Cat]
  (E B C : τ (Catd K)) ⊢
  @Functord_cat K E (@Product_catd_transparent_check K B C)
    ≡ @Product_cat
        (@Functord_cat K E B)
        (@Functord_cat K E C);

// Pullback stability remains a separate comparison/theorem boundary.
assertnot [A K : Cat]
  (F : τ (Functor A K))
  (B C : τ (Catd K)) ⊢
  @Pullback_catd
      A K
      (@Product_catd_transparent_check K B C)
      F
    ≡ @Product_catd_transparent_check
        A
        (@Pullback_catd A K B F)
        (@Pullback_catd A K C F);

// Fixed-base fibrewise product projections and pairing.
//
// These check-only aliases expose swap and diagonal as transparent
// compositions of the three active structural owners.
symbol Product_swap_funcd_check [K : Cat]
  (B C : τ (Catd K))
  : τ (Functord
      (@Product_catd_transparent_check K B C)
      (@Product_catd_transparent_check K C B))
≔ @Product_pair_funcd
    K
    (@Product_catd_transparent_check K B C)
    C
    B
    (@Product_projR_funcd K B C)
    (@Product_projL_funcd K B C);

symbol Product_diag_funcd_check [K : Cat]
  (B : τ (Catd K))
  : τ (Functord
      B
      (@Product_catd_transparent_check K B B))
≔ @Product_pair_funcd
    K
    B
    B
    B
    (@id_funcd K B)
    (@id_funcd K B);

// Both point projections expose the ordinary fibre projections.
assert [K : Cat]
  (B C : τ (Catd K))
  (k : τ (Obj K)) ⊢
  @tapp0_fapp0
      K
      Cat_cat
      (@Product_catd_transparent_check K B C)
      B
      k
      (@Product_projL_funcd K B C)
    ≡ @Product_projL_func
        (Fibre_cat B k)
        (Fibre_cat C k);

assert [K : Cat]
  (B C : τ (Catd K))
  (k : τ (Obj K)) ⊢
  @tapp0_fapp0
      K
      Cat_cat
      (@Product_catd_transparent_check K B C)
      C
      k
      (@Product_projR_funcd K B C)
    ≡ @Product_projR_func
        (Fibre_cat B k)
        (Fibre_cat C k);

// Full projection action remains at iterable functor level.
assert [K : Cat]
  (B C : τ (Catd K))
  (x y : τ (Obj K)) ⊢
  @tapp1_func
      K
      Cat_cat
      (@Product_catd_transparent_check K B C)
      B
      x
      y
      (@Product_projL_funcd K B C)
    ≡ @comp_cat_fapp0
        (Hom_cat K x y)
        (Functor_cat (Fibre_cat B x) (Fibre_cat B y))
        (Functor_cat
          (Fibre_cat (@Product_catd_transparent_check K B C) x)
          (Fibre_cat B y))
        (@comp_cat_con_func
          (Fibre_cat (@Product_catd_transparent_check K B C) x)
          (Fibre_cat B x)
          (Fibre_cat B y)
          (@Product_projL_func
            (Fibre_cat B x)
            (Fibre_cat C x)))
        (@fapp1_func K Cat_cat B x y);

assert [K : Cat]
  (B C : τ (Catd K))
  (x y : τ (Obj K)) ⊢
  @tapp1_func
      K
      Cat_cat
      (@Product_catd_transparent_check K B C)
      C
      x
      y
      (@Product_projR_funcd K B C)
    ≡ @comp_cat_fapp0
        (Hom_cat K x y)
        (Functor_cat (Fibre_cat C x) (Fibre_cat C y))
        (Functor_cat
          (Fibre_cat (@Product_catd_transparent_check K B C) x)
          (Fibre_cat C y))
        (@comp_cat_con_func
          (Fibre_cat (@Product_catd_transparent_check K B C) x)
          (Fibre_cat C x)
          (Fibre_cat C y)
          (@Product_projR_func
            (Fibre_cat B x)
            (Fibre_cat C x)))
        (@fapp1_func K Cat_cat C x y);

// Capped projection actions retain stable precomposition owners.
assert [K : Cat]
  (B C : τ (Catd K))
  (x y : τ (Obj K))
  (p : τ (Hom K x y)) ⊢
  @tapp1_fapp0
      K
      Cat_cat
      (@Product_catd_transparent_check K B C)
      B
      x
      y
      (@Product_projL_funcd K B C)
      p
    ≡ @hom_precomp_along_fapp0
        Cat_cat
        Cat_cat
        (@id Cat_cat Cat_cat)
        (Fibre_cat B y)
        (Fibre_cat (@Product_catd_transparent_check K B C) x)
        (Fibre_cat B x)
        (@Product_projL_func
          (Fibre_cat B x)
          (Fibre_cat C x))
        (@fapp1_fapp0 K Cat_cat B x y p);

assert [K : Cat]
  (B C : τ (Catd K))
  (x y : τ (Obj K))
  (p : τ (Hom K x y)) ⊢
  @tapp1_fapp0
      K
      Cat_cat
      (@Product_catd_transparent_check K B C)
      C
      x
      y
      (@Product_projR_funcd K B C)
      p
    ≡ @hom_precomp_along_fapp0
        Cat_cat
        Cat_cat
        (@id Cat_cat Cat_cat)
        (Fibre_cat C y)
        (Fibre_cat (@Product_catd_transparent_check K B C) x)
        (Fibre_cat C x)
        (@Product_projR_func
          (Fibre_cat B x)
          (Fibre_cat C x))
        (@fapp1_fapp0 K Cat_cat C x y p);

// Pairing computes pointwise and at both full and capped base action.
assert [K : Cat]
  (E B C : τ (Catd K))
  (FF : τ (Functord E B))
  (GG : τ (Functord E C))
  (k : τ (Obj K)) ⊢
  @tapp0_fapp0
      K
      Cat_cat
      E
      (@Product_catd_transparent_check K B C)
      k
      (@Product_pair_funcd K E B C FF GG)
    ≡ @Product_pair
        (Functor_cat (Fibre_cat E k) (Fibre_cat B k))
        (Functor_cat (Fibre_cat E k) (Fibre_cat C k))
        (@tapp0_fapp0 K Cat_cat E B k FF)
        (@tapp0_fapp0 K Cat_cat E C k GG);

assert [K : Cat]
  (E B C : τ (Catd K))
  (FF : τ (Functord E B))
  (GG : τ (Functord E C))
  (x y : τ (Obj K)) ⊢
  @tapp1_func
      K
      Cat_cat
      E
      (@Product_catd_transparent_check K B C)
      x
      y
      (@Product_pair_funcd K E B C FF GG)
    ≡ @Product_pair
        (Functor_cat (Hom_cat K x y)
          (Functor_cat (Fibre_cat E x) (Fibre_cat B y)))
        (Functor_cat (Hom_cat K x y)
          (Functor_cat (Fibre_cat E x) (Fibre_cat C y)))
        (@tapp1_func K Cat_cat E B x y FF)
        (@tapp1_func K Cat_cat E C x y GG);

assert [K : Cat]
  (E B C : τ (Catd K))
  (FF : τ (Functord E B))
  (GG : τ (Functord E C))
  (x y : τ (Obj K))
  (p : τ (Hom K x y)) ⊢
  @tapp1_fapp0
      K
      Cat_cat
      E
      (@Product_catd_transparent_check K B C)
      x
      y
      (@Product_pair_funcd K E B C FF GG)
      p
    ≡ @Product_pair
        (Functor_cat (Fibre_cat E x) (Fibre_cat B y))
        (Functor_cat (Fibre_cat E x) (Fibre_cat C y))
        (@tapp1_fapp0 K Cat_cat E B x y FF p)
        (@tapp1_fapp0 K Cat_cat E C x y GG p);

// The canonical internalized cell of displayed pairing is componentwise.
assert [K : Cat]
  [E B C : τ (Catd K)]
  (FF : τ (Functord E B))
  (GG : τ (Functord E C))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @fdapp1_int_cell
    K
    E
    (@Product_catd_transparent_check K B C)
    (@Product_pair_funcd K E B C FF GG)
    x
    y
    p
    u
  ≡ @Product_pair
      (Hom_cat
        (Fibre_cat B y)
        (@fapp0
          (Fibre_cat E x)
          (Fibre_cat B y)
          (@functord_transport_lhs_func K E B FF x y p)
          u)
        (@fapp0
          (Fibre_cat E x)
          (Fibre_cat B y)
          (@functord_transport_rhs_func K E B FF x y p)
          u))
      (Hom_cat
        (Fibre_cat C y)
        (@fapp0
          (Fibre_cat E x)
          (Fibre_cat C y)
          (@functord_transport_lhs_func K E C GG x y p)
          u)
        (@fapp0
          (Fibre_cat E x)
          (Fibre_cat C y)
          (@functord_transport_rhs_func K E C GG x y p)
          u))
      (@fdapp1_int_cell K E B FF x y p u)
      (@fdapp1_int_cell K E C GG x y p u);

// Componentwise computation does not identify the paired cell with an
// arbitrary opaque arrow having the same endpoints.
assertnot [K : Cat]
  [E B C : τ (Catd K)]
  (FF : τ (Functord E B))
  (GG : τ (Functord E C))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x)))
  (h : τ (Hom
    (Fibre_cat (@Product_catd_transparent_check K B C) y)
    (@fapp0
      (Fibre_cat E x)
      (Fibre_cat (@Product_catd_transparent_check K B C) y)
      (@functord_transport_lhs_func
        K
        E
        (@Product_catd_transparent_check K B C)
        (@Product_pair_funcd K E B C FF GG)
        x
        y
        p)
      u)
    (@fapp0
      (Fibre_cat E x)
      (Fibre_cat (@Product_catd_transparent_check K B C) y)
      (@functord_transport_rhs_func
        K
        E
        (@Product_catd_transparent_check K B C)
        (@Product_pair_funcd K E B C FF GG)
        x
        y
        p)
      u))) ⊢
  @fdapp1_int_cell
      K
      E
      (@Product_catd_transparent_check K B C)
      (@Product_pair_funcd K E B C FF GG)
      x
      y
      p
      u
  ≡ h;

// Whole displayed universal-property betas.
assert [K : Cat]
  (E B C : τ (Catd K))
  (FF : τ (Functord E B))
  (GG : τ (Functord E C)) ⊢
  @comp_fapp0
      (@Catd_cat K)
      E
      (@Product_catd_transparent_check K B C)
      B
      (@Product_projL_funcd K B C)
      (@Product_pair_funcd K E B C FF GG)
    ≡ FF;

assert [K : Cat]
  (E B C : τ (Catd K))
  (FF : τ (Functord E B))
  (GG : τ (Functord E C)) ⊢
  @comp_fapp0
      (@Catd_cat K)
      E
      (@Product_catd_transparent_check K B C)
      C
      (@Product_projR_funcd K B C)
      (@Product_pair_funcd K E B C FF GG)
    ≡ GG;

// Derived exchange and contraction have the expected fibre components.
assert [K : Cat]
  (B C : τ (Catd K))
  (k : τ (Obj K)) ⊢
  @tapp0_fapp0
      K
      Cat_cat
      (@Product_catd_transparent_check K B C)
      (@Product_catd_transparent_check K C B)
      k
      (@Product_swap_funcd_check K B C)
    ≡ @Product_pair
        (Functor_cat
          (Product_cat (Fibre_cat B k) (Fibre_cat C k))
          (Fibre_cat C k))
        (Functor_cat
          (Product_cat (Fibre_cat B k) (Fibre_cat C k))
          (Fibre_cat B k))
        (@Product_projR_func
          (Fibre_cat B k)
          (Fibre_cat C k))
        (@Product_projL_func
          (Fibre_cat B k)
          (Fibre_cat C k));

assert [K : Cat]
  (B : τ (Catd K))
  (k : τ (Obj K)) ⊢
  @tapp0_fapp0
      K
      Cat_cat
      B
      (@Product_catd_transparent_check K B B)
      k
      (@Product_diag_funcd_check K B)
    ≡ @Product_pair
        (Functor_cat (Fibre_cat B k) (Fibre_cat B k))
        (Functor_cat (Fibre_cat B k) (Fibre_cat B k))
        (@id_func (Fibre_cat B k))
        (@id_func (Fibre_cat B k));

// The full projection actions accept a genuine next base cell.
symbol Product_projL_funcd_higher_check
  [K : Cat]
  [B C : τ (Catd K)]
  [x y : τ (Obj K)]
  [p q : τ (Hom K x y)]
  (alpha : τ (Hom (Hom_cat K x y) p q))
  : τ (Transf
      (@tapp1_fapp0
        K
        Cat_cat
        (@Product_catd_transparent_check K B C)
        B
        x
        y
        (@Product_projL_funcd K B C)
        p)
      (@tapp1_fapp0
        K
        Cat_cat
        (@Product_catd_transparent_check K B C)
        B
        x
        y
        (@Product_projL_funcd K B C)
        q))
≔ @fapp1_fapp0
    (Hom_cat K x y)
    (Functor_cat
      (Fibre_cat (@Product_catd_transparent_check K B C) x)
      (Fibre_cat B y))
    (@tapp1_func
      K
      Cat_cat
      (@Product_catd_transparent_check K B C)
      B
      x
      y
      (@Product_projL_funcd K B C))
    p
    q
    alpha;

symbol Product_projR_funcd_higher_check
  [K : Cat]
  [B C : τ (Catd K)]
  [x y : τ (Obj K)]
  [p q : τ (Hom K x y)]
  (alpha : τ (Hom (Hom_cat K x y) p q))
  : τ (Transf
      (@tapp1_fapp0
        K
        Cat_cat
        (@Product_catd_transparent_check K B C)
        C
        x
        y
        (@Product_projR_funcd K B C)
        p)
      (@tapp1_fapp0
        K
        Cat_cat
        (@Product_catd_transparent_check K B C)
        C
        x
        y
        (@Product_projR_funcd K B C)
        q))
≔ @fapp1_fapp0
    (Hom_cat K x y)
    (Functor_cat
      (Fibre_cat (@Product_catd_transparent_check K B C) x)
      (Fibre_cat C y))
    (@tapp1_func
      K
      Cat_cat
      (@Product_catd_transparent_check K B C)
      C
      x
      y
      (@Product_projR_funcd K B C))
    p
    q
    alpha;

// Pairing's full action remains iterable, and both higher projections compute.
symbol Product_pair_funcd_higher_check
  [K : Cat]
  [E B C : τ (Catd K)]
  [FF : τ (Functord E B)]
  [GG : τ (Functord E C)]
  [x y : τ (Obj K)]
  [p q : τ (Hom K x y)]
  (alpha : τ (Hom (Hom_cat K x y) p q))
  : τ (Transf
      (@tapp1_fapp0
        K
        Cat_cat
        E
        (@Product_catd_transparent_check K B C)
        x
        y
        (@Product_pair_funcd K E B C FF GG)
        p)
      (@tapp1_fapp0
        K
        Cat_cat
        E
        (@Product_catd_transparent_check K B C)
        x
        y
        (@Product_pair_funcd K E B C FF GG)
        q))
≔ @fapp1_fapp0
    (Hom_cat K x y)
    (Functor_cat
      (Fibre_cat E x)
      (Fibre_cat (@Product_catd_transparent_check K B C) y))
    (@tapp1_func
      K
      Cat_cat
      E
      (@Product_catd_transparent_check K B C)
      x
      y
      (@Product_pair_funcd K E B C FF GG))
    p
    q
    alpha;

assert [K : Cat]
  (E B C : τ (Catd K))
  (FF : τ (Functord E B))
  (GG : τ (Functord E C))
  (x y : τ (Obj K))
  (p q : τ (Hom K x y))
  (alpha : τ (Hom (Hom_cat K x y) p q)) ⊢
  sigma_Fst
      (@Product_pair_funcd_higher_check
        K E B C FF GG x y p q alpha)
    ≡ @fapp1_fapp0
        (Hom_cat K x y)
        (Functor_cat (Fibre_cat E x) (Fibre_cat B y))
        (@tapp1_func K Cat_cat E B x y FF)
        p
        q
        alpha;

assert [K : Cat]
  (E B C : τ (Catd K))
  (FF : τ (Functord E B))
  (GG : τ (Functord E C))
  (x y : τ (Obj K))
  (p q : τ (Hom K x y))
  (alpha : τ (Hom (Hom_cat K x y) p q)) ⊢
  sigma_Snd
      (@Product_pair_funcd_higher_check
        K E B C FF GG x y p q alpha)
    ≡ @fapp1_fapp0
        (Hom_cat K x y)
        (Functor_cat (Fibre_cat E x) (Fibre_cat C y))
        (@tapp1_func K Cat_cat E C x y GG)
        p
        q
        alpha;

// catalog-area: Constant-domain displayed evaluation
// Coherent displayed evaluation with a constant ordinary domain.
symbol Displayed_eval_subject_check [K A : Cat] (B : τ (Catd K))
  : τ (Catd K)
≔ @Functor_catd K (@Const_catd (Op_cat K) A) B;

symbol Displayed_eval_source_check [K A : Cat] (B : τ (Catd K))
  : τ (Catd K)
≔ @comp_cat_fapp0
    K
    (Product_cat Cat_cat Cat_cat)
    Cat_cat
    (@uncurry_func Cat_cat Cat_cat Cat_cat Product_cat_func)
    (Struct_sigma
      (@Displayed_eval_subject_check K A B)
      (@Const_catd K A));

// The stable displayed evaluator projects to ordinary product evaluation.
assert [K A : Cat]
  (B : τ (Catd K))
  (k : τ (Obj K)) ⊢
  @tapp0_fapp0
      K Cat_cat
      (@Displayed_eval_source_check K A B)
      B
      k
      (@Eval_funcd K A B)
    ≡ @Eval_func A (Fibre_cat B k);

// Object beta at a fibre computes to ordinary functor application.
assert [K A : Cat]
  (B : τ (Catd K))
  (k : τ (Obj K))
  (F : τ (Functor A (Fibre_cat B k)))
  (a : τ (Obj A)) ⊢
  @fapp0
      (Product_cat (Functor_cat A (Fibre_cat B k)) A)
      (Fibre_cat B k)
      (@tapp0_fapp0
        K Cat_cat
        (@Displayed_eval_source_check K A B)
        B
        k
        (@Eval_funcd K A B))
      (Struct_sigma F a)
    ≡ @fapp0 A (Fibre_cat B k) F a;

// Displayed terminal weakening projects to the ordinary unique functor.
assert [K : Cat]
  (E : τ (Catd K))
  (k : τ (Obj K)) ⊢
  @tapp0_fapp0
      K Cat_cat E (@Const_catd K Terminal_cat) k
      (@Terminal_funcd K E)
    ≡ @Terminal_func (Fibre_cat E k);

// A coherent constant map from any displayed source is derived, not
// primitive.
symbol Const_funcd_check [K A : Cat]
  [E : τ (Catd K)]
  (a : τ (Obj A))
  : τ (Functord E (@Const_catd K A))
≔ @comp_fapp0
    (@Catd_cat K)
    E
    (@Const_catd K Terminal_cat)
    (@Const_catd K A)
    (@Const_func K A a)
    (@Terminal_funcd K E);

// Varying displayed functor and varying coherent argument.
symbol Displayed_eval_varying_check [K A : Cat]
  [E B : τ (Catd K)]
  (FF : τ (Functord E (@Displayed_eval_subject_check K A B)))
  (xx : τ (Functord E (@Const_catd K A)))
  : τ (Functord E B)
≔ @comp_fapp0
    (@Catd_cat K)
    E
    (@Displayed_eval_source_check K A B)
    B
    (@Eval_funcd K A B)
    (@Product_pair_funcd
      K E
      (@Displayed_eval_subject_check K A B)
      (@Const_catd K A)
      FF xx);

assert [K A : Cat]
  (E B : τ (Catd K))
  (FF : τ (Functord E (@Displayed_eval_subject_check K A B)))
  (xx : τ (Functord E (@Const_catd K A)))
  (k : τ (Obj K))
  (e : τ (Obj (Fibre_cat E k))) ⊢
  @fapp0
      (Fibre_cat E k)
      (Fibre_cat B k)
      (@tapp0_fapp0
        K Cat_cat E B k
        (@Displayed_eval_varying_check K A E B FF xx))
      e
    ≡ @fapp0
        A
        (Fibre_cat B k)
        (@fapp0
          (Fibre_cat E k)
          (Functor_cat A (Fibre_cat B k))
          (@tapp0_fapp0
            K Cat_cat E
            (@Displayed_eval_subject_check K A B)
            k FF)
          e)
        (@fapp0
          (Fibre_cat E k)
          A
          (@tapp0_fapp0 K Cat_cat E (@Const_catd K A) k xx)
          e);

// Fixed evaluation is derived through Terminal_funcd rather than a third
// stable owner.
symbol Displayed_eval_fixed_check [K A : Cat]
  [B : τ (Catd K)]
  (a : τ (Obj A))
  : τ (Functord (@Displayed_eval_subject_check K A B) B)
≔ @comp_fapp0
    (@Catd_cat K)
    (@Displayed_eval_subject_check K A B)
    (@Displayed_eval_source_check K A B)
    B
    (@Eval_funcd K A B)
    (@Product_pair_funcd
      K
      (@Displayed_eval_subject_check K A B)
      (@Displayed_eval_subject_check K A B)
      (@Const_catd K A)
      (@id
        (@Catd_cat K)
        (@Displayed_eval_subject_check K A B))
      (@Const_funcd_check
        K A
        (@Displayed_eval_subject_check K A B)
        a));

assert [K A : Cat]
  (B : τ (Catd K))
  (a : τ (Obj A))
  (k : τ (Obj K))
  (F : τ (Functor A (Fibre_cat B k))) ⊢
  @fapp0
      (Functor_cat A (Fibre_cat B k))
      (Fibre_cat B k)
      (@tapp0_fapp0
        K Cat_cat
        (@Displayed_eval_subject_check K A B)
        B k
        (@Displayed_eval_fixed_check K A B a))
      F
    ≡ @fapp0 A (Fibre_cat B k) F a;

// Base-arrow action is inherited from the generic displayed-functor
// projection and remains at iterable functor level.
assert [K A : Cat]
  (B : τ (Catd K))
  (x y : τ (Obj K)) ⊢
  @tapp1_func
      K Cat_cat
      (@Displayed_eval_source_check K A B)
      B x y
      (@Eval_funcd K A B)
    : τ (Functor
        (Hom_cat K x y)
        (Functor_cat
          (Fibre_cat (@Displayed_eval_source_check K A B) x)
          (Fibre_cat B y)));

// The same generic action remains iterable at the next hom level.
symbol Displayed_eval_higher_check [K A : Cat]
  [B : τ (Catd K)]
  [x y : τ (Obj K)]
  [p q : τ (Hom K x y)]
  (alpha : τ (Hom (Hom_cat K x y) p q))
  : τ (Transf
      (@tapp1_fapp0
        K Cat_cat
        (@Displayed_eval_source_check K A B)
        B x y
        (@Eval_funcd K A B)
        p)
      (@tapp1_fapp0
        K Cat_cat
        (@Displayed_eval_source_check K A B)
        B x y
        (@Eval_funcd K A B)
        q))
≔ @fapp1_fapp0
    (Hom_cat K x y)
    (Functor_cat
      (Fibre_cat (@Displayed_eval_source_check K A B) x)
      (Fibre_cat B y))
    (@tapp1_func
      K Cat_cat
      (@Displayed_eval_source_check K A B)
      B x y
      (@Eval_funcd K A B))
    p q alpha;

// The arbitrary mixed-domain/plain-argument route would require identifying
// the directed base with its opposite; that collapse remains absent.
assertnot [K : Cat] ⊢ Op_cat K ≡ K;

// catalog-area: Displayed dependent chain
// One genuine dependency edge:
//
//   k : K, a : A[k], b : B[(k,a)].
//
// The direct terms remain displayed functors. The outer variable is first
// internalized as a section over Sigma(A), then weakened along the next Sigma
// projection; the inner variable is the displayed identity at B.
symbol Displayed_chain_K_check : Cat;
symbol Displayed_chain_A_check
  : τ (Catd Displayed_chain_K_check);
symbol Displayed_chain_B_check
  : τ (Catd
      (@Sigma_cat
        Displayed_chain_K_check
        Displayed_chain_A_check));

symbol Displayed_chain_A_var_check
  : τ (Obj
      (@Functord_cat
        (@Sigma_cat
          Displayed_chain_K_check
          Displayed_chain_A_check)
        (@Const_catd
          (@Sigma_cat
            Displayed_chain_K_check
            Displayed_chain_A_check)
          Terminal_cat)
        (@Sigma_proj1_pullback_catd
          Displayed_chain_K_check
          Displayed_chain_A_check
          Displayed_chain_A_check)))
≔ @sigma_functord_sec
    Displayed_chain_K_check
    Displayed_chain_A_check
    Displayed_chain_A_check
    (@id_funcd
      Displayed_chain_K_check
      Displayed_chain_A_check);

symbol Displayed_chain_A_after_B_check
  : τ (Obj
      (@Functord_cat
        (@Sigma_cat
          (@Sigma_cat
            Displayed_chain_K_check
            Displayed_chain_A_check)
          Displayed_chain_B_check)
        (@Const_catd
          (@Sigma_cat
            (@Sigma_cat
              Displayed_chain_K_check
              Displayed_chain_A_check)
            Displayed_chain_B_check)
          Terminal_cat)
        (@Sigma_proj1_pullback_catd
          (@Sigma_cat
            Displayed_chain_K_check
            Displayed_chain_A_check)
          Displayed_chain_B_check
          (@Sigma_proj1_pullback_catd
            Displayed_chain_K_check
            Displayed_chain_A_check
            Displayed_chain_A_check))))
≔ @fapp0
    (@Functord_cat
      (@Sigma_cat
        Displayed_chain_K_check
        Displayed_chain_A_check)
      (@Const_catd
        (@Sigma_cat
          Displayed_chain_K_check
          Displayed_chain_A_check)
        Terminal_cat)
      (@Sigma_proj1_pullback_catd
        Displayed_chain_K_check
        Displayed_chain_A_check
        Displayed_chain_A_check))
    (@Functord_cat
      (@Sigma_cat
        (@Sigma_cat
          Displayed_chain_K_check
          Displayed_chain_A_check)
        Displayed_chain_B_check)
      (@Const_catd
        (@Sigma_cat
          (@Sigma_cat
            Displayed_chain_K_check
            Displayed_chain_A_check)
          Displayed_chain_B_check)
        Terminal_cat)
      (@Sigma_proj1_pullback_catd
        (@Sigma_cat
          Displayed_chain_K_check
          Displayed_chain_A_check)
        Displayed_chain_B_check
        (@Sigma_proj1_pullback_catd
          Displayed_chain_K_check
          Displayed_chain_A_check
          Displayed_chain_A_check)))
    (@section_pullback_func
      (@Sigma_cat
        (@Sigma_cat
          Displayed_chain_K_check
          Displayed_chain_A_check)
        Displayed_chain_B_check)
      (@Sigma_cat
        Displayed_chain_K_check
        Displayed_chain_A_check)
      (@Sigma_proj1_func
        (@Sigma_cat
          Displayed_chain_K_check
          Displayed_chain_A_check)
        Displayed_chain_B_check)
      (@Sigma_proj1_pullback_catd
        Displayed_chain_K_check
        Displayed_chain_A_check
        Displayed_chain_A_check))
    Displayed_chain_A_var_check;

symbol Displayed_chain_B_var_check
  : τ (Obj
      (@Functord_cat
        (@Sigma_cat
          (@Sigma_cat
            Displayed_chain_K_check
            Displayed_chain_A_check)
          Displayed_chain_B_check)
        (@Const_catd
          (@Sigma_cat
            (@Sigma_cat
              Displayed_chain_K_check
              Displayed_chain_A_check)
            Displayed_chain_B_check)
          Terminal_cat)
        (@Sigma_proj1_pullback_catd
          (@Sigma_cat
            Displayed_chain_K_check
            Displayed_chain_A_check)
          Displayed_chain_B_check
          Displayed_chain_B_check)))
≔ @sigma_functord_sec
    (@Sigma_cat
      Displayed_chain_K_check
      Displayed_chain_A_check)
    Displayed_chain_B_check
    Displayed_chain_B_check
    (@id_funcd
      (@Sigma_cat
        Displayed_chain_K_check
        Displayed_chain_A_check)
      Displayed_chain_B_check);

// Immediate and recursively weakened variable objects both compute.
assert
  (k : τ (Obj Displayed_chain_K_check))
  (a : τ (Obj (Fibre_cat Displayed_chain_A_check k))) ⊢
  @piapp0
    (@Sigma_cat
      Displayed_chain_K_check
      Displayed_chain_A_check)
    (@Sigma_proj1_pullback_catd
      Displayed_chain_K_check
      Displayed_chain_A_check
      Displayed_chain_A_check)
    Displayed_chain_A_var_check
    (Struct_sigma k a)
  ≡ a;

assert
  (k : τ (Obj Displayed_chain_K_check))
  (a : τ (Obj (Fibre_cat Displayed_chain_A_check k)))
  (b : τ (Obj
      (Fibre_cat
        Displayed_chain_B_check
        (Struct_sigma k a)))) ⊢
  @piapp0
    (@Sigma_cat
      (@Sigma_cat
        Displayed_chain_K_check
        Displayed_chain_A_check)
      Displayed_chain_B_check)
    (@Sigma_proj1_pullback_catd
      (@Sigma_cat
        Displayed_chain_K_check
        Displayed_chain_A_check)
      Displayed_chain_B_check
      (@Sigma_proj1_pullback_catd
        Displayed_chain_K_check
        Displayed_chain_A_check
        Displayed_chain_A_check))
    Displayed_chain_A_after_B_check
    (Struct_sigma (Struct_sigma k a) b)
  ≡ a;

assert
  (k : τ (Obj Displayed_chain_K_check))
  (a : τ (Obj (Fibre_cat Displayed_chain_A_check k)))
  (b : τ (Obj
      (Fibre_cat
        Displayed_chain_B_check
        (Struct_sigma k a)))) ⊢
  @piapp0
    (@Sigma_cat
      (@Sigma_cat
        Displayed_chain_K_check
        Displayed_chain_A_check)
      Displayed_chain_B_check)
    (@Sigma_proj1_pullback_catd
      (@Sigma_cat
        Displayed_chain_K_check
        Displayed_chain_A_check)
      Displayed_chain_B_check
      Displayed_chain_B_check)
    Displayed_chain_B_var_check
    (Struct_sigma (Struct_sigma k a) b)
  ≡ b;

symbol Displayed_chain_D_check
  : τ (Catd Displayed_chain_K_check);
symbol Displayed_chain_FF_check
  : τ (Functord
      Displayed_chain_A_check
      Displayed_chain_D_check);

// The bridge preserves an arbitrary displayed functor's object action.
assert
  (k : τ (Obj Displayed_chain_K_check))
  (a : τ (Obj (Fibre_cat Displayed_chain_A_check k))) ⊢
  @piapp0
    (@Sigma_cat
      Displayed_chain_K_check
      Displayed_chain_A_check)
    (@Sigma_proj1_pullback_catd
      Displayed_chain_K_check
      Displayed_chain_A_check
      Displayed_chain_D_check)
    (@sigma_functord_sec
      Displayed_chain_K_check
      Displayed_chain_A_check
      Displayed_chain_D_check
      Displayed_chain_FF_check)
    (Struct_sigma k a)
  ≡ @fapp0
      (Fibre_cat Displayed_chain_A_check k)
      (Fibre_cat Displayed_chain_D_check k)
      (@tapp0_fapp0
        Displayed_chain_K_check
        Cat_cat
        Displayed_chain_A_check
        Displayed_chain_D_check
        k
        Displayed_chain_FF_check)
      a;

symbol Displayed_chain_k0_check
  : τ (Obj Displayed_chain_K_check);
symbol Displayed_chain_k1_check
  : τ (Obj Displayed_chain_K_check);
symbol Displayed_chain_a0_check
  : τ (Obj
      (Fibre_cat
        Displayed_chain_A_check
        Displayed_chain_k0_check));
symbol Displayed_chain_a1_check
  : τ (Obj
      (Fibre_cat
        Displayed_chain_A_check
        Displayed_chain_k1_check));
symbol Displayed_chain_p_check
  : τ (Hom
      Displayed_chain_K_check
      Displayed_chain_k0_check
      Displayed_chain_k1_check);
symbol Displayed_chain_alpha_check
  : τ (Hom
      (Fibre_cat
        Displayed_chain_A_check
        Displayed_chain_k1_check)
      (@fapp0
        (Fibre_cat
          Displayed_chain_A_check
          Displayed_chain_k0_check)
        (Fibre_cat
          Displayed_chain_A_check
          Displayed_chain_k1_check)
        (@catd_transport_func
          Displayed_chain_K_check
          Displayed_chain_A_check
          Displayed_chain_k0_check
          Displayed_chain_k1_check
          Displayed_chain_p_check)
        Displayed_chain_a0_check)
      Displayed_chain_a1_check);
symbol Displayed_chain_q_check
  : τ (Hom
      (@Sigma_cat
        Displayed_chain_K_check
        Displayed_chain_A_check)
      (Struct_sigma
        Displayed_chain_k0_check
        Displayed_chain_a0_check)
      (Struct_sigma
        Displayed_chain_k1_check
        Displayed_chain_a1_check))
≔ @sigma_arrow
    Displayed_chain_K_check
    Displayed_chain_A_check
    Displayed_chain_k0_check
    Displayed_chain_k1_check
    Displayed_chain_a0_check
    Displayed_chain_a1_check
    Displayed_chain_p_check
    Displayed_chain_alpha_check;

// The total projection and its pulled-back family preserve the base arrow.
assert ⊢
  @fapp1_fapp0
    (@Sigma_cat
      Displayed_chain_K_check
      Displayed_chain_A_check)
    Displayed_chain_K_check
    (@Sigma_proj1_func
      Displayed_chain_K_check
      Displayed_chain_A_check)
    (Struct_sigma
      Displayed_chain_k0_check
      Displayed_chain_a0_check)
    (Struct_sigma
      Displayed_chain_k1_check
      Displayed_chain_a1_check)
    Displayed_chain_q_check
  ≡ Displayed_chain_p_check;

assert ⊢
  @fapp1_fapp0
    (@Sigma_cat
      Displayed_chain_K_check
      Displayed_chain_A_check)
    Cat_cat
    (@Sigma_proj1_pullback_catd
      Displayed_chain_K_check
      Displayed_chain_A_check
      Displayed_chain_D_check)
    (Struct_sigma
      Displayed_chain_k0_check
      Displayed_chain_a0_check)
    (Struct_sigma
      Displayed_chain_k1_check
      Displayed_chain_a1_check)
    Displayed_chain_q_check
  ≡ @fapp1_fapp0
      Displayed_chain_K_check
      Cat_cat
      Displayed_chain_D_check
      Displayed_chain_k0_check
      Displayed_chain_k1_check
      Displayed_chain_p_check;

// The bridge's structured-arrow component delegates to the already
// internalized displayed hom action, retaining the fibre arrow alpha.
assert ⊢
  @fdapp1_int_cell
    (@Sigma_cat
      Displayed_chain_K_check
      Displayed_chain_A_check)
    (@Const_catd
      (@Sigma_cat
        Displayed_chain_K_check
        Displayed_chain_A_check)
      Terminal_cat)
    (@Sigma_proj1_pullback_catd
      Displayed_chain_K_check
      Displayed_chain_A_check
      Displayed_chain_A_check)
    (@sigma_functord_sec
      Displayed_chain_K_check
      Displayed_chain_A_check
      Displayed_chain_A_check
      (@id_funcd
        Displayed_chain_K_check
        Displayed_chain_A_check))
    (Struct_sigma
      Displayed_chain_k0_check
      Displayed_chain_a0_check)
    (Struct_sigma
      Displayed_chain_k1_check
      Displayed_chain_a1_check)
    (Struct_sigma
      Displayed_chain_p_check
      Displayed_chain_alpha_check)
    Terminal_obj
  ≡ @fdapp1_int_hom_fapp0
      Displayed_chain_K_check
      Displayed_chain_A_check
      Displayed_chain_A_check
      (@id_funcd
        Displayed_chain_K_check
        Displayed_chain_A_check)
      Displayed_chain_k0_check
      Displayed_chain_k1_check
      Displayed_chain_p_check
      Displayed_chain_a0_check
      Displayed_chain_a1_check
      Displayed_chain_alpha_check;

symbol Displayed_chain_b0_check
  : τ (Obj
      (Fibre_cat
        Displayed_chain_B_check
        (Struct_sigma
          Displayed_chain_k0_check
          Displayed_chain_a0_check)));

// Weakening the outer variable preserves that same internalized action and
// is independent of the object in the new source fibre.
assert ⊢
  @fdapp1_int_cell
    (@Sigma_cat
      Displayed_chain_K_check
      Displayed_chain_A_check)
    Displayed_chain_B_check
    (@Sigma_proj1_pullback_catd
      Displayed_chain_K_check
      Displayed_chain_A_check
      Displayed_chain_A_check)
    (@section_pullback_sec
      (@Sigma_cat
        (@Sigma_cat
          Displayed_chain_K_check
          Displayed_chain_A_check)
        Displayed_chain_B_check)
      (@Sigma_cat
        Displayed_chain_K_check
        Displayed_chain_A_check)
      (@Sigma_proj1_func
        (@Sigma_cat
          Displayed_chain_K_check
          Displayed_chain_A_check)
        Displayed_chain_B_check)
      (@Sigma_proj1_pullback_catd
        Displayed_chain_K_check
        Displayed_chain_A_check
        Displayed_chain_A_check)
      (@sigma_functord_sec
        Displayed_chain_K_check
        Displayed_chain_A_check
        Displayed_chain_A_check
        (@id_funcd
          Displayed_chain_K_check
          Displayed_chain_A_check)))
    (Struct_sigma
      Displayed_chain_k0_check
      Displayed_chain_a0_check)
    (Struct_sigma
      Displayed_chain_k1_check
      Displayed_chain_a1_check)
    (Struct_sigma
      Displayed_chain_p_check
      Displayed_chain_alpha_check)
    Displayed_chain_b0_check
  ≡ @fdapp1_int_hom_fapp0
      Displayed_chain_K_check
      Displayed_chain_A_check
      Displayed_chain_A_check
      (@id_funcd
        Displayed_chain_K_check
        Displayed_chain_A_check)
      Displayed_chain_k0_check
      Displayed_chain_k1_check
      Displayed_chain_p_check
      Displayed_chain_a0_check
      Displayed_chain_a1_check
      Displayed_chain_alpha_check;

// A generic section of the same classifier does not become the explicit
// displayed-functor bridge.
symbol Displayed_chain_generic_section_check
  : τ (Obj
      (@Pi_cat
        (@Sigma_cat
          Displayed_chain_K_check
          Displayed_chain_A_check)
        (@Sigma_proj1_pullback_catd
          Displayed_chain_K_check
          Displayed_chain_A_check
          Displayed_chain_D_check)));

assertnot ⊢
  Displayed_chain_generic_section_check
  ≡ @sigma_functord_sec
      Displayed_chain_K_check
      Displayed_chain_A_check
      Displayed_chain_D_check
      Displayed_chain_FF_check;

// catalog-area: auto
assert [A B : Cat] (F : τ (Functor A B)) (x : τ (Obj A)) ⊢
  fapp0 (@Eval_func A B) (Struct_sigma F x)
    ≡ fapp0 F x;

assert [A B : Cat]
  (F G : τ (Functor A B))
  (x y : τ (Obj A)) ⊢
  @fapp1_func
    (Product_cat (Functor_cat A B) A)
    B
    (@Eval_func A B)
    (Struct_sigma F x)
    (Struct_sigma G y)
  ≡ @Eval_fapp1_func A B F G x y;

assert [A B : Cat]
  (F G : τ (Functor A B))
  (x y : τ (Obj A))
  (eta : τ (Transf F G))
  (p : τ (Hom A x y)) ⊢
  @fapp1_fapp0
    (Product_cat (Functor_cat A B) A)
    B
    (@Eval_func A B)
    (Struct_sigma F x)
    (Struct_sigma G y)
    (Struct_sigma eta p)
  ≡ @tapp1_fapp0 A B F G x y eta p;

assert [A B : Cat] (x : τ (Obj A)) (F : τ (Functor A B)) ⊢
  fapp0 (fapp0_func x) F
    ≡ fapp0 F x;

assert [A B : Cat] (x : τ (Obj A)) (F G : τ (Functor A B)) ⊢
  @fapp1_func
    (Functor_cat A B)
    B
    (@fapp0_func A B x)
    F
    G
  ≡ @tapp0_func A B F G x;

assert [A B : Cat] (x : τ (Obj A)) (F G : τ (Functor A B))
  (eta : τ (Transf F G)) ⊢
  @fapp1_fapp0
    (Functor_cat A B)
    B
    (@fapp0_func A B x)
    F
    G
    eta
  ≡ @tapp0_fapp0 A B F G x eta;

assert [A B : Cat] (x : τ (Obj A)) ⊢
  @comp_cat_fapp0
    (Functor_cat A B)
    (Product_cat (Functor_cat A B) A)
    B
    (@Eval_func A B)
    (@Eval_at_func A B x)
  ≡ @fapp0_func A B x;

assert [A B C : Cat]
  (G : τ (Functor A (Functor_cat B C)))
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  fapp0 (uncurry_func G) (Struct_sigma x y)
    ≡ @fapp0
        (Product_cat A B)
        C
        (@hom_postcomp_fapp0
          Cat_cat
          Cat_cat
          (@id Cat_cat Cat_cat)
          (Product_cat A B)
          (Product_cat (Functor_cat B C) B)
          C
          (@Eval_func B C)
          (@Product_cat_fapp1_tapp0_func A (Functor_cat B C) B G))
        (Struct_sigma x y);

assert [A B C : Cat]
  (G : τ (Functor A (Functor_cat B C)))
  (x x' : τ (Obj A))
  (y y' : τ (Obj B))
  (p : τ (Hom A x x'))
  (q : τ (Hom B y y')) ⊢
  @fapp1_fapp0
    (Product_cat A B)
    C
    (@uncurry_func A B C G)
    (Struct_sigma x y)
    (Struct_sigma x' y')
    (Struct_sigma p q)
    ≡ @fapp1_fapp0
      (Product_cat A B)
      C
      (@hom_postcomp_fapp0
        Cat_cat
        Cat_cat
        (@id Cat_cat Cat_cat)
        (Product_cat A B)
        (Product_cat (Functor_cat B C) B)
        C
        (@Eval_func B C)
        (@Product_cat_fapp1_tapp0_func A (Functor_cat B C) B G))
      (Struct_sigma x y)
      (Struct_sigma x' y')
      (Struct_sigma p q);

assert [A B C : Cat]
  (F : τ (Functor (Product_cat A B) C)) ⊢
  fapp0 curry_func_func F
    ≡ curry_func F;

assert [A B C : Cat]
  (G : τ (Functor A (Functor_cat B C))) ⊢
  fapp0 uncurry_func_func G
    ≡ uncurry_func G;

// Indexed adjunction triangles, opposite, and operation-trust boundary.
// catalog-area: Indexed adjunction triangles, opposite, and operation trust
assert [R L : Cat]
  [F : τ (Functor R L)]
  [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G)) ⊢
  @left_adj_func R L F G J
  ≡ F;

assert [R L : Cat]
  [F : τ (Functor R L)]
  [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G)) ⊢
  @right_adj_func R L F G J
  ≡ G;

assert [R L : Cat]
  [F : τ (Functor R L)]
  [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G))
  (X X' : τ (Obj R))
  (Y : τ (Obj L))
  (g : τ (Hom R X X'))
  (f : τ (Hom L (@fapp0 R L F X') Y)) ⊢
  comp_fapp0
    (@tapp1_fapp0
      L
      L
      (@comp_cat_fapp0
        L
        R
        L
        F
        G)
      (@id_func L)
      (@fapp0 R L F X')
      Y
      (@counit_adj_transf R L F G J)
      f)
    (@fapp1_fapp0
      R
      L
      F
      X
      (@fapp0 L R G
        (@fapp0 R L F X'))
      (@tapp1_fapp0
        R
        R
        (@id_func R)
        (@comp_cat_fapp0
          R
          L
          R
          G
          F)
        X
        X'
        (@unit_adj_transf R L F G J)
        g))
  ≡ comp_fapp0
      f
      (@fapp1_fapp0 R L F X X' g);

assert [R L : Cat]
  [F : τ (Functor R L)]
  [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G))
  (X : τ (Obj R))
  (Y' Y : τ (Obj L))
  (f : τ (Hom R X (@fapp0 L R G Y')))
  (g : τ (Hom L Y' Y)) ⊢
  comp_fapp0
    (@fapp1_fapp0
      L
      R
      G
      (@fapp0 R L F
        (@fapp0 L R G Y'))
      Y
      (@tapp1_fapp0
        L
        L
        (@comp_cat_fapp0
          L
          R
          L
          F
          G)
        (@id_func L)
        Y'
        Y
        (@counit_adj_transf R L F G J)
        g))
    (@tapp1_fapp0
      R
      R
      (@id_func R)
      (@comp_cat_fapp0
        R
        L
        R
        G
        F)
      X
      (@fapp0 L R G Y')
      (@unit_adj_transf R L F G J)
      f)
  ≡ comp_fapp0
      (@fapp1_fapp0 L R G Y' Y g)
      f;

// Independently named operations have no declaration-backed comparison with
// the stable observations and therefore do not compute or unify with them.
assertnot [R L : Cat]
  [F : τ (Functor R L)]
  [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G))
  (eta : τ (Transf
      (@id_func R)
      (@comp_cat_fapp0 R L R G F))) ⊢
  @unit_adj_transf R L F G J
  ≡ eta;

assertnot [R L : Cat]
  [F : τ (Functor R L)]
  [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G))
  (epsilon : τ (Transf
      (@comp_cat_fapp0 L R L F G)
      (@id_func L))) ⊢
  @counit_adj_transf R L F G J
  ≡ epsilon;

// A raw eta/epsilon spelling intentionally lacks the stable observation
// heads that select triangle cut-elimination.
assertnot [R L : Cat]
  [F : τ (Functor R L)]
  [G : τ (Functor L R)]
  (eta : τ (Transf
      (@id_func R)
      (@comp_cat_fapp0 R L R G F)))
  (epsilon : τ (Transf
      (@comp_cat_fapp0 L R L F G)
      (@id_func L)))
  (X X' : τ (Obj R))
  (Y : τ (Obj L))
  (g : τ (Hom R X X'))
  (f : τ (Hom L (@fapp0 R L F X') Y)) ⊢
  comp_fapp0
    (@tapp1_fapp0
      L L
      (@comp_cat_fapp0 L R L F G)
      (@id_func L)
      (@fapp0 R L F X')
      Y
      epsilon
      f)
    (@fapp1_fapp0
      R L F
      X
      (@fapp0 L R G (@fapp0 R L F X'))
      (@tapp1_fapp0
        R R
        (@id_func R)
        (@comp_cat_fapp0 R L R G F)
        X X'
        eta
        g))
  ≡ comp_fapp0 f (@fapp1_fapp0 R L F X X' g);

assert [A B : Cat]
  [F G : τ (Functor A B)]
  (eta : τ (Transf F G)) ⊢
  @Op_transf A B F G eta
  : τ (Transf (@Op_func A B G) (@Op_func A B F));

assert [A B : Cat]
  [F G : τ (Functor A B)]
  (eta : τ (Transf F G)) ⊢
  @Op_transf
    (Op_cat A) (Op_cat B)
    (@Op_func A B G)
    (@Op_func A B F)
    (@Op_transf A B F G eta)
  ≡ eta;

assert [A B : Cat]
  (F : τ (Functor A B)) ⊢
  @Op_transf
    A B F F
    (@id (Functor_cat A B) F)
  ≡ @id
      (Functor_cat (Op_cat A) (Op_cat B))
      (@Op_func A B F);

assert [A B : Cat]
  [F : τ (Functor A B)]
  [G : τ (Functor B A)]
  (adj : τ (@Adjunction A B F G)) ⊢
  @left_adj_func
    (Op_cat B) (Op_cat A)
    (@Op_func B A G)
    (@Op_func A B F)
    (@Op_adjunction A B F G adj)
  ≡ @Op_func B A G;

assert [A B : Cat]
  [F : τ (Functor A B)]
  [G : τ (Functor B A)]
  (adj : τ (@Adjunction A B F G)) ⊢
  @right_adj_func
    (Op_cat B) (Op_cat A)
    (@Op_func B A G)
    (@Op_func A B F)
    (@Op_adjunction A B F G adj)
  ≡ @Op_func A B F;

assert [A B : Cat]
  [F : τ (Functor A B)]
  [G : τ (Functor B A)]
  (adj : τ (@Adjunction A B F G)) ⊢
  @unit_adj_transf
    (Op_cat B) (Op_cat A)
    (@Op_func B A G)
    (@Op_func A B F)
    (@Op_adjunction A B F G adj)
  ≡ @Op_transf
      B B
      (@comp_cat_fapp0
        B A B
        F
        G)
      (@id_func B)
      (@counit_adj_transf A B F G adj);

assert [A B : Cat]
  [F : τ (Functor A B)]
  [G : τ (Functor B A)]
  (adj : τ (@Adjunction A B F G)) ⊢
  @counit_adj_transf
    (Op_cat B) (Op_cat A)
    (@Op_func B A G)
    (@Op_func A B F)
    (@Op_adjunction A B F G adj)
  ≡ @Op_transf
      A A
      (@id_func A)
      (@comp_cat_fapp0
        A B A
        G
        F)
      (@unit_adj_transf A B F G adj);

assert [A B : Cat]
  [F : τ (Functor A B)]
  [G : τ (Functor B A)]
  (adj : τ (@Adjunction A B F G)) ⊢
  @Op_adjunction
    (Op_cat B)
    (Op_cat A)
    (@Op_func B A G)
    (@Op_func A B F)
    (@Op_adjunction A B F G adj)
  ≡ adj;

// catalog-area: auto

assert [A B : Cat]
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  @fapp0
    (Product_cat A B)
    (Product_cat B A)
    (@Product_swap_func A B)
    (Struct_sigma x y)
  ≡ @Struct_sigma
      (Obj B)
      (λ _ : τ (Obj B), Obj A)
      y x;

assert [A B : Cat] ⊢
  @comp_cat_fapp0
    (Product_cat A B)
    (Product_cat B A)
    (Product_cat A B)
    (@Product_swap_func B A)
    (@Product_swap_func A B)
  ≡ @id_func (Product_cat A B);

assert [A B : Cat] ⊢
  @Op_func
    (Product_cat A B)
    (Product_cat B A)
    (@Product_swap_func A B)
  ≡ @Product_swap_func (Op_cat A) (Op_cat B);

assert [A B : Cat]
  (R : τ (Prof A B))
  (a : τ (Obj A))
  (b : τ (Obj B)) ⊢
  @fapp0
    (Product_cat B (Op_cat A))
    Cat_cat
    (@Op_prof A B R)
    (Struct_sigma b a)
  ≡ @fapp0
      (Product_cat (Op_cat A) B)
      Cat_cat
      R
      (Struct_sigma a b);

assert [A B X : Cat]
  (F : τ (Functor A X))
  (G : τ (Functor B X))
  (a : τ (Obj A))
  (b : τ (Obj B)) ⊢
  @fapp0
    (Product_cat B (Op_cat A))
    Cat_cat
    (@Op_prof A B (@Hom_prof_along A B X F G))
    (Struct_sigma b a)
  ≡ @Hom_cat
      X
      (@fapp0 A X F a)
      (@fapp0 B X G b);

assert [A B : Cat]
  (R : τ (Prof A B)) ⊢
  @fapp0
    (@Prof_cat A B)
    (@Prof_cat (Op_cat B) (Op_cat A))
    (@Op_prof_func A B)
    R
  ≡ @Op_prof A B R;

assert [A B : Cat]
  (R : τ (Prof A B)) ⊢
  @Op_prof (Op_cat B) (Op_cat A) (@Op_prof A B R)
  ≡ R;

assert [A B : Cat]
  (R : τ (Prof A B))
  (a a' : τ (Obj A))
  (b b' : τ (Obj B))
  (p : τ (Hom A a' a))
  (q : τ (Hom B b b')) ⊢
  @fapp1_fapp0
    (Product_cat B (Op_cat A))
    Cat_cat
    (@Op_prof A B R)
    (Struct_sigma b a)
    (Struct_sigma b' a')
    (Struct_sigma q p)
  ≡ @fapp1_fapp0
      (Product_cat (Op_cat A) B)
      Cat_cat
      R
      (Struct_sigma a b)
      (Struct_sigma a' b')
      (Struct_sigma p q);

assert [A B : Cat]
  (R : τ (Prof A B)) ⊢
  eq_refl (@Op_prof A B R)
  : τ (
      @Op_prof A B R
      =
      @Pullback_catd
        (Product_cat B (Op_cat A))
        (Product_cat (Op_cat A) B)
        R
        (@Product_swap_func B (Op_cat A)));

assert [A B : Cat] ⊢
  eq_refl (@Op_prof_func A B)
  : τ (
      @Op_prof_func A B
      =
      @Pullback_catd_func
        (Product_cat B (Op_cat A))
        (Product_cat (Op_cat A) B)
        (@Product_swap_func B (Op_cat A)));

assert [A B : Cat]
  [P Q : τ (Prof A B)]
  (r : τ (ProfMap P Q)) ⊢
  @Op_prof_map A B P Q r
  : τ (@ProfMap
      (Op_cat B)
      (Op_cat A)
      (@Op_prof A B P)
      (@Op_prof A B Q));

assert [A A' B B' : Cat]
  [R : τ (Prof A B)]
  [F : τ (Functor A' A)]
  [G : τ (Functor B' B)] ⊢
  @Prof_reindex
    (Op_cat B)
    (Op_cat B')
    (Op_cat A)
    (Op_cat A')
    (@Op_prof A B R)
    (@Op_func B' B G)
    (@Op_func A' A F)
  ≡ @Op_prof
      A' B'
      (@Prof_reindex A A' B B' R F G);

assert [A B : Cat] (F : τ (Functor A B)) (X : τ (Obj A)) ⊢
  @tapp0_fapp0
      (Op_cat A)
      (@Catd_cat A)
      (@hom_int A A (@id_func A))
      (@comp_cat_fapp0
        (Op_cat A)
        (Op_cat B)
        (@Catd_cat A)
        (@hom_int B A F)
        (@Op_func A B F))
      X
      (@fapp1_int_transf A B F)
    ≡ @fapp1_at_transf A B F X;

assert [A B : Cat] (F : τ (Functor A B)) (X : τ (Obj A)) ⊢
  @tapp1_at_transf A B F F X (id (Functor_cat A B) F)
    ≡ @fapp1_at_transf A B F X;

assert [A B : Cat] (F : τ (Functor A B)) (X Y : τ (Obj A)) ⊢
  @tapp0_fapp0
      A
      Cat_cat
      (@hom_ A A (@id_func A) X)
      (@hom_ B A F (@fapp0 A B F X))
      Y
      (@fapp1_at_transf A B F X)
    ≡ @fapp1_func A B F X Y;

assert [A B : Cat] (F : τ (Functor A B)) (X Y : τ (Obj A)) ⊢
  @tapp0_fapp0
      A
      Cat_cat
      _
      _
      Y
      (@tapp0_fapp0
        (Op_cat A)
        (@Catd_cat A)
        _
        _
        X
        (@fapp1_int_transf A B F))
    ≡ @fapp1_func A B F X Y;

assert [A B : Cat] (F : τ (Functor A B))
  (X Y : τ (Obj A)) (f : τ (Hom A X Y)) ⊢
  fapp0 (@fapp1_func A B F X Y) f
    ≡ @fapp1_fapp0 A B F X Y f;

assert [A B : Cat] (F G : τ (Functor A B))
  (ϵ : τ (Transf F G)) (X : τ (Obj A)) ⊢
  @tapp0_fapp0
      (Op_cat A)
      (@Catd_cat A)
      (@hom_int A A (@id_func A))
      (@comp_cat_fapp0
        (Op_cat A)
        (Op_cat B)
        (@Catd_cat A)
        (@hom_int B A G)
        (@Op_func A B F))
      X
      (@tapp1_int_fapp0_transf A B F G ϵ)
    ≡ @tapp1_at_transf A B F G X ϵ;

assert [A B : Cat] (F G : τ (Functor A B))
  (ϵ : τ (Transf F G)) (X Y : τ (Obj A)) ⊢
  @tapp0_fapp0
      A
      Cat_cat
      (@hom_ A A (@id_func A) X)
      (@hom_ B A G (@fapp0 A B F X))
      Y
      (@tapp1_at_transf A B F G X ϵ)
    ≡ @tapp1_func A B F G X Y ϵ;

assert [A B : Cat] (F G : τ (Functor A B))
  (ϵ : τ (Transf F G)) (X Y : τ (Obj A)) ⊢
  @tapp0_fapp0
      A
      Cat_cat
      _
      _
      Y
      (@tapp0_fapp0
        (Op_cat A)
        (@Catd_cat A)
        _
        _
        X
        (@tapp1_int_fapp0_transf A B F G ϵ))
    ≡ @tapp1_func A B F G X Y ϵ;

assert [A B : Cat] (F G : τ (Functor A B)) (ϵ : τ (Transf F G)) ⊢
  fapp0 (@tapp1_int_func_transf A B F G) ϵ
    ≡ @tapp1_int_fapp0_transf A B F G ϵ;

assert [A B : Cat] (F G : τ (Functor A B))
  (ϵ ϵ' : τ (Transf F G)) ⊢
  @fapp1_func _ _ (@tapp1_int_func_transf A B F G) ϵ ϵ'
    ≡ @tapp1_int_fapp1_func_transf A B F G ϵ ϵ';

assert [A B : Cat] (F G : τ (Functor A B))
  (X Y Z : τ (Obj A))
  (f : τ (Hom A X Y))
  (g : τ (Hom A Y Z))
  (ϵ : τ (Transf F G)) ⊢
  @comp_fapp0
    B
    (@fapp0 A B F X)
    (@fapp0 A B G Y)
    (@fapp0 A B G Z)
    (@fapp1_fapp0 A B G Y Z g)
    (@tapp1_fapp0 A B F G X Y ϵ f)
    ≡ @tapp1_fapp0 A B F G X Z ϵ
        (@comp_fapp0 A X Y Z g f);

assert [A B : Cat] (F G : τ (Functor A B))
  (X0 X Y : τ (Obj A))
  (g : τ (Hom A X0 X))
  (f : τ (Hom A X Y))
  (ϵ : τ (Transf F G)) ⊢
  @comp_fapp0
    B
    (@fapp0 A B F X0)
    (@fapp0 A B F X)
    (@fapp0 A B G Y)
    (@tapp1_fapp0 A B F G X Y ϵ f)
    (@fapp1_fapp0 A B F X0 X g)
    ≡ @tapp1_fapp0 A B F G X0 Y ϵ
        (@comp_fapp0 A X0 X Y f g);

// Full strict naturality: post/left accumulation before capping.
assert [A B : Cat] (F G : τ (Functor A B)) (X Y Z : τ (Obj A))
  (g : τ (Hom A Y Z)) (ϵ : τ (Transf F G)) ⊢
  @comp_cat_fapp0
    (Hom_cat A X Y)
    (Hom_cat B (@fapp0 A B F X) (@fapp0 A B G Y))
    (Hom_cat B (@fapp0 A B F X) (@fapp0 A B G Z))
    (@hom_postcomp_func B A G (@fapp0 A B F X) Y Z g)
    (@tapp1_func A B F G X Y ϵ)
  ≡ @comp_cat_fapp0
    (Hom_cat A X Y)
    (Hom_cat A X Z)
    (Hom_cat B (@fapp0 A B F X) (@fapp0 A B G Z))
    (@tapp1_func A B F G X Z ϵ)
    (@hom_postcomp_func A A (@id_func A) X Y Z g);

assert [A B : Cat] (F G : τ (Functor A B)) (X Y Z : τ (Obj A))
  (f : τ (Hom A X Y)) (g : τ (Hom A Y Z)) (ϵ : τ (Transf F G)) ⊢
  fapp0
    (@comp_cat_fapp0
      (Hom_cat A X Y)
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B G Y))
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B G Z))
      (@hom_postcomp_func B A G (@fapp0 A B F X) Y Z g)
      (@tapp1_func A B F G X Y ϵ))
    f
  ≡ @tapp1_fapp0 A B F G X Z ϵ
      (@hom_postcomp_fapp0 A A (@id_func A) X Y Z g f);

// Full strict naturality: pre/right accumulation before capping.
assert [A B : Cat] (F G : τ (Functor A B)) (W X Y : τ (Obj A))
  (h : τ (Hom A W X)) (ϵ : τ (Transf F G)) ⊢
  @comp_cat_fapp0
    (Hom_cat A X Y)
    (Hom_cat B (@fapp0 A B F X) (@fapp0 A B G Y))
    (Hom_cat B (@fapp0 A B F W) (@fapp0 A B G Y))
    (@hom_precomp_along_func A B F (@fapp0 A B G Y) W X h)
    (@tapp1_func A B F G X Y ϵ)
  ≡ @comp_cat_fapp0
    (Hom_cat A X Y)
    (Hom_cat A W Y)
    (Hom_cat B (@fapp0 A B F W) (@fapp0 A B G Y))
    (@tapp1_func A B F G W Y ϵ)
    (@hom_precomp_along_func A A (@id_func A) Y W X h);

assert [A B : Cat] (F G : τ (Functor A B)) (W X Y : τ (Obj A))
  (h : τ (Hom A W X)) (f : τ (Hom A X Y)) (ϵ : τ (Transf F G)) ⊢
  fapp0
    (@comp_cat_fapp0
      (Hom_cat A X Y)
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B G Y))
      (Hom_cat B (@fapp0 A B F W) (@fapp0 A B G Y))
      (@hom_precomp_along_func A B F (@fapp0 A B G Y) W X h)
      (@tapp1_func A B F G X Y ϵ))
    f
  ≡ @tapp1_fapp0 A B F G W Y ϵ
      (@hom_precomp_along_fapp0 A A (@id_func A) Y W X h f);

// Full strict functoriality: post/left accumulation for a single functor.
assert [A B : Cat] (F : τ (Functor A B)) (X Y Z : τ (Obj A))
  (g : τ (Hom A Y Z)) ⊢
  @comp_cat_fapp0
    (Hom_cat A X Y)
    (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Y))
    (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
    (@hom_postcomp_func B A F (@fapp0 A B F X) Y Z g)
    (@fapp1_func A B F X Y)
  ≡ @comp_cat_fapp0
    (Hom_cat A X Y)
    (Hom_cat A X Z)
    (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
    (@fapp1_func A B F X Z)
    (@hom_postcomp_func A A (@id_func A) X Y Z g);

assert [A B : Cat] (F : τ (Functor A B)) (X Y Z : τ (Obj A))
  (f : τ (Hom A X Y)) (g : τ (Hom A Y Z)) ⊢
  fapp0
    (@comp_cat_fapp0
      (Hom_cat A X Y)
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Y))
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
      (@hom_postcomp_func B A F (@fapp0 A B F X) Y Z g)
      (@fapp1_func A B F X Y))
    f
  ≡ @fapp1_fapp0 A B F X Z
      (@hom_postcomp_fapp0 A A (@id_func A) X Y Z g f);

// Full strict functoriality: pre/right accumulation for a single functor.
assert [A B : Cat] (F : τ (Functor A B)) (W X Y : τ (Obj A))
  (h : τ (Hom A W X)) ⊢
  @comp_cat_fapp0
    (Hom_cat A X Y)
    (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Y))
    (Hom_cat B (@fapp0 A B F W) (@fapp0 A B F Y))
    (@hom_precomp_along_func A B F (@fapp0 A B F Y) W X h)
    (@fapp1_func A B F X Y)
  ≡ @comp_cat_fapp0
    (Hom_cat A X Y)
    (Hom_cat A W Y)
    (Hom_cat B (@fapp0 A B F W) (@fapp0 A B F Y))
    (@fapp1_func A B F W Y)
    (@hom_precomp_along_func A A (@id_func A) Y W X h);

assert [A B : Cat] (F : τ (Functor A B)) (W X Y : τ (Obj A))
  (h : τ (Hom A W X)) (f : τ (Hom A X Y)) ⊢
  fapp0
    (@comp_cat_fapp0
      (Hom_cat A X Y)
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Y))
      (Hom_cat B (@fapp0 A B F W) (@fapp0 A B F Y))
      (@hom_precomp_along_func A B F (@fapp0 A B F Y) W X h)
      (@fapp1_func A B F X Y))
    f
  ≡ @fapp1_fapp0 A B F W Y
      (@hom_precomp_along_fapp0 A A (@id_func A) Y W X h f);

// Raw adjacent hom-action folds. These are diagnostic conversion checks for
// runtime accumulation rules kept in `emdash3_2.lp`, not reviewer-facing
// mathematical lemmas.
assert [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A))
  [X Y Z : τ (Obj B)]
  (p : τ (Hom B X Y)) (q : τ (Hom B Y Z))
  (g : τ (Hom A W (@fapp0 B A F X))) ⊢
  @comp_fapp0
    A
    W
    (@fapp0 B A F Y)
    (@fapp0 B A F Z)
    (@fapp1_fapp0 B A F Y Z q)
    (@hom_postcomp_fapp0 A B F W X Y p g)
  ≡ @hom_postcomp_fapp0
      A B F W X Z
      (@comp_fapp0 B X Y Z q p)
      g;

assert [A B : Cat] (F : τ (Functor A B)) (Z : τ (Obj B))
  [V W X : τ (Obj A)]
  (q : τ (Hom A V W)) (p : τ (Hom A W X))
  (g : τ (Hom B (@fapp0 A B F X) Z)) ⊢
  @comp_fapp0
    B
    (@fapp0 A B F V)
    (@fapp0 A B F W)
    Z
    (@hom_precomp_along_fapp0 A B F Z W X p g)
    (@fapp1_fapp0 A B F V W q)
  ≡ @hom_precomp_along_fapp0
      A B F Z V X
      (@comp_fapp0 A V W X p q)
      g;

// Pre-configured four-cell interchange for the Cat-valued representable
// `hom_` (postcomposition). This is the generalized form needed before the
// Eckmann-Hilton specialization:
//   ((e_gh)_*[beta]) · ((e_fg)_*[alpha])
//     -> (e_gh · e_fg)_*[beta · alpha].
assert [B : Cat] [M N L : τ (Obj B)]
  [f g h : τ (Hom B N L)]
  (e_fg : τ (Hom (Hom_cat B N L) f g))
  (e_gh : τ (Hom (Hom_cat B N L) g h))
  [X Y Z : τ (Hom B M N)]
  (alpha : τ (Hom (Hom_cat B M N) X Y))
  (beta : τ (Hom (Hom_cat B M N) Y Z)) ⊢
  @comp_fapp0
    (Hom_cat B M L)
    (@hom_postcomp_fapp0 B B (@id_func B) M N L f X)
    (@hom_postcomp_fapp0 B B (@id_func B) M N L g Y)
    (@hom_postcomp_fapp0 B B (@id_func B) M N L h Z)
    (@tapp1_fapp0
      (Hom_cat B M N)
      (Hom_cat B M L)
      (@hom_postcomp_func B B (@id_func B) M N L g)
      (@hom_postcomp_func B B (@id_func B) M N L h)
      Y
      Z
      (@hom_postcomp_tele_fapp1_fapp0 B B (@id_func B) M N L g h e_gh)
      beta)
    (@tapp1_fapp0
      (Hom_cat B M N)
      (Hom_cat B M L)
      (@hom_postcomp_func B B (@id_func B) M N L f)
      (@hom_postcomp_func B B (@id_func B) M N L g)
      X
      Y
      (@hom_postcomp_tele_fapp1_fapp0 B B (@id_func B) M N L f g e_fg)
      alpha)
  ≡ @tapp1_fapp0
      (Hom_cat B M N)
      (Hom_cat B M L)
      (@hom_postcomp_func B B (@id_func B) M N L f)
      (@hom_postcomp_func B B (@id_func B) M N L h)
      X
      Z
      (@hom_postcomp_tele_fapp1_fapp0
        B B (@id_func B) M N L f h
        (@comp_fapp0 (Hom_cat B N L) f g h e_gh e_fg))
      (@comp_fapp0 (Hom_cat B M N) X Y Z beta alpha);

assert [A B : Cat] (F : τ (Functor A B)) ⊢
  @tapp1_int_fapp0_transf A B F F (id (Functor_cat A B) F)
    ≡ @fapp1_int_transf A B F;

assert [A B : Cat] (F : τ (Functor A B)) ⊢
  fapp0 (@tapp1_int_func_transf A B F F) (id (Functor_cat A B) F)
    ≡ @fapp1_int_transf A B F;

assert [Z : Cat] (x y z : τ (Obj Z)) (p : τ (Hom Z x y)) ⊢
  @tapp0_fapp0
    Z
    Cat_cat
    (@Rep_catd Z y)
    (@Rep_catd Z x)
    z
    (@fapp1_fapp0 (Op_cat Z) (@Catd_cat Z) (@Rep_catd_func Z) y x p)
    ≡ @hom_precomp_along_func Z Z (@id_func Z) z x y p;

assert [Z : Cat] (x : τ (Obj Z)) (E : τ (Catd (@PathOut_cat Z x))) ⊢
  Fibre_cat (@PathInd_src_catd Z x) E
    ≡ Fibre_cat E (@pathout_refl_obj Z x);

assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @PathInd_src_catd Z x
    ≡ @pathout_refl_eval_func Z x;

assert [Z : Cat] (x : τ (Obj Z)) (E : τ (Catd (@PathOut_cat Z x))) ⊢
  Fibre_cat (@PathInd_tgt_catd Z x) E
    ≡ Pi_cat E;

assert [Z : Cat] (x : τ (Obj Z))
  (E : τ (Catd (@PathOut_cat Z x)))
  (u : τ (Obj (Fibre_cat E (@pathout_refl_obj Z x)))) ⊢
  @fapp0
    (Fibre_cat E (@pathout_refl_obj Z x))
    (Pi_cat E)
    (@path_ind_func_fapp0 Z x E)
    u
    ≡ @path_ind_sec Z x E u;

assert [Z : Cat] (x : τ (Obj Z)) (E : τ (Catd (@PathOut_cat Z x))) ⊢
  @tapp0_fapp0
    (@Catd_cat (@PathOut_cat Z x))
    Cat_cat
    (@PathInd_src_catd Z x)
    (@PathInd_tgt_catd Z x)
    E
    (@PathInd_func Z x)
    ≡ @path_ind_func_fapp0 Z x E;

assert [Z : Cat] (E : τ (Catd Z)) (x : τ (Obj Z)) ⊢
  @fapp0 Z Cat_cat (@Homd_target_catd Z E) x
    ≡ Pi_cat (@Homd_target_section_catd Z E x);

assert [Z : Cat] (D : τ (Catd Z)) (x : τ (Obj Z))
  (u : τ (Obj (Fibre_cat D x))) ⊢
  @path_ind_sec
    Z
    x
    (@Sigma_proj1_pullback_catd Z (@Rep_catd Z x) D)
    u
    ≡ @fib_cov_transf Z D x u;

assert [Z : Cat] (x y : τ (Obj Z)) ⊢
  Fibre_cat (@CompTarget_catd Z x) y
    ≡ @Functord_cat Z (@Rep_catd Z y) (@Rep_catd Z x);

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y)) ⊢
  Fibre_cat (@CompMotive_catd Z x) (@pathout_obj Z x y p)
    ≡ @Functord_cat Z (@Rep_catd Z y) (@Rep_catd Z x);

assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @eq_refl Cat_grpd
    (@Pi_cat (@PathOut_cat Z x) (@CompMotive_catd Z x))
  : τ (@= Cat_grpd
      (@Pi_cat (@PathOut_cat Z x) (@CompMotive_catd Z x))
      (@Functord_cat Z (@Rep_catd Z x) (@CompTarget_catd Z x)));

assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @path_ind_sec
    Z
    x
    (@CompMotive_catd Z x)
    (@id_funcd Z (@Rep_catd Z x))
    ≡ @path_comp_sec Z x;

assert [Z : Cat] (x y : τ (Obj Z))
  (p : τ (Hom Z x y)) ⊢
  @fapp1_fapp0
    Z
    Cat_cat
    (@CompTarget_catd Z x)
    x
    y
    p
    ≡ @CompTarget_fapp1_func Z x x y p;

// Active transitivity-benchmark diagnostics.
//
// These assert the same mathematical strength as the original benchmark:
// fixed-x path induction computes to representable precomposition, and
// observing that result at q computes to categorical composition. The adapted
// final normal form is the stable precomposition owner
// `hom_precomp_along_fapp0(id,p,q)`, preserving the represented source
// variance while still computing the composite `q ∘ p`.

assert [Z : Cat] (x y : τ (Obj Z))
  (p : τ (Hom Z x y)) ⊢
  @fapp0
    (Hom_cat Z x y)
    (@Functord_cat Z (@Rep_catd Z y) (@Rep_catd Z x))
    (@tapp0_fapp0
      Z
      Cat_cat
      (@Rep_catd Z x)
      (@CompTarget_catd Z x)
      y
      (@path_comp_sec Z x))
    p
    ≡ @path_comp_func Z x y p;

assert [Z : Cat] (x y z : τ (Obj Z))
  (p : τ (Hom Z x y))
  (q : τ (Hom Z y z)) ⊢
  @fapp0
    (Hom_cat Z y z)
    (Hom_cat Z x z)
    (@tapp0_fapp0
      Z
      Cat_cat
      (@Rep_catd Z y)
      (@Rep_catd Z x)
      z
      (@path_comp_func Z x y p))
    q
    ≡ @hom_precomp_along_fapp0 Z Z (@id_func Z) z x y p q;

assert [Z : Cat] (x y z : τ (Obj Z))
  (p : τ (Hom Z x y))
  (q : τ (Hom Z y z)) ⊢
  @fapp0
    (Hom_cat Z y z)
    (Hom_cat Z x z)
    (@tapp0_fapp0
      Z
      Cat_cat
      (@Rep_catd Z y)
      (@Rep_catd Z x)
      z
      (@fapp0
        (Hom_cat Z x y)
        (@Functord_cat Z (@Rep_catd Z y) (@Rep_catd Z x))
        (@tapp0_fapp0
          Z
          Cat_cat
          (@Rep_catd Z x)
          (@CompTarget_catd Z x)
          y
          (@path_comp_sec Z x))
        p))
    q
    ≡ @hom_precomp_along_fapp0 Z Z (@id_func Z) z x y p q;

assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @tdapp0_fapp0
    Z
    (@PathOutMotives_catd Z)
    (@Const_catd Z Cat_cat)
    (@PathOutReflEval_funcd Z)
    (@PathOutPi_funcd Z)
    x
    (@PathInd_transfd Z)
    ≡ @PathInd_func Z x;

assert [Z : Cat] (x : τ (Obj Z)) (E : τ (Catd (@PathOut_cat Z x))) ⊢
  @tapp0_fapp0
    (@Catd_cat (@PathOut_cat Z x))
    Cat_cat
    (@PathInd_src_catd Z x)
    (@PathInd_tgt_catd Z x)
    E
    (@tdapp0_fapp0
      Z
      (@PathOutMotives_catd Z)
      (@Const_catd Z Cat_cat)
      (@PathOutReflEval_funcd Z)
      (@PathOutPi_funcd Z)
      x
      (@PathInd_transfd Z))
    ≡ @path_ind_func_fapp0 Z x E;

assert [Z : Cat] (x : τ (Obj Z))
  (E : τ (Catd (@PathOut_cat Z x)))
  (u : τ (Obj (Fibre_cat E (@pathout_refl_obj Z x)))) ⊢
  @fapp0
    (Fibre_cat E (@pathout_refl_obj Z x))
    (Pi_cat E)
    (@tapp0_fapp0
      (@Catd_cat (@PathOut_cat Z x))
      Cat_cat
      (@PathInd_src_catd Z x)
      (@PathInd_tgt_catd Z x)
      E
      (@tdapp0_fapp0
        Z
        (@PathOutMotives_catd Z)
        (@Const_catd Z Cat_cat)
        (@PathOutReflEval_funcd Z)
        (@PathOutPi_funcd Z)
        x
        (@PathInd_transfd Z)))
    u
    ≡ @path_ind_sec Z x E u;

assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @fapp0
    (Fibre_cat (@CompMotive_catd Z x) (@pathout_refl_obj Z x))
    (@Pi_cat (@PathOut_cat Z x) (@CompMotive_catd Z x))
    (@tapp0_fapp0
      (@Catd_cat (@PathOut_cat Z x))
      Cat_cat
      (@PathInd_src_catd Z x)
      (@PathInd_tgt_catd Z x)
      (@CompMotive_catd Z x)
      (@tdapp0_fapp0
        Z
        (@PathOutMotives_catd Z)
        (@Const_catd Z Cat_cat)
        (@PathOutReflEval_funcd Z)
        (@PathOutPi_funcd Z)
        x
        (@PathInd_transfd Z)))
    (@id_funcd Z (@Rep_catd Z x))
    ≡ @path_comp_sec Z x;

assert [Z : Cat] (x y z : τ (Obj Z))
  (p : τ (Hom Z x y))
  (q : τ (Hom Z y z)) ⊢
  @fapp0
    (Hom_cat Z y z)
    (Hom_cat Z x z)
    (@tapp0_fapp0
      Z
      Cat_cat
      (@Rep_catd Z y)
      (@Rep_catd Z x)
      z
      (@fapp0
        (Hom_cat Z x y)
        (@Functord_cat Z (@Rep_catd Z y) (@Rep_catd Z x))
        (@tapp0_fapp0
          Z
          Cat_cat
          (@Rep_catd Z x)
          (@CompTarget_catd Z x)
          y
          (@fapp0
            (Fibre_cat (@CompMotive_catd Z x) (@pathout_refl_obj Z x))
            (@Pi_cat (@PathOut_cat Z x) (@CompMotive_catd Z x))
            (@tapp0_fapp0
              (@Catd_cat (@PathOut_cat Z x))
              Cat_cat
              (@PathInd_src_catd Z x)
              (@PathInd_tgt_catd Z x)
              (@CompMotive_catd Z x)
              (@tdapp0_fapp0
                Z
                (@PathOutMotives_catd Z)
                (@Const_catd Z Cat_cat)
                (@PathOutReflEval_funcd Z)
                (@PathOutPi_funcd Z)
                x
                (@PathInd_transfd Z)))
            (@id_funcd Z (@Rep_catd Z x))))
        p))
    q
    ≡ @hom_precomp_along_fapp0 Z Z (@id_func Z) z x y p q;

assert [K : Cat] (R : τ (Catd K))
  (S T : τ (Functord R (@Const_catd K Cat_cat)))
  (eta : τ (Transfd S T))
  (k : τ (Obj K))
  (r : τ (Obj (Fibre_cat R k))) ⊢
  @tapp0_fapp0
    (@Sigma_cat K R)
    Cat_cat
    (@Sigma_catd_functord_catd K R S)
    (@Sigma_catd_functord_catd K R T)
    (Struct_sigma k r)
    (@Sigma_transfd_funcd K R S T eta)
    ≡ @tapp0_fapp0
        (Fibre_cat R k)
        Cat_cat
        (@Fibre_func K R (@Const_catd K Cat_cat) S k)
        (@Fibre_func K R (@Const_catd K Cat_cat) T k)
        r
        (@tdapp0_fapp0
          K
          R
          (@Const_catd K Cat_cat)
          S
          T
          k
          eta);

assert [Z : Cat] (x : τ (Obj Z)) (E : τ (Catd (@PathOut_cat Z x))) ⊢
  @tapp0_fapp0
    (@Sigma_cat Z (@PathOutMotives_catd Z))
    Cat_cat
    (@PathIndSrc_catd Z)
    (@PathIndTgt_catd Z)
    (Struct_sigma x E)
    (@PathInd_funcd Z)
    ≡ @path_ind_func_fapp0 Z x E;

assert [Z : Cat] (x : τ (Obj Z))
  (E : τ (Catd (@PathOut_cat Z x)))
  (u : τ (Obj (Fibre_cat E (@pathout_refl_obj Z x)))) ⊢
  @fapp0
    (Fibre_cat E (@pathout_refl_obj Z x))
    (Pi_cat E)
    (@tapp0_fapp0
      (@Sigma_cat Z (@PathOutMotives_catd Z))
      Cat_cat
      (@PathIndSrc_catd Z)
      (@PathIndTgt_catd Z)
      (Struct_sigma x E)
      (@PathInd_funcd Z))
    u
    ≡ @path_ind_sec Z x E u;

assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @fapp0
    (Fibre_cat (@CompMotive_catd Z x) (@pathout_refl_obj Z x))
    (@Pi_cat (@PathOut_cat Z x) (@CompMotive_catd Z x))
    (@tapp0_fapp0
      (@Sigma_cat Z (@PathOutMotives_catd Z))
      Cat_cat
      (@PathIndSrc_catd Z)
      (@PathIndTgt_catd Z)
      (Struct_sigma x (@CompMotive_catd Z x))
      (@PathInd_funcd Z))
    (@id_funcd Z (@Rep_catd Z x))
    ≡ @path_comp_sec Z x;

assert [Z : Cat] (x y z : τ (Obj Z))
  (p : τ (Hom Z x y))
  (q : τ (Hom Z y z)) ⊢
  @fapp0
    (Hom_cat Z y z)
    (Hom_cat Z x z)
    (@tapp0_fapp0
      Z
      Cat_cat
      (@Rep_catd Z y)
      (@Rep_catd Z x)
      z
      (@fapp0
        (Hom_cat Z x y)
        (@Functord_cat Z (@Rep_catd Z y) (@Rep_catd Z x))
        (@tapp0_fapp0
          Z
          Cat_cat
          (@Rep_catd Z x)
          (@CompTarget_catd Z x)
          y
          (@fapp0
            (Fibre_cat (@CompMotive_catd Z x) (@pathout_refl_obj Z x))
            (@Pi_cat (@PathOut_cat Z x) (@CompMotive_catd Z x))
            (@tapp0_fapp0
              (@Sigma_cat Z (@PathOutMotives_catd Z))
              Cat_cat
              (@PathIndSrc_catd Z)
              (@PathIndTgt_catd Z)
              (Struct_sigma x (@CompMotive_catd Z x))
              (@PathInd_funcd Z))
            (@id_funcd Z (@Rep_catd Z x))))
        p))
    q
    ≡ @hom_precomp_along_fapp0 Z Z (@id_func Z) z x y p q;

assert [K : Cat] (E D : τ (Catd K)) (FF GG : τ (Functord E D))
  (ϵ : τ (Transfd FF GG)) (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @Fibre_transf_app
    K
    (@Op_catd K E)
    (@Homd_target_catd K E)
    (@homd_int K E E (@id_funcd K E))
    (@comp_catd_fapp0
      K
      (@Op_catd K E)
      (@Op_catd K D)
      (@Homd_target_catd K E)
      (@homd_int K E D GG)
      (@Op_funcd K E D FF))
    (@tdapp1_int_fapp0_transfd K E D FF GG ϵ)
    x
    u
    ≡ @tdapp1_int_section_arrow K E D FF GG ϵ x u;

assert [K : Cat] (E D : τ (Catd K)) (FF GG : τ (Functord E D))
  (ϵ : τ (Transfd FF GG)) (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  tapp0_fapp0
    Terminal_obj
    (tdapp0_fapp0 y (@tdapp1_int_section_arrow K E D FF GG ϵ x u))
    ≡ @tdapp1_int_tgt_arrow K E D FF GG ϵ x u y;

assert [K : Cat] (E D : τ (Catd K)) (FF GG : τ (Functord E D))
  (ϵ : τ (Transfd FF GG)) (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y))) ⊢
  @tapp0_fapp0
    (Fibre_cat E y)
    (Functor_cat (Op_cat (Hom_cat K x y)) Cat_cat)
    (@homd_id_tgt_func K E x u y)
    (@homd_tdapp1_tgt_func K E D FF GG x u y)
    v
    (@tdapp1_int_tgt_arrow K E D FF GG ϵ x u y)
    ≡ @tdapp1_int_presheaf_arrow K E D FF GG ϵ x u y v;

assert [K : Cat] (E D : τ (Catd K)) (FF GG : τ (Functord E D))
  (ϵ : τ (Transfd FF GG)) (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y))) ⊢
  @fapp1_fapp0
    (Functor_cat (Op_cat (Hom_cat K x y)) Cat_cat)
    Cat_cat
    (@fapp0_func (Op_cat (Hom_cat K x y)) Cat_cat p)
    (fapp0 (@homd_id_tgt_func K E x u y) v)
    (fapp0 (@homd_tdapp1_tgt_func K E D FF GG x u y) v)
    (@tdapp1_int_presheaf_arrow K E D FF GG ϵ x u y v)
    ≡ @tdapp1_int_hom_func K E D FF GG ϵ x y p u v;

assert [K : Cat] (E D : τ (Catd K)) (FF GG : τ (Functord E D))
  (ϵ : τ (Transfd FF GG)) (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  fapp0
    (@tdapp1_int_hom_func K E D FF GG ϵ x y p u _)
    (@id
      (@fapp0 K Cat_cat E y)
      (fapp0 (@fapp1_fapp0 K Cat_cat E x y p) u))
    ≡ @tdapp1_int_cell K E D FF GG ϵ x y p u;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x : τ (Obj K)) (u : τ (Obj (Fibre_cat E x))) ⊢
  @tdapp1_int_section_arrow
      K E D FF FF (@id_transfd K E D FF) x u
    ≡ @fdapp1_int_section_arrow K E D FF x u;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K)) (u : τ (Obj (Fibre_cat E x))) ⊢
  @tdapp1_int_tgt_arrow
      K E D FF FF (@id_transfd K E D FF) x u y
    ≡ @fdapp1_int_tgt_arrow K E D FF x u y;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y))) ⊢
  @tdapp1_int_presheaf_arrow
      K E D FF FF (@id_transfd K E D FF) x u y v
    ≡ @fdapp1_int_presheaf_arrow K E D FF x u y v;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y))) ⊢
  @tdapp1_int_hom_func
      K E D FF FF (@id_transfd K E D FF) x y p u v
    ≡ @fdapp1_int_hom_func K E D FF x y p u v;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @tdapp1_int_cell
      K E D FF FF (@id_transfd K E D FF) x y p u
    ≡ @fdapp1_int_cell K E D FF x y p u;

// The proof-time-comparable ordinary identity presentation reaches the same
// identity-specialized displayed cell owner.
assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @tdapp1_int_cell
      K E D FF FF (@id (@Transf_cat K Cat_cat E D) FF) x y p u
    ≡ @fdapp1_int_cell K E D FF x y p u;

assert [K A : Cat] (x y : τ (Obj A)) (p : τ (Hom A x y)) ⊢
  @fapp1_fapp0
      A
      (@Pi_cat K (@Const_catd K A))
      (@const_section_func K A)
      x y p
    ≡ @Const_transfd K A x y p;

assert [K A : Cat] (x y : τ (Obj A)) (p : τ (Hom A x y))
  (k : τ (Obj K)) ⊢
  @tdapp0_fapp0
    K
    (@Const_catd K Terminal_cat)
    (@Const_catd K A)
    (@Const_func K A x)
    (@Const_func K A y)
    k
    (@Const_transfd K A x y p)
  ≡ @Const_transf Terminal_cat A x y p;

assert [A B : Cat] (x : τ (Obj A)) (y : τ (Obj B)) ⊢
  sigma_Fst
    (@fapp0
      B
      (Product_cat A B)
      (@fapp0
        A
        (Functor_cat B (Product_cat A B))
        (@Product_pair_tele_func A B)
        x)
      y)
    ≡ x;

assert [A B : Cat] (x : τ (Obj A)) (y : τ (Obj B)) ⊢
  sigma_Snd
    (@fapp0
      B
      (Product_cat A B)
      (@fapp0
        A
        (Functor_cat B (Product_cat A B))
        (@Product_pair_tele_func A B)
        x)
      y)
    ≡ y;

assert [A B : Cat] (x x' : τ (Obj A)) (p : τ (Hom A x x'))
  (y : τ (Obj B)) ⊢
  sigma_Fst
    (@tapp0_fapp0
      B
      (Product_cat A B)
      (@fapp0 A (Functor_cat B (Product_cat A B))
        (@Product_pair_tele_func A B) x)
      (@fapp0 A (Functor_cat B (Product_cat A B))
        (@Product_pair_tele_func A B) x')
      y
      (@fapp1_fapp0 A (Functor_cat B (Product_cat A B))
        (@Product_pair_tele_func A B) x x' p))
    ≡ p;

assert [A B : Cat] (x x' : τ (Obj A)) (p : τ (Hom A x x'))
  (y : τ (Obj B)) ⊢
  sigma_Snd
    (@tapp0_fapp0
      B
      (Product_cat A B)
      (@fapp0 A (Functor_cat B (Product_cat A B))
        (@Product_pair_tele_func A B) x)
      (@fapp0 A (Functor_cat B (Product_cat A B))
        (@Product_pair_tele_func A B) x')
      y
      (@fapp1_fapp0 A (Functor_cat B (Product_cat A B))
        (@Product_pair_tele_func A B) x x' p))
    ≡ @id B y;

assert [A B : Cat] (x x' : τ (Obj A)) (p : τ (Hom A x x'))
  (y y' : τ (Obj B)) ⊢
  sigma_Fst
    (@tapp1_func
      B
      (Product_cat A B)
      (@fapp0 A (Functor_cat B (Product_cat A B))
        (@Product_pair_tele_func A B) x)
      (@fapp0 A (Functor_cat B (Product_cat A B))
        (@Product_pair_tele_func A B) x')
      y y'
      (@fapp1_fapp0 A (Functor_cat B (Product_cat A B))
        (@Product_pair_tele_func A B) x x' p))
    ≡ @Const_func (Hom_cat B y y') (Hom_cat A x x') p;

assert [A B : Cat] (x x' : τ (Obj A)) (p : τ (Hom A x x'))
  (y y' : τ (Obj B)) ⊢
  sigma_Snd
    (@tapp1_func
      B
      (Product_cat A B)
      (@fapp0 A (Functor_cat B (Product_cat A B))
        (@Product_pair_tele_func A B) x)
      (@fapp0 A (Functor_cat B (Product_cat A B))
        (@Product_pair_tele_func A B) x')
      y y'
      (@fapp1_fapp0 A (Functor_cat B (Product_cat A B))
        (@Product_pair_tele_func A B) x x' p))
    ≡ @fapp1_func B B (@id_func B) y y';

assert [A : Cat] (x y : τ (Obj A)) ⊢
  @fapp1_func A A (@id_func A) x y
    ≡ @id_func (Hom_cat A x y);

// CATALIAS-03: generic `Cat_cat` composition owner, separate from public alias spelling.
assert [A B C : Cat] (F : τ (Functor B C)) (G : τ (Functor A B)) ⊢
  @comp_cat_fapp0 A B C F G ≡ @comp_fapp0 Cat_cat A B C F G;

assert [A B C : Cat] (F : τ (Functor B C)) (G : τ (Functor A B))
  (x : τ (Obj A)) ⊢
  @fapp0 A C (@comp_fapp0 Cat_cat A B C F G) x
  ≡ @fapp0 B C F (@fapp0 A B G x);

assert [A B C : Cat] (F : τ (Functor B C)) (G : τ (Functor A B))
  (x y : τ (Obj A)) (p : τ (Hom A x y)) ⊢
  @fapp1_fapp0 A C (@comp_fapp0 Cat_cat A B C F G) x y p
  ≡ @fapp1_fapp0 B C F
      (@fapp0 A B G x)
      (@fapp0 A B G y)
      (@fapp1_fapp0 A B G x y p);

assert [A B C : Cat] (F : τ (Functor B C)) (G : τ (Functor A B))
  (x y : τ (Obj A)) ⊢
  @fapp1_func A C (@comp_fapp0 Cat_cat A B C F G) x y
  ≡ @comp_fapp0
      Cat_cat
      (Hom_cat A x y)
      (Hom_cat B (@fapp0 A B G x) (@fapp0 A B G y))
      (Hom_cat C
        (@fapp0 B C F (@fapp0 A B G x))
        (@fapp0 B C F (@fapp0 A B G y)))
      (@fapp1_func B C F (@fapp0 A B G x) (@fapp0 A B G y))
      (@fapp1_func A B G x y);

assert [A B C : Cat] (F : τ (Functor B C)) (G : τ (Functor A B))
  (x y : τ (Obj A)) ⊢
  @fapp1_func A C (@comp_cat_fapp0 A B C F G) x y
    ≡ @comp_cat_fapp0
        (Hom_cat A x y)
        (Hom_cat B
          (@fapp0 A B G x)
          (@fapp0 A B G y))
        (Hom_cat C
          (@fapp0 B C F (@fapp0 A B G x))
          (@fapp0 B C F (@fapp0 A B G y)))
        (@fapp1_func
          B
          C
          F
          (@fapp0 A B G x)
          (@fapp0 A B G y))
        (@fapp1_func A B G x y);

assert [A B C : Cat]
  (F G : τ (Functor (Product_cat A B) C)) ⊢
  @fapp1_func
    (Functor_cat (Product_cat A B) C)
    (Functor_cat A (Functor_cat B C))
    (@curry_func_func A B C)
    F
    G
  ≡ @comp_fapp0
      Cat_cat
      (@Transf_cat (Product_cat A B) C F G)
      (@Transf_cat
        (Product_cat (Functor_cat B A) (Functor_cat B B))
        (Functor_cat B C)
        (@hom_postcomp_func
          Cat_cat
          Cat_cat
          (@id Cat_cat Cat_cat)
          B
          (Product_cat A B)
          C
          F)
        (@hom_postcomp_func
          Cat_cat
          Cat_cat
          (@id Cat_cat Cat_cat)
          B
          (Product_cat A B)
          C
          G))
      (@Transf_cat
        A
        (Functor_cat B C)
        (@hom_precomp_along_fapp0
          Cat_cat
          Cat_cat
          (@id Cat_cat Cat_cat)
          (Functor_cat B C)
          A
          (Product_cat (Functor_cat B A) (Functor_cat B B))
          (@Product_pair_tele_func A B)
          (@hom_postcomp_func
            Cat_cat
            Cat_cat
            (@id Cat_cat Cat_cat)
            B
            (Product_cat A B)
            C
            F))
        (@hom_precomp_along_fapp0
          Cat_cat
          Cat_cat
          (@id Cat_cat Cat_cat)
          (Functor_cat B C)
          A
          (Product_cat (Functor_cat B A) (Functor_cat B B))
          (@Product_pair_tele_func A B)
          (@hom_postcomp_func
            Cat_cat
            Cat_cat
            (@id Cat_cat Cat_cat)
            B
            (Product_cat A B)
            C
            G)))
      (@hom_precomp_along_fapp1_func
        Cat_cat
        Cat_cat
        (@id Cat_cat Cat_cat)
        (Functor_cat B C)
        A
        (Product_cat (Functor_cat B A) (Functor_cat B B))
        (@Product_pair_tele_func A B)
        (@hom_postcomp_func
          Cat_cat
          Cat_cat
          (@id Cat_cat Cat_cat)
          B
          (Product_cat A B)
          C
          F)
        (@hom_postcomp_func
          Cat_cat
          Cat_cat
          (@id Cat_cat Cat_cat)
          B
          (Product_cat A B)
          C
          G))
      (@hom_postcomp_tele_fapp1_func
        Cat_cat
        Cat_cat
        (@id Cat_cat Cat_cat)
        B
        (Product_cat A B)
        C
        F
        G);

assert [A B C : Cat]
  (F G : τ (Functor (Product_cat A B) C))
  (eta : τ (Transf F G)) ⊢
  @fapp1_fapp0
    (Functor_cat (Product_cat A B) C)
    (Functor_cat A (Functor_cat B C))
    (@curry_func_func A B C)
    F
    G
    eta
  ≡ @hom_precomp_along_fapp1_fapp0
      Cat_cat
      Cat_cat
      (@id Cat_cat Cat_cat)
      (Functor_cat B C)
      A
      (Product_cat (Functor_cat B A) (Functor_cat B B))
      (@Product_pair_tele_func A B)
      (@hom_postcomp_func
        Cat_cat
        Cat_cat
        (@id Cat_cat Cat_cat)
        B
        (Product_cat A B)
        C
        F)
      (@hom_postcomp_func
        Cat_cat
        Cat_cat
        (@id Cat_cat Cat_cat)
        B
        (Product_cat A B)
        C
        G)
      (@hom_postcomp_tele_fapp1_fapp0
        Cat_cat
        Cat_cat
        (@id Cat_cat Cat_cat)
        B
        (Product_cat A B)
        C
        F
        G
        eta);

assert [A B C : Cat]
  (F G : τ (Functor (Product_cat A B) C))
  (eta : τ (Transf F G))
  (x : τ (Obj A)) ⊢
  @tapp0_fapp0
    A
    (Functor_cat B C)
    (@curry_func A B C F)
    (@curry_func A B C G)
    x
    (@fapp1_fapp0
      (Functor_cat (Product_cat A B) C)
      (Functor_cat A (Functor_cat B C))
      (@curry_func_func A B C)
      F
      G
      eta)
  ≡ @tapp0_fapp0
      A
      (Functor_cat B C)
      (@hom_precomp_along_fapp0
        Cat_cat
        Cat_cat
        (@id Cat_cat Cat_cat)
        (Functor_cat B C)
        A
        (Product_cat (Functor_cat B A) (Functor_cat B B))
        (@Product_pair_tele_func A B)
        (@hom_postcomp_func
          Cat_cat
          Cat_cat
          (@id Cat_cat Cat_cat)
          B
          (Product_cat A B)
          C
          F))
      (@hom_precomp_along_fapp0
        Cat_cat
        Cat_cat
        (@id Cat_cat Cat_cat)
        (Functor_cat B C)
        A
        (Product_cat (Functor_cat B A) (Functor_cat B B))
        (@Product_pair_tele_func A B)
        (@hom_postcomp_func
          Cat_cat
          Cat_cat
          (@id Cat_cat Cat_cat)
          B
          (Product_cat A B)
          C
          G))
      x
      (@hom_precomp_along_fapp1_fapp0
        Cat_cat
        Cat_cat
        (@id Cat_cat Cat_cat)
        (Functor_cat B C)
        A
        (Product_cat (Functor_cat B A) (Functor_cat B B))
        (@Product_pair_tele_func A B)
        (@hom_postcomp_func
          Cat_cat
          Cat_cat
          (@id Cat_cat Cat_cat)
          B
          (Product_cat A B)
          C
          F)
        (@hom_postcomp_func
          Cat_cat
          Cat_cat
          (@id Cat_cat Cat_cat)
          B
          (Product_cat A B)
          C
          G)
        (@hom_postcomp_tele_fapp1_fapp0
          Cat_cat
          Cat_cat
          (@id Cat_cat Cat_cat)
          B
          (Product_cat A B)
          C
          F
          G
          eta));

assert [A B C : Cat]
  (F G : τ (Functor (Product_cat A B) C))
  (eta : τ (Transf F G))
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  @tapp0_fapp0
    B
    C
    (@fapp0 A (Functor_cat B C) (@curry_func A B C F) x)
    (@fapp0 A (Functor_cat B C) (@curry_func A B C G) x)
    y
    (@tapp0_fapp0
      A
      (Functor_cat B C)
      (@curry_func A B C F)
      (@curry_func A B C G)
      x
      (@fapp1_fapp0
        (Functor_cat (Product_cat A B) C)
        (Functor_cat A (Functor_cat B C))
        (@curry_func_func A B C)
        F
        G
        eta))
  ≡ @tapp0_fapp0
      B
      C
      (@fapp0
        A
        (Functor_cat B C)
        (@hom_precomp_along_fapp0
          Cat_cat
          Cat_cat
          (@id Cat_cat Cat_cat)
          (Functor_cat B C)
          A
          (Product_cat (Functor_cat B A) (Functor_cat B B))
          (@Product_pair_tele_func A B)
          (@hom_postcomp_func
            Cat_cat
            Cat_cat
            (@id Cat_cat Cat_cat)
            B
            (Product_cat A B)
            C
            F))
        x)
      (@fapp0
        A
        (Functor_cat B C)
        (@hom_precomp_along_fapp0
          Cat_cat
          Cat_cat
          (@id Cat_cat Cat_cat)
          (Functor_cat B C)
          A
          (Product_cat (Functor_cat B A) (Functor_cat B B))
          (@Product_pair_tele_func A B)
          (@hom_postcomp_func
            Cat_cat
            Cat_cat
            (@id Cat_cat Cat_cat)
            B
            (Product_cat A B)
            C
            G))
        x)
      y
      (@tapp0_fapp0
        A
        (Functor_cat B C)
        (@hom_precomp_along_fapp0
          Cat_cat
          Cat_cat
          (@id Cat_cat Cat_cat)
          (Functor_cat B C)
          A
          (Product_cat (Functor_cat B A) (Functor_cat B B))
          (@Product_pair_tele_func A B)
          (@hom_postcomp_func
            Cat_cat
            Cat_cat
            (@id Cat_cat Cat_cat)
            B
            (Product_cat A B)
            C
            F))
        (@hom_precomp_along_fapp0
          Cat_cat
          Cat_cat
          (@id Cat_cat Cat_cat)
          (Functor_cat B C)
          A
          (Product_cat (Functor_cat B A) (Functor_cat B B))
          (@Product_pair_tele_func A B)
          (@hom_postcomp_func
            Cat_cat
            Cat_cat
            (@id Cat_cat Cat_cat)
            B
            (Product_cat A B)
            C
            G))
        x
        (@hom_precomp_along_fapp1_fapp0
          Cat_cat
          Cat_cat
          (@id Cat_cat Cat_cat)
          (Functor_cat B C)
          A
          (Product_cat (Functor_cat B A) (Functor_cat B B))
          (@Product_pair_tele_func A B)
          (@hom_postcomp_func
            Cat_cat
            Cat_cat
            (@id Cat_cat Cat_cat)
            B
            (Product_cat A B)
            C
            F)
          (@hom_postcomp_func
            Cat_cat
            Cat_cat
            (@id Cat_cat Cat_cat)
            B
            (Product_cat A B)
            C
            G)
          (@hom_postcomp_tele_fapp1_fapp0
            Cat_cat
            Cat_cat
            (@id Cat_cat Cat_cat)
            B
            (Product_cat A B)
            C
            F
            G
            eta)));

assert [A B C : Cat]
  (F : τ (Functor (Product_cat A B) C))
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  @fapp0 B C
    (@fapp0 A (Functor_cat B C) (@curry_func A B C F) x)
    y
    ≡ @fapp0 B C
        (@fapp0
          A
          (Functor_cat B C)
          (@hom_precomp_along_fapp0
            Cat_cat
            Cat_cat
            (@id Cat_cat Cat_cat)
            (Functor_cat B C)
            A
            (Product_cat (Functor_cat B A) (Functor_cat B B))
            (@Product_pair_tele_func A B)
            (@hom_postcomp_func
              Cat_cat
              Cat_cat
              (@id Cat_cat Cat_cat)
              B
              (Product_cat A B)
              C
              F))
          x)
        y;

assert [A B C : Cat]
  (F : τ (Functor (Product_cat A B) C))
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  @fapp0 (Product_cat A B) C
    (@uncurry_func A B C (@curry_func A B C F))
    (Struct_sigma x y)
    ≡ @fapp0
        (Product_cat A B)
        C
        (@hom_postcomp_fapp0
          Cat_cat
          Cat_cat
          (@id Cat_cat Cat_cat)
          (Product_cat A B)
          (Product_cat (Functor_cat B C) B)
          C
          (@Eval_func B C)
          (@Product_cat_fapp1_tapp0_func
            A
            (Functor_cat B C)
            B
            (@hom_precomp_along_fapp0
              Cat_cat
              Cat_cat
              (@id Cat_cat Cat_cat)
              (Functor_cat B C)
              A
              (Product_cat (Functor_cat B A) (Functor_cat B B))
              (@Product_pair_tele_func A B)
              (@hom_postcomp_func
                Cat_cat
                Cat_cat
                (@id Cat_cat Cat_cat)
                B
                (Product_cat A B)
                C
                F))))
        (Struct_sigma x y);

assert [A B C : Cat]
  (G : τ (Functor A (Functor_cat B C)))
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  @fapp0 B C
    (@fapp0 A (Functor_cat B C)
      (@curry_func A B C (@uncurry_func A B C G))
      x)
    y
    ≡ @fapp0 B C
        (@fapp0
          A
          (Functor_cat B C)
          (@hom_precomp_along_fapp0
            Cat_cat
            Cat_cat
            (@id Cat_cat Cat_cat)
            (Functor_cat B C)
            A
            (Product_cat (Functor_cat B A) (Functor_cat B B))
            (@Product_pair_tele_func A B)
            (@hom_postcomp_func
              Cat_cat
              Cat_cat
              (@id Cat_cat Cat_cat)
              B
              (Product_cat A B)
              C
              (@hom_postcomp_fapp0
                Cat_cat
                Cat_cat
                (@id Cat_cat Cat_cat)
                (Product_cat A B)
                (Product_cat (Functor_cat B C) B)
                C
                (@Eval_func B C)
                (@Product_cat_fapp1_tapp0_func A (Functor_cat B C) B G))))
          x)
        y;

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x))) ⊢
  @pathout_pi_transport_func Z x y p E
    ≡ @section_pullback_func
        (@PathOut_cat Z y)
        (@PathOut_cat Z x)
        (@PathOut_transport_func Z x y p)
        E;

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x))) ⊢
  @PathIndTgt_transport_func Z x y p E
    ≡ @pathout_pi_transport_func Z x y p E;

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x))) ⊢
  @fdapp1_int_cell
    Z
    (@PathOutMotives_catd Z)
    (@Const_catd Z Cat_cat)
    (@PathOutPi_funcd Z)
    x
    y
    p
    E
    ≡ @PathIndTgt_transport_func Z x y p E;

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  (s : τ (Obj (@Pi_cat (@PathOut_cat Z x) E))) ⊢
  @fapp0
    (Fibre_cat (@PathIndTgt_catd Z) (Struct_sigma x E))
    (Fibre_cat
      (@PathIndTgt_catd Z)
      (Struct_sigma y (@pathout_motive_transport_obj Z x y p E)))
    (@PathIndTgt_transport_func Z x y p E)
    s
    ≡ @section_pullback_sec
        (@PathOut_cat Z y)
        (@PathOut_cat Z x)
        (@PathOut_transport_func Z x y p)
        E
        s;

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  (s : τ (Obj (@Pi_cat (@PathOut_cat Z x) E)))
  (q : τ (Obj (@PathOut_cat Z y))) ⊢
  @piapp0
    (@PathOut_cat Z y)
    (@pathout_motive_transport_obj Z x y p E)
    (@fapp0
      (Fibre_cat (@PathIndTgt_catd Z) (Struct_sigma x E))
      (Fibre_cat
        (@PathIndTgt_catd Z)
        (Struct_sigma y (@pathout_motive_transport_obj Z x y p E)))
      (@PathIndTgt_transport_func Z x y p E)
      s)
    q
    ≡ @piapp0
        (@PathOut_cat Z x)
        E
        s
        (@fapp0
          (@PathOut_cat Z y)
          (@PathOut_cat Z x)
          (@PathOut_transport_func Z x y p)
          q);

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  (s : τ (Obj (@Pi_cat (@PathOut_cat Z x) E))) ⊢
  @piapp0
    (@PathOut_cat Z y)
    (@pathout_motive_transport_obj Z x y p E)
    (@fapp0
      (Fibre_cat (@PathIndTgt_catd Z) (Struct_sigma x E))
      (Fibre_cat
        (@PathIndTgt_catd Z)
        (Struct_sigma y (@pathout_motive_transport_obj Z x y p E)))
      (@PathIndTgt_transport_func Z x y p E)
      s)
    (@pathout_refl_obj Z y)
    ≡ @piapp0
        (@PathOut_cat Z x)
        E
        s
        (@pathout_obj Z x y p);

assert [K : Cat] (E : τ (Catd K)) (k : τ (Obj K)) ⊢
  Fibre_cat E k ≡ @fapp0 K Cat_cat E k;

assert [K : Cat] (A : Cat) (k : τ (Obj K)) ⊢
  Fibre_cat (Const_catd K A) k ≡ A;

assert [K : Cat] (k : τ (Obj K)) ⊢
  Fibre_cat (Terminal_catd K) k ≡ Terminal_cat;

assert [K : Cat] ⊢
  Terminal_catd K ≡ Const_catd K Terminal_cat;

assert [K : Cat] (E : τ (Catd K)) (k : τ (Obj K)) ⊢
  Fibre_cat (Op_catd E) k ≡ Op_cat (Fibre_cat E k);

assert [K : Cat] (A : Cat) ⊢
  Op_catd (Const_catd K A) ≡ Const_catd K (Op_cat A);

assert [A B : Cat] (E : τ (Catd B)) (F : τ (Functor A B)) (a : τ (Obj A)) ⊢
  Fibre_cat (Pullback_catd E F) a ≡ Fibre_cat E (fapp0 F a);

assert [A B : Cat]
  (E : τ (Catd B))
  (F : τ (Functor A B)) ⊢
  eq_refl (@comp_cat_fapp0 A B Cat_cat E F)
  : τ (
      @comp_cat_fapp0 A B Cat_cat E F
      =
      @Pullback_catd A B E F);

assert [A B : Cat]
  (F : τ (Functor A B)) ⊢
  eq_refl (@comp_cat_con_func A B Cat_cat F)
  : τ (
      @comp_cat_con_func A B Cat_cat F
      =
      @Pullback_catd_func A B F);

assert [A B C : Cat]
  (E : τ (Catd C))
  (F : τ (Functor B C))
  (H : τ (Functor A B)) ⊢
  eq_refl
    (@comp_cat_fapp0
      A B Cat_cat
      (@Pullback_catd B C E F)
      H)
  : τ (
      @comp_cat_fapp0
        A B Cat_cat
        (@Pullback_catd B C E F)
        H
      =
      @Pullback_catd
        A C E
        (@comp_cat_fapp0 A B C F H));

assert [A B C : Cat]
  (E : τ (Catd C))
  (F : τ (Functor B C))
  (H : τ (Functor A B))
  (a : τ (Obj A)) ⊢
  @fapp0 A Cat_cat
    (@comp_cat_fapp0
      A B Cat_cat
      (@Pullback_catd B C E F)
      H)
    a
  ≡ @Fibre_cat
      C
      E
      (@fapp0
        A
        C
        (@comp_cat_fapp0 A B C F H)
        a);

assert [A B : Cat]
  (E : τ (Catd B))
  (F : τ (Functor A B))
  (a a' : τ (Obj A))
  (p : τ (Hom A a a')) ⊢
  @fapp1_fapp0 A Cat_cat (@Pullback_catd A B E F) a a' p
    ≡ @fapp1_fapp0
        B
        Cat_cat
        E
        (@fapp0 A B F a)
        (@fapp0 A B F a')
        (@fapp1_fapp0 A B F a a' p);

assert [A : Cat] (E : τ (Catd A)) ⊢
  @Pullback_catd A A E (@id_func A) ≡ E;

assert [A B C : Cat]
  (E : τ (Catd C))
  (F : τ (Functor B C))
  (H : τ (Functor A B)) ⊢
  @Pullback_catd A B (@Pullback_catd B C E F) H
    ≡ @Pullback_catd
        A C E
        (@comp_cat_fapp0 A B C F H);

assert [A B : Cat] (F : τ (Functor A B)) (C : Cat) ⊢
  @Pullback_catd A B (@Const_catd B C) F
    ≡ @Const_catd A C;

assert [K : Cat] (E : τ (Catd K)) ⊢
  @Pullback_catd K Cat_cat op E
    ≡ @Op_catd K E;

assert [K : Cat] ⊢
  @eq_refl Cat_grpd
    (@fapp0 (Op_cat Cat_cat) Cat_cat Catd_cat_func K)
  : τ (@= Cat_grpd
      (@fapp0 (Op_cat Cat_cat) Cat_cat Catd_cat_func K)
      (Catd_cat K));

assert [A B : Cat] (F : τ (Functor A B)) ⊢
  @fapp1_fapp0
    (Op_cat Cat_cat)
    Cat_cat
    Catd_cat_func
    B
    A
    F
    ≡ @Pullback_catd_func A B F;

assert [A B : Cat] (F : τ (Functor A B)) (E : τ (Catd B)) ⊢
  @fapp0 (@Catd_cat B) (@Catd_cat A) (@Pullback_catd_func A B F) E
    ≡ @Pullback_catd A B E F;

// Derived classifier for displayed categories over the fibres of K.
assert [L : Cat] (K : τ (Catd L)) (l : τ (Obj L)) ⊢
  @eq_refl Cat_grpd (Fibre_cat (Catd_catd_con K) l)
  : τ (@= Cat_grpd
      (Fibre_cat (Catd_catd_con K) l)
      (Catd_cat (Fibre_cat K l)));

assert [L : Cat] (K : τ (Catd L)) (x y : τ (Obj L))
  (p : τ (Hom L x y)) ⊢
  @fapp1_fapp0
    (Op_cat L)
    Cat_cat
    (@Catd_catd_con L K)
    y
    x
    p
    ≡ @Pullback_catd_func
        (Fibre_cat K x)
        (Fibre_cat K y)
        (@fapp1_fapp0 L Cat_cat K x y p);

assert [K : Cat] (G : τ (Functor K (Op_cat Cat_cat))) ⊢
  @fapp1_fapp0
    (@Catd_cat (Op_cat Cat_cat))
    (@Catd_cat K)
    (@Pullback_catd_func K (Op_cat Cat_cat) G)
    Catd_cat_func
    (@Const_catd (Op_cat Cat_cat) Cat_cat)
    Pi_int_funcd
    ≡ @Pi_pullback_funcd K G;

assert [K : Cat] (G : τ (Functor K (Op_cat Cat_cat)))
  (x : τ (Obj K)) ⊢
  @tapp0_fapp0
    K
    Cat_cat
    (@Pullback_catd K (Op_cat Cat_cat) Catd_cat_func G)
    (@Const_catd K Cat_cat)
    x
    (@Pi_pullback_funcd K G)
    ≡ @Pi_func (@fapp0 K (Op_cat Cat_cat) G x);

assert [K : Cat] (E : τ (Catd K)) ⊢
  fapp1_fapp0 (Pi_func K) id_funcd ≡ id_func;

assert [K : Cat] (E : τ (Catd K)) ⊢
  @eq_refl Cat_grpd (@Transf_cat K Cat_cat (@Terminal_catd K) E)
  : τ (@= Cat_grpd
      (@Transf_cat K Cat_cat (@Terminal_catd K) E)
      (Pi_cat E));

assert [K : Cat] (E : τ (Catd K)) ⊢
  @eq_refl Cat_grpd (Pi_cat E)
  : τ (@= Cat_grpd
      (Pi_cat E)
      (@Functord_cat K (@Terminal_catd K) E));

assert [K : Cat] (E : τ (Catd K)) ⊢
  Obj (Pi_cat E)
    ≡ Obj (@Functord_cat K (@Terminal_catd K) E);

assert [K : Cat] (A : Cat) ⊢
  @eq_refl Cat_grpd (Pi_cat (Const_catd K A))
  : τ (@= Cat_grpd
      (Pi_cat (Const_catd K A))
      (Functor_cat K A));

assert [K : Cat] (A : Cat) ⊢
  @eq_refl Grpd_grpd (Obj (Pi_cat (Const_catd K A)))
  : τ (@= Grpd_grpd
      (Obj (Pi_cat (Const_catd K A)))
      (Obj (Functor_cat K A)));

assert [K : Cat] (A : Cat) ⊢
  @eq_refl Grpd_grpd
    (Obj
      (@Transf_cat
        K Cat_cat
        (@Const_catd K Terminal_cat)
        (@Const_catd K A)))
  : τ (@= Grpd_grpd
      (Obj
        (@Transf_cat
          K Cat_cat
          (@Const_catd K Terminal_cat)
          (@Const_catd K A)))
      (Obj (Functor_cat K A)));

assert [K : Cat] (A : Cat) ⊢
  @eq_refl Grpd_grpd
    (Obj
      (@Functord_cat
        K
        (@Const_catd K Terminal_cat)
        (@Const_catd K A)))
  : τ (@= Grpd_grpd
      (Obj
        (@Functord_cat
          K
          (@Const_catd K Terminal_cat)
          (@Const_catd K A)))
      (Obj (Functor_cat K A)));

assert [K : Cat] (E : τ (Catd K)) (s t : τ (Obj (Pi_cat E))) ⊢
  Hom_cat (Pi_cat E) s t
    ≡ @Transfd_cat K (@Const_catd K Terminal_cat) E s t;

assert [K : Cat] (A : Cat)
  (s t : τ (Obj (Pi_cat (@Const_catd K A)))) ⊢
  @eq_refl Cat_grpd
    (Hom_cat (Pi_cat (@Const_catd K A)) s t)
  : τ (@= Cat_grpd
      (Hom_cat (Pi_cat (@Const_catd K A)) s t)
      (@Transf_cat K A s t));

assert [K : Cat] (A : Cat)
  (F : τ (Obj (Pi_cat (Const_catd K A))))
  (k : τ (Obj K)) ⊢
  @piapp0 K (@Const_catd K A) F k
    ≡ @fapp0 K A F k;

assert [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  (k : τ (Obj K)) ⊢
  @fapp0
    Terminal_cat
    (Fibre_cat E k)
    (@tapp0_fapp0 K Cat_cat (@Const_catd K Terminal_cat) E k s)
    Terminal_obj
    ≡ @piapp0 K E s k;

// The named Pi evaluation functor computes on section objects through the
// same terminal-source component route.
assert [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  (k : τ (Obj K)) ⊢
  @fapp0
    (@Pi_cat K E)
    (Fibre_cat E k)
    (@piapp0_func K E k)
    s
    ≡ @piapp0 K E s k;

// The hom action of Pi evaluation is the displayed component of the arrow
// between sections.
assert [K : Cat] (E : τ (Catd K))
  (s t : τ (Obj (Pi_cat E)))
  (eta : τ (Hom (Pi_cat E) s t))
  (k : τ (Obj K)) ⊢
  @fapp1_fapp0
    (@Pi_cat K E)
    (Fibre_cat E k)
    (@piapp0_func K E k)
    s
    t
    eta
    ≡ @pi_hom_fapp0 K E s t eta k;

assert [K : Cat] (E : τ (Catd K)) ⊢
  @fapp0 (Catd_cat K) Cat_cat (Pi_func K) E ≡ Pi_cat E;

assert [K : Cat] ⊢
  @tapp0_fapp0
    (Op_cat Cat_cat)
    Cat_cat
    Catd_cat_func
    (@Const_catd (Op_cat Cat_cat) Cat_cat)
    K
    Pi_int_funcd
    ≡ @Pi_func K;

assert [K : Cat] (E : τ (Catd K))
  (k : τ (Obj K))
  (u : τ (Obj (Fibre_cat E k))) ⊢
  @fapp0
    (Fibre_cat E k)
    (@Sigma_cat K E)
    (@tapp0_fapp0
      K
      Cat_cat
      E
      (@Const_catd K (@Sigma_cat K E))
      k
      (@sigma_intro_transf K E))
    u
    ≡ @Struct_sigma
        (Obj K)
        (λ kk : τ (Obj K), Obj (Fibre_cat E kk))
        k
        u;

assert [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  (k : τ (Obj K)) ⊢
  @fapp0
    (Pi_cat E)
    (Fibre_cat E k)
    (@tapp0_fapp0
      K
      Cat_cat
      (@Const_catd K (@Pi_cat K E))
      E
      k
      (@pi_eval_transf K E))
    s
    ≡ @piapp0 K E s k;

assert [K : Cat] (A : Cat)
  (a : τ (Obj A)) ⊢
  @fapp0 A (@Pi_cat K (@Const_catd K A)) (@const_section_func K A) a
    ≡ @Const_func K A a;

assert [A : Cat] (a : τ (Obj A)) ⊢
  @Obj_func A a ≡ @Const_func Terminal_cat A a;

assert [A : Cat] (a : τ (Obj A)) ⊢
  @fapp0 A (@Pi_cat Terminal_cat (@Const_catd Terminal_cat A))
    (@const_section_func Terminal_cat A) a
    ≡ @Obj_func A a;

assert [A : Cat] (a : τ (Obj A)) (x y : τ (Obj Terminal_cat)) ⊢
  @fapp1_func Terminal_cat A (@Obj_func A a) x y
    ≡ @Obj_func (Hom_cat A a a) (@id A a);

assert [A : Cat] (a : τ (Obj A)) (x y : τ (Obj Terminal_cat))
  (f : τ (Hom Terminal_cat x y)) ⊢
  @fapp1_fapp0 Terminal_cat A (@Obj_func A a) x y f
    ≡ @id A a;

assert [K : Cat] (A : Cat)
  (a : τ (Obj A))
  (k : τ (Obj K)) ⊢
  @piapp0
    K
    (@Const_catd K A)
    (@fapp0 A (@Pi_cat K (@Const_catd K A)) (@const_section_func K A) a)
    k
    ≡ a;

assert [A B : Cat] (b : τ (Obj B)) ⊢
  @fapp0 B (Functor_cat A B) (@Const_func_func A B) b
    ≡ @Const_func A B b;

assert [A B : Cat] (x y : τ (Obj B)) (p : τ (Hom B x y)) ⊢
  @fapp1_fapp0
      B
      (Functor_cat A B)
      (@Const_func_func A B)
      x y p
    ≡ @Const_transf A B x y p;

assert [A B : Cat] (x y : τ (Obj B)) (p : τ (Hom B x y))
  (a : τ (Obj A)) ⊢
  @tapp0_fapp0
      A
      B
      (@Const_func A B x)
      (@Const_func A B y)
      a
      (@fapp1_fapp0
        B
        (Functor_cat A B)
        (@Const_func_func A B)
        x y p)
    ≡ p;

assert [A B : Cat] (x y : τ (Obj B)) (p : τ (Hom B x y))
  (a a' : τ (Obj A)) (q : τ (Hom A a a')) ⊢
  @tapp1_fapp0
      A
      B
      (@Const_func A B x)
      (@Const_func A B y)
      a
      a'
      (@fapp1_fapp0
        B
        (Functor_cat A B)
        (@Const_func_func A B)
        x y p)
      q
    ≡ p;

assert [A B C : Cat] (H : τ (Functor A (Functor_cat B C))) ⊢
  @fapp0
      (Functor_cat A (Functor_cat B C))
      (Functor_cat B (Functor_cat A C))
      (@sym_func_func A B C)
      H
    ≡ @sym_func A B C H;

assert [A B C : Cat] (H : τ (Functor A (Functor_cat B C)))
  (a : τ (Obj A)) (b : τ (Obj B)) ⊢
  @fapp0
      A
      C
      (@fapp0
        B
        (Functor_cat A C)
        (@fapp0
          (Functor_cat A (Functor_cat B C))
          (Functor_cat B (Functor_cat A C))
          (@sym_func_func A B C)
          H)
        b)
      a
    ≡ @fapp0 B C (@fapp0 A (Functor_cat B C) H a) b;

assert [A B C : Cat] (H : τ (Functor A (Functor_cat B C)))
  (a a' : τ (Obj A)) (p : τ (Hom A a a')) (b : τ (Obj B)) ⊢
  @fapp1_fapp0
      A
      C
      (@sym_fapp0_func A B C H b)
      a
      a'
      p
    ≡ @tapp0_fapp0
        B
        C
        (@fapp0 A (Functor_cat B C) H a)
        (@fapp0 A (Functor_cat B C) H a')
        b
        (@fapp1_fapp0 A (Functor_cat B C) H a a' p);

assert [A B C : Cat] (H : τ (Functor A (Functor_cat B C)))
  (b b' : τ (Obj B)) (q : τ (Hom B b b')) ⊢
  @fapp1_fapp0
      B
      (Functor_cat A C)
      (@sym_func A B C H)
      b
      b'
      q
    ≡ @sym_tapp1_fapp0_transf A B C H b b' q;

assert [A B C : Cat] (H : τ (Functor A (Functor_cat B C)))
  (a : τ (Obj A)) (b b' : τ (Obj B)) (q : τ (Hom B b b')) ⊢
  @tapp0_fapp0
      A
      C
      (@sym_fapp0_func A B C H b)
      (@sym_fapp0_func A B C H b')
      a
      (@sym_tapp1_fapp0_transf A B C H b b' q)
    ≡ @fapp1_fapp0
        B
        C
        (@fapp0 A (Functor_cat B C) H a)
        b
        b'
        q;

assert [A B C : Cat] (H : τ (Functor A (Functor_cat B C)))
  (a a' : τ (Obj A)) (p : τ (Hom A a a'))
  (b b' : τ (Obj B)) (q : τ (Hom B b b')) ⊢
  @tapp1_fapp0
      A
      C
      (@sym_fapp0_func A B C H b)
      (@sym_fapp0_func A B C H b')
      a
      a'
      (@sym_tapp1_fapp0_transf A B C H b b' q)
      p
    ≡ @tapp1_fapp0
        B
        C
        (@fapp0 A (Functor_cat B C) H a)
        (@fapp0 A (Functor_cat B C) H a')
        b
        b'
        (@fapp1_fapp0 A (Functor_cat B C) H a a' p)
        q;

assert [A B C : Cat]
  (H K : τ (Functor A (Functor_cat B C)))
  (eta : τ (Transf H K))
  (b : τ (Obj B)) ⊢
  @tapp0_fapp0
      B
      (Functor_cat A C)
      (@sym_func A B C H)
      (@sym_func A B C K)
      b
      (@fapp1_fapp0
        (Functor_cat A (Functor_cat B C))
        (Functor_cat B (Functor_cat A C))
        (@sym_func_func A B C)
        H
        K
        eta)
    ≡ @sym_transf_tapp0_transf A B C H K eta b;

assert [A B C : Cat]
  (H K : τ (Functor A (Functor_cat B C)))
  (eta : τ (Transf H K))
  (a : τ (Obj A)) (b : τ (Obj B)) ⊢
  @tapp0_fapp0
      A
      C
      (@sym_fapp0_func A B C H b)
      (@sym_fapp0_func A B C K b)
      a
      (@sym_transf_tapp0_transf A B C H K eta b)
    ≡ @tapp0_fapp0
        B
        C
        (@fapp0 A (Functor_cat B C) H a)
        (@fapp0 A (Functor_cat B C) K a)
        b
        (@tapp0_fapp0 A (Functor_cat B C) H K a eta);

assert [A C : Cat] (H : τ (Functor A (Functor_cat A C))) ⊢
  @fapp0
      (Functor_cat A (Functor_cat A C))
      (Functor_cat A C)
      (@diag_func_func A C)
      H
    ≡ @diag_func A C H;

assert [A C : Cat] (H : τ (Functor A (Functor_cat A C)))
  (a : τ (Obj A)) ⊢
  @fapp0 A C (@diag_func A C H) a
    ≡ @fapp0 A C (@fapp0 A (Functor_cat A C) H a) a;

assert [A C : Cat] (H : τ (Functor A (Functor_cat A C)))
  (a a' : τ (Obj A)) (p : τ (Hom A a a')) ⊢
  @fapp1_fapp0 A C (@diag_func A C H) a a' p
    ≡ @tapp1_fapp0
        A
        C
        (@fapp0 A (Functor_cat A C) H a)
        (@fapp0 A (Functor_cat A C) H a')
        a
        a'
        (@fapp1_fapp0 A (Functor_cat A C) H a a' p)
        p;

assert [A C : Cat]
  (H K : τ (Functor A (Functor_cat A C)))
  (eta : τ (Transf H K))
  (a : τ (Obj A)) ⊢
  @tapp0_fapp0
      A
      C
      (@diag_func A C H)
      (@diag_func A C K)
      a
      (@fapp1_fapp0
        (Functor_cat A (Functor_cat A C))
        (Functor_cat A C)
        (@diag_func_func A C)
        H
        K
        eta)
    ≡ @tapp0_fapp0
        A
        C
        (@fapp0 A (Functor_cat A C) H a)
        (@fapp0 A (Functor_cat A C) K a)
        a
        (@tapp0_fapp0 A (Functor_cat A C) H K a eta);

assert [A C : Cat] (H : τ (Functor A (Functor_cat A C)))
  (a a' : τ (Obj A)) (p : τ (Hom A a a')) ⊢
  fapp0 (@fapp1_func A C (@diag_func A C H) a a') p
    ≡ @tapp1_fapp0
        A
        C
        (@fapp0 A (Functor_cat A C) H a)
        (@fapp0 A (Functor_cat A C) H a')
        a
        a'
        (@fapp1_fapp0 A (Functor_cat A C) H a a' p)
        p;

assert [A B : Cat] (F : τ (Functor A B)) (E : τ (Catd B))
  (s : τ (Obj (@Functord_cat B (@Const_catd B Terminal_cat) E))) ⊢
  @fapp0
    (@Functord_cat B (@Const_catd B Terminal_cat) E)
    (@Functord_cat A (@Const_catd A Terminal_cat) (@Pullback_catd A B E F))
    (@section_pullback_func A B F E)
    s
    ≡ @section_pullback_sec A B F E s;

assert [A B : Cat] (F : τ (Functor A B)) (E : τ (Catd B))
  (s : τ (Obj (@Functord_cat B (@Const_catd B Terminal_cat) E)))
  (a : τ (Obj A)) ⊢
  @piapp0
    A
    (@Pullback_catd A B E F)
    (@fapp0
      (@Functord_cat B (@Const_catd B Terminal_cat) E)
      (@Functord_cat A (@Const_catd A Terminal_cat) (@Pullback_catd A B E F))
      (@section_pullback_func A B F E)
      s)
    a
    ≡ @piapp0 B E s (@fapp0 A B F a);

assert [A B : Cat] (F : τ (Functor A B)) (E : τ (Catd B)) ⊢
  @tapp0_fapp0
    (@Catd_cat B)
    Cat_cat
    (@Pi_func B)
    (@comp_cat_fapp0
      (@Catd_cat B)
      (@Catd_cat A)
      Cat_cat
      (@Pi_func A)
      (@Pullback_catd_func A B F))
    E
    (@section_pullback_transf A B F)
    ≡ @section_pullback_func A B F E;

assert [A B : Cat] (F : τ (Functor A B)) (E : τ (Catd B)) ⊢
  @fdapp1_int_cell
    (Op_cat Cat_cat)
    Catd_cat_func
    (@Const_catd (Op_cat Cat_cat) Cat_cat)
    Pi_int_funcd
    B
    A
    F
    E
    ≡ @section_pullback_func A B F E;

assert [K : Cat] (G : τ (Functor K (Op_cat Cat_cat)))
  (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (E : τ (Catd (@fapp0 K (Op_cat Cat_cat) G x))) ⊢
  @fdapp1_int_cell
    K
    (@Pullback_catd K (Op_cat Cat_cat) Catd_cat_func G)
    (@Const_catd K Cat_cat)
    (@Pi_pullback_funcd K G)
    x
    y
    p
    E
    ≡ @section_pullback_func
        (@fapp0 K (Op_cat Cat_cat) G y)
        (@fapp0 K (Op_cat Cat_cat) G x)
        (@fapp1_fapp0 K (Op_cat Cat_cat) G x y p)
        E;

assert [K : Cat] (E : τ (Catd K)) ⊢
  @fapp0 (Catd_cat K) Cat_cat (Sigma_func K) E ≡ Sigma_cat E;

assert [K : Cat] (E D : τ (Catd K)) (η : τ (Functord E D)) ⊢
  @fapp1_fapp0 (Catd_cat K) Cat_cat (@Sigma_func K) E D η
    ≡ @sigma_map_func K E D η;

// The generic second hom action of Sigma totalization reaches the stable
// totalized-transfor projection.
assert [K : Cat]
  [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)]
  (eta : τ (Transfd FF GG)) ⊢
  @fapp1_fapp0
    (@Functord_cat K E D)
    (Functor_cat (@Sigma_cat K E) (@Sigma_cat K D))
    (@fapp1_func
      (@Catd_cat K)
      Cat_cat
      (@Sigma_func K)
      E D)
    FF GG eta
  ≡ @sigma_map_transf K E D FF GG eta;

// Its point component is the fibrewise component over the identity base
// arrow, packaged as an arrow of the Sigma-total category.
assert [K : Cat]
  [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)]
  (eta : τ (Transfd FF GG))
  (k : τ (Obj K))
  (u : τ (Obj (Fibre_cat E k))) ⊢
  @tapp0_fapp0
    (@Sigma_cat K E)
    (@Sigma_cat K D)
    (@sigma_map_func K E D FF)
    (@sigma_map_func K E D GG)
    (Struct_sigma k u)
    (@sigma_map_transf K E D FF GG eta)
  ≡ @sigma_arrow
      K D
      k k
      (@fapp0
        (Fibre_cat E k)
        (Fibre_cat D k)
        (@Fibre_func K E D FF k)
        u)
      (@fapp0
        (Fibre_cat E k)
        (Fibre_cat D k)
        (@Fibre_func K E D GG k)
        u)
      (@id K k)
      (@tapp0_fapp0
        (Fibre_cat E k)
        (Fibre_cat D k)
        (@Fibre_func K E D FF k)
        (@Fibre_func K E D GG k)
        u
        (@tdapp0_fapp0 K E D FF GG k eta));

assert [K : Cat] (E : τ (Catd K)) (k : τ (Obj K)) (u : τ (Obj (Fibre_cat E k))) ⊢
  fapp0 (Sigma_proj1_func E) (Struct_sigma k u) ≡ k;

assert [K : Cat] (R D : τ (Catd K)) ⊢
  @Pullback_catd (@Sigma_cat K R) K D (@Sigma_proj1_func K R)
    ≡ @Sigma_proj1_pullback_catd K R D;

assert [K : Cat] (R D : τ (Catd K))
  (k : τ (Obj K))
  (r : τ (Obj (Fibre_cat R k))) ⊢
  Fibre_cat (@Sigma_proj1_pullback_catd K R D) (Struct_sigma k r)
    ≡ Fibre_cat D k;

assert [K : Cat] (R D : τ (Catd K)) ⊢
  @eq_refl Cat_grpd
    (@Pi_cat (@Sigma_cat K R) (@Sigma_proj1_pullback_catd K R D))
  : τ (@= Cat_grpd
      (@Pi_cat (@Sigma_cat K R) (@Sigma_proj1_pullback_catd K R D))
      (@Functord_cat K R D));

assert [K : Cat] (R D : τ (Catd K)) ⊢
  Obj (@Pi_cat (@Sigma_cat K R) (@Sigma_proj1_pullback_catd K R D))
    ≡ Obj (@Functord_cat K R D);

assert [K : Cat] (R D : τ (Catd K))
  (s t : τ (Obj (@Pi_cat (@Sigma_cat K R) (@Sigma_proj1_pullback_catd K R D)))) ⊢
  Hom_cat (@Pi_cat (@Sigma_cat K R) (@Sigma_proj1_pullback_catd K R D)) s t
    ≡ @Transfd_cat K R D s t;

assert [K A : Cat] ⊢
  @Sigma_cat K (@Const_catd K A) ≡ Product_cat K A;

assert [K A : Cat]
  (x y : τ (Obj K))
  (u v : τ (Obj A)) ⊢
  @Hom_cat
    (@Sigma_cat K (@Const_catd K A))
    (Struct_sigma x u)
    (Struct_sigma y v)
    ≡ @Product_cat
        (Hom_cat K x y)
        (Hom_cat A u v);

assert [K A : Cat]
  (x y : τ (Obj K))
  (u v : τ (Obj A))
  (p : τ (Hom K x y))
  (alpha : τ (Hom A u v)) ⊢
  @sigma_arrow K (@Const_catd K A) x y u v p alpha
    ≡ @Struct_sigma
        (Obj (Hom_cat K x y))
        (λ _ : τ (Obj (Hom_cat K x y)), Obj (Hom_cat A u v))
        p
        alpha;

assert [K : Cat] (A : τ (Catd (Op_cat K))) (B : τ (Catd K)) (k : τ (Obj K)) ⊢
  Fibre_cat (Functor_catd A B) k
    ≡ Functor_cat (Fibre_cat A k) (Fibre_cat B k);

assert [K : Cat] (A : τ (Catd (Op_cat K))) (B : τ (Catd K)) ⊢
  @fapp0 (Catd_cat K) (Catd_cat K)
    (@fapp0
      (Op_cat (Catd_cat (Op_cat K)))
      (Functor_cat (Catd_cat K) (Catd_cat K))
      (@Functor_catd_func K)
      A)
    B
    ≡ Functor_catd A B;

assert [K : Cat] (E : τ (Catd K))
  (X : τ (Obj (Pi_cat (Op_catd E))))
  (Y : τ (Obj (Pi_cat E)))
  (k : τ (Obj K)) ⊢
  Fibre_cat (Hom_catd E X Y) k
    ≡ Hom_cat
        (Fibre_cat E k)
        (@piapp0 K (@Op_catd K E) X k)
        (@piapp0 K E Y k);

assert [K : Cat] (A : τ (Catd (Op_cat K))) (B : τ (Catd K))
  (FF : τ (Obj (Pi_cat (Op_catd (Functor_catd A B)))))
  (GG : τ (Obj (Pi_cat (Functor_catd A B))))
  (k : τ (Obj K)) ⊢
  Fibre_cat (Transf_catd A B FF GG) k
    ≡ Transf_cat
        (@piapp0 K (@Op_catd K (@Functor_catd K A B)) FF k)
        (@piapp0 K (@Functor_catd K A B) GG k);

assert [K : Cat]
  (X : τ (Obj (Pi_cat (Op_catd (Const_catd K Cat_cat)))))
  (Y : τ (Obj (Pi_cat (Const_catd K Cat_cat)))) ⊢
  Hom_catd (Const_catd K Cat_cat) X Y
    ≡ Functor_catd (@Op_func K (Op_cat Cat_cat) X) Y;

assert [K : Cat] (A : τ (Catd (Op_cat K))) (B : τ (Catd K))
  (FF : τ (Obj (Pi_cat (Op_catd (Functor_catd A B)))))
  (GG : τ (Obj (Pi_cat (Functor_catd A B)))) ⊢
  Hom_catd (Functor_catd A B) FF GG
    ≡ Transf_catd A B FF GG;

assert [Z : Cat] (x y : τ (Obj Z)) ⊢
  Fibre_cat (@Rep_catd Z x) y
    ≡ Hom_cat Z x y;

assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @PathOut_cat Z x
    ≡ @Sigma_cat Z (@Rep_catd Z x);

assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @fapp0 (Op_cat Z) Cat_cat (@PathOut_cat_func Z) x
    ≡ @PathOut_cat Z x;

assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @eq_refl Cat_grpd (Fibre_cat (@PathOutMotives_catd Z) x)
  : τ (@= Cat_grpd
      (Fibre_cat (@PathOutMotives_catd Z) x)
      (@Catd_cat (@PathOut_cat Z x)));

assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @fapp0
    (@Catd_cat (@PathOut_cat Z x))
    Cat_cat
    (@pathout_refl_eval_func Z x)
    (@Rep_catd (@PathOut_cat Z x) (@pathout_refl_obj Z x))
    ≡ @Fibre_cat
        (@PathOut_cat Z x)
        (@Rep_catd (@PathOut_cat Z x) (@pathout_refl_obj Z x))
        (@pathout_refl_obj Z x);

assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @tapp0_fapp0
    Z
    Cat_cat
    (@PathOutMotives_catd Z)
    (@Const_catd Z Cat_cat)
    x
    (@PathOutReflEval_funcd Z)
    ≡ @pathout_refl_eval_func Z x;

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x))) ⊢
  Fibre_cat
    (@fapp0
      (@Catd_cat (@PathOut_cat Z x))
      (@Catd_cat (@PathOut_cat Z y))
      (@fapp1_fapp0
        Z
        Cat_cat
        (@PathOutMotives_catd Z)
        x
        y
        p)
      E)
    (@pathout_refl_obj Z y)
    ≡ Fibre_cat E (@pathout_obj Z x y p);

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x))) ⊢
  @pathout_motive_transport_obj Z x y p E
    ≡ @fapp0
        (@Catd_cat (@PathOut_cat Z x))
        (@Catd_cat (@PathOut_cat Z y))
        (@fapp1_fapp0
          Z
          Cat_cat
          (@PathOutMotives_catd Z)
          x
          y
          p)
        E;

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y)) ⊢
  @PathOut_transport_func Z x y p
    ≡ @fapp1_fapp0
        (Op_cat Z)
        Cat_cat
        (@PathOut_cat_func Z)
        y
        x
        p;

assert [Z : Cat] (x y z : τ (Obj Z)) (p : τ (Hom Z x y))
  (q : τ (Hom Z y z)) ⊢
  @fapp0
    (@PathOut_cat Z y)
    (@PathOut_cat Z x)
    (@PathOut_transport_func Z x y p)
    (@pathout_obj Z y z q)
    ≡ @pathout_obj
        Z
        x
        z
        (@hom_precomp_along_fapp0 Z Z (@id_func Z) z x y p q);

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x))) ⊢
  @pathout_motive_transport_obj Z x y p E
    ≡ @Pullback_catd
        (@PathOut_cat Z y)
        (@PathOut_cat Z x)
        E
        (@PathOut_transport_func Z x y p);

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x))) ⊢
  @pathout_motive_transport_arrow Z x y p E
    ≡ @sigma_transport_arrow
        Z
        (@PathOutMotives_catd Z)
        x
        y
        p
        E;

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y)) ⊢
  @fapp0
    (@PathOut_cat Z y)
    (@PathOut_cat Z x)
    (@PathOut_transport_func Z x y p)
    (@pathout_refl_obj Z y)
    ≡ @pathout_obj Z x y p;

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y)) ⊢
  @fapp0
    (Fibre_cat (@Rep_catd Z x) x)
    (Fibre_cat (@Rep_catd Z x) y)
    (@catd_transport_func Z (@Rep_catd Z x) x y p)
    (@id Z x)
    ≡ p;

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y)) ⊢
  @pathout_refl_arrow Z x y p
    ≡ @sigma_transport_arrow
        Z
        (@Rep_catd Z x)
        x
        y
        p
        (@id Z x);

assert [Z : Cat] (x y z : τ (Obj Z)) (p : τ (Hom Z x y))
  (q : τ (Hom Z y z)) ⊢
  @fapp1_fapp0
    (@PathOut_cat Z y)
    (@PathOut_cat Z x)
    (@PathOut_transport_func Z x y p)
    (@pathout_refl_obj Z y)
    (@pathout_obj Z y z q)
    (@pathout_refl_arrow Z y z q)
    ≡ @sigma_map_transport_arrow
        Z
        (@Rep_catd Z y)
        (@Rep_catd Z x)
        (@fapp1_fapp0
          (Op_cat Z)
          (@Catd_cat Z)
          (@Rep_catd_func Z)
          y
          x
          p)
        y
        z
        q
        (@id Z y);

assert [Z : Cat] (x y z : τ (Obj Z))
  (p : τ (Hom Z x y))
  (q : τ (Hom Z y z)) ⊢
  @comp_fapp0
    (@PathOut_cat Z x)
    (@pathout_refl_obj Z x)
    (@pathout_obj Z x y p)
    (@pathout_obj
      Z
      x
      z
      (@hom_precomp_along_fapp0 Z Z (@id_func Z) z x y p q))
    (@fapp1_fapp0
      (@PathOut_cat Z y)
      (@PathOut_cat Z x)
      (@PathOut_transport_func Z x y p)
      (@pathout_refl_obj Z y)
      (@pathout_obj Z y z q)
      (@pathout_refl_arrow Z y z q))
    (@pathout_refl_arrow Z x y p)
    ≡ @Struct_sigma
        (Obj (Hom_cat Z x z))
        (λ f : τ (Obj (Hom_cat Z x z)),
          Obj
            (Hom_cat
              (Hom_cat Z x z)
              f
              (@hom_precomp_along_fapp0 Z Z (@id_func Z) z x y p q)))
        (@comp_fapp0 Z x y z q p)
        (@comp_fapp0
          (Hom_cat Z x z)
          (@comp_fapp0 Z x y z q p)
          (@hom_postcomp_fapp0 Z Z (@id_func Z) x y z q p)
          (@hom_precomp_along_fapp0 Z Z (@id_func Z) z x y p q)
          (@id
            (Hom_cat Z x z)
            (@hom_precomp_along_fapp0 Z Z (@id_func Z) z x y p q))
          (@id
            (Hom_cat Z x z)
            (@hom_postcomp_fapp0 Z Z (@id_func Z) x y z q p)));

// The same inferred identity package collapses the complete PathOut/Sigma
// fibre proof to one identity, with endpoint presentation joined at proof time.
assert [Z : Cat] (x y z : τ (Obj Z))
  (p : τ (Hom Z x y))
  (q : τ (Hom Z y z)) ⊢
  eq_refl
    (@Struct_sigma
      (Obj (Hom_cat Z x z))
      (λ f : τ (Obj (Hom_cat Z x z)),
        Obj
          (Hom_cat
            (Hom_cat Z x z)
            f
            (@hom_precomp_along_fapp0 Z Z (@id_func Z) z x y p q)))
      (@comp_fapp0 Z x y z q p)
      (@id
        (Hom_cat Z x z)
        (@hom_precomp_along_fapp0 Z Z (@id_func Z) z x y p q)))
  : τ (
      @comp_fapp0
        (@PathOut_cat Z x)
        (@pathout_refl_obj Z x)
        (@pathout_obj Z x y p)
        (@pathout_obj
          Z
          x
          z
          (@hom_precomp_along_fapp0 Z Z (@id_func Z) z x y p q))
        (@fapp1_fapp0
          (@PathOut_cat Z y)
          (@PathOut_cat Z x)
          (@PathOut_transport_func Z x y p)
          (@pathout_refl_obj Z y)
          (@pathout_obj Z y z q)
          (@pathout_refl_arrow Z y z q))
        (@pathout_refl_arrow Z x y p)
      =
      @Struct_sigma
        (Obj (Hom_cat Z x z))
        (λ f : τ (Obj (Hom_cat Z x z)),
          Obj
            (Hom_cat
              (Hom_cat Z x z)
              f
              (@hom_precomp_along_fapp0 Z Z (@id_func Z) z x y p q)))
        (@comp_fapp0 Z x y z q p)
        (@id
          (Hom_cat Z x z)
          (@hom_precomp_along_fapp0 Z Z (@id_func Z) z x y p q)));

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x))) ⊢
  @pathout_refl_eval_base_func Z x y p E
    ≡ @fapp1_fapp0
        (@PathOut_cat Z x)
        Cat_cat
        E
        (@pathout_refl_obj Z x)
        (@pathout_obj Z x y p)
        (@pathout_refl_arrow Z x y p);

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  (u : τ (Obj (Fibre_cat E (@pathout_refl_obj Z x)))) ⊢
  @fapp0
    (Fibre_cat E (@pathout_refl_obj Z x))
    (Fibre_cat E (@pathout_obj Z x y p))
    (@pathout_refl_eval_base_func Z x y p E)
    u
    ≡ @fapp0
        (Hom_cat
          (@PathOut_cat Z x)
          (@pathout_refl_obj Z x)
          (@pathout_obj Z x y p))
        (Fibre_cat E (@pathout_obj Z x y p))
        (@fib_cov_tapp0_func
          (@PathOut_cat Z x)
          E
          (@pathout_refl_obj Z x)
          (@pathout_obj Z x y p)
          u)
        (@pathout_refl_arrow Z x y p);

assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @tapp0_fapp0
    Z
    Cat_cat
    (@PathOutMotives_catd Z)
    (@Const_catd Z Cat_cat)
    x
    (@PathOutPi_funcd Z)
    ≡ @Pi_func (@PathOut_cat Z x);

assert [Z : Cat] ⊢
  @PathOutPi_funcd Z
    ≡ @Pi_pullback_funcd
        Z
        (@Op_func (Op_cat Z) Cat_cat (@PathOut_cat_func Z));

assert [Z : Cat] (x : τ (Obj Z)) (E : τ (Catd (@PathOut_cat Z x))) ⊢
  Fibre_cat (@PathIndTgt_catd Z) (Struct_sigma x E)
    ≡ @Pi_cat (@PathOut_cat Z x) E;

assert [Z : Cat] (x : τ (Obj Z)) (E : τ (Catd (@PathOut_cat Z x))) ⊢
  Fibre_cat (@PathIndSrc_catd Z) (Struct_sigma x E)
    ≡ Fibre_cat E (@pathout_refl_obj Z x);

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x))) ⊢
  Fibre_cat
    (@PathIndSrc_catd Z)
    (Struct_sigma y (@pathout_motive_transport_obj Z x y p E))
    ≡ Fibre_cat E (@pathout_obj Z x y p);

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x))) ⊢
  @PathIndSrc_transport_func Z x y p E
    ≡ @pathout_refl_eval_base_func Z x y p E;

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  (u : τ (Obj (Fibre_cat E (@pathout_refl_obj Z x)))) ⊢
  @fapp0
    (Fibre_cat (@PathIndSrc_catd Z) (Struct_sigma x E))
    (Fibre_cat
      (@PathIndSrc_catd Z)
      (Struct_sigma y (@pathout_motive_transport_obj Z x y p E)))
    (@PathIndSrc_transport_func Z x y p E)
    u
    ≡ @fapp0
        (Hom_cat
          (@PathOut_cat Z x)
          (@pathout_refl_obj Z x)
          (@pathout_obj Z x y p))
        (Fibre_cat E (@pathout_obj Z x y p))
        (@fib_cov_tapp0_func
          (@PathOut_cat Z x)
          E
          (@pathout_refl_obj Z x)
          (@pathout_obj Z x y p)
          u)
        (@pathout_refl_arrow Z x y p);

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y)) ⊢
  @pathout_obj Z x y p
    ≡ @Struct_sigma
        (Obj Z)
        (λ yy : τ (Obj Z), Obj (Fibre_cat (@Rep_catd Z x) yy))
        y
        p;

assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @pathout_refl_obj Z x
    ≡ @Struct_sigma
        (Obj Z)
        (λ yy : τ (Obj Z), Obj (Fibre_cat (@Rep_catd Z x) yy))
        x
        (@id Z x);

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y)) ⊢
  fapp0 (@Sigma_proj1_func Z (@Rep_catd Z x)) (@pathout_obj Z x y p)
    ≡ y;

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y)) ⊢
  @piapp0
    (@PathOut_cat Z x)
    (@Rep_catd (@PathOut_cat Z x) (@pathout_refl_obj Z x))
    (@pathout_refl_arrow_sec Z x)
    (@pathout_obj Z x y p)
    ≡ @pathout_refl_arrow Z x y p;

assert [Z : Cat] (D : τ (Catd Z)) (x : τ (Obj Z)) ⊢
  @eq_refl Cat_grpd
    (@Pi_cat
      (@PathOut_cat Z x)
      (@Sigma_proj1_pullback_catd Z (@Rep_catd Z x) D))
  : τ (@= Cat_grpd
      (@Pi_cat
        (@PathOut_cat Z x)
        (@Sigma_proj1_pullback_catd Z (@Rep_catd Z x) D))
      (@Functord_cat Z (@Rep_catd Z x) D));

assert [A B : Cat] (x : τ (Obj A)) (F G : τ (Functor A B))
  (η : τ (Transf F G)) ⊢
  @fapp1_fapp0
    (@Functor_cat A B)
    B
    (@fapp0_func A B x)
    F
    G
    η
    ≡ @tapp0_fapp0 A B F G x η;

assert [Z : Cat] (x : τ (Obj Z))
  (E D : τ (Catd (@PathOut_cat Z x)))
  (η : τ (Functord E D)) ⊢
  @fapp1_fapp0
    (@Catd_cat (@PathOut_cat Z x))
    Cat_cat
    (@pathout_refl_eval_func Z x)
    E
    D
    η
    ≡ @tapp0_fapp0
        (@PathOut_cat Z x)
        Cat_cat
        E
        D
        (@pathout_refl_obj Z x)
        η;

assert [Z : Cat] (D : τ (Catd Z)) (x : τ (Obj Z)) ⊢
  Fibre_cat (@FibCov_target_catd Z D) x
    ≡ @Functord_cat Z (@Rep_catd Z x) D;

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  (u : τ (Obj (Fibre_cat E (@pathout_refl_obj Z x)))) ⊢
  @piapp0
    (@PathOut_cat Z x)
    E
    (@path_ind_sec Z x E u)
    (@pathout_obj Z x y p)
    ≡ @fapp0
        (Hom_cat (@PathOut_cat Z x)
          (@pathout_refl_obj Z x)
          (@pathout_obj Z x y p))
        (Fibre_cat E (@pathout_obj Z x y p))
        (@fib_cov_tapp0_func
          (@PathOut_cat Z x)
          E
          (@pathout_refl_obj Z x)
          (@pathout_obj Z x y p)
          u)
        (@pathout_refl_arrow Z x y p);

assert [Z : Cat] (x : τ (Obj (Op_cat Z))) (y : τ (Obj Z)) ⊢
  @fapp0 Z Cat_cat
    (@fapp0 (Op_cat Z) (Catd_cat Z) (@Edge_catd_func Z) x)
    y
    ≡ Op_cat (Hom_cat Z x y);

assert [Z : Cat] (x : τ (Obj Z)) (y : τ (Obj (Op_cat Z))) ⊢
  Fibre_cat (@fapp0 Z (Catd_cat (Op_cat Z)) (@HomPresheaf_catd_func Z) x) y
    ≡ Functor_cat (Op_cat (Hom_cat Z x y)) Cat_cat;

assert [Z : Cat] (E : τ (Catd Z)) (x : τ (Obj Z)) ⊢
  @Homd_target_section_catd Z E x
    ≡ @Functor_catd
        (Op_cat Z)
        E
        (@fapp0 Z (Catd_cat (Op_cat Z)) (@HomPresheaf_catd_func Z) x);

assert [Z : Cat] (E : τ (Catd Z)) (x : τ (Obj Z)) ⊢
  @fapp0 Z Cat_cat (@Homd_target_catd Z E) x
    ≡ Pi_cat
        (Functor_catd
          E
          (@fapp0 Z (Catd_cat (Op_cat Z)) (@HomPresheaf_catd_func Z) x));

assert [K : Cat] (E : τ (Catd K)) (x : τ (Obj K)) ⊢
  Fibre_cat (@FibCov_target_catd K E) x
    ≡ @Functord_cat K (@hom_ K K (@id_func K) x) E;

assert [K : Cat] (E : τ (Catd K)) (x : τ (Obj K)) ⊢
  Obj (Fibre_cat (@FibCov_target_catd K E) x)
    ≡ @Functord K (@hom_ K K (@id_func K) x) E;

assert [K : Cat] (E : τ (Catd K)) (x : τ (Obj K)) ⊢
  @eq_refl Cat_grpd
    (@Transf_cat K Cat_cat (@hom_ K K (@id_func K) x) E)
  : τ (@= Cat_grpd
      (@Transf_cat K Cat_cat (@hom_ K K (@id_func K) x) E)
      (@Functord_cat K (@hom_ K K (@id_func K) x) E));

assert [K : Cat] (E : τ (Catd K))
  (x : τ (Obj K)) ⊢
  @tapp0_fapp0
    K
    Cat_cat
    E
    (@FibCov_target_catd K E)
    x
    (@fib_cov_int K E)
    ≡ @fib_cov_src_func K E x;

assert [K : Cat] (E : τ (Catd K))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  fapp0 (@fib_cov_src_func K E x) u
    ≡ @fib_cov_transf K E x u;

assert [K : Cat] (E : τ (Catd K))
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @tapp0_fapp0
    K
    Cat_cat
    (@hom_ K K (@id_func K) x)
    E
    y
    (@fib_cov_transf K E x u)
    ≡ @fib_cov_tapp0_func K E x y u;

assert [K : Cat] (E : τ (Catd K)) ⊢
  @Op_funcd K E E (@id_funcd K E)
    ≡ @id_funcd K (@Op_catd K E);

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D)) ⊢
  @Op_funcd K (@Op_catd K E) (@Op_catd K D) (@Op_funcd K E D FF)
    ≡ FF;

assert [K : Cat] (E D C : τ (Catd K))
  (FF : τ (Functord D C))
  (GG : τ (Functord E D)) ⊢
  @comp_fapp0 (@Catd_cat K) E D C FF GG
    ≡ @comp_catd_fapp0 K E D C FF GG;

// CATALIAS-03: generic `Catd_cat` composition owner, separate from public alias spelling.
assert [K : Cat] [E D C : τ (Catd K)]
  (FF : τ (Functord D C)) (GG : τ (Functord E D)) ⊢
  @comp_catd_fapp0 K E D C FF GG
  ≡ @comp_fapp0 (@Catd_cat K) E D C FF GG;

assert [K : Cat] (E C : τ (Catd K))
  (FF : τ (Functord E C)) ⊢
  @comp_catd_fapp0 K E E C FF (@id_funcd K E)
    ≡ FF;

// CATALIAS-02: generic `Catd_cat` identity owner, separate from public alias spelling.
assert [K : Cat] (E : τ (Catd K)) ⊢
  @id_funcd K E ≡ @id (@Catd_cat K) E;

assert [K : Cat] [E C : τ (Catd K)] (FF : τ (Functord E C)) ⊢
  @comp_catd_fapp0 K E E C FF (@id (@Catd_cat K) E) ≡ FF;

assert [K : Cat] [B : Cat] (F : τ (Functor (@Catd_cat K) B)) [E : τ (Catd K)] ⊢
  @fapp1_fapp0 (@Catd_cat K) B F E E (@id (@Catd_cat K) E)
    ≡ @id B (@fapp0 (@Catd_cat K) B F E);

assert [K : Cat] (E D : τ (Catd K))
  (GG : τ (Functord E D)) ⊢
  @comp_catd_fapp0 K E D D (@id_funcd K D) GG
    ≡ GG;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x : τ (Obj K)) ⊢
  @tapp0_fapp0
    K
    Cat_cat
    (@Op_catd K E)
    (@Op_catd K D)
    x
    (@Op_funcd K E D FF)
    ≡ @Op_func
        (Fibre_cat E x)
        (Fibre_cat D x)
        (@tapp0_fapp0 K Cat_cat E D x FF);

assert [K : Cat] (E : τ (Catd K)) (y : τ (Obj K)) ⊢
  @tapp0_fapp0 K Cat_cat E E y (@id_funcd K E)
    ≡ @id_func (Fibre_cat E y);

assert [K : Cat] (E : τ (Catd K)) (y : τ (Obj K)) ⊢
  @tapp0_fapp0 K Cat_cat E E y (@id (@Catd_cat K) E)
    ≡ @id Cat_cat (@fapp0 K Cat_cat E y);

assert [K : Cat] (E D : τ (Catd K)) (FF GG : τ (Functord E D))
  (ϵ : τ (@Transfd K E D FF GG)) ⊢
  fapp0 (@tdapp1_int_func_transfd K E D FF GG) ϵ
    ≡ @tdapp1_int_fapp0_transfd K E D FF GG ϵ;

assert [K : Cat] (E D : τ (Catd K)) (FF GG : τ (Functord E D))
  (ϵ ϵ' : τ (@Transfd K E D FF GG)) ⊢
  @fapp1_func _ _ (@tdapp1_int_func_transfd K E D FF GG) ϵ ϵ'
    ≡ @tdapp1_int_fapp1_func_transfd K E D FF GG ϵ ϵ';

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D)) ⊢
  @tdapp1_int_fapp0_transfd K E D FF FF
    (@id (@Functord_cat K E D) FF)
    ≡ @fdapp1_int_transfd K E D FF;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D)) ⊢
  @tdapp1_int_fapp0_transfd K E D FF FF
    (@id (@Transf_cat K Cat_cat E D) FF)
    ≡ @fdapp1_int_transfd K E D FF;

assert [K : Cat] (E : τ (Catd K)) (s : τ (Obj (Pi_cat E))) ⊢
  @tdapp1_int_fapp0_transfd
    K
    (@Const_catd K Terminal_cat)
    E
    s
    s
    (@id_transfd K (@Const_catd K Terminal_cat) E s)
    ≡ @fdapp1_int_transfd K (@Const_catd K Terminal_cat) E s;

assert [K : Cat] (E D : τ (Catd K)) (FF GG : τ (Functord E D))
  (z : τ (Obj K)) (ϵ : τ (@Transfd K E D FF GG)) ⊢
  fapp0 (@tdapp0_func K E D FF GG z) ϵ
    ≡ @tdapp0_fapp0 K E D FF GG z ϵ;

// Displayed component identities join through both stable category
// presentations and the generic identity owner.
assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (z : τ (Obj K)) ⊢
  @tdapp0_fapp0
      K E D FF FF z (@id (@Functord_cat K E D) FF)
    ≡ @id
        (Functor_cat (Fibre_cat E z) (Fibre_cat D z))
        (@Fibre_func K E D FF z);

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (z : τ (Obj K)) ⊢
  @tdapp0_fapp0
      K E D FF FF z (@id (@Transf_cat K Cat_cat E D) FF)
    ≡ @id
        (Functor_cat (Fibre_cat E z) (Fibre_cat D z))
        (@Fibre_func K E D FF z);

// Displayed vertical composition projects pointwise at the stable displayed
// category presentation.
assert [K : Cat] (E D : τ (Catd K))
  (FF GG HH : τ (Functord E D))
  (eta : τ (Transfd GG HH)) (epsilon : τ (Transfd FF GG))
  (z : τ (Obj K)) ⊢
  @tdapp0_fapp0 K E D FF HH z
    (@comp_fapp0
      (@Functord_cat K E D)
      FF GG HH eta epsilon)
  ≡ @comp_fapp0
      (Functor_cat (Fibre_cat E z) (Fibre_cat D z))
      (@Fibre_func K E D FF z)
      (@Fibre_func K E D GG z)
      (@Fibre_func K E D HH z)
      (@tdapp0_fapp0 K E D GG HH z eta)
      (@tdapp0_fapp0 K E D FF GG z epsilon);

// The proof-time-comparable ordinary category presentation reaches the same
// runtime pointwise normal form through its own typed clause.
assert [K : Cat] (E D : τ (Catd K))
  (FF GG HH : τ (Functord E D))
  (eta : τ (Transfd GG HH)) (epsilon : τ (Transfd FF GG))
  (z : τ (Obj K)) ⊢
  @tdapp0_fapp0 K E D FF HH z
    (@comp_fapp0
      (@Transf_cat K Cat_cat E D)
      FF GG HH eta epsilon)
  ≡ @comp_fapp0
      (Functor_cat (Fibre_cat E z) (Fibre_cat D z))
      (@Fibre_func K E D FF z)
      (@Fibre_func K E D GG z)
      (@Fibre_func K E D HH z)
      (@tdapp0_fapp0 K E D GG HH z eta)
      (@tdapp0_fapp0 K E D FF GG z epsilon);

// The generic Cat-valued component action on a composite joins the direct
// stable displayed projection.
assert [K : Cat] (E D : τ (Catd K))
  (FF GG HH : τ (Functord E D))
  (eta : τ (Transfd GG HH)) (epsilon : τ (Transfd FF GG))
  (z : τ (Obj K)) ⊢
  @fapp1_fapp0
      (@Transf_cat K Cat_cat E D)
      (Functor_cat (Fibre_cat E z) (Fibre_cat D z))
      (@tapp0_func K Cat_cat E D z)
      FF HH
      (@comp_fapp0
        (@Transf_cat K Cat_cat E D)
        FF GG HH eta epsilon)
  ≡ @comp_fapp0
      (Functor_cat (Fibre_cat E z) (Fibre_cat D z))
      (@Fibre_func K E D FF z)
      (@Fibre_func K E D GG z)
      (@Fibre_func K E D HH z)
      (@tdapp0_fapp0 K E D GG HH z eta)
      (@tdapp0_fapp0 K E D FF GG z epsilon);

// Generic strict-action-first and operand-projection-first reduction orders
// join at the pointwise displayed component normal form.
assert [K : Cat] (E D : τ (Catd K))
  (FF GG HH : τ (Functord E D))
  (eta : τ (Transfd GG HH)) (epsilon : τ (Transfd FF GG))
  (z : τ (Obj K)) ⊢
  @comp_fapp0
      (Functor_cat (Fibre_cat E z) (Fibre_cat D z))
      (@Fibre_func K E D FF z)
      (@Fibre_func K E D GG z)
      (@Fibre_func K E D HH z)
      (@fapp1_fapp0
        (@Transf_cat K Cat_cat E D)
        (Functor_cat (Fibre_cat E z) (Fibre_cat D z))
        (@tapp0_func K Cat_cat E D z)
        GG HH eta)
      (@fapp1_fapp0
        (@Transf_cat K Cat_cat E D)
        (Functor_cat (Fibre_cat E z) (Fibre_cat D z))
        (@tapp0_func K Cat_cat E D z)
        FF GG epsilon)
  ≡ @tdapp0_fapp0 K E D FF HH z
      (@comp_fapp0
        (@Transf_cat K Cat_cat E D)
        FF GG HH eta epsilon);

// The projection beta is coherent with the existing generic right-identity
// cut and the displayed component-of-identity rule.
assert [K : Cat] (E D : τ (Catd K))
  (FF GG : τ (Functord E D))
  (eta : τ (Transfd FF GG))
  (z : τ (Obj K)) ⊢
  @tdapp0_fapp0 K E D FF GG z
    (@comp_fapp0
      (@Functord_cat K E D)
      FF FF GG eta (@id (@Functord_cat K E D) FF))
  ≡ @tdapp0_fapp0 K E D FF GG z eta;

// The ordinary category presentation also joins the generic left-identity
// cut after pointwise projection.
assert [K : Cat] (E D : τ (Catd K))
  (FF GG : τ (Functord E D))
  (eta : τ (Transfd FF GG))
  (z : τ (Obj K)) ⊢
  @tdapp0_fapp0 K E D FF GG z
    (@comp_fapp0
      (@Transf_cat K Cat_cat E D)
      FF GG GG (@id (@Transf_cat K Cat_cat E D) GG) eta)
  ≡ @tdapp0_fapp0 K E D FF GG z eta;

// Product-valued target normalization must not prevent selection of the
// pointwise projection beta.
assert [K A B C : Cat]
  (FF GG HH : τ (Functord
    (@Const_catd K C)
    (@Const_catd K (Product_cat A B))))
  (eta : τ (Transfd GG HH)) (epsilon : τ (Transfd FF GG))
  (z : τ (Obj K)) ⊢
  @tdapp0_fapp0
      K
      (@Const_catd K C)
      (@Const_catd K (Product_cat A B))
      FF HH z
      (@comp_fapp0
        (@Functord_cat
          K
          (@Const_catd K C)
          (@Const_catd K (Product_cat A B)))
        FF GG HH eta epsilon)
  ≡ @comp_fapp0
      (Functor_cat C (Product_cat A B))
      (@Fibre_func K
        (@Const_catd K C)
        (@Const_catd K (Product_cat A B)) FF z)
      (@Fibre_func K
        (@Const_catd K C)
        (@Const_catd K (Product_cat A B)) GG z)
      (@Fibre_func K
        (@Const_catd K C)
        (@Const_catd K (Product_cat A B)) HH z)
      (@tdapp0_fapp0 K
        (@Const_catd K C)
        (@Const_catd K (Product_cat A B)) GG HH z eta)
      (@tdapp0_fapp0 K
        (@Const_catd K C)
        (@Const_catd K (Product_cat A B)) FF GG z epsilon);

// One further ordinary component projection preserves the same pointwise
// vertical-composition orientation at the next iterated-hom rung.
assert [K : Cat] (E D : τ (Catd K))
  (FF GG HH : τ (Functord E D))
  (eta : τ (Transfd GG HH)) (epsilon : τ (Transfd FF GG))
  (z : τ (Obj K)) (u : τ (Obj (Fibre_cat E z))) ⊢
  @tapp0_fapp0
      (Fibre_cat E z)
      (Fibre_cat D z)
      (@Fibre_func K E D FF z)
      (@Fibre_func K E D HH z)
      u
      (@tdapp0_fapp0 K E D FF HH z
        (@comp_fapp0
          (@Functord_cat K E D)
          FF GG HH eta epsilon))
  ≡ @comp_fapp0
      (Fibre_cat D z)
      (@fapp0
        (Fibre_cat E z)
        (Fibre_cat D z)
        (@Fibre_func K E D FF z)
        u)
      (@fapp0
        (Fibre_cat E z)
        (Fibre_cat D z)
        (@Fibre_func K E D GG z)
        u)
      (@fapp0
        (Fibre_cat E z)
        (Fibre_cat D z)
        (@Fibre_func K E D HH z)
        u)
      (@tapp0_fapp0
        (Fibre_cat E z)
        (Fibre_cat D z)
        (@Fibre_func K E D GG z)
        (@Fibre_func K E D HH z)
        u
        (@tdapp0_fapp0 K E D GG HH z eta))
      (@tapp0_fapp0
        (Fibre_cat E z)
        (Fibre_cat D z)
        (@Fibre_func K E D FF z)
        (@Fibre_func K E D GG z)
        u
        (@tdapp0_fapp0 K E D FF GG z epsilon));

// Cat-valued component evaluation retains its full hom functor through the
// stable displayed component projection.
assert [K : Cat] (E D : τ (Catd K))
  (FF GG : τ (Functord E D))
  (z : τ (Obj K)) ⊢
  @fapp1_func
    (@Transf_cat K Cat_cat E D)
    (Functor_cat (Fibre_cat E z) (Fibre_cat D z))
    (@tapp0_func K Cat_cat E D z)
    FF
    GG
  ≡ @tdapp0_func K E D FF GG z;

// Projection-first and generic-first pre/right naturality have the same
// off-diagonal component normal form.
assert [K : Cat] (E D : τ (Catd K))
  (FF GG HH : τ (Functord E D))
  (z : τ (Obj K))
  (G : τ (Functor
        (@Transf_cat K Cat_cat E D)
        (Functor_cat (Fibre_cat E z) (Fibre_cat D z))))
  (epsilon : τ (@Transf
        (@Transf_cat K Cat_cat E D)
        (Functor_cat (Fibre_cat E z) (Fibre_cat D z))
        (@tapp0_func K Cat_cat E D z)
        G))
  (f : τ (Transfd GG HH))
  (g : τ (Transfd FF GG)) ⊢
  comp_fapp0
    (@tapp1_fapp0
      (@Transf_cat K Cat_cat E D)
      (Functor_cat (Fibre_cat E z) (Fibre_cat D z))
      (@tapp0_func K Cat_cat E D z)
      G GG HH epsilon f)
    (@tdapp0_fapp0 K E D FF GG z g)
  ≡ @tapp1_fapp0
      (@Transf_cat K Cat_cat E D)
      (Functor_cat (Fibre_cat E z) (Fibre_cat D z))
      (@tapp0_func K Cat_cat E D z)
      G FF HH epsilon
      (@comp_fapp0
        (@Transf_cat K Cat_cat E D)
        FF GG HH f g);

// The naturality bridge survives when the target fibre is product-valued and
// the outer functor category has already reduced to a product category.
assert [K A B C : Cat]
  (FF GG HH : τ (Functord
        (@Const_catd K C)
        (@Const_catd K (Product_cat A B))))
  (z : τ (Obj K))
  (G : τ (Functor
        (@Transf_cat K Cat_cat
          (@Const_catd K C)
          (@Const_catd K (Product_cat A B)))
        (Functor_cat C (Product_cat A B))))
  (epsilon : τ (@Transf
        (@Transf_cat K Cat_cat
          (@Const_catd K C)
          (@Const_catd K (Product_cat A B)))
        (Functor_cat C (Product_cat A B))
        (@tapp0_func K Cat_cat
          (@Const_catd K C)
          (@Const_catd K (Product_cat A B)) z)
        G))
  (f : τ (@Transfd K
        (@Const_catd K C)
        (@Const_catd K (Product_cat A B)) GG HH))
  (g : τ (@Transfd K
        (@Const_catd K C)
        (@Const_catd K (Product_cat A B)) FF GG)) ⊢
  comp_fapp0
    (@tapp1_fapp0
      (@Transf_cat K Cat_cat
        (@Const_catd K C)
        (@Const_catd K (Product_cat A B)))
      (Functor_cat C (Product_cat A B))
      (@tapp0_func K Cat_cat
        (@Const_catd K C)
        (@Const_catd K (Product_cat A B)) z)
      G GG HH epsilon f)
    (@tdapp0_fapp0 K
      (@Const_catd K C)
      (@Const_catd K (Product_cat A B)) FF GG z g)
  ≡ @tapp1_fapp0
      (@Transf_cat K Cat_cat
        (@Const_catd K C)
        (@Const_catd K (Product_cat A B)))
      (Functor_cat C (Product_cat A B))
      (@tapp0_func K Cat_cat
        (@Const_catd K C)
        (@Const_catd K (Product_cat A B)) z)
      G FF HH epsilon
      (@comp_fapp0
        (@Transf_cat K Cat_cat
          (@Const_catd K C)
          (@Const_catd K (Product_cat A B)))
        FF GG HH f g);

// Post/left naturality has the mirror projection-order join.
assert [K : Cat] (E D : τ (Catd K))
  (FF GG HH : τ (Functord E D))
  (z : τ (Obj K))
  (F : τ (Functor
        (@Transf_cat K Cat_cat E D)
        (Functor_cat (Fibre_cat E z) (Fibre_cat D z))))
  (epsilon : τ (@Transf
        (@Transf_cat K Cat_cat E D)
        (Functor_cat (Fibre_cat E z) (Fibre_cat D z))
        F
        (@tapp0_func K Cat_cat E D z)))
  (g : τ (Transfd GG HH))
  (f : τ (Transfd FF GG)) ⊢
  comp_fapp0
    (@tdapp0_fapp0 K E D GG HH z g)
    (@tapp1_fapp0
      (@Transf_cat K Cat_cat E D)
      (Functor_cat (Fibre_cat E z) (Fibre_cat D z))
      F (@tapp0_func K Cat_cat E D z)
      FF GG epsilon f)
  ≡ @tapp1_fapp0
      (@Transf_cat K Cat_cat E D)
      (Functor_cat (Fibre_cat E z) (Fibre_cat D z))
      F (@tapp0_func K Cat_cat E D z)
      FF HH epsilon
      (@comp_fapp0
        (@Transf_cat K Cat_cat E D)
        FF GG HH g f);

// If tapp1(epsilon,id) reduces first, the ordinary tapp0 component still
// joins the same pre/right naturality result.
assert [K : Cat] (E D : τ (Catd K))
  (FF GG : τ (Functord E D))
  (z : τ (Obj K))
  (G : τ (Functor
        (@Transf_cat K Cat_cat E D)
        (Functor_cat (Fibre_cat E z) (Fibre_cat D z))))
  (epsilon : τ (@Transf
        (@Transf_cat K Cat_cat E D)
        (Functor_cat (Fibre_cat E z) (Fibre_cat D z))
        (@tapp0_func K Cat_cat E D z)
        G))
  (g : τ (Transfd FF GG)) ⊢
  comp_fapp0
    (@tapp0_fapp0
      (@Transf_cat K Cat_cat E D)
      (Functor_cat (Fibre_cat E z) (Fibre_cat D z))
      (@tapp0_func K Cat_cat E D z)
      G GG epsilon)
    (@tdapp0_fapp0 K E D FF GG z g)
  ≡ @tapp1_fapp0
      (@Transf_cat K Cat_cat E D)
      (Functor_cat (Fibre_cat E z) (Fibre_cat D z))
      (@tapp0_func K Cat_cat E D z)
      G FF GG epsilon g;

// Identity-base post/left naturality joins symmetrically.
assert [K : Cat] (E D : τ (Catd K))
  (FF GG : τ (Functord E D))
  (z : τ (Obj K))
  (F : τ (Functor
        (@Transf_cat K Cat_cat E D)
        (Functor_cat (Fibre_cat E z) (Fibre_cat D z))))
  (epsilon : τ (@Transf
        (@Transf_cat K Cat_cat E D)
        (Functor_cat (Fibre_cat E z) (Fibre_cat D z))
        F
        (@tapp0_func K Cat_cat E D z)))
  (g : τ (Transfd FF GG)) ⊢
  comp_fapp0
    (@tdapp0_fapp0 K E D FF GG z g)
    (@tapp0_fapp0
      (@Transf_cat K Cat_cat E D)
      (Functor_cat (Fibre_cat E z) (Fibre_cat D z))
      F (@tapp0_func K Cat_cat E D z)
      FF epsilon)
  ≡ @tapp1_fapp0
      (@Transf_cat K Cat_cat E D)
      (Functor_cat (Fibre_cat E z) (Fibre_cat D z))
      F (@tapp0_func K Cat_cat E D z)
      FF GG epsilon g;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (z : τ (Obj K)) ⊢
  @Fibre_func K E D FF z
    ≡ @tapp0_fapp0 K Cat_cat E D z FF;

assert [K : Cat] (E : τ (Catd K)) (z : τ (Obj K)) ⊢
  @Fibre_func K E E (@id_funcd K E) z
    ≡ @id_func (Fibre_cat E z);

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (z : τ (Obj K)) ⊢
  @Fibre_func
    K
    (@Op_catd K E)
    (@Op_catd K D)
    (@Op_funcd K E D FF)
    z
    ≡ @Op_func
        (Fibre_cat E z)
        (Fibre_cat D z)
        (@Fibre_func K E D FF z);

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (z : τ (Obj K))
  (u : τ (Obj (Fibre_cat (@Op_catd K E) z))) ⊢
  @fapp0
    (Fibre_cat (@Op_catd K E) z)
    (Fibre_cat (@Op_catd K D) z)
    (@Fibre_func K (@Op_catd K E) (@Op_catd K D) (@Op_funcd K E D FF) z)
    u
    ≡ @fapp0
        (Fibre_cat E z)
        (Fibre_cat D z)
        (@Fibre_func K E D FF z)
        u;

assert [K : Cat] (E D : τ (Catd K)) (FF GG : τ (Functord E D))
  (ϵ : τ (@Transfd K E D FF GG)) (z : τ (Obj K)) ⊢
  @Fibre_transf K E D FF GG ϵ z
    ≡ @tdapp0_fapp0 K E D FF GG z ϵ;

assert [K : Cat] (E D : τ (Catd K)) (FF GG : τ (Functord E D))
  (ϵ : τ (@Transfd K E D FF GG))
  (z : τ (Obj K))
  (u : τ (Obj (Fibre_cat E z))) ⊢
  @Fibre_transf_app K E D FF GG ϵ z u
    ≡ @tapp0_fapp0
        (Fibre_cat E z)
        (Fibre_cat D z)
        (@Fibre_func K E D FF z)
        (@Fibre_func K E D GG z)
        u
        (@Fibre_transf K E D FF GG ϵ z);

assert [K : Cat] (E : τ (Catd K))
  (x y : τ (Obj K))
  (p : τ (Hom K x y)) ⊢
  @catd_transport_func K E x y p
    ≡ @fapp1_fapp0 K Cat_cat E x y p;

assert [K : Cat] (E : τ (Catd K))
  (x y z : τ (Obj K))
  (p : τ (Hom K x y))
  (q : τ (Hom K y z))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @fapp0
    (Fibre_cat E y)
    (Fibre_cat E z)
    (@catd_transport_func K E y z q)
    (@fapp0
      (Fibre_cat E x)
      (Fibre_cat E y)
      (@catd_transport_func K E x y p)
      u)
    ≡ @fapp0
        (Fibre_cat E x)
        (Fibre_cat E z)
        (@catd_transport_func K E x z (@comp_fapp0 K x y z q p))
        u;

assert [K : Cat] (E : τ (Catd K))
  (x y z : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y)))
  (w : τ (Obj (Fibre_cat E z)))
  (p : τ (Hom K x y))
  (q : τ (Hom K y z))
  (alpha : τ (Hom
      (Fibre_cat E y)
      (@fapp0
        (Fibre_cat E x)
        (Fibre_cat E y)
        (@catd_transport_func K E x y p)
        u)
      v))
  (beta : τ (Hom
      (Fibre_cat E z)
      (@fapp0
        (Fibre_cat E y)
        (Fibre_cat E z)
        (@catd_transport_func K E y z q)
        v)
      w)) ⊢
  @comp_fapp0
    (@Sigma_cat K E)
    (Struct_sigma x u)
    (Struct_sigma y v)
    (Struct_sigma z w)
    (@sigma_arrow K E y z v w q beta)
    (@sigma_arrow K E x y u v p alpha)
    ≡ @sigma_arrow
        K
        E
        x
        z
        u
        w
        (@comp_fapp0 K x y z q p)
        (@comp_fapp0
          (Fibre_cat E z)
          (@fapp0
            (Fibre_cat E x)
            (Fibre_cat E z)
            (@catd_transport_func K E x z (@comp_fapp0 K x y z q p))
            u)
          (@fapp0
            (Fibre_cat E y)
            (Fibre_cat E z)
            (@catd_transport_func K E y z q)
            v)
          w
          beta
          (@fapp1_fapp0
            (Fibre_cat E y)
            (Fibre_cat E z)
            (@catd_transport_func K E y z q)
            (@fapp0
              (Fibre_cat E x)
              (Fibre_cat E y)
              (@catd_transport_func K E x y p)
              u)
            v
            alpha));

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K))
  (p : τ (Hom K x y)) ⊢
  @functord_transport_func K E D FF x y p
    ≡ @tapp1_fapp0 K Cat_cat E D x y FF p;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @fapp0
    (Fibre_cat E x)
    (Fibre_cat D y)
    (@functord_transport_lhs_func K E D FF x y p)
    u
    ≡ @fapp0
        (Fibre_cat D x)
        (Fibre_cat D y)
        (@catd_transport_func K D x y p)
        (@fapp0
          (Fibre_cat E x)
          (Fibre_cat D x)
          (@Fibre_func K E D FF x)
          u);

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @fapp0
    (Fibre_cat E x)
    (Fibre_cat D y)
    (@functord_transport_rhs_func K E D FF x y p)
    u
    ≡ @fapp0
        (Fibre_cat E y)
        (Fibre_cat D y)
        (@Fibre_func K E D FF y)
        (@fapp0
          (Fibre_cat E x)
          (Fibre_cat E y)
          (@catd_transport_func K E x y p)
          u);

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @fapp0
    (Fibre_cat E x)
    (Fibre_cat D y)
    (@functord_transport_lhs_func K E D FF x y p)
    u
    ≡ @fapp0
        (Fibre_cat E x)
        (Fibre_cat D y)
        (@functord_transport_func K E D FF x y p)
        u;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @fapp0
    (Fibre_cat E x)
    (Fibre_cat D y)
    (@functord_transport_rhs_func K E D FF x y p)
    u
    ≡ @fapp0
        (Fibre_cat E x)
        (Fibre_cat D y)
        (@functord_transport_func K E D FF x y p)
        u;

assert [K : Cat] (R : τ (Catd K))
  (FF : τ (Functord R (@Const_catd K Cat_cat)))
  (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (r : τ (Obj (Fibre_cat R x))) ⊢
  @fapp1_fapp0
    (@Sigma_cat K R)
    Cat_cat
    (@Sigma_catd_functord_catd K R FF)
    (Struct_sigma x r)
    (Struct_sigma y
      (@fapp0
        (Fibre_cat R x)
        (Fibre_cat R y)
        (@catd_transport_func K R x y p)
        r))
    (@sigma_transport_arrow K R x y p r)
    ≡ @Sigma_catd_transport_func K R FF x y p r;

assert [Z : Cat] (D E : τ (Catd Z)) (FF : τ (Functord D E))
  (x : τ (Obj Z)) ⊢
  @tapp0_fapp0
    Z
    Cat_cat
    (@Op_catd Z E)
    (@Homd_target_catd Z D)
    x
    (@homd_int Z D E FF)
    ≡ @homd_src_func Z D E FF x;

assert [Z : Cat] (D E : τ (Catd Z)) (FF : τ (Functord D E))
  (x : τ (Obj Z)) ⊢
  @Fibre_func
    Z
    (@Op_catd Z E)
    (@Homd_target_catd Z D)
    (@homd_int Z D E FF)
    x
    ≡ @homd_src_func Z D E FF x;

assert [Z : Cat] (D E : τ (Catd Z)) (FF : τ (Functord D E))
  (x : τ (Obj Z))
  (u : τ (Obj (Fibre_cat (@Op_catd Z E) x))) ⊢
  @fapp0
    (Fibre_cat (@Op_catd Z E) x)
    (Fibre_cat (@Homd_target_catd Z D) x)
    (@Fibre_func Z (@Op_catd Z E) (@Homd_target_catd Z D) (@homd_int Z D E FF) x)
    u
    ≡ @homd_src_sec Z D E FF x u;

assert [Z : Cat] (E : τ (Catd Z))
  (x : τ (Obj Z)) ⊢
  @tapp0_fapp0
    Z
    Cat_cat
    (@Op_catd Z E)
    (@Homd_target_catd Z E)
    x
    (@homd_int Z E E (@id_funcd Z E))
    ≡ @homd_src_func Z E E (@id_funcd Z E) x;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D)) ⊢
  fapp0 (@tdapp1_int_func_transfd K E D FF FF)
    (@id (@Functord_cat K E D) FF)
    ≡ @fdapp1_int_transfd K E D FF;

assert [Z : Cat] (D E : τ (Catd Z)) (FF : τ (Functord D E))
  (x : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  fapp0 (@homd_src_func Z D E FF x) u
    ≡ @homd_src_sec Z D E FF x u;

assert [Z : Cat] (E : τ (Catd Z))
  (x : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  fapp0 (@homd_src_func Z E E (@id_funcd Z E) x) u
    ≡ @homd_src_sec Z E E (@id_funcd Z E) x u;

assert [K : Cat] (x : τ (Obj K)) ⊢
  @homd_src_func K
    (@Const_catd K Terminal_cat)
    (@Const_catd K Terminal_cat)
    (@id_funcd K (@Const_catd K Terminal_cat))
    x
    ≡ @Obj_func
        (Pi_cat (@Homd_target_section_catd K (@Const_catd K Terminal_cat) x))
        (@homd_src_sec K
          (@Const_catd K Terminal_cat)
          (@Const_catd K Terminal_cat)
          (@id_funcd K (@Const_catd K Terminal_cat))
          x
          Terminal_obj);

assert [K : Cat] (x : τ (Obj K)) ⊢
  @Fibre_func
    K
    (@Op_catd K (@Const_catd K Terminal_cat))
    (@Homd_target_catd K (@Const_catd K Terminal_cat))
    (@homd_int
      K
      (@Const_catd K Terminal_cat)
      (@Const_catd K Terminal_cat)
      (@id_funcd K (@Const_catd K Terminal_cat)))
    x
    ≡ @Obj_func
        (Pi_cat (@Homd_target_section_catd K (@Const_catd K Terminal_cat) x))
        (@homd_src_sec K
          (@Const_catd K Terminal_cat)
          (@Const_catd K Terminal_cat)
          (@id_funcd K (@Const_catd K Terminal_cat))
          x
          Terminal_obj);

assert [Z : Cat] (D E : τ (Catd Z)) (FF : τ (Functord D E))
  (x y : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @piapp0
    (Op_cat Z)
    (@Functor_catd
      (Op_cat Z)
      D
      (@fapp0 Z (Catd_cat (Op_cat Z)) (@HomPresheaf_catd_func Z) x))
    (@homd_src_sec Z D E FF x u)
    y
    ≡ @homd_tgt_func Z D E FF x u y;

assert [Z : Cat] (E : τ (Catd Z))
  (x y : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @piapp0
    (Op_cat Z)
    (@Functor_catd
      (Op_cat Z)
      E
      (@fapp0 Z (Catd_cat (Op_cat Z)) (@HomPresheaf_catd_func Z) x))
    (@homd_src_sec Z E E (@id_funcd Z E) x u)
    y
    ≡ @homd_tgt_func Z E E (@id_funcd Z E) x u y;

assert [Z : Cat] (E : τ (Catd Z))
  (x y : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y))) ⊢
  fapp0 (@homd_tgt_func Z E E (@id_funcd Z E) x u y) v
    ≡ @homd_ Z E E (@id_funcd Z E) x u y v;

assert [K : Cat] (x y : τ (Obj K)) ⊢
  @homd_tgt_func K
    (@Const_catd K Terminal_cat)
    (@Const_catd K Terminal_cat)
    (@id_funcd K (@Const_catd K Terminal_cat))
    x
    Terminal_obj
    y
    ≡ @Obj_func
        (Fibre_cat
          (@fapp0 K (Catd_cat (Op_cat K)) (@HomPresheaf_catd_func K) x)
          y)
        (@Terminal_catd (Op_cat (Hom_cat K x y)));

assert [K : Cat] (E : τ (Catd K)) (s : τ (Obj (Pi_cat E)))
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @homd_tgt_func K (@Const_catd K Terminal_cat) E s x u y
    ≡ @Obj_func
        (Fibre_cat
          (@fapp0 K (Catd_cat (Op_cat K)) (@HomPresheaf_catd_func K) x)
          y)
        (@homd_
          K
          E
          E
          (@id_funcd K E)
          x
          u
          y
          (@piapp0 K E s y));

assert [K : Cat] (E : τ (Catd K)) (s : τ (Obj (Pi_cat E)))
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @piapp0
    (Op_cat K)
    (@Homd_target_section_catd K (@Const_catd K Terminal_cat) x)
    (@homd_src_sec K (@Const_catd K Terminal_cat) E s x u)
    y
    ≡ @Obj_func
        (Fibre_cat
          (@fapp0 K (Catd_cat (Op_cat K)) (@HomPresheaf_catd_func K) x)
          y)
        (@homd_
          K
          E
          E
          (@id_funcd K E)
          x
          u
          y
          (@piapp0 K E s y));

assert [K : Cat] (E : τ (Catd K)) (s : τ (Obj (Pi_cat E)))
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  fapp0 (@homd_tgt_func K (@Const_catd K Terminal_cat) E s x u y) Terminal_obj
    ≡ @homd_
        K
        E
        E
        (@id_funcd K E)
        x
        u
        y
        (@piapp0 K E s y);

// catalog-area: auto

assert [K : Cat] (E : τ (Catd K)) (s : τ (Obj (Pi_cat E)))
  (x y : τ (Obj K)) ⊢
  fapp0
    (@piapp0
      (Op_cat K)
      (@Homd_target_section_catd K (@Const_catd K Terminal_cat) x)
      (@homd_src_sec
        K
        (@Const_catd K Terminal_cat)
        E
        s
        x
        (@piapp0 K E s x))
      y)
    Terminal_obj
    ≡ @homd_
        K
        E
        E
        (@id_funcd K E)
        x
        (@piapp0 K E s x)
        y
        (@piapp0 K E s y);

// catalog-area: Categorical-universe direct equality-valued

// Public category-universe equality now has the stable equality-valued facade normal form.
assert [A B : Cat] ⊢
  @= (Obj Cat_cat) A B
  ≡ @OmegaEquiv Cat_cat A B;

assert [A B : Cat]
  (p : τ (@= (Obj Cat_cat) A B)) ⊢
  p : τ (@OmegaEquiv Cat_cat A B);

assert [A B : Cat]
  (e : τ (@OmegaEquiv Cat_cat A B)) ⊢
  e : τ (@= (Obj Cat_cat) A B);

// Explicit equality-valued reflexivity is computational; raw equality reflexivity keeps
// its separate generic-J normal form.
assert [A : Cat] ⊢
  @omega_equiv_refl Cat_cat A
  : τ (@= (Obj Cat_cat) A A);

assert [A : Cat] ⊢
  @eq_refl (Obj Cat_cat) A
  : τ (@OmegaEquiv Cat_cat A A);

assert [A : Cat] ⊢
  @omega_equiv_to Cat_cat A A
    (@omega_equiv_refl Cat_cat A)
  ≡ @id_func A;

assert [A : Cat] ⊢
  @omega_equiv_evidence Cat_cat A A
    (@omega_equiv_refl Cat_cat A)
  ≡ @omega_equiv_along_refl Cat_cat A;

// The native self-universe facade remains finite.
assert ⊢
  @= (Obj Cat_cat) Cat_cat Cat_cat
  ≡ @OmegaEquiv Cat_cat Cat_cat Cat_cat;

assert [A : Cat] ⊢
  @ind_eqr
    (Obj Cat_cat)
    A
    (λ X : Cat, λ _ : τ (@= (Obj Cat_cat) X A), Unit_grpd)
    tt
    A
    (@eq_refl (Obj Cat_cat) A)
  ≡ tt;

// Native provenance boundaries remain explicit.
assertnot [A : Cat] ⊢
  @eq_refl (Obj Cat_cat) A
  ≡ @omega_equiv_refl Cat_cat A;

assertnot [A : Cat] ⊢
  @omega_equiv_to
    Cat_cat A A (@eq_refl (Obj Cat_cat) A)
  ≡ @id_func A;

assertnot [A : Cat] ⊢
  @ind_eqr
    (Obj Cat_cat)
    A
    (λ X : Cat, λ _ : τ (@= (Obj Cat_cat) X A), Unit_grpd)
    tt
    A
    (@omega_equiv_refl Cat_cat A)
  ≡ tt;

// catalog-area: auto

assert [K : Cat] (x y : τ (Obj K)) ⊢
  fapp0
    (@homd_tgt_func K
      (@Const_catd K Terminal_cat)
      (@Const_catd K Terminal_cat)
      (@id_funcd K (@Const_catd K Terminal_cat))
      x
      Terminal_obj
      y)
    Terminal_obj
    ≡ @Terminal_catd (Op_cat (Hom_cat K x y));

assert [Z : Cat] (D E : τ (Catd Z)) (FF : τ (Functord D E))
  (x y : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat D y))) ⊢
  fapp0 (@homd_tgt_func Z D E FF x u y) v
    ≡ @homd_ Z D E FF x u y v;

assert [Z : Cat] (D E : τ (Catd Z)) (FF : τ (Functord D E))
  (x y : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat D y))) ⊢
  @homd_ Z D E FF x u y v
    ≡ @hom_con
        (Fibre_cat E y)
        (@fapp0
          (Fibre_cat D y)
          (Fibre_cat E y)
          (@tapp0_fapp0 Z Cat_cat D E y FF)
        v)
        (Hom_cat Z x y)
        (@fib_cov_tapp0_func Z E x y u);

assert [Z : Cat] (E : τ (Catd Z))
  (x y : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y))) ⊢
  @homd_ Z E E (@id_funcd Z E) x u y v
    ≡ @hom_con
        (Fibre_cat E y)
        v
        (Hom_cat Z x y)
        (@fib_cov_tapp0_func Z E x y u);

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  fapp0
    (@fdapp1_int_hom_func K E D FF x y p u _)
    (@id
      (@fapp0 K Cat_cat E y)
      (fapp0 (@fapp1_fapp0 K Cat_cat E x y p) u))
    ≡ @fdapp1_int_cell K E D FF x y p u;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  fapp0
    (@fdapp1_int_hom_func
      K E D FF x y p u
      (fapp0 (@fapp1_fapp0 K Cat_cat E x y p) u))
    (@id
      (@fapp0 K Cat_cat E y)
      (fapp0 (@fapp1_fapp0 K Cat_cat E x y p) u))
    ≡ @fdapp1_int_cell K E D FF x y p u;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @fdapp1_int_hom_fapp0
    K
    E
    D
    FF
    x
    y
    p
    u
    (fapp0 (@fapp1_fapp0 K Cat_cat E x y p) u)
    (@id
      (@fapp0 K Cat_cat E y)
      (fapp0 (@fapp1_fapp0 K Cat_cat E x y p) u))
    ≡ @fdapp1_int_cell K E D FF x y p u;

// Terminal-source displayed laxity now compares with ordinary action only at
// proof time; the transparent theorem exercises the typed unification rule.
assert [K A : Cat]
  (s : τ (Functord
      (@Const_catd K Terminal_cat)
      (@Const_catd K A)))
  (x y : τ (Obj K))
  (p : τ (Hom K x y)) ⊢
  @terminal_fdapp1_int_cell_eq K A s x y p
  : τ (@=
      (Hom A
        (@fapp0 K A s x)
        (@fapp0 K A s y))
      (@fdapp1_int_cell
        K
        (@Const_catd K Terminal_cat)
        (@Const_catd K A)
        s x y p Terminal_obj)
      (@fapp1_fapp0 K A s x y p));

// The comparison deliberately does not select a runtime normal form.
assertnot [K A : Cat]
  (s : τ (Functord
      (@Const_catd K Terminal_cat)
      (@Const_catd K A)))
  (x y : τ (Obj K))
  (p : τ (Hom K x y)) ⊢
  @fdapp1_int_cell
      K
      (@Const_catd K Terminal_cat)
      (@Const_catd K A)
      s x y p Terminal_obj
  ≡ @fapp1_fapp0 K A s x y p;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @Fibre_transf_app
    K
    (@Op_catd K E)
    (@Homd_target_catd K E)
    (@homd_int K E E (@id_funcd K E))
    (@comp_catd_fapp0
      K
      (@Op_catd K E)
      (@Op_catd K D)
      (@Homd_target_catd K E)
      (@homd_int K E D FF)
      (@Op_funcd K E D FF))
    (@fdapp1_int_transfd K E D FF)
    x
    u
    ≡ @fdapp1_int_section_arrow K E D FF x u;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  tapp0_fapp0
    Terminal_obj
    (tdapp0_fapp0 y (@fdapp1_int_section_arrow K E D FF x u))
    ≡ @fdapp1_int_tgt_arrow K E D FF x u y;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y))) ⊢
  @tapp0_fapp0
    (Fibre_cat E y)
    (Functor_cat (Op_cat (Hom_cat K x y)) Cat_cat)
    (@homd_id_tgt_func K E x u y)
    (@homd_ff_tgt_func K E D FF x u y)
    v
    (@fdapp1_int_tgt_arrow K E D FF x u y)
    ≡ @fdapp1_int_presheaf_arrow K E D FF x u y v;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y))) ⊢
  @fapp1_fapp0
    (Functor_cat (Op_cat (Hom_cat K x y)) Cat_cat)
    Cat_cat
    (@fapp0_func (Op_cat (Hom_cat K x y)) Cat_cat p)
    (fapp0 (@homd_id_tgt_func K E x u y) v)
    (fapp0 (@homd_ff_tgt_func K E D FF x u y) v)
    (@fdapp1_int_presheaf_arrow K E D FF x u y v)
    ≡ @fdapp1_int_hom_func K E D FF x y p u v;

assert [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  (x y : τ (Obj K)) ⊢
  @homd_
    K
    (@Const_catd K Terminal_cat)
    E
    s
    x
    (@piapp0 K E s x)
    y
    Terminal_obj
    ≡ @homd_
        K
        E
        E
        (@id_funcd K E)
        x
        (@piapp0 K E s x)
        y
        (@piapp0 K E s y);

// Cat-valued profunctor facade and representable hom action.
assert [A B : Cat] ⊢
  Prof_base A B ≡ Product_cat (Op_cat A) B;

assert [A B : Cat] ⊢
  @eq_refl Cat_grpd (Prof_cat A B)
  : τ (@= Cat_grpd
      (Prof_cat A B)
      (Catd_cat (Product_cat (Op_cat A) B)));

assert [A B : Cat] ⊢
  Prof A B ≡ Obj (Catd_cat (Product_cat (Op_cat A) B));

assert [A B : Cat] (P Q : τ (Prof A B)) ⊢
  ProfMap P Q
  ≡ Functord P Q;

assert [A B : Cat] (P : τ (Prof A B)) ⊢
  @id (Prof_cat A B) P
  : τ (ProfMap P P);

assert [A B : Cat] [P Q R : τ (Prof A B)]
  (q : τ (ProfMap Q R))
  (p : τ (ProfMap P Q)) ⊢
  @comp_fapp0 (Prof_cat A B) P Q R q p
  : τ (ProfMap P R);

assert [A B X : Cat]
  (F : τ (Functor A X))
  (G : τ (Functor B X))
  (a : τ (Obj A))
  (b : τ (Obj B)) ⊢
  Fibre_cat
    (@Hom_prof_along A B X F G)
    (Struct_sigma a b)
  ≡ Hom_cat X (fapp0 F a) (fapp0 G b);

assert [A B X : Cat]
  (F : τ (Functor A X))
  (G : τ (Functor B X))
  (a a' : τ (Obj A))
  (b b' : τ (Obj B)) ⊢
  @fapp1_func
    (Product_cat (Op_cat A) B)
    Cat_cat
    (@Hom_prof_along A B X F G)
    (Struct_sigma a b)
    (Struct_sigma a' b')
  ≡ @Prof_reindex_fapp1_func
      X A X B (@Unit_prof X) F G
      (Struct_sigma a b)
      (Struct_sigma a' b');

assert [A B X : Cat]
  (F : τ (Functor A X))
  (G : τ (Functor B X))
  (a a' : τ (Obj A))
  (b b' : τ (Obj B))
  (p : τ (Hom A a' a))
  (q : τ (Hom B b b')) ⊢
  @fapp1_fapp0
    (Product_cat (Op_cat A) B)
    Cat_cat
    (@Hom_prof_along A B X F G)
    (Struct_sigma a b)
    (Struct_sigma a' b')
    (Struct_sigma p q)
  ≡ @Hom_func
      X
      (fapp0 F a)
      (fapp0 F a')
      (fapp0 G b)
      (fapp0 G b')
      (@fapp1_fapp0 A X F a' a p)
      (@fapp1_fapp0 B X G b b' q);

assert [A B X : Cat]
  (F : τ (Functor A X))
  (G : τ (Functor B X))
  (a a' : τ (Obj A))
  (b b' : τ (Obj B))
  (p : τ (Hom A a' a))
  (q : τ (Hom B b b'))
  (h : τ (Hom X (fapp0 F a) (fapp0 G b))) ⊢
  fapp0
    (@fapp1_fapp0
      (Product_cat (Op_cat A) B)
      Cat_cat
      (@Hom_prof_along A B X F G)
      (Struct_sigma a b)
      (Struct_sigma a' b')
      (Struct_sigma p q))
    h
  ≡ @Hom_fapp0
      X
      (fapp0 F a)
      (fapp0 F a')
      (fapp0 G b)
      (fapp0 G b')
      (@fapp1_fapp0 A X F a' a p)
      (@fapp1_fapp0 B X G b b' q)
      h;

assert [B X : Cat]
  (G : τ (Functor B X))
  (x : τ (Obj X))
  (b : τ (Obj B)) ⊢
  Fibre_cat (@Hom_prof B X G) (Struct_sigma x b)
  ≡ Hom_cat X x (fapp0 G b);

assert [X : Cat]
  (x y : τ (Obj X)) ⊢
  Fibre_cat (@Unit_prof X) (Struct_sigma x y)
  ≡ Hom_cat X x y;

assert [X : Cat]
  (x x' y y' : τ (Obj X))
  (p : τ (Hom X x' x))
  (q : τ (Hom X y y')) ⊢
  fapp0
    (@fapp1_func
      (Product_cat (Op_cat X) X)
      Cat_cat
      (@Unit_prof X)
      (Struct_sigma x y)
      (Struct_sigma x' y'))
    (Struct_sigma p q)
  ≡ @Hom_func X x x' y y' p q;

assert [X : Cat]
  (x x' y y' : τ (Obj X))
  (p : τ (Hom X x' x))
  (q : τ (Hom X y y'))
  (h : τ (Hom X x y)) ⊢
  fapp0
    (fapp0
      (@fapp1_func
        (Product_cat (Op_cat X) X)
        Cat_cat
        (@Unit_prof X)
        (Struct_sigma x y)
        (Struct_sigma x' y'))
      (Struct_sigma p q))
    h
  ≡ @Hom_fapp0 X x x' y y' p q h;

assert [X : Cat]
  (x x' y y' : τ (Obj X))
  (p : τ (Hom X x' x))
  (q : τ (Hom X y y')) ⊢
  @fapp1_fapp0
    (Product_cat (Op_cat X) X)
    Cat_cat
    (@Unit_prof X)
    (Struct_sigma x y)
    (Struct_sigma x' y')
    (Struct_sigma p q)
  ≡ @Hom_func X x x' y y' p q;

assert [A B X : Cat]
  (F : τ (Functor A X))
  (G : τ (Functor B X))
  (a : τ (Obj A))
  (b : τ (Obj B)) ⊢
  Fibre_cat
    (@Hom_catd
      (Product_cat (Op_cat A) B)
      (@Const_catd (Product_cat (Op_cat A) B) X)
      (@comp_cat_fapp0
        (Product_cat (Op_cat A) B)
        (Op_cat A)
        (Op_cat X)
        (@Op_func A X F)
        (@Product_projL_func (Op_cat A) B))
      (@comp_cat_fapp0
        (Product_cat (Op_cat A) B)
        B
        X
        G
        (@Product_projR_func (Op_cat A) B)))
    (Struct_sigma a b)
  ≡ Fibre_cat
      (@Hom_prof_along A B X F G)
      (Struct_sigma a b);

// General two-sided product maps used by profunctor reindexing.
// The product/projection cut used by the book keeps the selected Sigma
// projection normal form.  The literal raw composite with `pi1` remains a
// separately documented formal consequence, not a new broad product-eta rule.
assert [A0 A1 B0 B1 : Cat]
  (F : τ (Functor A0 A1))
  (G : τ (Functor B0 B1)) ⊢
  sigma_Fst (@Product_map_func A0 A1 B0 B1 F G)
  ≡ @comp_cat_fapp0
      (Product_cat A0 B0) A0 A1
      F
      (@Product_projL_func A0 B0);

assert [A0 A1 B0 B1 C : Cat]
  (F : τ (Functor A0 A1))
  (G : τ (Functor B0 B1))
  (H : τ (Functor A1 C)) ⊢
  @hom_precomp_along_fapp0
    Cat_cat Cat_cat (@id_func Cat_cat)
    C
    (Product_cat A0 B0) A0
    (@Product_projL_func A0 B0)
    (@hom_precomp_along_fapp0
      Cat_cat Cat_cat (@id_func Cat_cat)
      C A0 A1 F H)
  ≡
  @hom_precomp_along_fapp0
    Cat_cat Cat_cat (@id_func Cat_cat)
    C
    (Product_cat A0 B0) A1
    (sigma_Fst (@Product_map_func A0 A1 B0 B1 F G))
    H;

assert [A A' B B' : Cat]
  (F : τ (Functor A A'))
  (G : τ (Functor B B'))
  (a : τ (Obj A))
  (b : τ (Obj B)) ⊢
  @fapp0
    (Product_cat A B)
    (Product_cat A' B')
    (@Product_map_func A A' B B' F G)
    (Struct_sigma a b)
  ≡ @Product_pair A' B' (fapp0 F a) (fapp0 G b);

assert [A A' B B' : Cat]
  (F : τ (Functor A A'))
  (G : τ (Functor B B'))
  (a a' : τ (Obj A))
  (b b' : τ (Obj B))
  (p : τ (Hom A a a'))
  (q : τ (Hom B b b')) ⊢
  sigma_Fst
    (@fapp1_fapp0
      (Product_cat A B)
      (Product_cat A' B')
      (@Product_map_func A A' B B' F G)
      (Struct_sigma a b)
      (Struct_sigma a' b')
      (Struct_sigma p q))
  ≡ fapp1_fapp0 F p;

assert [A A' B B' : Cat]
  (F : τ (Functor A A'))
  (G : τ (Functor B B'))
  (a a' : τ (Obj A))
  (b b' : τ (Obj B))
  (p : τ (Hom A a a'))
  (q : τ (Hom B b b')) ⊢
  sigma_Snd
    (@fapp1_fapp0
      (Product_cat A B)
      (Product_cat A' B')
      (@Product_map_func A A' B B' F G)
      (Struct_sigma a b)
      (Struct_sigma a' b')
      (Struct_sigma p q))
  ≡ fapp1_fapp0 G q;

assert [A A' B B' : Cat]
  (F : τ (Functor A A'))
  (G : τ (Functor B B'))
  (a a' : τ (Obj A))
  (b b' : τ (Obj B)) ⊢
  sigma_Fst
    (@fapp1_func
      (Product_cat A B)
      (Product_cat A' B')
      (@Product_map_func A A' B B' F G)
      (Struct_sigma a b)
      (Struct_sigma a' b'))
  ≡ @comp_cat_fapp0
      (Product_cat (Hom_cat A a a') (Hom_cat B b b'))
      (Hom_cat A a a')
      (Hom_cat A' (fapp0 F a) (fapp0 F a'))
      (@fapp1_func A A' F a a')
      (@Product_projL_func (Hom_cat A a a') (Hom_cat B b b'));

assert [A A' B B' : Cat]
  (F : τ (Functor A A'))
  (G : τ (Functor B B'))
  (a a' : τ (Obj A))
  (b b' : τ (Obj B)) ⊢
  sigma_Snd
    (@fapp1_func
      (Product_cat A B)
      (Product_cat A' B')
      (@Product_map_func A A' B B' F G)
      (Struct_sigma a b)
      (Struct_sigma a' b'))
  ≡ @comp_cat_fapp0
      (Product_cat (Hom_cat A a a') (Hom_cat B b b'))
      (Hom_cat B b b')
      (Hom_cat B' (fapp0 G b) (fapp0 G b'))
      (@fapp1_func B B' G b b')
      (@Product_projR_func (Hom_cat A a a') (Hom_cat B b b'));

assert [A0 A1 A2 B0 B1 B2 : Cat]
  (F01 : τ (Functor A0 A1))
  (F12 : τ (Functor A1 A2))
  (G01 : τ (Functor B0 B1))
  (G12 : τ (Functor B1 B2)) ⊢
  @comp_cat_fapp0
    (Product_cat A0 B0)
    (Product_cat A1 B1)
    (Product_cat A2 B2)
    (@Product_map_func A1 A2 B1 B2 F12 G12)
    (@Product_map_func A0 A1 B0 B1 F01 G01)
  ≡ @Product_map_func
      A0 A2 B0 B2
      (@comp_cat_fapp0 A0 A1 A2 F12 F01)
      (@comp_cat_fapp0 B0 B1 B2 G12 G01);

assert [A B : Cat] ⊢
  eq_refl
    (@Product_map_func A A B B (@id_func A) (@id_func B))
  : τ (
      @Product_map_func A A B B (@id_func A) (@id_func B)
      =
      @Struct_sigma
        (Obj (Functor_cat (Product_cat A B) A))
        (λ _ : τ (Obj (Functor_cat (Product_cat A B) A)),
          Obj (Functor_cat (Product_cat A B) B))
        (@Product_projL_func A B)
        (@Product_projR_func A B));

assert [A B : Cat] ⊢
  eq_refl
    (@Product_map_func A A B B (@id_func A) (@id_func B))
  : τ (
      @Product_map_func A A B B (@id_func A) (@id_func B)
      =
      @id_func (Product_cat A B));

assert [A A' B B' : Cat]
  (F : τ (Functor A' A))
  (G : τ (Functor B' B))
  (a : τ (Obj A'))
  (b : τ (Obj B')) ⊢
  @fapp0
    (Product_cat (Op_cat A') B')
    (Product_cat (Op_cat A) B)
    (@Prof_reindex_base_func A A' B B' F G)
    (Struct_sigma a b)
  ≡ @fapp0
      (Product_cat (Op_cat A') B')
      (Product_cat (Op_cat A) B)
      (@Product_map_func
        (Op_cat A') (Op_cat A) B' B
        (@Op_func A' A F)
        G)
      (Struct_sigma a b);

assert [A B : Cat]
  (xy : τ (Obj (Product_cat A B))) ⊢
  eq_refl (@id (Product_cat A B) xy)
  : τ (
      @id (Product_cat A B) xy
      =
      @Struct_sigma
        (Obj (Hom_cat A (sigma_Fst xy) (sigma_Fst xy)))
        (λ _ : τ (Obj (Hom_cat A (sigma_Fst xy) (sigma_Fst xy))),
          Obj (Hom_cat B (sigma_Snd xy) (sigma_Snd xy)))
        (@id A (sigma_Fst xy))
        (@id B (sigma_Snd xy)));

// Stable profunctor reindexing and its representable fold.
assert [A A' B B' : Cat]
  (R : τ (Prof A B))
  (F : τ (Functor A' A))
  (G : τ (Functor B' B))
  (a : τ (Obj A'))
  (b : τ (Obj B')) ⊢
  Fibre_cat
    (@Prof_reindex A A' B B' R F G)
    (Struct_sigma a b)
  ≡ Fibre_cat
      R
      (@Product_pair (Op_cat A) B (fapp0 F a) (fapp0 G b));

assert [A A' B B' : Cat]
  (R : τ (Prof A B))
  (F : τ (Functor A' A))
  (G : τ (Functor B' B))
  (a a' : τ (Obj A'))
  (b b' : τ (Obj B')) ⊢
  @fapp1_func
    (Product_cat (Op_cat A') B')
    Cat_cat
    (@Prof_reindex A A' B B' R F G)
    (Struct_sigma a b)
    (Struct_sigma a' b')
  ≡ @Prof_reindex_fapp1_func
      A A' B B' R F G
      (Struct_sigma a b)
      (Struct_sigma a' b');

assert [A A' B B' : Cat]
  (R : τ (Prof A B))
  (F : τ (Functor A' A))
  (G : τ (Functor B' B))
  (a a' : τ (Obj A'))
  (b b' : τ (Obj B'))
  (p : τ (Hom A' a' a))
  (q : τ (Hom B' b b')) ⊢
  @fapp1_fapp0
    (Product_cat (Op_cat A') B')
    Cat_cat
    (@Prof_reindex A A' B B' R F G)
    (Struct_sigma a b)
    (Struct_sigma a' b')
    (Struct_sigma p q)
  ≡ @fapp1_fapp0
      (Product_cat (Op_cat A) B)
      Cat_cat
      R
      (Struct_sigma (fapp0 F a) (fapp0 G b))
      (Struct_sigma (fapp0 F a') (fapp0 G b'))
      (Struct_sigma (fapp1_fapp0 F p) (fapp1_fapp0 G q));

assert [A A' B B' X : Cat]
  (F : τ (Functor A X))
  (G : τ (Functor B X))
  (F' : τ (Functor A' A))
  (G' : τ (Functor B' B)) ⊢
  @Prof_reindex
    A A' B B'
    (@Hom_prof_along A B X F G)
    F'
    G'
  ≡ @Hom_prof_along
      A' B' X
      (@comp_cat_fapp0 A' A X F F')
      (@comp_cat_fapp0 B' B X G G');

assert [A B X : Cat]
  (F : τ (Functor A X))
  (G : τ (Functor B X)) ⊢
  @Prof_reindex
    X A B B
    (@Hom_prof B X G)
    F
    (@id_func B)
  ≡ @Hom_prof_along A B X F G;

assert [A B : Cat] (F : τ (Functor A B)) ⊢
  @Companion_prof A B F
  ≡ @Hom_prof_along A B B F (@id_func B);

assert [A B : Cat] (F : τ (Functor A B)) ⊢
  @Conjoint_prof A B F
  ≡ @Hom_prof A B F;

assert [B J : Cat]
  (P : τ (Prof B J))
  (L : τ (Functor J B)) ⊢
  @IsRepresentedBy_iso B J P L
  ≡ IsoEvidence
      (Prof_cat B J)
      P
      (@Conjoint_prof J B L);

assert [B J : Cat]
  (P : τ (Prof B J)) ⊢
  @Representation_iso B J P
  ≡ `Σ_ L : τ (Functor J B),
      @IsRepresentedBy_iso B J P L;

// Shaped profunctor cells and elements.
assert [A A' B B' : Cat]
  (R' : τ (Prof A' B'))
  (F : τ (Functor A' A))
  (R : τ (Prof A B))
  (G : τ (Functor B' B)) ⊢
  @Prof_transf_cat A A' B B' R' F R G
  ≡ @Functord_cat
      (Product_cat (Op_cat A') B')
      R'
      (@Prof_reindex A A' B B' R F G);

assert [I A B : Cat]
  (F : τ (Functor I A))
  (R : τ (Prof A B))
  (G : τ (Functor I B)) ⊢
  @Prof_hom_cat I A B F R G
  ≡ @Functord_cat
      (Product_cat (Op_cat I) I)
      (@Unit_prof I)
      (@Prof_reindex A I B I R F G);

assert [I A B : Cat]
  (F : τ (Functor I A))
  (R : τ (Prof A B))
  (G : τ (Functor I B)) ⊢
  @Prof_hom I A B F R G
  ≡ Obj
      (@Functord_cat
        (Product_cat (Op_cat I) I)
        (@Unit_prof I)
        (@Prof_reindex A I B I R F G));

assert [I C : Cat]
  (F G : τ (Functor I C)) ⊢
  @Prof_hom_cat I C C F (@Unit_prof C) G
  ≡ @Functord_cat
      (Product_cat (Op_cat I) I)
      (@Unit_prof I)
      (@Hom_prof_along I I C F G);

assert [I A' B' A B : Cat]
  [R' : τ (Prof A' B')]
  [R : τ (Prof A B)]
  [F : τ (Functor A' A)]
  [G : τ (Functor B' B)]
  [a : τ (Functor I A')]
  [b : τ (Functor I B')]
  (c : τ (Obj (@Prof_transf_cat A A' B B' R' F R G)))
  (r : τ (@Prof_hom I A' B' a R' b)) ⊢
  @Prof_cell_apply I A' B' A B R' R F G a b c r
  : τ (@Prof_hom
      I A B
      (@comp_cat_fapp0 I A' A F a)
      R
      (@comp_cat_fapp0 I B' B G b));

assert [A A' B B' X : Cat]
  (R' : τ (Prof A' B'))
  (F : τ (Functor A' A))
  (H : τ (Functor A X))
  (K : τ (Functor B X))
  (G : τ (Functor B' B)) ⊢
  @Prof_transf_cat
    A A' B B'
    R'
    F
    (@Hom_prof_along A B X H K)
    G
  ≡ @Functord_cat
      (Product_cat (Op_cat A') B')
      R'
      (@Hom_prof_along
        A' B' X
        (@comp_cat_fapp0 A' A X H F)
        (@comp_cat_fapp0 B' B X K G));

// Primitive profunctor tensor and exposed-endpoint reindexing.
assert [A B : Cat]
  (R : τ (Prof A B)) ⊢
  @Prof_reindex A A B B R (@id_func A) (@id_func B)
  ≡ R;

assert [A A' B X X' : Cat]
  (R : τ (Prof A B))
  (S : τ (Prof B X))
  (F : τ (Functor A' A))
  (G : τ (Functor X' X)) ⊢
  @Prof_reindex
    A A' X X'
    (@Prof_tensor A B X R S)
    F
    G
  ≡ @Prof_tensor
      A' B X'
      (@Prof_reindex A A' B B R F (@id_func B))
      (@Prof_reindex B B X X' S (@id_func B) G);

assert [A A' B X : Cat]
  (R : τ (Prof A B))
  (S : τ (Prof B X))
  (F : τ (Functor A' A)) ⊢
  @Prof_reindex
    A A' X X
    (@Prof_tensor A B X R S)
    F
    (@id_func X)
  ≡ @Prof_tensor
      A' B X
      (@Prof_reindex A A' B B R F (@id_func B))
      S;

assert [A B X X' : Cat]
  (R : τ (Prof A B))
  (S : τ (Prof B X))
  (G : τ (Functor X' X)) ⊢
  @Prof_reindex
    A A X X'
    (@Prof_tensor A B X R S)
    (@id_func A)
    G
  ≡ @Prof_tensor
      A B X'
      R
      (@Prof_reindex B B X X' S (@id_func B) G);

assert [A B X : Cat]
  (R : τ (Prof A B))
  (S : τ (Prof B X)) ⊢
  @Prof_reindex
    A A X X
    (@Prof_tensor A B X R S)
    (@id_func A)
    (@id_func X)
  ≡ @Prof_tensor A B X R S;

assert [A A' B X Y : Cat]
  (H : τ (Functor A Y))
  (K : τ (Functor B Y))
  (S : τ (Prof B X))
  (F : τ (Functor A' A)) ⊢
  @Prof_reindex
    A A' X X
    (@Prof_tensor
      A B X
      (@Hom_prof_along A B Y H K)
      S)
    F
    (@id_func X)
  ≡ @Prof_tensor
      A' B X
      (@Hom_prof_along
        A' B Y
        (@comp_cat_fapp0 A' A Y H F)
        K)
      S;

assert [A B X : Cat]
  [P P' : τ (Prof A B)]
  [Q Q' : τ (Prof B X)]
  (r : τ (ProfMap P P'))
  (s : τ (ProfMap Q Q')) ⊢
  @Prof_tensor_map A B X P P' Q Q' r s
  : τ (ProfMap
      (@Prof_tensor A B X P Q)
      (@Prof_tensor A B X P' Q'));

assert [A B X : Cat] ⊢
  @Prof_tensor_func A B X
  : τ (Functor
      (Product_cat (@Prof_cat A B) (@Prof_cat B X))
      (@Prof_cat A X));

assert [A B X : Cat]
  (P : τ (Prof A B))
  (Q : τ (Prof B X)) ⊢
  @fapp0
    (Product_cat (@Prof_cat A B) (@Prof_cat B X))
    (@Prof_cat A X)
    (@Prof_tensor_func A B X)
    (Struct_sigma P Q)
  ≡ @Prof_tensor A B X P Q;

assert [A B X : Cat]
  [P P' : τ (Prof A B)]
  [Q Q' : τ (Prof B X)]
  (r : τ (ProfMap P P'))
  (s : τ (ProfMap Q Q')) ⊢
  @fapp1_fapp0
    (Product_cat (@Prof_cat A B) (@Prof_cat B X))
    (@Prof_cat A X)
    (@Prof_tensor_func A B X)
    (Struct_sigma P Q)
    (Struct_sigma P' Q')
    (Struct_sigma r s)
  ≡ @Prof_tensor_map A B X P P' Q Q' r s;

assert [I A B X : Cat]
  [R : τ (Prof A B)]
  [S : τ (Prof B X)]
  [F : τ (Functor I A)]
  [G : τ (Functor I X)]
  (M : τ (Functor I B))
  (r : τ (@Prof_hom I A B F R M))
  (s : τ (@Prof_hom I B X M S G)) ⊢
  @Prof_tensor_hom_hom I A B X R S F G M r s
  : τ (@Prof_hom I A X F (@Prof_tensor A B X R S) G);

assert [A B : Cat]
  (P : τ (Prof A B)) ⊢
  @fapp0
    (@Prof_cat A B)
    (@Prof_cat A B)
    (@Prof_tensor_right_unit_func A B)
    P
  ≡ @Prof_tensor A B B P (@Unit_prof B);

assert [A B : Cat]
  [P P' : τ (Prof A B)]
  (r : τ (ProfMap P P')) ⊢
  @fapp1_fapp0
    (@Prof_cat A B)
    (@Prof_cat A B)
    (@Prof_tensor_right_unit_func A B)
    P P' r
  ≡ @Prof_tensor_map
      A B B
      P P'
      (@Unit_prof B)
      (@Unit_prof B)
      r
      (@id (@Prof_cat B B) (@Unit_prof B));

assert [A B : Cat] ⊢
  @Prof_coyoneda_cov_transf A B
  : τ (Transf
      (@Prof_tensor_right_unit_func A B)
      (@id_func (@Prof_cat A B)));

assert [A B : Cat]
  (P : τ (Prof A B)) ⊢
  @Prof_coyoneda_cov_map A B P
  : τ (ProfMap
      (@Prof_tensor A B B P (@Unit_prof B))
      P);

assert [A B : Cat]
  (P : τ (Prof A B)) ⊢
  @Prof_coyoneda_cov_map A B P
  ≡ @tapp0_fapp0
      (@Prof_cat A B)
      (@Prof_cat A B)
      (@Prof_tensor_right_unit_func A B)
      (@id_func (@Prof_cat A B))
      P
      (@Prof_coyoneda_cov_transf A B);

assert [A B : Cat]
  [P P' : τ (Prof A B)]
  (r : τ (ProfMap P P')) ⊢
  @tapp1_fapp0
    (@Prof_cat A B)
    (@Prof_cat A B)
    (@Prof_tensor_right_unit_func A B)
    (@id_func (@Prof_cat A B))
    P P'
    (@Prof_coyoneda_cov_transf A B)
    r
  : τ (ProfMap
      (@Prof_tensor A B B P (@Unit_prof B))
      P');

assert [A B : Cat]
  (P : τ (Prof A B)) ⊢
  @fapp0
    (@Prof_cat A B)
    (@Prof_cat A B)
    (@Prof_tensor_left_unit_func A B)
    P
  ≡ @Prof_tensor A A B (@Unit_prof A) P;

assert [A B : Cat]
  [P P' : τ (Prof A B)]
  (r : τ (ProfMap P P')) ⊢
  @fapp1_fapp0
    (@Prof_cat A B)
    (@Prof_cat A B)
    (@Prof_tensor_left_unit_func A B)
    P P' r
  ≡ @Prof_tensor_map
      A A B
      (@Unit_prof A)
      (@Unit_prof A)
      P P'
      (@id (@Prof_cat A A) (@Unit_prof A))
      r;

assert [A B : Cat] ⊢
  @Prof_coyoneda_con_transf A B
  : τ (Transf
      (@Prof_tensor_left_unit_func A B)
      (@id_func (@Prof_cat A B)));

assert [A B : Cat]
  (P : τ (Prof A B)) ⊢
  @Prof_coyoneda_con_map A B P
  : τ (ProfMap
      (@Prof_tensor A A B (@Unit_prof A) P)
      P);

assert [A B : Cat]
  (P : τ (Prof A B)) ⊢
  @Prof_coyoneda_con_map A B P
  ≡ @tapp0_fapp0
      (@Prof_cat A B)
      (@Prof_cat A B)
      (@Prof_tensor_left_unit_func A B)
      (@id_func (@Prof_cat A B))
      P
      (@Prof_coyoneda_con_transf A B);

assert [A B : Cat]
  [P P' : τ (Prof A B)]
  (r : τ (ProfMap P P')) ⊢
  @tapp1_fapp0
    (@Prof_cat A B)
    (@Prof_cat A B)
    (@Prof_tensor_left_unit_func A B)
    (@id_func (@Prof_cat A B))
    P P'
    (@Prof_coyoneda_con_transf A B)
    r
  : τ (ProfMap
      (@Prof_tensor A A B (@Unit_prof A) P)
      P');

// General equipment-cell reindexing and composition.
assert [A B C D : Cat]
  (F : τ (Functor A B))
  (G : τ (Functor B C))
  (H : τ (Functor C D)) ⊢
  @comp_cat_fapp0
    A C D H
    (@comp_cat_fapp0 A B C G F)
  ≡ @comp_cat_fapp0
      A B D
      (@comp_cat_fapp0 B C D H G)
      F;

assert [A A' A'' B B' B'' : Cat]
  (R : τ (Prof A B))
  (F : τ (Functor A' A))
  (G : τ (Functor B' B))
  (F' : τ (Functor A'' A'))
  (G' : τ (Functor B'' B')) ⊢
  @Prof_reindex
    A' A'' B' B''
    (@Prof_reindex A A' B B' R F G)
    F'
    G'
  ≡ @Prof_reindex
      A A'' B B''
      R
      (@comp_cat_fapp0 A'' A' A F F')
      (@comp_cat_fapp0 B'' B' B G G');

assert [A A' B B' : Cat]
  (F : τ (Functor A' A))
  (G : τ (Functor B' B))
  (R : τ (Prof A B)) ⊢
  @fapp0
    (@Prof_cat A B)
    (@Prof_cat A' B')
    (@Prof_reindex_func A A' B B' F G)
    R
  ≡ @Prof_reindex A A' B B' R F G;

assert [A A' B B' : Cat]
  (F : τ (Functor A' A))
  (G : τ (Functor B' B))
  (R : τ (Catd (Product_cat (Op_cat A) B))) ⊢
  @fapp0
    (@Catd_cat (Product_cat (Op_cat A) B))
    (@Catd_cat (Product_cat (Op_cat A') B'))
    (@Pullback_catd_func
      (Product_cat (Op_cat A') B')
      (Product_cat (Op_cat A) B)
      (@Prof_reindex_base_func A A' B B' F G))
    R
  ≡ @Prof_reindex A A' B B' R F G;

assert [A A' B B' : Cat]
  (F : τ (Functor A' A))
  (G : τ (Functor B' B)) ⊢
  @Pullback_catd_func
    (Product_cat (Op_cat A') B')
    (Product_cat (Op_cat A) B)
    (@Prof_reindex_base_func A A' B B' F G)
  ≡ @Prof_reindex_func A A' B B' F G;

assert [A A' B B' : Cat]
  (F : τ (Functor A A'))
  (G : τ (Functor B B')) ⊢
  @Pullback_catd_func
    (Product_cat A B)
    (Product_cat A' B')
    (@Product_map_func A A' B B' F G)
  ≡ @Prof_reindex_func
      (Op_cat A')
      (Op_cat A)
      B'
      B
      (@Op_func A A' F)
      G;

assert [A A' B B' : Cat]
  (F : τ (Functor A A'))
  (G : τ (Functor B B'))
  (R : τ (Catd (Product_cat A' B'))) ⊢
  @Pullback_catd
    (Product_cat A B)
    (Product_cat A' B')
    R
    (@Product_map_func A A' B B' F G)
  ≡ @Prof_reindex
      (Op_cat A')
      (Op_cat A)
      B'
      B
      R
      (@Op_func A A' F)
      G;

assert [A A' B B' : Cat]
  (F : τ (Functor A A'))
  (G : τ (Functor B B'))
  (R : τ (Catd (Product_cat A' B'))) ⊢
  @fapp0
    (@Catd_cat (Product_cat A' B'))
    (@Catd_cat (Product_cat A B))
    (@Pullback_catd_func
      (Product_cat A B)
      (Product_cat A' B')
      (@Product_map_func A A' B B' F G))
    R
  ≡ @Prof_reindex
      (Op_cat A')
      (Op_cat A)
      B'
      B
      R
      (@Op_func A A' F)
      G;

assert [A A' B B' : Cat]
  (F : τ (Functor A A'))
  (G : τ (Functor B B'))
  (R : τ (Catd (Product_cat A' B'))) ⊢
  @fapp0
    (@Catd_cat (Product_cat A' B'))
    (@Catd_cat (Product_cat A B))
    (@Pullback_catd_func
      (Product_cat A B)
      (Product_cat A' B')
      (@Product_map_func A A' B B' F G))
    R
  ≡ @Pullback_catd
      (Product_cat A B)
      (Product_cat A' B')
      R
      (@Product_map_func A A' B B' F G);

assert [A A' B B' : Cat]
  (F : τ (Functor A' A))
  (G : τ (Functor B' B))
  (C : Cat) ⊢
  @Prof_reindex
    A A' B B'
    (@Const_catd (Product_cat (Op_cat A) B) C)
    F G
  ≡ @Const_catd (Product_cat (Op_cat A') B') C;

assert [A A' B B' : Cat]
  [R S : τ (Prof A B)]
  (r : τ (ProfMap R S))
  (F : τ (Functor A' A))
  (G : τ (Functor B' B)) ⊢
  @Prof_reindex_transf A A' B B' R S r F G
  : τ (ProfMap
      (@Prof_reindex A A' B B' R F G)
      (@Prof_reindex A A' B B' S F G));

assert [A B : Cat]
  [R S : τ (Prof A B)]
  (r : τ (ProfMap R S)) ⊢
  @Prof_reindex_transf
    A A B B
    R S r
    (@id_func A)
    (@id_func B)
  ≡ r;

assert [A B : Cat]
  (R : τ (Prof A B)) ⊢
  @Op_prof_map
    A B R R
    (@id (@Prof_cat A B) R)
  ≡ @id
      (@Prof_cat (Op_cat B) (Op_cat A))
      (@Op_prof A B R);

assert [B J J' : Cat]
  [F : τ (Functor J B)]
  [W : τ (Prof J' J)]
  [L : τ (Functor J' B)]
  (isl : τ (@IsWeightedLimit_cov_comp B J J' F W L)) ⊢
  @Op_weighted_colimit_con
    (Op_cat B)
    (Op_cat J)
    (Op_cat J')
    (@Op_func J B F)
    (@Op_prof J' J W)
    (@Op_func J' B L)
    (@Op_weighted_limit_cov B J J' F W L isl)
  ≡ isl;

assert [A J J' B : Cat]
  [Ladj : τ (Functor A B)]
  [Radj : τ (Functor B A)]
  [F : τ (Functor J A)]
  [W : τ (Prof J J')]
  [L : τ (Functor J' A)]
  (isc : τ (@WeightedColimit_con A J J' F W L))
  (adj : τ (@Adjunction A B Ladj Radj)) ⊢
  @left_adjoint_preserves_weighted_colimit_con
    A J J' B Ladj Radj F W L isc adj
  : τ (@WeightedColimit_con
      B J J'
      (@comp_cat_fapp0 J A B Ladj F)
      W
      (@comp_cat_fapp0 J' A B Ladj L));

assert [A B : Cat]
  (a : τ (Obj A))
  (b : τ (Obj B)) ⊢
  @fapp0
    (Product_cat (Op_cat A) B)
    Cat_cat
    (@Terminal_prof A B)
    (Struct_sigma a b)
  ≡ Terminal_cat;

assert [I A' B' A B : Cat]
  [R : τ (Prof A B)]
  [F : τ (Functor A' A)]
  [G : τ (Functor B' B)]
  [a : τ (Functor I A')]
  [b : τ (Functor I B')]
  (c : τ (Obj
      (@Prof_transf_cat A A' B B'
        (@Terminal_prof A' B') F R G))) ⊢
  @Prof_cell_eval I A' B' A B R F G a b c
  ≡ @Prof_cell_apply
      I A' B' A B
      (@Terminal_prof A' B')
      R
      F G a b
      c
      (@Prof_terminal_hom I A' B' a b);

assert [A B : Cat]
  (F : τ (Functor A B)) ⊢
  @Prof_func_hom A B F
  : τ (@Prof_hom A B B F (@Unit_prof B) F);

assert [A : Cat] ⊢
  @Prof_id_hom A
  ≡ @id_funcd
      (Product_cat (Op_cat A) A)
      (@Unit_prof A);

assert [A : Cat] ⊢
  @Prof_func_hom A A (@id_func A)
  ≡ @Prof_id_hom A;

assert [A B : Cat]
  (F : τ (Functor A B))
  (ab : τ (Obj (Product_cat (Op_cat A) A))) ⊢
  @tapp0_fapp0
      (Product_cat (Op_cat A) A)
      Cat_cat
      (@Unit_prof A)
      (@Hom_prof_along A A B F F)
      ab
      (@Prof_func_hom A B F)
  ≡ @fapp1_func
      A
      B
      F
      (sigma_Fst ab)
      (sigma_Snd ab);

assert [A B : Cat]
  (F : τ (Functor A B))
  (ab ab' : τ (Obj (Product_cat (Op_cat A) A)))
  (pq : τ (Hom (Product_cat (Op_cat A) A) ab ab')) ⊢
  @tapp1_fapp0
      (Product_cat (Op_cat A) A)
      Cat_cat
      (@Unit_prof A)
      (@Hom_prof_along A A B F F)
      ab
      ab'
      (@Prof_func_hom A B F)
      pq
  ≡ @tapp1_fapp0
      A
      Cat_cat
      (@hom_ A A (@id_func A) (sigma_Fst ab))
      (@hom_ B A F (@fapp0 A B F (sigma_Fst ab')))
      (sigma_Snd ab)
      (sigma_Snd ab')
      (@tapp1_fapp0
        (Op_cat A)
        (@Catd_cat A)
        (@hom_int A A (@id_func A))
        (@comp_cat_fapp0
          (Op_cat A)
          (Op_cat B)
          (@Catd_cat A)
          (@hom_int B A F)
          (@Op_func A B F))
        (sigma_Fst ab)
        (sigma_Fst ab')
        (@fapp1_int_transf A B F)
        (sigma_Fst pq))
      (sigma_Snd pq);

assert [A B : Cat] ⊢
  @join_cross_transf A B
  : τ (Obj
      (@Prof_transf_cat
        (@Join_cat A B) A
        (@Join_cat A B) B
        (@Terminal_prof A B)
        (@join_fst_func A B)
        (@Unit_prof (@Join_cat A B))
        (@join_snd_func A B)));

assert [A B E : Cat]
  (first : τ (Functor A E))
  (second : τ (Functor B E))
  (cross : τ (Obj
      (@Prof_transf_cat
        E A E B
        (@Terminal_prof A B)
        first
        (@Unit_prof E)
        second))) ⊢
  @comp_cat_fapp0
    A
    (@Join_cat A B)
    E
    (@join_elim_func A B E first second cross)
    (@join_fst_func A B)
  ≡ first;

assert [A B E : Cat]
  (first : τ (Functor A E))
  (second : τ (Functor B E))
  (cross : τ (Obj
      (@Prof_transf_cat
        E A E B
        (@Terminal_prof A B)
        first
        (@Unit_prof E)
        second))) ⊢
  @comp_cat_fapp0
    B
    (@Join_cat A B)
    E
    (@join_elim_func A B E first second cross)
    (@join_snd_func A B)
  ≡ second;

assert [A B I : Cat]
  (a : τ (Functor I A))
  (b : τ (Functor I B)) ⊢
  @join_cross_hom A B I a b
  : τ (@Prof_hom
      I
      (@Join_cat A B)
      (@Join_cat A B)
      (@comp_cat_fapp0
        I A (@Join_cat A B)
        (@join_fst_func A B)
        a)
      (@Unit_prof (@Join_cat A B))
      (@comp_cat_fapp0
        I B (@Join_cat A B)
        (@join_snd_func A B)
        b));

assert [A B I : Cat]
  (a : τ (Functor I A))
  (b : τ (Functor I B)) ⊢
  @join_cross_hom A B I a b
  ≡ @Prof_cell_eval
      I A B
      (@Join_cat A B)
      (@Join_cat A B)
      (@Unit_prof (@Join_cat A B))
      (@join_fst_func A B)
      (@join_snd_func A B)
      a b
      (@join_cross_transf A B);

assert [A B E : Cat]
  (first : τ (Functor A E))
  (second : τ (Functor B E))
  (cross : τ (Obj
      (@Prof_transf_cat
        E A E B
        (@Terminal_prof A B)
        first
        (@Unit_prof E)
        second))) ⊢
  @join_elim_cross_transf A B E first second cross
  : τ (Obj
      (@Prof_transf_cat
        E A E B
        (@Terminal_prof A B)
        first
        (@Unit_prof E)
        second));

assert [A B E : Cat]
  (first : τ (Functor A E))
  (second : τ (Functor B E))
  (cross : τ (Obj
      (@Prof_transf_cat
        E A E B
        (@Terminal_prof A B)
        first
        (@Unit_prof E)
        second))) ⊢
  @join_elim_cross_transf A B E first second cross
  ≡ cross;

assert [A B E I : Cat]
  (first : τ (Functor A E))
  (second : τ (Functor B E))
  (cross : τ (Obj
      (@Prof_transf_cat
        E A E B
        (@Terminal_prof A B)
        first
        (@Unit_prof E)
        second)))
  (a : τ (Functor I A))
  (b : τ (Functor I B)) ⊢
  @Prof_cell_eval
    I A B E E
    (@Unit_prof E)
    first second
    a b
    (@join_elim_cross_transf A B E first second cross)
  ≡ @Prof_cell_eval
      I A B E E
      (@Unit_prof E)
      first second
      a b
      cross;

// catalog-area: Internal Path action and explicit Core-inclusion kappa
// Path_cat_func inherits the generic identity and composition owners.
assert [A : Grpd] ⊢
  @path_map_func A A (@id Grpd_cat A)
  ≡ @id Cat_cat (Path_cat A);

assert [A B C : Grpd]
  (g : τ (@Function_grpd B C))
  (f : τ (@Function_grpd A B)) ⊢
  @comp_cat_fapp0
    (Path_cat A) (Path_cat B) (Path_cat C)
    (@path_map_func B C g)
    (@path_map_func A B f)
  ≡ @path_map_func
      A C (@comp_fapp0 Grpd_cat A B C g f);

// Object and equality action retain an iterable Path-category functor.
assert [A B : Grpd]
  (f : τ (@Function_grpd A B))
  (x : τ A) ⊢
  @fapp0 (Path_cat A) (Path_cat B)
    (@path_map_func A B f) x
  ≡ f x;

assert [A B : Grpd]
  (f : τ (@Function_grpd A B))
  (x y : τ A)
  (p : τ (@= A x y)) ⊢
  @fapp1_fapp0 (Path_cat A) (Path_cat B)
    (@path_map_func A B f) x y p
  ≡ @eq_ap A B f x y p;

assert [A B : Grpd]
  (f : τ (@Function_grpd A B))
  (x y : τ A) ⊢
  @fapp1_func (Path_cat A) (Path_cat B)
    (@path_map_func A B f) x y
  : τ (Functor
      (Path_cat (@= A x y))
      (Path_cat (@= B (f x) (f y))));

// Function equality supplies point, off-diagonal, and full higher actions.
assert [A B : Grpd]
  (f g : τ (@Function_grpd A B))
  (h : τ (@= (@Function_grpd A B) f g))
  (x : τ A) ⊢
  @tapp0_fapp0
    (Path_cat A) (Path_cat B)
    (@path_map_func A B f)
    (@path_map_func A B g)
    x (@path_map_transf A B f g h)
  ≡ @PiHapply A (λ _ : τ A, B) f g h x;

assert [A B : Grpd]
  (f g : τ (@Function_grpd A B))
  (h : τ (@= (@Function_grpd A B) f g))
  (x y : τ A)
  (p : τ (@= A x y)) ⊢
  @tapp1_fapp0
    (Path_cat A) (Path_cat B)
    (@path_map_func A B f)
    (@path_map_func A B g)
    x y (@path_map_transf A B f g h) p
  ≡ @path_map_transf_cell A B f g h x y p;

assert [A B : Grpd]
  (f g : τ (@Function_grpd A B))
  (h : τ (@= (@Function_grpd A B) f g))
  (x y : τ A) ⊢
  @tapp1_func
    (Path_cat A) (Path_cat B)
    (@path_map_func A B f)
    (@path_map_func A B g)
    x y (@path_map_transf A B f g h)
  : τ (Functor
      (Path_cat (@= A x y))
      (Path_cat (@= B (f x) (g y))));

// The former Core-specific strict naturality boundary is deliberately absent.
// Naturality is now represented by the explicit CoreInclTransf kappa below.
assertnot [C D : Cat]
  (F : τ (Functor C D)) ⊢
  @comp_cat_fapp0
    (Core_cat C) C D F (Core_incl_func C)
  ≡ @comp_cat_fapp0
      (Core_cat C) (Core_cat D) D
      (Core_incl_func D)
      (@path_map_func
        (Obj C) (Obj D)
        (@functor_object_function C D F));

// The stable whiskered form is likewise no longer a runtime fold.
assertnot [A : Grpd] [C D : Cat]
  (F : τ (Functor C D))
  (G : τ (Functor (Path_cat A) (Core_cat C))) ⊢
  @comp_cat_fapp0
    (Path_cat A) C D F
    (@hom_postcomp_fapp0
      Cat_cat Cat_cat (@id Cat_cat Cat_cat)
      (Path_cat A) (Path_cat (Obj C)) C
      (Core_incl_func C) G)
  ≡ @hom_postcomp_fapp0
      Cat_cat Cat_cat (@id Cat_cat Cat_cat)
      (Path_cat A) (Path_cat (Obj D)) D
      (Core_incl_func D)
      (@comp_cat_fapp0
        (Path_cat A) (Path_cat (Obj C)) (Path_cat (Obj D))
        (@path_map_func
          (Obj C) (Obj D)
          (@functor_object_function C D F))
        G);

/*
  Exact generic spiral diagnostic.

  These check-local names exercise the permanent PathLift/Core-inclusion
  owners before the walking-HIT module specializes them. They do not install a
  second public recursion or action interface.
*/
symbol path_action_iter_power_check
  [C : Cat]
  (S : τ (Functor C C))
  (c : τ (Obj C))
  (n : τ Nat_grpd)
  : τ (Obj C)
≔ @nat_elim
    (λ _ : τ Nat_grpd, Obj C)
    c
    (λ _ : τ Nat_grpd,
      λ x : τ (Obj C), @fapp0 C C S x)
    n;

symbol path_action_iter_power_function_check
  [C : Cat]
  (S : τ (Functor C C))
  (c : τ (Obj C))
  : τ (@Function_grpd Nat_grpd (Obj C))
≔ λ n : τ Nat_grpd, @path_action_iter_power_check C S c n;

symbol path_action_iter_left_function_check
  [C : Cat]
  (S : τ (Functor C C))
  (c : τ (Obj C))
  : τ (@Function_grpd Nat_grpd (Obj C))
≔ @comp_fapp0
    Grpd_cat Nat_grpd (Obj C) (Obj C)
    (@functor_object_function C C S)
    (@path_action_iter_power_function_check C S c);

symbol path_action_iter_right_function_check
  [C : Cat]
  (S : τ (Functor C C))
  (c : τ (Obj C))
  : τ (@Function_grpd Nat_grpd (Obj C))
≔ @comp_fapp0
    Grpd_cat Nat_grpd Nat_grpd (Obj C)
    (@path_action_iter_power_function_check C S c)
    nat_succ_function;

symbol path_action_iter_step_path_check
  [C : Cat]
  (S : τ (Functor C C))
  (c : τ (Obj C))
  : τ (@=
      (@Function_grpd Nat_grpd (Obj C))
      (@path_action_iter_left_function_check C S c)
      (@path_action_iter_right_function_check C S c))
≔ @PiFunext
    Nat_grpd
    (λ _ : τ Nat_grpd, Obj C)
    (@path_action_iter_left_function_check C S c)
    (@path_action_iter_right_function_check C S c)
    (λ n : τ Nat_grpd,
      @eq_refl
        (Obj C)
        (@fapp0 C C S (@path_action_iter_power_check C S c n)));

symbol path_action_iter_power_func_check
  [C : Cat]
  (S : τ (Functor C C))
  (c : τ (Obj C))
  : τ (Functor (Path_cat Nat_grpd) C)
≔ @fapp0
    (Path_cat (@Function_grpd Nat_grpd (Obj C)))
    (Functor_cat (Path_cat Nat_grpd) C)
    (@path_lift_func Nat_grpd C)
    (@path_action_iter_power_function_check C S c);

symbol path_action_iter_exact_spiral_check
  [C : Cat]
  (S : τ (Functor C C))
  (c : τ (Obj C))
  : τ (Transf
      (@comp_cat_fapp0
        (Path_cat Nat_grpd) C C
        S
        (@path_action_iter_power_func_check C S c))
      (@comp_cat_fapp0
        (Path_cat Nat_grpd) (Path_cat Nat_grpd) C
        (@path_action_iter_power_func_check C S c)
        NatSucc_func))
≔ @path_lift_non_strict_spiral
    Nat_grpd C
    S
    (@path_action_iter_power_function_check C S c)
    nat_succ_function
    (@path_action_iter_step_path_check C S c);

assert [C : Cat]
  (S : τ (Functor C C))
  (c : τ (Obj C))
  (n : τ Nat_grpd) ⊢
  @fapp0
    (Path_cat Nat_grpd) C
    (@path_action_iter_power_func_check C S c) n
  ≡ @path_action_iter_power_check C S c n;

assert [C : Cat]
  (S : τ (Functor C C))
  (c : τ (Obj C)) ⊢
  @path_action_iter_exact_spiral_check C S c
  : τ (Transf
      (@comp_cat_fapp0
        (Path_cat Nat_grpd) C C
        S (@path_action_iter_power_func_check C S c))
      (@comp_cat_fapp0
        (Path_cat Nat_grpd) (Path_cat Nat_grpd) C
        (@path_action_iter_power_func_check C S c)
        NatSucc_func));

// The readable endpoint-adjusted point component is directed transport around
// the explicit kappa-left square; it is not the raw identity presentation.
assertnot [C : Cat]
  (S : τ (Functor C C))
  (c : τ (Obj C))
  (n : τ Nat_grpd) ⊢
  @tapp0_fapp0
    (Path_cat Nat_grpd) C
    (@comp_cat_fapp0
      (Path_cat Nat_grpd) C C
      S (@path_action_iter_power_func_check C S c))
    (@comp_cat_fapp0
      (Path_cat Nat_grpd) (Path_cat Nat_grpd) C
      (@path_action_iter_power_func_check C S c)
      NatSucc_func)
    n
    (@path_action_iter_exact_spiral_check C S c)
  ≡ @id C
      (@fapp0 C C S (@path_action_iter_power_check C S c n));

assert [C : Cat]
  (S : τ (Functor C C))
  (c : τ (Obj C))
  (n m : τ Nat_grpd) ⊢
  @tapp1_func
    (Path_cat Nat_grpd) C
    (@comp_cat_fapp0
      (Path_cat Nat_grpd) C C
      S (@path_action_iter_power_func_check C S c))
    (@comp_cat_fapp0
      (Path_cat Nat_grpd) (Path_cat Nat_grpd) C
      (@path_action_iter_power_func_check C S c)
      NatSucc_func)
    n m
    (@path_action_iter_exact_spiral_check C S c)
  : τ (Functor
      (Path_cat (@= Nat_grpd n m))
      (Hom_cat C
        (@fapp0 C C S (@path_action_iter_power_check C S c n))
        (@path_action_iter_power_check C S c (succ m))));

// catalog-area: Equality-local skeleton and restricted Core inclusion
// Sk⁼ formation retains the selected directed dimensions and replaces the
// remaining higher action by the existing Path/Core owners.
assert (A : Cat) ⊢
  EqSkeleton_cat cat_zero A
  ≡ Core_cat A;

assert (n : CatDim) (A : Cat) ⊢
  Obj (EqSkeleton_cat n A)
  ≡ Obj A;

assert
  (n : CatDim)
  (A : Cat)
  (x y : τ (Obj A)) ⊢
  Hom_cat (EqSkeleton_cat (cat_succ n) A) x y
  ≡ EqSkeleton_cat n (Hom_cat A x y);

symbol eq_skeleton_id_path_check
  (n : CatDim)
  (A : Cat)
  (x : τ (Obj A))
  : τ (@=
      (Hom A x x)
      (@id (EqSkeleton_cat (cat_succ n) A) x)
      (@id A x))
≔ @eq_refl (Hom A x x) (@id A x);

assert
  (n : CatDim)
  (A : Cat)
  (x : τ (Obj A)) ⊢
  @eq_skeleton_id_path_check n A x
  : τ (@=
      (Hom A x x)
      (@id (EqSkeleton_cat (cat_succ n) A) x)
      (@id A x));

// Inherited successor composition is deliberately runtime computation even
// though its generic-owner overlaps remain visible in the warning inventory.
symbol eq_skeleton_comp_path_check
  (n : CatDim)
  (A : Cat)
  (w x y : τ (Obj A))
  (f : τ (Hom A w x))
  (g : τ (Hom A x y))
  : τ (@=
      (Hom A w y)
      (@comp_fapp0
        (EqSkeleton_cat (cat_succ n) A)
        w x y g f)
      (@comp_fapp0 A w x y g f))
≔ @eq_refl
    (Hom A w y)
    (@comp_fapp0 A w x y g f);

assert
  (n : CatDim)
  (A : Cat)
  (w x y : τ (Obj A))
  (f : τ (Hom A w x))
  (g : τ (Hom A x y)) ⊢
  @eq_skeleton_comp_path_check n A w x y f g
  : τ (@=
      (Hom A w y)
      (@comp_fapp0
        (EqSkeleton_cat (cat_succ n) A)
        w x y g f)
      (@comp_fapp0 A w x y g f));

// The simultaneous zero action is exactly PathMap of the object function.
assert (A B : Cat) (F : τ (Functor A B)) ⊢
  @eq_skeleton_map_func cat_zero A B F
  ≡ @path_map_func
      (Obj A) (Obj B)
      (@functor_object_function A B F);

assert
  (n : CatDim)
  (A B : Cat)
  (F : τ (Functor A B))
  (x : τ (Obj A)) ⊢
  @fapp0
    (EqSkeleton_cat n A)
    (EqSkeleton_cat n B)
    (@eq_skeleton_map_func n A B F)
    x
  ≡ @fapp0 A B F x;

assert
  (n : CatDim)
  (A B : Cat)
  (F : τ (Functor A B))
  (x y : τ (Obj A)) ⊢
  @fapp1_func
    (EqSkeleton_cat (cat_succ n) A)
    (EqSkeleton_cat (cat_succ n) B)
    (@eq_skeleton_map_func (cat_succ n) A B F)
    x y
  ≡ @eq_skeleton_map_func
      n
      (Hom_cat A x y)
      (Hom_cat B
        (@fapp0 A B F x)
        (@fapp0 A B F y))
      (@fapp1_func A B F x y);

assert
  (n : CatDim)
  (A B : Cat)
  (F : τ (Functor A B))
  (x y : τ (Obj A))
  (f : τ (Hom A x y)) ⊢
  @fapp1_fapp0
    (EqSkeleton_cat (cat_succ n) A)
    (EqSkeleton_cat (cat_succ n) B)
    (@eq_skeleton_map_func (cat_succ n) A B F)
    x y f
  ≡ @fapp0
      (EqSkeleton_cat n (Hom_cat A x y))
      (EqSkeleton_cat n
        (Hom_cat B
          (@fapp0 A B F x)
          (@fapp0 A B F y)))
      (@eq_skeleton_map_func
        n
        (Hom_cat A x y)
        (Hom_cat B
          (@fapp0 A B F x)
          (@fapp0 A B F y))
        (@fapp1_func A B F x y))
      f;

// Whole-functor identity and composition are part of the selected runtime
// action contract, not proof-time substitutes for it.
assert (n : CatDim) (A : Cat) ⊢
  @eq_skeleton_map_func n A A (@id Cat_cat A)
  ≡ @id Cat_cat (EqSkeleton_cat n A);

assert
  (n : CatDim)
  (A B C : Cat)
  (F : τ (Functor A B))
  (G : τ (Functor B C)) ⊢
  @comp_fapp0
    Cat_cat
    (EqSkeleton_cat n A)
    (EqSkeleton_cat n B)
    (EqSkeleton_cat n C)
    (@eq_skeleton_map_func n B C G)
    (@eq_skeleton_map_func n A B F)
  ≡ @eq_skeleton_map_func
      n A C
      (@comp_fapp0 Cat_cat A B C G F);

// The recursive inclusion has a complete object/full-hom/capped ladder.
assert (A : Cat) ⊢
  eq_skeleton_incl_func cat_zero A
  ≡ Core_incl_func A;

assert
  (n : CatDim)
  (A : Cat)
  (x : τ (Obj A)) ⊢
  @fapp0
    (EqSkeleton_cat n A) A
    (eq_skeleton_incl_func n A)
    x
  ≡ x;

assert
  (n : CatDim)
  (A : Cat)
  (x y : τ (Obj A)) ⊢
  @fapp1_func
    (EqSkeleton_cat (cat_succ n) A) A
    (eq_skeleton_incl_func (cat_succ n) A)
    x y
  ≡ eq_skeleton_incl_func n (Hom_cat A x y);

assert
  (n : CatDim)
  (A : Cat)
  (x y : τ (Obj A))
  (f : τ (Hom A x y)) ⊢
  @fapp1_fapp0
    (EqSkeleton_cat (cat_succ n) A) A
    (eq_skeleton_incl_func (cat_succ n) A)
    x y f
  ≡ @fapp0
      (EqSkeleton_cat n (Hom_cat A x y))
      (Hom_cat A x y)
      (eq_skeleton_incl_func n (Hom_cat A x y))
      f;

// Cat₁⁼ retains ordinary functors and equality-valued higher cells.
assert (C D : Cat) ⊢
  Hom_cat Cat1Eq_cat C D
  ≡ Path_cat (Functor C D);

assert (C D : Cat) ⊢
  @fapp1_func Cat1Eq_cat Cat_cat Cat1Eq_incl_func C D
  ≡ Core_incl_func (Functor_cat C D);

// Core₁ maps categories to their cores and functors to PathMap of object maps.
assert (C : Cat) ⊢
  @fapp0 Cat1Eq_cat Cat_cat Core1_func C
  ≡ Core_cat C;

assert (C D : Cat) ⊢
  @fapp1_func Cat1Eq_cat Cat_cat Core1_func C D
  ≡ @core1_hom_func C D;

assert (C D : Cat) (F : τ (Functor C D)) ⊢
  @fapp1_fapp0 Cat1Eq_cat Cat_cat Core1_func C D F
  ≡ @path_map_func
      (Obj C) (Obj D)
      (@functor_object_function C D F);

// The capped Core₁ beta above remains runtime despite its expected outer
// identity/composition projection overlaps.
assert (C : Cat) ⊢
  @tapp0_fapp0
    Cat1Eq_cat Cat_cat
    Core1_func Cat1Eq_incl_func
    C CoreInclTransf
  ≡ Core_incl_func C;

assert (C D : Cat) ⊢
  @tapp1_func
    Cat1Eq_cat Cat_cat
    Core1_func Cat1Eq_incl_func
    C D CoreInclTransf
  ≡ @core_incl_diagonal_func C D;

// tapp₁(CoreInclTransf,F) is the common diagonal functor.  The kappa square
// comparing its boundary composites is the separate derived next cell below.
assert (C D : Cat) (F : τ (Functor C D)) ⊢
  @tapp1_fapp0
    Cat1Eq_cat Cat_cat
    Core1_func Cat1Eq_incl_func
    C D CoreInclTransf F
  ≡ @hom_postcomp_fapp0
      Cat_cat Cat_cat (@id Cat_cat Cat_cat)
      (Core_cat C) (Core_cat D) D
      (Core_incl_func D)
      (@path_map_func
        (Obj C) (Obj D)
        (@functor_object_function C D F));

// The explicit kappa has the two deliberately non-convertible boundary
// functors; its projection ladder is routed through the common diagonal.
assert (C D : Cat) (F : τ (Functor C D)) ⊢
  @core_incl_transf_kappa C D F
  : τ (Transf
      (@comp_cat_fapp0
        (Core_cat C) C D
        F (Core_incl_func C))
      (@comp_cat_fapp0
        (Core_cat C) (Core_cat D) D
        (Core_incl_func D)
        (@path_map_func
          (Obj C) (Obj D)
          (@functor_object_function C D F))));

assert (C D : Cat) (F : τ (Functor C D))
  (x : τ (Obj C)) ⊢
  @tapp0_fapp0
    (Core_cat C) D
    (@comp_cat_fapp0
      (Core_cat C) C D
      (@fapp1_fapp0
        Cat1Eq_cat Cat_cat Cat1Eq_incl_func C D F)
      (@tapp0_fapp0
        Cat1Eq_cat Cat_cat
        Core1_func Cat1Eq_incl_func
        C CoreInclTransf))
    (@comp_cat_fapp0
      (Core_cat C) (Core_cat D) D
      (@tapp0_fapp0
        Cat1Eq_cat Cat_cat
        Core1_func Cat1Eq_incl_func
        D CoreInclTransf)
      (@fapp1_fapp0
        Cat1Eq_cat Cat_cat Core1_func C D F))
    x (@core_incl_transf_kappa C D F)
  ≡ @id
      D
      (@fapp0
        (Core_cat C) D
        (@core_incl_transf_diagonal_fapp0 C D F)
        x);

assert (C D : Cat) (F : τ (Functor C D))
  (x y : τ (Obj C)) ⊢
  @tapp1_func
    (Core_cat C) D
    (@comp_cat_fapp0
      (Core_cat C) C D F (Core_incl_func C))
    (@comp_cat_fapp0
      (Core_cat C) (Core_cat D) D
      (Core_incl_func D)
      (@path_map_func
        (Obj C) (Obj D)
        (@functor_object_function C D F)))
    x y (@core_incl_transf_kappa C D F)
  : τ (Functor
      (Hom_cat (Core_cat C) x y)
      (Hom_cat
        D
        (@fapp0
          (Core_cat C) D
          (@comp_cat_fapp0
            (Core_cat C) C D F (Core_incl_func C))
          x)
        (@fapp0
          (Core_cat C) D
          (@comp_cat_fapp0
            (Core_cat C) (Core_cat D) D
            (Core_incl_func D)
            (@path_map_func
              (Obj C) (Obj D)
              (@functor_object_function C D F)))
          y)));

// Generic precomposition owns whiskering; explicit paths/adjustments align
// only the associativity and readable PathLift presentations.
assert [A : Grpd] (C D : Cat)
  (F : τ (Functor C D))
  (p : τ (@Function_grpd A (Obj C))) ⊢
  @core_incl_transf_kappa_left_raw A C D F p
  : τ (Transf
      (@core_incl_transf_kappa_left_raw_source A C D F p)
      (@core_incl_transf_kappa_left_raw_target A C D F p));

assert [A : Grpd] (C D : Cat)
  (F : τ (Functor C D))
  (p : τ (@Function_grpd A (Obj C))) ⊢
  @core_incl_transf_kappa_left A C D F p
  : τ (Transf
      (@comp_cat_fapp0
        (Path_cat A) C D
        F (@path_lift_fapp0 A C p))
      (@path_lift_fapp0
        A D
        (@comp_fapp0
          Grpd_cat
          A (Obj C) (Obj D)
          (@functor_object_function C D F)
          p)));

assert [A B : Grpd] (C : Cat)
  (p : τ (@Function_grpd B (Obj C)))
  (s : τ (@Function_grpd A B)) ⊢
  @path_lift_kappa_right A B C p s
  ≡ @id
      (Functor_cat (Path_cat A) C)
      (@path_lift_fapp0
        A C
        (@comp_fapp0 Grpd_cat A B (Obj C) p s));

// Kappa-right remains the definitional PathInt-functoriality comparison.
assert [A : Grpd] (C : Cat)
  (S : τ (Functor C C))
  (p : τ (@Function_grpd A (Obj C)))
  (s : τ (@Function_grpd A A))
  (h : τ (@=
      (@Function_grpd A (Obj C))
      (@comp_fapp0
        Grpd_cat
        A (Obj C) (Obj C)
        (@functor_object_function C C S)
        p)
      (@comp_fapp0 Grpd_cat A A (Obj C) p s))) ⊢
  @path_lift_non_strict_spiral A C S p s h
  ≡ @comp_fapp0
      (Functor_cat (Path_cat A) C)
      (@comp_cat_fapp0
        (Path_cat A) C C
        S (@path_lift_fapp0 A C p))
      (@path_lift_fapp0
        A C
        (@comp_fapp0
          Grpd_cat
          A (Obj C) (Obj C)
          (@functor_object_function C C S)
          p))
      (@comp_cat_fapp0
        (Path_cat A) (Path_cat A) C
        (@path_lift_fapp0 A C p)
        (@path_map_func A A s))
      (@fapp1_fapp0
        (Path_cat (@Function_grpd A (Obj C)))
        (Functor_cat (Path_cat A) C)
        (@path_lift_func A C)
        (@comp_fapp0
          Grpd_cat
          A (Obj C) (Obj C)
          (@functor_object_function C C S)
          p)
        (@comp_fapp0 Grpd_cat A A (Obj C) p s)
        h)
      (@core_incl_transf_kappa_left A C C S p);

// catalog-area: Nat arithmetic and sethood prerequisites
// Successor is available as a concrete iterable equality action.
assert (n : τ Nat_grpd) ⊢
  @fapp0
    (Path_cat Nat_grpd) (Path_cat Nat_grpd)
    NatSucc_func n
  ≡ succ n;

assert (n m : τ Nat_grpd)
  (p : τ (@= Nat_grpd n m)) ⊢
  @fapp1_fapp0
    (Path_cat Nat_grpd) (Path_cat Nat_grpd)
    NatSucc_func n m p
  ≡ @eq_ap Nat_grpd Nat_grpd nat_succ_function n m p;

assert (n m : τ Nat_grpd) ⊢
  @fapp1_func
    (Path_cat Nat_grpd) (Path_cat Nat_grpd)
    NatSucc_func n m
  : τ (Functor
      (Path_cat (@= Nat_grpd n m))
      (Path_cat (@= Nat_grpd (succ n) (succ m))));

// Arithmetic prerequisites remain transparent and reusable.
assert (m n : τ Nat_grpd) ⊢
  @nat_add m n
  : τ Nat_grpd;

// Constructor computation and both open unit orientations.
assert (n : τ Nat_grpd) ⊢
  @nat_add zero n
  ≡ n;

assert (m n : τ Nat_grpd) ⊢
  @nat_add (succ m) n
  ≡ succ (@nat_add m n);

assert (m : τ Nat_grpd) ⊢
  @nat_add m zero
  ≡ m;

// The successor/right-unit critical pair joins at the same numeral.
assert (m : τ Nat_grpd) ⊢
  @nat_add (succ m) zero
  ≡ succ m;

assert ⊢
  @nat_add (succ (succ zero)) (succ zero)
  ≡ succ (succ (succ zero));

// Open addition is not proof-erased to a commutative runtime normal form.
assertnot (m n : τ Nat_grpd) ⊢
  @nat_add m n
  ≡ @nat_add n m;

assert (m n k : τ Nat_grpd) ⊢
  @nat_add_assoc m n k
  : τ (@= Nat_grpd
      (@nat_add (@nat_add m n) k)
      (@nat_add m (@nat_add n k)));

assert ⊢
  unit_is_contr
  : τ (IsContr Unit_grpd);

assert ⊢
  is_contr_center unit_is_contr
  ≡ tt;

assert ⊢
  unit_is_prop
  : τ (IsPropGrpd Unit_grpd);

assert ⊢
  empty_is_prop
  : τ (IsPropGrpd Empty_grpd);

// This is the internal sethood witness required by the future Nat model.
assert ⊢
  nat_is_set
  : τ (IsSetGrpd Nat_grpd);

assert (m n : τ Nat_grpd) ⊢
  nat_is_set m n
  : τ (IsPropGrpd (@= Nat_grpd m n));

// catalog-area: Opaque walking endomorphism HIT and contextual elimination
// WalkingEnd has only opaque constructors, explicit one-dimensional evidence,
// and contextual Functord computation. BNat is a separate consistency model.
assert ⊢ walking_base
  : τ (Obj WalkingEnd_cat);

assert ⊢ walking_loop
  : τ (Hom WalkingEnd_cat walking_base walking_base);

assert ⊢ walking_end_is_one_cat
  : τ (IsNCat (cat_succ cat_zero) WalkingEnd_cat);

assert ⊢ walking_end_one_cat
  : τ OneCat;

assert
  (x y : τ (Obj WalkingEnd_cat)) ⊢
  @walking_end_hom_discrete x y
  : τ (IsDiscreteCat (Hom_cat WalkingEnd_cat x y));

assert
  (x : τ (Obj WalkingEnd_cat)) ⊢
  @walking_end_based_hom_discrete x
  : τ (IsDiscreteCat
      (Hom_cat WalkingEnd_cat walking_base x));

assert
  (x : τ (Obj WalkingEnd_cat))
  [p q : τ (Hom WalkingEnd_cat walking_base x)]
  (alpha : τ (Hom
      (Hom_cat WalkingEnd_cat walking_base x)
      p q)) ⊢
  @walking_end_based_cell_to_path x p q alpha
  : τ (@= (Hom WalkingEnd_cat walking_base x) p q);

// One-dimensionality is homwise and does not make WalkingEnd discrete.
assertnot ⊢
  walking_end_is_one_cat
  : τ (IsDiscreteCat WalkingEnd_cat);

// The four category operations remain opaque.
assertnot ⊢ Obj WalkingEnd_cat ≡ Unit_grpd;

assertnot ⊢
  Hom_cat WalkingEnd_cat walking_base walking_base
  ≡ Path_cat Nat_grpd;

assertnot ⊢
  @id WalkingEnd_cat walking_base
  ≡ walking_loop;

assertnot ⊢
  @comp_fapp0
    WalkingEnd_cat walking_base walking_base walking_base
    walking_loop walking_loop
  ≡ walking_loop;

// Contextual algebra data has the selected orientation D[loop] o u => u o R[loop].
assert
  (R D : τ (Catd WalkingEnd_cat))
  (u : τ (Functor
      (Fibre_cat R walking_base)
      (Fibre_cat D walking_base))) ⊢
  @walking_end_loop_lhs_func R D u
  : τ (Functor
      (Fibre_cat R walking_base)
      (Fibre_cat D walking_base));

assert
  (R D : τ (Catd WalkingEnd_cat))
  (u : τ (Functor
      (Fibre_cat R walking_base)
      (Fibre_cat D walking_base))) ⊢
  @walking_end_loop_rhs_func R D u
  : τ (Functor
      (Fibre_cat R walking_base)
      (Fibre_cat D walking_base));

assert
  (R D : τ (Catd WalkingEnd_cat))
  (u : τ (Functor
      (Fibre_cat R walking_base)
      (Fibre_cat D walking_base))) ⊢
  @walking_end_loop_coherence R D u
  ≡ @Transf
      (Fibre_cat R walking_base)
      (Fibre_cat D walking_base)
      (@walking_end_loop_lhs_func R D u)
      (@walking_end_loop_rhs_func R D u);

assert
  (R D : τ (Catd WalkingEnd_cat))
  (u : τ (Functor
      (Fibre_cat R walking_base)
      (Fibre_cat D walking_base)))
  (sigma : τ (@walking_end_loop_coherence R D u)) ⊢
  @walking_end_ind_funcd R D u sigma
  : τ (Functord R D);

// These are the contextual HIT constructor betas. The derived ordinary
// recursor exposes the same base/loop computations at fapp0/fapp1 below.
assert
  (R D : τ (Catd WalkingEnd_cat))
  (u : τ (Functor
      (Fibre_cat R walking_base)
      (Fibre_cat D walking_base)))
  (sigma : τ (@walking_end_loop_coherence R D u)) ⊢
  @Fibre_func
      WalkingEnd_cat R D
      (@walking_end_ind_funcd R D u sigma)
      walking_base
  ≡ u;

assert
  (R D : τ (Catd WalkingEnd_cat))
  (u : τ (Functor
      (Fibre_cat R walking_base)
      (Fibre_cat D walking_base)))
  (sigma : τ (@walking_end_loop_coherence R D u))
  (r : τ (Obj (Fibre_cat R walking_base))) ⊢
  @fdapp1_int_cell
      WalkingEnd_cat R D
      (@walking_end_ind_funcd R D u sigma)
      walking_base walking_base walking_loop r
  ≡ @tapp0_fapp0
      (Fibre_cat R walking_base)
      (Fibre_cat D walking_base)
      (@walking_end_loop_lhs_func R D u)
      (@walking_end_loop_rhs_func R D u)
      r sigma;

assert
  (R D : τ (Catd WalkingEnd_cat))
  (u : τ (Functor
      (Fibre_cat R walking_base)
      (Fibre_cat D walking_base)))
  (sigma : τ (@walking_end_loop_coherence R D u)) ⊢
  @walking_end_ind_funcd_beta_base R D u sigma
  : τ (@=
      (Functor
        (Fibre_cat R walking_base)
        (Fibre_cat D walking_base))
      (@Fibre_func
        WalkingEnd_cat R D
        (@walking_end_ind_funcd R D u sigma)
        walking_base)
      u);

// The ordinary section specialization is transparent and computes through
// the contextual owner at its canonical piapp0/piapp1 observers.
assert
  (D : τ (Catd WalkingEnd_cat))
  (u : τ (Obj (Fibre_cat D walking_base)))
  (ell : τ (@walking_end_loop_lift_grpd D u)) ⊢
  @walking_end_loop_lift_transf D u ell
  : τ (@walking_end_loop_coherence
      (@Const_catd WalkingEnd_cat Terminal_cat)
      D
      (@Obj_func (Fibre_cat D walking_base) u));

assert
  (D : τ (Catd WalkingEnd_cat))
  (u : τ (Obj (Fibre_cat D walking_base)))
  (ell : τ (@walking_end_loop_lift_grpd D u)) ⊢
  @walking_end_ind_sec D u ell
  : τ (Obj (Pi_cat D));

assert
  (D : τ (Catd WalkingEnd_cat))
  (u : τ (Obj (Fibre_cat D walking_base)))
  (ell : τ (@walking_end_loop_lift_grpd D u)) ⊢
  @piapp0 WalkingEnd_cat D (@walking_end_ind_sec D u ell) walking_base
  ≡ u;

assert
  (D : τ (Catd WalkingEnd_cat))
  (u : τ (Obj (Fibre_cat D walking_base)))
  (ell : τ (@walking_end_loop_lift_grpd D u)) ⊢
  @piapp1_fapp0
    WalkingEnd_cat D (@walking_end_ind_sec D u ell)
    walking_base walking_base walking_loop
  ≡ ell;

assert
  (D : τ (Catd WalkingEnd_cat))
  (u : τ (Obj (Fibre_cat D walking_base)))
  (ell : τ (@walking_end_loop_lift_grpd D u)) ⊢
  @walking_end_ind_sec_beta_base D u ell
  : τ (@=
      (Obj (Fibre_cat D walking_base))
      (@piapp0 WalkingEnd_cat D
        (@walking_end_ind_sec D u ell)
        walking_base)
      u);

assert
  (D : τ (Catd WalkingEnd_cat))
  (u : τ (Obj (Fibre_cat D walking_base)))
  (ell : τ (@walking_end_loop_lift_grpd D u)) ⊢
  @walking_end_ind_sec_beta_loop D u ell
  : τ (@=
      (@walking_end_loop_lift_grpd D u)
      (@piapp1_fapp0
        WalkingEnd_cat D (@walking_end_ind_sec D u ell)
        walking_base walking_base walking_loop)
      ell);

// The constant recursor is derived. Narrow terminal/constant projection joins
// expose the usual runtime constructor equations at its ordinary observers.
assert [C : Cat]
  (x : τ (Obj C))
  (f : τ (Hom C x x)) ⊢
  @walking_end_rec_func C x f
  : τ (Functor WalkingEnd_cat C);

assert [C : Cat]
  (x : τ (Obj C))
  (f : τ (Hom C x x)) ⊢
  @fapp0 WalkingEnd_cat C (@walking_end_rec_func C x f) walking_base
  ≡ x;

assert [C : Cat]
  (x : τ (Obj C))
  (f : τ (Hom C x x)) ⊢
  @fapp1_fapp0
    WalkingEnd_cat C (@walking_end_rec_func C x f)
    walking_base walking_base walking_loop
  ≡ f;

assert [C : Cat]
  (x : τ (Obj C))
  (f : τ (Hom C x x)) ⊢
  @walking_end_rec_base_contextual_func_eq C x f
  : τ (@=
      (Functor Terminal_cat C)
      (@Fibre_func
        WalkingEnd_cat
        (@Const_catd WalkingEnd_cat Terminal_cat)
        (@Const_catd WalkingEnd_cat C)
        (@walking_end_rec_func C x f)
        walking_base)
      (@Obj_func C x));

assert [C : Cat]
  (x : τ (Obj C))
  (f : τ (Hom C x x)) ⊢
  @walking_end_rec_base_projection_func_eq C x f
  : τ (@=
      (Functor Terminal_cat C)
      (@Fibre_func
        WalkingEnd_cat
        (@Const_catd WalkingEnd_cat Terminal_cat)
        (@Const_catd WalkingEnd_cat C)
        (@walking_end_rec_func C x f)
        walking_base)
      (@Obj_func C
        (@fapp0 WalkingEnd_cat C
          (@walking_end_rec_func C x f)
          walking_base)));

assert [C : Cat]
  (x : τ (Obj C))
  (f : τ (Hom C x x)) ⊢
  @walking_end_rec_beta_base C x f
  : τ (@=
      (Obj C)
      (@fapp0 WalkingEnd_cat C
        (@walking_end_rec_func C x f)
        walking_base)
      x);

assert [C : Cat]
  (x : τ (Obj C))
  (f : τ (Hom C x x)) ⊢
  @walking_end_rec_beta_loop C x f
  ≡ @walking_end_ind_sec_beta_loop
      (@Const_catd WalkingEnd_cat C)
      x f;

assert [C : Cat]
  (x : τ (Obj C))
  (f : τ (Hom C x x)) ⊢
  @walking_end_rec_beta_loop_ordinary C x f
  : τ (@=
      (Hom C x x)
      (@fapp1_fapp0
        WalkingEnd_cat C (@walking_end_rec_func C x f)
        walking_base walking_base walking_loop)
      f);

// The generic piapp1/fapp1 comparison remains available independently of the
// now-runtime ordinary constructor equation.
assert [C : Cat]
  (x : τ (Obj C))
  (f : τ (Hom C x x)) ⊢
  @walking_end_rec_loop_ordinary_comparison C x f
  : τ (@=
      (Hom C
        (@fapp0 WalkingEnd_cat C
          (@walking_end_rec_func C x f)
          walking_base)
        (@fapp0 WalkingEnd_cat C
          (@walking_end_rec_func C x f)
          walking_base))
      (@piapp1_fapp0
        WalkingEnd_cat
        (@Const_catd WalkingEnd_cat C)
        (@walking_end_rec_func C x f)
        walking_base walking_base walking_loop)
      (@fapp1_fapp0
        WalkingEnd_cat C (@walking_end_rec_func C x f)
        walking_base walking_base walking_loop));

// BNat remains a separate one-object Nat monoid consistency model.
assert ⊢ Obj BNat_cat ≡ Unit_grpd;

assert ⊢
  Hom_cat BNat_cat bnat_obj bnat_obj
  ≡ Path_cat Nat_grpd;

assert ⊢ @id BNat_cat bnat_obj ≡ zero;
assert ⊢ bnat_generator ≡ succ zero;

assert (g f : τ Nat_grpd) ⊢
  @comp_fapp0 BNat_cat tt tt tt (succ g) f
  ≡ succ (@comp_fapp0 BNat_cat tt tt tt g f);

assert (g f : τ Nat_grpd) ⊢
  @bnat_comp_nat_add g f
  : τ (@= Nat_grpd
      (@comp_fapp0 BNat_cat tt tt tt g f)
      (@nat_add g f));

assertnot (g f : τ Nat_grpd) ⊢
  @comp_fapp0 BNat_cat tt tt tt g f
  ≡ @nat_add g f;

assert ⊢ bnat_is_one_cat
  : τ (IsNCat (cat_succ cat_zero) BNat_cat);

assert ⊢ bnat_one_cat
  : τ OneCat;

assert ⊢ walking_bnat_model_func
  : τ (Functor WalkingEnd_cat BNat_cat);

assert ⊢ walking_bnat_model_beta_base
  : τ (@=
      (Obj BNat_cat)
      (@fapp0
        WalkingEnd_cat BNat_cat walking_bnat_model_func walking_base)
      bnat_obj);

assert ⊢ walking_bnat_model_beta_loop
  ≡ @walking_end_rec_beta_loop
      BNat_cat bnat_obj bnat_generator;

// catalog-area: Walking Code, powers, and directed spiral
// Code uses the ordinary runtime HIT equations; the representable and all
// higher action remain owned by the generic Catd/fapp/tapp calculus.
assert ⊢
  Fibre_cat walking_Code_catd walking_base
  ≡ Path_cat Nat_grpd;

assert ⊢
  @catd_transport_func
    WalkingEnd_cat walking_Code_catd
    walking_base walking_base walking_loop
  ≡ NatSucc_func;

assert ⊢ walking_Code_beta_base
  : τ (@=
      (Obj Cat_cat)
      (Fibre_cat walking_Code_catd walking_base)
      (Path_cat Nat_grpd));

assert ⊢ walking_Code_beta_loop
  : τ (@=
      (Hom Cat_cat (Path_cat Nat_grpd) (Path_cat Nat_grpd))
      (@catd_transport_func
        WalkingEnd_cat walking_Code_catd
        walking_base walking_base walking_loop)
      NatSucc_func);

assert
  (x : τ (Obj WalkingEnd_cat))
  (p : τ (Hom WalkingEnd_cat walking_base x)) ⊢
  @walking_encode x p
  : τ (Obj (Fibre_cat walking_Code_catd x));

assert ⊢
  walking_based_rep_catd
  : τ (Catd WalkingEnd_cat);

assert
  (x : τ (Obj WalkingEnd_cat))
  (p : τ (Hom WalkingEnd_cat walking_base x))
  (q : τ (Hom WalkingEnd_cat walking_base walking_base)) ⊢
  @walking_based_rep_postcomp_eq x p q
  : τ (@=
      (Hom WalkingEnd_cat walking_base x)
      (@fapp0
        (Fibre_cat walking_based_rep_catd walking_base)
        (Fibre_cat walking_based_rep_catd x)
        (@catd_transport_func
          WalkingEnd_cat walking_based_rep_catd
          walking_base x p)
        q)
      (@comp_fapp0
        WalkingEnd_cat walking_base walking_base x p q));

// The generic representable keeps stable hom_postcomp_fapp0 as its runtime
// owner; its raw-composition view above is deliberately proof-time.
assertnot
  (x : τ (Obj WalkingEnd_cat))
  (p : τ (Hom WalkingEnd_cat walking_base x))
  (q : τ (Hom WalkingEnd_cat walking_base walking_base)) ⊢
  @fapp0
    (Fibre_cat walking_based_rep_catd walking_base)
    (Fibre_cat walking_based_rep_catd x)
    (@catd_transport_func
      WalkingEnd_cat walking_based_rep_catd
      walking_base x p)
    q
  ≡ @comp_fapp0
      WalkingEnd_cat walking_base walking_base x p q;

assert ⊢
  walking_power zero
  ≡ @id WalkingEnd_cat walking_base;

assert (n : τ Nat_grpd) ⊢
  walking_power (succ n)
  ≡ @comp_fapp0
      WalkingEnd_cat walking_base walking_base walking_base
      walking_loop (walking_power n);

assert (n : τ Nat_grpd) ⊢
  @fapp0
    (Path_cat Nat_grpd)
    (Hom_cat WalkingEnd_cat walking_base walking_base)
    walking_power_func n
  ≡ walking_power n;

assert (n m : τ Nat_grpd) ⊢
  @fapp1_func
    (Path_cat Nat_grpd)
    (Hom_cat WalkingEnd_cat walking_base walking_base)
    walking_power_func n m
  : τ (Functor
      (Path_cat (@= Nat_grpd n m))
      (Hom_cat
        (Hom_cat WalkingEnd_cat walking_base walking_base)
        (walking_power n)
        (walking_power m)));

assert ⊢ walking_power_spiral
  : τ (@walking_end_loop_coherence
      walking_Code_catd
      walking_based_rep_catd
      walking_power_func);

// The restricted CoreInclTransf construction supplies the selected two-factor
// spiral: explicit kappa-left followed by PathLift(step). Kappa-right is
// judgmentally identity and therefore is not inserted as a third factor.
assert ⊢ walking_power_spiral_coreincl
  : τ (@walking_end_loop_coherence
      walking_Code_catd
      walking_based_rep_catd
      walking_power_func);

assert ⊢
  walking_power_spiral_coreincl
  ≡ walking_power_spiral;

assert (n : τ Nat_grpd) ⊢
  @tapp0_fapp0
    (Path_cat Nat_grpd)
    (Hom_cat WalkingEnd_cat walking_base walking_base)
    (@walking_end_loop_lhs_func
      walking_Code_catd walking_based_rep_catd walking_power_func)
    (@walking_end_loop_rhs_func
      walking_Code_catd walking_based_rep_catd walking_power_func)
    n
    walking_power_spiral_coreincl
  ≡ @walking_power_spiral_component n;

assert (n : τ Nat_grpd) ⊢
  @walking_power_spiral_cell n
  : τ (Hom
      (Hom_cat WalkingEnd_cat walking_base walking_base)
      (@comp_fapp0
        WalkingEnd_cat walking_base walking_base walking_base
        walking_loop (walking_power n))
      (walking_power (succ n)));

// The point equality driving the generic Path action is judgmental
// reflexivity at the raw power equation.
assert (n : τ Nat_grpd) ⊢
  @PiHapply
    Nat_grpd
    (λ _ : τ Nat_grpd,
      Hom WalkingEnd_cat walking_base walking_base)
    walking_power_left_function
    walking_power_right_function
    walking_power_step_path
    n
  ≡ @eq_refl
      (Hom WalkingEnd_cat walking_base walking_base)
      (@comp_fapp0
        WalkingEnd_cat walking_base walking_base walking_base
        walking_loop (walking_power n));

assert (n : τ Nat_grpd) ⊢
  @tapp0_fapp0
    (Path_cat Nat_grpd)
    (Path_cat (Hom WalkingEnd_cat walking_base walking_base))
    (@path_map_func
      Nat_grpd
      (Hom WalkingEnd_cat walking_base walking_base)
      walking_power_left_function)
    (@path_map_func
      Nat_grpd
      (Hom WalkingEnd_cat walking_base walking_base)
      walking_power_right_function)
    n
    (@path_map_transf
      Nat_grpd
      (Hom WalkingEnd_cat walking_base walking_base)
      walking_power_left_function
      walking_power_right_function
      walking_power_step_path)
  ≡ @eq_refl
      (Hom WalkingEnd_cat walking_base walking_base)
      (@comp_fapp0
        WalkingEnd_cat walking_base walking_base walking_base
        walking_loop (walking_power n));

// PathLift(step) still has the canonical path_to_hom component below, but the
// selected spiral first traverses explicit kappa-left. Consequently the whole
// endpoint-adjusted component does not collapse to that second factor alone.
assertnot (n : τ Nat_grpd) ⊢
  @tapp0_fapp0
    (Path_cat Nat_grpd)
    (Hom_cat WalkingEnd_cat walking_base walking_base)
    (@comp_cat_fapp0
      (Path_cat Nat_grpd)
      (Hom_cat WalkingEnd_cat walking_base walking_base)
      (Hom_cat WalkingEnd_cat walking_base walking_base)
      walking_loop_postcomp_func
      walking_power_func)
    (@comp_cat_fapp0
      (Path_cat Nat_grpd)
      (Path_cat Nat_grpd)
      (Hom_cat WalkingEnd_cat walking_base walking_base)
      walking_power_func
      NatSucc_func)
    n
    walking_power_spiral
  ≡ @path_to_hom
      (Hom_cat WalkingEnd_cat walking_base walking_base)
      (@fapp0
        (Path_cat Nat_grpd)
        (Hom_cat WalkingEnd_cat walking_base walking_base)
        (@comp_cat_fapp0
          (Path_cat Nat_grpd)
          (Hom_cat WalkingEnd_cat walking_base walking_base)
          (Hom_cat WalkingEnd_cat walking_base walking_base)
          walking_loop_postcomp_func
          walking_power_func)
        n)
      (@fapp0
        (Path_cat Nat_grpd)
        (Hom_cat WalkingEnd_cat walking_base walking_base)
        (@comp_cat_fapp0
          (Path_cat Nat_grpd)
          (Path_cat Nat_grpd)
          (Hom_cat WalkingEnd_cat walking_base walking_base)
          walking_power_func
          NatSucc_func)
        n)
      (@PiHapply
        Nat_grpd
        (λ _ : τ Nat_grpd,
          Hom WalkingEnd_cat walking_base walking_base)
        walking_power_left_function
        walking_power_right_function
        walking_power_step_path
        n);

assertnot (n : τ Nat_grpd) ⊢
  @tapp0_fapp0
    (Path_cat Nat_grpd)
    (Hom_cat WalkingEnd_cat walking_base walking_base)
    (@comp_cat_fapp0
      (Path_cat Nat_grpd)
      (Hom_cat WalkingEnd_cat walking_base walking_base)
      (Hom_cat WalkingEnd_cat walking_base walking_base)
      walking_loop_postcomp_func
      walking_power_func)
    (@comp_cat_fapp0
      (Path_cat Nat_grpd)
      (Path_cat Nat_grpd)
      (Hom_cat WalkingEnd_cat walking_base walking_base)
      walking_power_func
      NatSucc_func)
    n
    walking_power_spiral
  ≡ @id
      (Hom_cat WalkingEnd_cat walking_base walking_base)
      (@comp_fapp0
        WalkingEnd_cat walking_base walking_base walking_base
        walking_loop (walking_power n));

assertnot (n : τ Nat_grpd) ⊢
  @walking_power_spiral_cell n
  ≡ @id
      (Hom_cat WalkingEnd_cat walking_base walking_base)
      (@comp_fapp0
        WalkingEnd_cat walking_base walking_base walking_base
        walking_loop (walking_power n));

// Open ordinary and higher representable/spiral action is inherited.
assert
  (x y : τ (Obj WalkingEnd_cat)) ⊢
  @fapp1_func
    WalkingEnd_cat Cat_cat walking_Code_catd x y
  : τ (Functor
      (Hom_cat WalkingEnd_cat x y)
      (Functor_cat
        (Fibre_cat walking_Code_catd x)
        (Fibre_cat walking_Code_catd y)));

assert
  (p q : τ (Hom WalkingEnd_cat walking_base walking_base))
  (alpha : τ (Hom
      (Hom_cat WalkingEnd_cat walking_base walking_base)
      p q)) ⊢
  @fapp1_fapp0
    (Hom_cat WalkingEnd_cat walking_base walking_base)
    (Functor_cat
      (Fibre_cat walking_based_rep_catd walking_base)
      (Fibre_cat walking_based_rep_catd walking_base))
    (@fapp1_func
      WalkingEnd_cat Cat_cat walking_based_rep_catd
      walking_base walking_base)
    p q alpha
  : τ (Transf
      (@catd_transport_func
        WalkingEnd_cat walking_based_rep_catd
        walking_base walking_base p)
      (@catd_transport_func
        WalkingEnd_cat walking_based_rep_catd
        walking_base walking_base q));

assert (n m : τ Nat_grpd) ⊢
  @tapp1_func
    (Path_cat Nat_grpd)
    (Hom_cat WalkingEnd_cat walking_base walking_base)
    (@walking_end_loop_lhs_func
      walking_Code_catd walking_based_rep_catd walking_power_func)
    (@walking_end_loop_rhs_func
      walking_Code_catd walking_based_rep_catd walking_power_func)
    n m walking_power_spiral
  : τ (Functor
      (Path_cat (@= Nat_grpd n m))
      (Hom_cat
        (Hom_cat WalkingEnd_cat walking_base walking_base)
        (@fapp0
          (Path_cat Nat_grpd)
          (Hom_cat WalkingEnd_cat walking_base walking_base)
          (@walking_end_loop_lhs_func
            walking_Code_catd walking_based_rep_catd walking_power_func)
          n)
        (@fapp0
          (Path_cat Nat_grpd)
          (Hom_cat WalkingEnd_cat walking_base walking_base)
          (@walking_end_loop_rhs_func
            walking_Code_catd walking_based_rep_catd walking_power_func)
          m)));

// WalkingEnd's Hom remains opaque despite the concrete encode/power data.
assertnot ⊢
  Hom_cat WalkingEnd_cat walking_base walking_base
  ≡ Path_cat Nat_grpd;

// catalog-area: Walking directed decoder and inverse paths
// The open composite comparison is proof-time; only literal constructor
// observations are runtime HIT betas.
assert [C : Cat]
  (x : τ (Obj C))
  (f : τ (Hom C x x))
  (p : τ (Hom WalkingEnd_cat walking_base walking_base)) ⊢
  @walking_end_rec_loop_prefix_eq C x f p
  : τ (@=
      (Hom C x x)
      (@fapp1_fapp0
        WalkingEnd_cat C (@walking_end_rec_func C x f)
        walking_base walking_base
        (@comp_fapp0
          WalkingEnd_cat walking_base walking_base walking_base
          walking_loop p))
      (@comp_fapp0
        C x x x f
        (@fapp1_fapp0
          WalkingEnd_cat C (@walking_end_rec_func C x f)
          walking_base walking_base p)));

assert ⊢ walking_directed_decode_funcd
  : τ (Functord walking_Code_catd walking_based_rep_catd);

assert ⊢
  @walking_directed_decode_func walking_base
  ≡ walking_power_func;

assert ⊢ walking_directed_decode_beta_base
  : τ (@=
      (Functor
        (Fibre_cat walking_Code_catd walking_base)
        (Fibre_cat walking_based_rep_catd walking_base))
      (@walking_directed_decode_func walking_base)
      walking_power_func);

assert
  (x : τ (Obj WalkingEnd_cat))
  (n : τ (Obj (Fibre_cat walking_Code_catd x))) ⊢
  @walking_directed_decode x n
  : τ (Obj (Fibre_cat walking_based_rep_catd x));

// This public milestone remains a directed cell and materially contains the
// generic displayed action at zero.
assert
  (x : τ (Obj WalkingEnd_cat))
  (p : τ (Hom WalkingEnd_cat walking_base x)) ⊢
  @walking_directed_normalization_cell x p
  : τ (Hom
      (Hom_cat WalkingEnd_cat walking_base x)
      p
      (@walking_directed_decode x (@walking_encode x p)));

assert
  (x : τ (Obj WalkingEnd_cat))
  (p : τ (Hom WalkingEnd_cat walking_base x)) ⊢
  @walking_directed_normalization_cell x p
  ≡ @fdapp1_int_cell
      WalkingEnd_cat
      walking_Code_catd
      walking_based_rep_catd
      walking_directed_decode_funcd
      walking_base x p zero;

assert
  (x : τ (Obj WalkingEnd_cat))
  (p : τ (Hom WalkingEnd_cat walking_base x)) ⊢
  @walking_directed_normalization_path x p
  : τ (@=
      (Hom WalkingEnd_cat walking_base x)
      p
      (@walking_directed_decode x (@walking_encode x p)));

assert
  (p : τ (Hom WalkingEnd_cat walking_base walking_base)) ⊢
  @walking_power_encode_roundtrip p
  : τ (@=
      (Hom WalkingEnd_cat walking_base walking_base)
      (walking_power (@walking_encode walking_base p))
      p);

assert
  (p : τ (Hom WalkingEnd_cat walking_base walking_base)) ⊢
  @walking_Code_loop_prefix_action_path p
  : τ (@=
      (Hom Cat_cat (Path_cat Nat_grpd) (Path_cat Nat_grpd))
      (@catd_transport_func
        WalkingEnd_cat walking_Code_catd
        walking_base walking_base
        (@comp_fapp0
          WalkingEnd_cat walking_base walking_base walking_base
          walking_loop p))
      (@comp_cat_fapp0
        (Path_cat Nat_grpd)
        (Path_cat Nat_grpd)
        (Path_cat Nat_grpd)
        NatSucc_func
        (@catd_transport_func
          WalkingEnd_cat walking_Code_catd
          walking_base walking_base p)));

assert ⊢
  @walking_encode walking_base (walking_power zero)
  ≡ zero;

assert (n : τ Nat_grpd) ⊢
  @walking_encode_power_succ_path n
  : τ (@= Nat_grpd
      (@walking_encode walking_base (walking_power (succ n)))
      (succ (@walking_encode walking_base (walking_power n))));

// Open successor action uses the named equation; it is not another runtime
// generator-prefix rewrite.
assertnot (n : τ Nat_grpd) ⊢
  @walking_encode walking_base (walking_power (succ n))
  ≡ succ (@walking_encode walking_base (walking_power n));

assert (n : τ Nat_grpd) ⊢
  @walking_encode_power_roundtrip n
  : τ (@= Nat_grpd
      (@walking_encode walking_base (walking_power n))
      n);

// catalog-area: Walking Hom-Nat packaging and directed consequences
// The generator-prefix fact is an ordinary equality theorem. Literal loop
// elimination remains runtime; no composite rewrite or unification rule is
// needed by the packaging below.
assert
  (p : τ (Hom WalkingEnd_cat walking_base walking_base)) ⊢
  @walking_encode_loop_prefix_path p
  : τ (@= Nat_grpd
      (@walking_encode walking_base
        (@comp_fapp0
          WalkingEnd_cat walking_base walking_base walking_base
          walking_loop p))
      (succ (@walking_encode walking_base p)));

assert ⊢ walking_encode_function
  : τ (@Function_grpd
      (Hom WalkingEnd_cat walking_base walking_base)
      Nat_grpd);

assert ⊢ walking_encode_func
  : τ (Functor
      (Hom_cat WalkingEnd_cat walking_base walking_base)
      (Path_cat Nat_grpd));

assert
  (p : τ (Hom WalkingEnd_cat walking_base walking_base)) ⊢
  @fapp0
    (Hom_cat WalkingEnd_cat walking_base walking_base)
    (Path_cat Nat_grpd)
    walking_encode_func p
  ≡ @walking_encode walking_base p;

assert ⊢ walking_hom_nat_by_inverse
  : τ (@EquivByInverse
      (Hom WalkingEnd_cat walking_base walking_base)
      Nat_grpd
      walking_encode_function
      walking_power_function);

assert ⊢ walking_hom_nat_type_equiv
  : τ (TypeEquiv
      (Hom WalkingEnd_cat walking_base walking_base)
      Nat_grpd);

assert ⊢
  @type_equiv_to
    (Hom WalkingEnd_cat walking_base walking_base)
    Nat_grpd
    walking_hom_nat_type_equiv
  ≡ walking_encode_function;

assert ⊢
  @type_equiv_from
    (Hom WalkingEnd_cat walking_base walking_base)
    Nat_grpd
    walking_hom_nat_type_equiv
  ≡ walking_power_function;

assert ⊢ walking_hom_nat_omega_equiv
  : τ (@OmegaEquiv
      Grpd_cat
      (Hom WalkingEnd_cat walking_base walking_base)
      Nat_grpd);

// Dimension evidence and carrier equivalence provide distinct sethood proofs.
assert ⊢ walking_end_hom_is_set_from_dimension
  : τ (IsSetGrpd
      (Hom WalkingEnd_cat walking_base walking_base));

assert ⊢ walking_end_hom_is_set_from_equiv
  : τ (IsSetGrpd
      (Hom WalkingEnd_cat walking_base walking_base));

assert
  (q : τ (@=
      (Hom WalkingEnd_cat walking_base walking_base)
      walking_loop
      (@id WalkingEnd_cat walking_base))) ⊢
  @walking_loop_not_identity q
  : τ Empty_grpd;

assert
  (r : τ (Hom WalkingEnd_cat walking_base walking_base))
  (q : τ (@=
      (Hom WalkingEnd_cat walking_base walking_base)
      (@comp_fapp0
        WalkingEnd_cat walking_base walking_base walking_base
        walking_loop r)
      (@id WalkingEnd_cat walking_base))) ⊢
  @walking_loop_no_right_inverse r q
  : τ Empty_grpd;

assert
  (u : τ (@OmegaEquivAlong
      WalkingEnd_cat walking_base walking_base walking_loop)) ⊢
  @walking_loop_not_omega_equiv u
  : τ Empty_grpd;

// The derived hom-action layer turns alleged internal groupoidality into the
// impossible loop equivalence evidence above.
assert
  (g : τ (@IsGroupoidalCat WalkingEnd_cat)) ⊢
  @walking_loop_not_omega_equiv
    (@groupoidal_arrow_equiv_along
      WalkingEnd_cat g walking_base walking_base walking_loop)
  : τ Empty_grpd;

// catalog-area: auto
assert
  [A B : Cat]
  [P Q R : τ (Prof A B)]
  (s : τ (ProfMap Q R))
  (r : τ (ProfMap P Q)) ⊢
  @comp_fapp0
    (@Prof_cat (Op_cat B) (Op_cat A))
    (@Op_prof A B P)
    (@Op_prof A B Q)
    (@Op_prof A B R)
    (@Op_prof_map A B Q R s)
    (@Op_prof_map A B P Q r)
  ≡ @Op_prof_map
      A B P R
      (@comp_fapp0
        (@Prof_cat A B)
        P Q R
        s r);

assert [I A B : Cat]
  [P : τ (Prof A B)]
  [F : τ (Functor I A)]
  [M : τ (Functor I B)]
  (p : τ (@Prof_hom I A B F P M)) ⊢
  @Prof_cell_apply
    I A B A B
    (@Prof_tensor
      A B B P
      (@Hom_prof_along B B B (@id_func B) (@id_func B)))
    P
    (@id_func A)
    (@id_func B)
    F
    M
    (@tapp0_fapp0
      (@Prof_cat A B)
      (@Prof_cat A B)
      (@Prof_tensor_right_unit_func A B)
      (@id_func (@Prof_cat A B))
      P
      (@Prof_coyoneda_cov_transf A B))
    (@Prof_tensor_hom_hom
      I A B B
      P
      (@Hom_prof_along B B B (@id_func B) (@id_func B))
      F
      M
      M
      p
      (@Prof_func_hom I B M))
  ≡ p;

assert [I A B : Cat]
  [P P' : τ (Prof A B)]
  [F : τ (Functor I A)]
  [M : τ (Functor I B)]
  (pp : τ (@ProfMap A B P P'))
  (p : τ (@Prof_hom I A B F P M)) ⊢
  @Prof_cell_apply
    I A B A B
    (@Prof_tensor
      A B B P
      (@Hom_prof_along B B B (@id_func B) (@id_func B)))
    P'
    (@id_func A)
    (@id_func B)
    F
    M
    (@tapp1_fapp0
      (@Prof_cat A B)
      (@Prof_cat A B)
      (@Prof_tensor_right_unit_func A B)
      (@id_func (@Prof_cat A B))
      P P'
      (@Prof_coyoneda_cov_transf A B)
      pp)
    (@Prof_tensor_hom_hom
      I A B B
      P
      (@Hom_prof_along B B B (@id_func B) (@id_func B))
      F
      M
      M
      p
      (@Prof_func_hom I B M))
  ≡ @Prof_cell_apply
      I A B A B
      P P'
      (@id_func A)
      (@id_func B)
      F
      M
      pp p;

assert [I A B : Cat]
  [P : τ (Prof A B)]
  [F : τ (Functor I A)]
  [G : τ (Functor I B)]
  (p : τ (@Prof_hom I A B F P G)) ⊢
  @Prof_cell_apply
    I A B A B
    (@Prof_tensor
      A A B
      (@Hom_prof_along A A A (@id_func A) (@id_func A))
      P)
    P
    (@id_func A)
    (@id_func B)
    F
    G
    (@tapp0_fapp0
      (@Prof_cat A B)
      (@Prof_cat A B)
      (@Prof_tensor_left_unit_func A B)
      (@id_func (@Prof_cat A B))
      P
      (@Prof_coyoneda_con_transf A B))
    (@Prof_tensor_hom_hom
      I A A B
      (@Hom_prof_along A A A (@id_func A) (@id_func A))
      P
      F
      G
      F
      (@Prof_func_hom I A F)
      p)
  ≡ p;

assert [I A B : Cat]
  [P P' : τ (Prof A B)]
  [F : τ (Functor I A)]
  [G : τ (Functor I B)]
  (pp : τ (@ProfMap A B P P'))
  (p : τ (@Prof_hom I A B F P G)) ⊢
  @Prof_cell_apply
    I A B A B
    (@Prof_tensor
      A A B
      (@Hom_prof_along A A A (@id_func A) (@id_func A))
      P)
    P'
    (@id_func A)
    (@id_func B)
    F
    G
    (@tapp1_fapp0
      (@Prof_cat A B)
      (@Prof_cat A B)
      (@Prof_tensor_left_unit_func A B)
      (@id_func (@Prof_cat A B))
      P P'
      (@Prof_coyoneda_con_transf A B)
      pp)
    (@Prof_tensor_hom_hom
      I A A B
      (@Hom_prof_along A A A (@id_func A) (@id_func A))
      P
      F
      G
      F
      (@Prof_func_hom I A F)
      p)
  ≡ @Prof_cell_apply
      I A B A B
      P P'
      (@id_func A)
      (@id_func B)
      F
      G
      pp p;

// Covariant profunctor implication and eval/lambda calculus.
assert [A A' B B' X : Cat]
  (O : τ (Prof A X))
  (Q : τ (Prof B X))
  (F : τ (Functor A' A))
  (M : τ (Functor B' B)) ⊢
  @Prof_reindex
    A A' B B'
    (@Prof_imply_cov A B X O Q)
    F
    M
  ≡ @Prof_imply_cov
      A' B' X
      (@Prof_reindex A A' X X O F (@id_func X))
      (@Prof_reindex B B' X X Q M (@id_func X));

assert [A B X : Cat]
  (O : τ (Prof A X))
  (Q : τ (Prof B X)) ⊢
  @Prof_reindex
    A A B B
    (@Prof_imply_cov A B X O Q)
    (@id_func A)
    (@id_func B)
  ≡ @Prof_imply_cov A B X O Q;

assert [A B X : Cat]
  (Q : τ (Prof B X))
  (O : τ (Prof A X)) ⊢
  fapp0 (@Prof_imply_cov_func A B X Q) O
  ≡ @Prof_imply_cov A B X O Q;

assert [A B X : Cat]
  (Q : τ (Prof B X))
  [O O' : τ (Prof A X)] ⊢
  fapp1_func (@Prof_imply_cov_func A B X Q) [O] [O']
  : τ (Functor
      (@Functord_cat
        (Product_cat (Op_cat A) X)
        O O')
      (@Functord_cat
        (Product_cat (Op_cat A) B)
        (@Prof_imply_cov A B X O Q)
        (@Prof_imply_cov A B X O' Q)));

assert [A B X : Cat]
  (Q : τ (Prof B X))
  [O O' : τ (Prof A X)]
  (o : τ (Functord O O')) ⊢
  fapp1_fapp0
    (@Prof_imply_cov_func A B X Q)
    [O] [O'] o
  : τ (Functord
      (@Prof_imply_cov A B X O Q)
      (@Prof_imply_cov A B X O' Q));

assert [A B X : Cat]
  (Q : τ (Prof B X))
  (O : τ (Prof A X)) ⊢
  @fapp1_fapp0
    (@Prof_cat A X)
    (@Prof_cat A B)
    (@Prof_imply_cov_func A B X Q)
    O O
    (@id (@Prof_cat A X) O)
  ≡ @id (@Prof_cat A B) (@Prof_imply_cov A B X O Q);

assert [A B X : Cat]
  (Q : τ (Prof B X))
  [O O' O'' : τ (Prof A X)]
  (o : τ (ProfMap O O'))
  (o' : τ (ProfMap O' O'')) ⊢
  @comp_fapp0
      (@Prof_cat A B)
      (@Prof_imply_cov A B X O Q)
      (@Prof_imply_cov A B X O' Q)
      (@Prof_imply_cov A B X O'' Q)
      (fapp1_fapp0
        (@Prof_imply_cov_func A B X Q)
        [O'] [O''] o')
      (fapp1_fapp0
        (@Prof_imply_cov_func A B X Q)
        [O] [O'] o)
  ≡ fapp1_fapp0
      (@Prof_imply_cov_func A B X Q)
      [O] [O'']
      (@comp_fapp0
        (@Prof_cat A X)
        O O' O'' o' o);

assert [A B X : Cat]
  (oq : τ (Obj
    (Product_cat
      (Prof_cat A X)
      (Op_cat (Prof_cat B X))))) ⊢
  @fapp0
    (Product_cat
      (Prof_cat A X)
      (Op_cat (Prof_cat B X)))
    (Prof_cat A B)
    (@Prof_imply_cov_func2 A B X)
    oq
  ≡ @Prof_imply_cov
      A B X
      (sigma_Fst oq)
      (sigma_Snd oq);

assert [A B X : Cat]
  [oq oq' : τ (Obj
    (Product_cat
      (Prof_cat A X)
      (Op_cat (Prof_cat B X))))] ⊢
  @fapp1_func
    (Product_cat
      (Prof_cat A X)
      (Op_cat (Prof_cat B X)))
    (Prof_cat A B)
    (@Prof_imply_cov_func2 A B X)
    oq oq'
  : τ (Functor
      (Hom_cat
        (Product_cat
          (Prof_cat A X)
          (Op_cat (Prof_cat B X)))
        oq oq')
      (Hom_cat
        (Prof_cat A B)
        (fapp0 (@Prof_imply_cov_func2 A B X) oq)
        (fapp0 (@Prof_imply_cov_func2 A B X) oq')));

assert [A B X : Cat]
  [oq oq' : τ (Obj
    (Product_cat
      (Prof_cat A X)
      (Op_cat (Prof_cat B X))))]
  (r : τ (Hom
    (Product_cat
      (Prof_cat A X)
      (Op_cat (Prof_cat B X)))
    oq oq')) ⊢
  @fapp1_fapp0
    (Product_cat
      (Prof_cat A X)
      (Op_cat (Prof_cat B X)))
    (Prof_cat A B)
    (@Prof_imply_cov_func2 A B X)
    oq oq' r
  : τ (Hom
      (Prof_cat A B)
      (@Prof_imply_cov A B X (sigma_Fst oq) (sigma_Snd oq))
      (@Prof_imply_cov A B X (sigma_Fst oq') (sigma_Snd oq')));

assert [A B X : Cat]
  (oq : τ (Obj
    (Product_cat
      (Prof_cat A X)
      (Op_cat (Prof_cat B X))))) ⊢
  @fapp1_fapp0
    (Product_cat
      (Prof_cat A X)
      (Op_cat (Prof_cat B X)))
    (Prof_cat A B)
    (@Prof_imply_cov_func2 A B X)
    oq oq
    (@id
      (Product_cat
        (Prof_cat A X)
        (Op_cat (Prof_cat B X)))
      oq)
  ≡ @id
      (@Prof_cat A B)
      (@Prof_imply_cov
        A B X
        (sigma_Fst oq)
        (sigma_Snd oq));

assert [A B X : Cat]
  [oq0 oq1 oq2 : τ (Obj
    (Product_cat
      (Prof_cat A X)
      (Op_cat (Prof_cat B X))))]
  (r01 : τ (Hom
    (Product_cat
      (Prof_cat A X)
      (Op_cat (Prof_cat B X)))
    oq0 oq1))
  (r12 : τ (Hom
    (Product_cat
      (Prof_cat A X)
      (Op_cat (Prof_cat B X)))
    oq1 oq2)) ⊢
  @comp_fapp0
      (Prof_cat A B)
      (fapp0 (@Prof_imply_cov_func2 A B X) oq0)
      (fapp0 (@Prof_imply_cov_func2 A B X) oq1)
      (fapp0 (@Prof_imply_cov_func2 A B X) oq2)
      (fapp1_fapp0 (@Prof_imply_cov_func2 A B X) r12)
      (fapp1_fapp0 (@Prof_imply_cov_func2 A B X) r01)
  ≡ fapp1_fapp0
      (@Prof_imply_cov_func2 A B X)
      (@comp_fapp0
        (Product_cat
          (Prof_cat A X)
          (Op_cat (Prof_cat B X)))
        oq0 oq1 oq2 r12 r01);

assert [A B X : Cat]
  [P : τ (Prof A B)]
  [Q : τ (Prof B X)]
  [O : τ (Prof A X)]
  (t : τ (ProfMap P (@Prof_imply_cov A B X O Q))) ⊢
  @Prof_lambda_cov_map A B X P Q O
    (@Prof_eval_cov_map A B X P Q O t)
  ≡ t;

assert [A B X : Cat]
  [P : τ (Prof A B)]
  [Q : τ (Prof B X)]
  [O : τ (Prof A X)]
  (t : τ (ProfMap (@Prof_tensor A B X P Q) O)) ⊢
  @Prof_eval_cov_map A B X P Q O
    (@Prof_lambda_cov_map A B X P Q O t)
  ≡ t;

assert [A B B' X X' : Cat]
  (P : τ (Prof A B))
  (O : τ (Prof A X))
  (M : τ (Functor B' B))
  (G : τ (Functor X' X)) ⊢
  @Prof_reindex
    B B' X X'
    (@Prof_imply_con A B X P O)
    M
    G
  ≡ @Prof_imply_con
      A B' X'
      (@Prof_reindex A A B B' P (@id_func A) M)
      (@Prof_reindex A A X X' O (@id_func A) G);

assert [A B X : Cat]
  (P : τ (Prof A B))
  (O : τ (Prof A X)) ⊢
  @Prof_reindex
    B B X X
    (@Prof_imply_con A B X P O)
    (@id_func B)
    (@id_func X)
  ≡ @Prof_imply_con A B X P O;

assert [A B X : Cat]
  [P : τ (Prof A B)]
  [Q : τ (Prof B X)]
  [O : τ (Prof A X)]
  (t : τ (ProfMap Q (@Prof_imply_con A B X P O))) ⊢
  @Prof_lambda_con_map A B X P Q O
    (@Prof_eval_con_map A B X P Q O t)
  ≡ t;

assert [A B X : Cat]
  [P : τ (Prof A B)]
  [Q : τ (Prof B X)]
  [O : τ (Prof A X)]
  (t : τ (ProfMap (@Prof_tensor A B X P Q) O)) ⊢
  @Prof_eval_con_map A B X P Q O
    (@Prof_lambda_con_map A B X P Q O t)
  ≡ t;

assert [B J J' : Cat]
  (F : τ (Functor J B))
  (W : τ (Prof J' J)) ⊢
  @WeightedCone_prof B J J' F W
  ≡ @Prof_imply_cov
      B J' J
      (@Hom_prof J B F)
      W;

// Weighted limit and colimit specialization typing.
//
// These assertions audit variance and classifier formation only.  They do
// not assert the missing semantic end/coend identifications with ordinary
// cone, cocone, or pointwise Kan-extension categories.
assert [B J : Cat]
  (F : τ (Functor J B))
  (L : τ (Functor Terminal_cat B)) ⊢
  @IsWeightedLimit_cov_comp
    B J Terminal_cat
    F
    (@Terminal_prof Terminal_cat J)
    L
  : Grpd;

assert [B J J' : Cat]
  (K : τ (Functor J J'))
  (F : τ (Functor J B))
  (Ran : τ (Functor J' B)) ⊢
  @IsWeightedLimit_cov_comp
    B J J'
    F
    (@Conjoint_prof J J' K)
    Ran
  : Grpd;

assert [B J : Cat]
  (F : τ (Functor J B))
  (L : τ (Functor Terminal_cat B)) ⊢
  @WeightedColimit_con
    B J Terminal_cat
    F
    (@Terminal_prof J Terminal_cat)
    L
  : Grpd;

assert [B J J' : Cat]
  (K : τ (Functor J J'))
  (F : τ (Functor J B))
  (Lan : τ (Functor J' B)) ⊢
  @WeightedColimit_con
    B J J'
    F
    (@Companion_prof J J' K)
    Lan
  : Grpd;

assert [B J J' : Cat]
  (F : τ (Functor J B))
  (W : τ (Prof J' J))
  (L : τ (Functor J' B)) ⊢
  @IsWeightedLimit_cov_iso B J J' F W L
  ≡ @IsoEvidence
      (@Prof_cat B J')
      (@Prof_imply_cov
        B J' J
        (@Hom_prof J B F)
        W)
      (@Conjoint_prof J' B L);

assert [B J J' : Cat]
  (W : τ (Prof J' J))
  [O O' : τ (Prof B J)]
  (i : τ (@IsoEvidence (@Prof_cat B J) O O')) ⊢
  @iso_evidence_fmap
    (@Prof_cat B J)
    (@Prof_cat B J')
    (@Prof_imply_cov_func B J' J W)
    O O' i
  : τ (@IsoEvidence
      (@Prof_cat B J')
      (@Prof_imply_cov B J' J O W)
      (@Prof_imply_cov B J' J O' W));

// Computational profunctor comparisons and weighted representability.
assert [A B : Cat]
  [P Q : τ (Prof A B)]
  (i : τ (@ProfComparison A B P Q)) ⊢
  @prof_comparison_evidence A B P Q i
  : τ (@IsoEvidence (@Prof_cat A B) P Q);

assert [A B : Cat]
  [P Q : τ (Prof A B)]
  (i : τ (@ProfComparison A B P Q)) ⊢
  @comp_fapp0
    (@Prof_cat A B)
    P Q P
    (@prof_comparison_from A B P Q i)
    (@prof_comparison_to A B P Q i)
  ≡ @id (@Prof_cat A B) P;

assert [A B : Cat]
  [P Q R S : τ (Prof A B)]
  (i : τ (@ProfComparison A B P Q))
  (r : τ (@ProfMap A B R P))
  (h : τ (@ProfMap A B S R)) ⊢
  @comp_fapp0
    (@Prof_cat A B)
    S R Q
    (@prof_comparison_push A B P Q i R r)
    h
  ≡ @prof_comparison_push A B P Q i S
      (@comp_fapp0
        (@Prof_cat A B)
        S R P r h);

assert [A B : Cat]
  [P Q R : τ (Prof A B)]
  (i : τ (@ProfComparison A B P Q))
  (r : τ (@ProfMap A B R P)) ⊢
  @prof_comparison_pull A B P Q i R
    (@prof_comparison_push A B P Q i R r)
  ≡ r;

assert [A B : Cat]
  [P Q R : τ (Prof A B)]
  (i : τ (@ProfComparison A B P Q))
  (s : τ (@ProfMap A B R Q)) ⊢
  @prof_comparison_push A B P Q i R
    (@prof_comparison_pull A B P Q i R s)
  ≡ s;

assert [A B : Cat]
  [P R : τ (Prof A B)]
  (r : τ (@ProfMap A B R P)) ⊢
  @prof_comparison_push
    A B P P
    (@prof_comparison_refl A B P)
    R r
  ≡ r;

assert [A B : Cat]
  [P Q S R : τ (Prof A B)]
  (i : τ (@ProfComparison A B P Q))
  (j : τ (@ProfComparison A B Q S))
  (r : τ (@ProfMap A B R P)) ⊢
  @prof_comparison_push
    A B P S
    (@prof_comparison_comp A B P Q S j i)
    R r
  ≡ @prof_comparison_push A B Q S j R
      (@prof_comparison_push A B P Q i R r);

assert [B J J' : Cat]
  [F : τ (Functor J B)]
  [W : τ (Prof J' J)]
  [L : τ (Functor J' B)]
  (isl : τ (@IsWeightedLimit_cov_comp B J J' F W L)) ⊢
  @prof_comparison_evidence
    B J'
    (@WeightedCone_prof B J J' F W)
    (@Hom_prof J' B L)
    isl
  : τ (@IsWeightedLimit_cov_iso B J J' F W L);

assert [B J J' I : Cat]
  [F : τ (Functor J B)]
  [W : τ (Prof J' J)]
  [L : τ (Functor J' B)]
  (isl : τ (@IsWeightedLimit_cov_comp B J J' F W L))
  (M : τ (Functor I B))
  [R : τ (Prof I J')]
  (r : τ (ProfMap
      R
      (@Prof_imply_cov
        I J' J
        (@Hom_prof_along I J B M F)
        W))) ⊢
  @weighted_limit_cov_pull B J J' F W L isl I M R
    (@weighted_limit_cov_push B J J' F W L isl I M R r)
  ≡ r;

assert [B J J' I : Cat]
  [F : τ (Functor J B)]
  [W : τ (Prof J' J)]
  [L : τ (Functor J' B)]
  (isl : τ (@IsWeightedLimit_cov_comp B J J' F W L))
  (M : τ (Functor I B))
  [R : τ (Prof I J')]
  (s : τ (ProfMap R (@Hom_prof_along I J' B M L))) ⊢
  @weighted_limit_cov_push B J J' F W L isl I M R
    (@weighted_limit_cov_pull B J J' F W L isl I M R s)
  ≡ s;

assert [B J J' A : Cat]
  [Ladj : τ (Functor A B)]
  [Radj : τ (Functor B A)]
  [W : τ (Prof J' J)]
  [F : τ (Functor J B)]
  [L : τ (Functor J' B)]
  (isl : τ (@IsWeightedLimit_cov_comp B J J' F W L))
  (adj : τ (@Adjunction A B Ladj Radj)) ⊢
  @right_adjoint_preserves_weighted_limit_cov_comp
    B J J' A Ladj Radj W F L isl adj
  : τ (@IsWeightedLimit_cov_comp
      A J J'
      (@comp_cat_fapp0
        J B A
        Radj
        F)
      W
      (@comp_cat_fapp0
        J' B A
        Radj
        L));

assert [A B I K : Cat]
  [Ladj : τ (Functor A B)]
  [Radj : τ (Functor B A)]
  (adj : τ (@Adjunction A B Ladj Radj))
  (M : τ (Functor I A))
  (F : τ (Functor K B))
  [R : τ (Prof I K)]
  (r : τ (ProfMap
    R
    (@Hom_prof_along
      I K B
      (@comp_cat_fapp0 I A B Ladj M)
      F))) ⊢
  @prof_comparison_pull
    I K
    (@Hom_prof_along
      I K B
      (@comp_cat_fapp0 I A B Ladj M)
      F)
    (@Hom_prof_along
      I K A
      M
      (@comp_cat_fapp0 K B A Radj F))
    (@Adjunction_hom_prof_comparison_along
      A B Ladj Radj adj I K M F)
    R
    (@prof_comparison_push
      I K
      (@Hom_prof_along
        I K B
        (@comp_cat_fapp0 I A B Ladj M)
        F)
      (@Hom_prof_along
        I K A
        M
        (@comp_cat_fapp0 K B A Radj F))
      (@Adjunction_hom_prof_comparison_along
        A B Ladj Radj adj I K M F)
      R r)
  ≡ r;

assert [A B I K : Cat]
  [Ladj : τ (Functor A B)]
  [Radj : τ (Functor B A)]
  (adj : τ (@Adjunction A B Ladj Radj))
  (M : τ (Functor I A))
  (F : τ (Functor K B))
  [R : τ (Prof I K)]
  (s : τ (ProfMap
    R
    (@Hom_prof_along
      I K A
      M
      (@comp_cat_fapp0 K B A Radj F)))) ⊢
  @prof_comparison_push
    I K
    (@Hom_prof_along
      I K B
      (@comp_cat_fapp0 I A B Ladj M)
      F)
    (@Hom_prof_along
      I K A
      M
      (@comp_cat_fapp0 K B A Radj F))
    (@Adjunction_hom_prof_comparison_along
      A B Ladj Radj adj I K M F)
    R
    (@prof_comparison_pull
      I K
      (@Hom_prof_along
        I K B
        (@comp_cat_fapp0 I A B Ladj M)
        F)
      (@Hom_prof_along
        I K A
        M
        (@comp_cat_fapp0 K B A Radj F))
      (@Adjunction_hom_prof_comparison_along
        A B Ladj Radj adj I K M F)
      R s)
  ≡ s;

assert [K : Cat] (A : Cat)
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat (Const_catd K A) x)))
  (v : τ (Obj (Fibre_cat (Const_catd K A) y))) ⊢
  @homd_ K
    (Const_catd K A)
    (Const_catd K A)
    (@id_funcd K (Const_catd K A))
    x u y v
    ≡ @Const_catd (Op_cat (Hom_cat K x y)) (Hom_cat A u v);

assert [K : Cat] (A : Cat)
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat (Const_catd K A) x)))
  (v : τ (Obj (Fibre_cat (Const_catd K A) y)))
  (f g : τ (Obj (Op_cat (Hom_cat K x y)))) ⊢
  @fapp1_func
    (Op_cat (Hom_cat K x y))
    Cat_cat
    (@homd_ K
      (Const_catd K A)
      (Const_catd K A)
      (@id_funcd K (Const_catd K A))
      x u y v)
    f
    g
    ≡ @fapp1_func
        (Op_cat (Hom_cat K x y))
        Cat_cat
        (@Const_catd (Op_cat (Hom_cat K x y)) (Hom_cat A u v))
        f
        g;

assert [K : Cat] (A : Cat)
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat (Const_catd K A) x)))
  (v : τ (Obj (Fibre_cat (Const_catd K A) y)))
  (f g : τ (Obj (Op_cat (Hom_cat K x y))))
  (alpha : τ (Hom (Op_cat (Hom_cat K x y)) f g)) ⊢
  @fapp1_fapp0
    (Op_cat (Hom_cat K x y))
    Cat_cat
    (@homd_ K
      (Const_catd K A)
      (Const_catd K A)
      (@id_funcd K (Const_catd K A))
      x u y v)
    f
    g
    alpha
    ≡ @fapp1_fapp0
        (Op_cat (Hom_cat K x y))
        Cat_cat
        (@Const_catd (Op_cat (Hom_cat K x y)) (Hom_cat A u v))
        f
        g
        alpha;

assert [K : Cat]
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat (Terminal_catd K) x)))
  (v : τ (Obj (Fibre_cat (Terminal_catd K) y))) ⊢
  @homd_ K
    (Terminal_catd K)
    (Terminal_catd K)
    (@id_funcd K (Terminal_catd K))
    x u y v
    ≡ @Terminal_catd (Op_cat (Hom_cat K x y));

assert [K : Cat]
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat (Terminal_catd K) x)))
  (v : τ (Obj (Fibre_cat (Terminal_catd K) y)))
  (f g : τ (Obj (Op_cat (Hom_cat K x y)))) ⊢
  @fapp1_func
    (Op_cat (Hom_cat K x y))
    Cat_cat
    (@homd_ K
      (Terminal_catd K)
      (Terminal_catd K)
      (@id_funcd K (Terminal_catd K))
      x u y v)
    f
    g
    ≡ @fapp1_func
        (Op_cat (Hom_cat K x y))
        Cat_cat
        (@Terminal_catd (Op_cat (Hom_cat K x y)))
        f
        g;

assert [K : Cat]
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat (Terminal_catd K) x)))
  (v : τ (Obj (Fibre_cat (Terminal_catd K) y)))
  (f g : τ (Obj (Op_cat (Hom_cat K x y))))
  (alpha : τ (Hom (Op_cat (Hom_cat K x y)) f g)) ⊢
  @fapp1_fapp0
    (Op_cat (Hom_cat K x y))
    Cat_cat
    (@homd_ K
      (Terminal_catd K)
      (Terminal_catd K)
      (@id_funcd K (Terminal_catd K))
      x u y v)
    f
    g
    alpha
    ≡ @fapp1_fapp0
        (Op_cat (Hom_cat K x y))
        Cat_cat
        (@Terminal_catd (Op_cat (Hom_cat K x y)))
        f
        g
        alpha;

assert [K : Cat] (A : Cat)
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat (Const_catd K A) x))) ⊢
  @fib_cov_tapp0_func K (@Const_catd K A) x y u
    ≡ @Const_func (Hom_cat K x y) A u;

assert [K : Cat] (A : Cat)
  (x y : τ (Obj K))
  (f : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat (Const_catd K A) x))) ⊢
  fapp0 (@fib_cov_tapp0_func K (@Const_catd K A) x y u) f
    ≡ u;

assert [K : Cat] (E : τ (Catd K))
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y)))
  (f : τ (Obj (Op_cat (Hom_cat K x y)))) ⊢
  @fapp0 (Op_cat (Hom_cat K x y)) Cat_cat
    (@homd_ K E E (@id_funcd K E) x u y v)
    f
    ≡ Hom_cat (Fibre_cat E y)
        (fapp0 (@fib_cov_tapp0_func K E x y u) f)
        v;

assert [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  (x y : τ (Obj K))
  (f : τ (Hom K x y)) ⊢
  @piapp1_src_obj K E s x y f
    ≡ fapp0 (@fib_cov_tapp0_func K E x y (@piapp0 K E s x)) f;

assert [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  (x y : τ (Obj K))
  (f : τ (Hom K x y)) ⊢
  fapp0
    (homd_
      (@id_funcd K E)
      x (@piapp0 K E s x)
      y (@piapp0 K E s y))
    f
    ≡ Hom_cat (Fibre_cat E y)
        (@piapp1_src_obj K E s x y f)
        (@piapp0 K E s y);

assert [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  (x y : τ (Obj K))
  (f : τ (Hom K x y)) ⊢
  @fapp0 (Op_cat (Hom_cat K x y)) Cat_cat
    (@homd_
      K
      (@Const_catd K Terminal_cat)
      E
      s
      x
      (@piapp0 K E s x)
      y
      Terminal_obj)
    f
    ≡ Hom_cat (Fibre_cat E y)
        (@piapp1_src_obj K E s x y f)
        (@piapp0 K E s y);

assert [K : Cat] (A : Cat)
  (s : τ (Obj (Pi_cat (Const_catd K A))))
  (x y : τ (Obj K))
  (f : τ (Hom K x y)) ⊢
  @piapp1_src_obj K (@Const_catd K A) s x y f
    ≡ @fapp0 K A s x;

assert [K : Cat] (E : τ (Catd K))
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y)))
  (f g : τ (Obj (Op_cat (Hom_cat K x y)))) ⊢
  @fapp1_func
    (Op_cat (Hom_cat K x y))
    Cat_cat
    (@homd_ K E E (@id_funcd K E) x u y v)
    f
    g
    ≡ @fapp1_func
        (Op_cat (Hom_cat K x y))
        Cat_cat
        (@hom_con
          (Fibre_cat E y)
          v
          (Hom_cat K x y)
          (@fib_cov_tapp0_func K E x y u))
        f
        g;

assert [K : Cat] (E : τ (Catd K))
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y)))
  (f g : τ (Obj (Op_cat (Hom_cat K x y))))
  (alpha : τ (Hom (Op_cat (Hom_cat K x y)) f g)) ⊢
  @fapp1_fapp0
    (Op_cat (Hom_cat K x y))
    Cat_cat
    (@homd_ K E E (@id_funcd K E) x u y v)
    f
    g
    alpha
    ≡ @fapp1_fapp0
        (Op_cat (Hom_cat K x y))
        Cat_cat
        (@hom_con
          (Fibre_cat E y)
          v
          (Hom_cat K x y)
          (@fib_cov_tapp0_func K E x y u))
        f
        g
        alpha;

assert [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  (x y : τ (Obj K))
  (f : τ (Hom K x y)) ⊢
  @piapp1_fapp0 K E s x y f
    ≡ piapp0 (@piapp1_func K E s x y) f;

// First higher action of the section-action section.  Its runtime result
// stays in the generic displayed internal-hom projection cascade.
assert [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  (x y : τ (Obj K))
  (f g : τ (Obj (Op_cat (Hom_cat K x y))))
  (alpha : τ (Hom (Op_cat (Hom_cat K x y)) f g)) ⊢
  @piapp1_fapp0
    (Op_cat (Hom_cat K x y))
    (@homd_
      K E E (@id_funcd K E)
      x (@piapp0 K E s x)
      y (@piapp0 K E s y))
    (@piapp1_func K E s x y)
    f
    g
    alpha
  ≡ @fdapp1_int_hom_fapp0
      (Op_cat (Hom_cat K x y))
      (@Const_catd (Op_cat (Hom_cat K x y)) Terminal_cat)
      (@homd_
        K E E (@id_funcd K E)
        x (@piapp0 K E s x)
        y (@piapp0 K E s y))
      (@piapp1_func K E s x y)
      f
      g
      alpha
      Terminal_obj
      Terminal_obj
      Terminal_obj;

assert [K : Cat] (A : Cat)
  (s : τ (Obj (Pi_cat (Const_catd K A))))
  (x y : τ (Obj K))
  (f : τ (Hom K x y)) ⊢
  @piapp1_const_fapp0_eq K A s x y f
  : τ (@=
      (Hom A
        (@fapp0 K A s x)
        (@fapp0 K A s y))
      (@piapp1_fapp0 K (@Const_catd K A) s x y f)
      (@fapp1_fapp0 K A s x y f));

assertnot [K : Cat] (A : Cat)
  (s : τ (Obj (Pi_cat (Const_catd K A))))
  (x y : τ (Obj K))
  (f : τ (Hom K x y)) ⊢
  @piapp1_fapp0 K (@Const_catd K A) s x y f
    ≡ @fapp1_fapp0 K A s x y f;

assert [Z : Cat] (E : τ (Catd Z))
  (x y : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y))) ⊢
  Hom_cat (@Sigma_cat Z E) (Struct_sigma x u) (Struct_sigma y v)
    ≡ Op_cat
        (@Sigma_cat
          (Op_cat (Hom_cat Z x y))
          (@homd_ Z E E (@id_funcd Z E) x u y v));

assert [K : Cat] (E D : τ (Catd K)) (η : τ (Functord E D))
  (k : τ (Obj K)) (u : τ (Obj (Fibre_cat E k))) ⊢
  @fapp0 (@Sigma_cat K E) (@Sigma_cat K D)
    (@sigma_map_func K E D η)
    (Struct_sigma k u)
    ≡ @Struct_sigma
        (Obj K)
        (λ kk : τ (Obj K), Obj (Fibre_cat D kk))
        k
        (@fapp0 (Fibre_cat E k) (Fibre_cat D k)
          (@tapp0_fapp0 K Cat_cat E D k η)
          u);

assert [K : Cat] (E D : τ (Catd K)) (η : τ (Functord E D))
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y))) ⊢
  @fapp1_func
    (@Sigma_cat K E)
    (@Sigma_cat K D)
    (@sigma_map_func K E D η)
    (Struct_sigma x u)
    (Struct_sigma y v)
    ≡ @Op_func
        (@Sigma_cat
          (Op_cat (Hom_cat K x y))
          (fapp0 (@homd_id_tgt_func K E x u y) v))
        (@Sigma_cat
          (Op_cat (Hom_cat K x y))
          (fapp0 (@homd_ff_tgt_func K E D η x u y) v))
        (@sigma_map_func
          (Op_cat (Hom_cat K x y))
          (fapp0 (@homd_id_tgt_func K E x u y) v)
          (fapp0 (@homd_ff_tgt_func K E D η x u y) v)
          (@fdapp1_int_presheaf_arrow K E D η x u y v));

assert [K : Cat] (E D : τ (Catd K)) (η : τ (Functord E D))
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y)))
  (p : τ (Hom K x y))
  (alpha : τ (Hom
      (Fibre_cat E y)
      (@fapp0
        (Fibre_cat E x)
        (Fibre_cat E y)
        (@catd_transport_func K E x y p)
        u)
      v)) ⊢
  @fapp1_fapp0
    (@Sigma_cat K E)
    (@Sigma_cat K D)
    (@sigma_map_func K E D η)
    (Struct_sigma x u)
    (Struct_sigma y v)
    (@sigma_arrow K E x y u v p alpha)
    ≡ @sigma_arrow
        K
        D
        x
        y
        (@fapp0
          (Fibre_cat E x)
          (Fibre_cat D x)
          (@tapp0_fapp0 K Cat_cat E D x η)
          u)
        (@fapp0
          (Fibre_cat E y)
          (Fibre_cat D y)
          (@tapp0_fapp0 K Cat_cat E D y η)
          v)
        p
        (@fdapp1_int_hom_fapp0
          K
          E
          D
          η
          x
          y
          p
          u
          v
          alpha);

assert [K : Cat] (E D : τ (Catd K)) (η : τ (Functord E D))
  (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @sigma_map_transport_arrow K E D η x y p u
    ≡ @sigma_arrow
        K
        D
        x
        y
        (@fapp0
          (Fibre_cat E x)
          (Fibre_cat D x)
          (@tapp0_fapp0 K Cat_cat E D x η)
          u)
        (@fapp0
          (Fibre_cat E y)
          (Fibre_cat D y)
          (@tapp0_fapp0 K Cat_cat E D y η)
          (fapp0 (@fapp1_fapp0 K Cat_cat E x y p) u))
        p
        (@fdapp1_int_cell K E D η x y p u);

assert [K : Cat] (E D : τ (Catd K)) (η : τ (Functord E D)) ⊢
  @comp_cat_fapp0 (@Sigma_cat K E) (@Sigma_cat K D) K
    (@Sigma_proj1_func K D)
    (@sigma_map_func K E D η)
    ≡ @Sigma_proj1_func K E;

// A terminal section gives the first, transparent factor of contextual
// pairing: A -> Sigma_A(const_A 1).
symbol sigma_terminal_total_func_check
  (A : Cat)
  : τ (Functor
      A
      (@Sigma_cat A (@Const_catd A Terminal_cat)))
≔ @Struct_sigma
    (Obj (Functor_cat A A))
    (λ _ : τ (Obj (Functor_cat A A)),
      Obj (Functor_cat A Terminal_cat))
    (@id_func A)
    (@Const_func A Terminal_cat Terminal_obj);

// Contextual pairing is not a second owner. It is the explicit composite of
// terminal totalization, the fixed-base Sigma map, and pullback totalization.
symbol contextual_pair_pullback_total_check
  [A K : Cat]
  (F : τ (Functor A K))
  (E : τ (Catd K))
  (s : τ (Obj (@Pi_cat A (@Pullback_catd A K E F))))
  : τ (Functor A (@Sigma_cat K E))
≔ @comp_cat_fapp0
    A
    (@Sigma_cat A (@Pullback_catd A K E F))
    (@Sigma_cat K E)
    (@sigma_pullback_total_func A K F E)
    (@comp_cat_fapp0
      A
      (@Sigma_cat A (@Const_catd A Terminal_cat))
      (@Sigma_cat A (@Pullback_catd A K E F))
      (@sigma_map_func
        A
        (@Const_catd A Terminal_cat)
        (@Pullback_catd A K E F)
        s)
      (@sigma_terminal_total_func_check A));

// Pullback totalization exposes exactly its base-changed dependent pair.
assert [A K : Cat]
  (F : τ (Functor A K))
  (D : τ (Catd K))
  (a : τ (Obj A))
  (u : τ (Obj (Fibre_cat (@Pullback_catd A K D F) a))) ⊢
  @fapp0
    (@Sigma_cat A (@Pullback_catd A K D F))
    (@Sigma_cat K D)
    (@sigma_pullback_total_func A K F D)
    (Struct_sigma a u)
  ≡ @Struct_sigma
      (Obj K)
      (λ k : τ (Obj K), Obj (Fibre_cat D k))
      (@fapp0 A K F a)
      u;

assert [A K : Cat]
  (F : τ (Functor A K))
  (D : τ (Catd K))
  (a b : τ (Obj A))
  (u : τ (Obj (Fibre_cat (@Pullback_catd A K D F) a)))
  (v : τ (Obj (Fibre_cat (@Pullback_catd A K D F) b)))
  (p : τ (Hom A a b))
  (alpha : τ (Hom
      (Fibre_cat D (@fapp0 A K F b))
      (@fapp0
        (Fibre_cat D (@fapp0 A K F a))
        (Fibre_cat D (@fapp0 A K F b))
        (@catd_transport_func
          K D
          (@fapp0 A K F a)
          (@fapp0 A K F b)
          (@fapp1_fapp0 A K F a b p))
        u)
      v)) ⊢
  @fapp1_fapp0
    (@Sigma_cat A (@Pullback_catd A K D F))
    (@Sigma_cat K D)
    (@sigma_pullback_total_func A K F D)
    (Struct_sigma a u)
    (Struct_sigma b v)
    (@sigma_arrow
      A
      (@Pullback_catd A K D F)
      a b u v p alpha)
  ≡ @sigma_arrow
      K
      D
      (@fapp0 A K F a)
      (@fapp0 A K F b)
      u
      v
      (@fapp1_fapp0 A K F a b p)
      alpha;

// The transparent contextual pair computes on both objects and base arrows.
assert [A K : Cat]
  (F : τ (Functor A K))
  (E : τ (Catd K))
  (s : τ (Obj (@Pi_cat A (@Pullback_catd A K E F))))
  (a : τ (Obj A)) ⊢
  @fapp0
    A
    (@Sigma_cat K E)
    (@contextual_pair_pullback_total_check A K F E s)
    a
  ≡ @Struct_sigma
      (Obj K)
      (λ k : τ (Obj K), Obj (Fibre_cat E k))
      (@fapp0 A K F a)
      (@piapp0 A (@Pullback_catd A K E F) s a);

assert [A K : Cat]
  (F : τ (Functor A K))
  (E : τ (Catd K))
  (s : τ (Obj (@Pi_cat A (@Pullback_catd A K E F))))
  (a b : τ (Obj A))
  (p : τ (Hom A a b)) ⊢
  @fapp1_fapp0
    A
    (@Sigma_cat K E)
    (@contextual_pair_pullback_total_check A K F E s)
    a b p
  ≡ @sigma_arrow
      K
      E
      (@fapp0 A K F a)
      (@fapp0 A K F b)
      (@piapp0 A (@Pullback_catd A K E F) s a)
      (@piapp0 A (@Pullback_catd A K E F) s b)
      (@fapp1_fapp0 A K F a b p)
      (@piapp1_fapp0
        A
        (@Pullback_catd A K E F)
        s
        a b p);

// Substitution of a further genuinely dependent family computes at objects.
assert [A K : Cat]
  (F : τ (Functor A K))
  (E : τ (Catd K))
  (s : τ (Obj (@Pi_cat A (@Pullback_catd A K E F))))
  (D : τ (Catd (@Sigma_cat K E)))
  (a : τ (Obj A)) ⊢
  @Fibre_cat
    A
    (@Pullback_catd
      A
      (@Sigma_cat K E)
      D
      (@contextual_pair_pullback_total_check A K F E s))
    a
  ≡ @Fibre_cat
      (@Sigma_cat K E)
      D
      (@Struct_sigma
        (Obj K)
        (λ k : τ (Obj K), Obj (Fibre_cat E k))
        (@fapp0 A K F a)
        (@piapp0 A (@Pullback_catd A K E F) s a));

// The same substitution retains the further family's directed arrow action.
assert [A K : Cat]
  (F : τ (Functor A K))
  (E : τ (Catd K))
  (s : τ (Obj (@Pi_cat A (@Pullback_catd A K E F))))
  (D : τ (Catd (@Sigma_cat K E)))
  (a b : τ (Obj A))
  (p : τ (Hom A a b)) ⊢
  @fapp1_fapp0
    A
    Cat_cat
    (@Pullback_catd
      A
      (@Sigma_cat K E)
      D
      (@contextual_pair_pullback_total_check A K F E s))
    a b p
  ≡ @fapp1_fapp0
      (@Sigma_cat K E)
      Cat_cat
      D
      (@Struct_sigma
        (Obj K)
        (λ k : τ (Obj K), Obj (Fibre_cat E k))
        (@fapp0 A K F a)
        (@piapp0 A (@Pullback_catd A K E F) s a))
      (@Struct_sigma
        (Obj K)
        (λ k : τ (Obj K), Obj (Fibre_cat E k))
        (@fapp0 A K F b)
        (@piapp0 A (@Pullback_catd A K E F) s b))
      (@sigma_arrow
        K
        E
        (@fapp0 A K F a)
        (@fapp0 A K F b)
        (@piapp0 A (@Pullback_catd A K E F) s a)
        (@piapp0 A (@Pullback_catd A K E F) s b)
        (@fapp1_fapp0 A K F a b p)
        (@piapp1_fapp0
          A
          (@Pullback_catd A K E F)
          s
          a b p));

// First projection computes pointwise, but no whole-functor beta is added.
assert [A K : Cat]
  (F : τ (Functor A K))
  (E : τ (Catd K))
  (s : τ (Obj (@Pi_cat A (@Pullback_catd A K E F))))
  (a : τ (Obj A)) ⊢
  @fapp0
    A
    K
    (@comp_cat_fapp0
      A
      (@Sigma_cat K E)
      K
      (@Sigma_proj1_func K E)
      (@contextual_pair_pullback_total_check A K F E s))
    a
  ≡ @fapp0 A K F a;

assertnot [A K : Cat]
  (F : τ (Functor A K))
  (E : τ (Catd K))
  (s : τ (Obj (@Pi_cat A (@Pullback_catd A K E F)))) ⊢
  @comp_cat_fapp0
    A
    (@Sigma_cat K E)
    K
    (@Sigma_proj1_func K E)
    (@contextual_pair_pullback_total_check A K F E s)
  ≡ F;

// An arbitrary total functor does not collapse to the new stable owner.
assertnot [A K : Cat]
  (F : τ (Functor A K))
  (D : τ (Catd K))
  (G : τ (Functor
      (@Sigma_cat A (@Pullback_catd A K D F))
      (@Sigma_cat K D))) ⊢
  G ≡ @sigma_pullback_total_func A K F D;

assert [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  (x : τ (Obj K)) ⊢
  @fapp0
    (Fibre_cat (@Op_catd K (@Const_catd K Terminal_cat)) x)
    (Fibre_cat (@Homd_target_catd K (@Const_catd K Terminal_cat)) x)
    (@Fibre_func
      K
      (@Op_catd K (@Const_catd K Terminal_cat))
      (@Homd_target_catd K (@Const_catd K Terminal_cat))
      (@comp_catd_fapp0
        K
        (@Op_catd K (@Const_catd K Terminal_cat))
        (@Op_catd K E)
        (@Homd_target_catd K (@Const_catd K Terminal_cat))
        (@homd_int K (@Const_catd K Terminal_cat) E s)
        (@Op_funcd K (@Const_catd K Terminal_cat) E s))
      x)
    Terminal_obj
    ≡ @homd_src_sec
        K
        (@Const_catd K Terminal_cat)
        E
        s
        x
        (@piapp0 K E s x);

assert [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  (x y : τ (Obj K)) ⊢
  fapp0
    (@piapp0
      (Op_cat K)
      (@Homd_target_section_catd K (@Const_catd K Terminal_cat) x)
      (@fapp0
        (Fibre_cat (@Op_catd K (@Const_catd K Terminal_cat)) x)
        (Fibre_cat (@Homd_target_catd K (@Const_catd K Terminal_cat)) x)
        (@Fibre_func
          K
          (@Op_catd K (@Const_catd K Terminal_cat))
          (@Homd_target_catd K (@Const_catd K Terminal_cat))
          (@comp_catd_fapp0
            K
            (@Op_catd K (@Const_catd K Terminal_cat))
            (@Op_catd K E)
            (@Homd_target_catd K (@Const_catd K Terminal_cat))
            (@homd_int K (@Const_catd K Terminal_cat) E s)
            (@Op_funcd K (@Const_catd K Terminal_cat) E s))
          x)
        Terminal_obj)
      y)
    Terminal_obj
    ≡ @homd_
        K
        E
        E
        (@id_funcd K E)
        x
        (@piapp0 K E s x)
        y
        (@piapp0 K E s y);

// catalog-area: Cat-valued presheaf facade and restriction
// The facade computes only through Obj/Hom and compares with Catd at proof time.
assert [K : Cat] ⊢
  Obj (@Psh_cat K)
  ≡ Obj (@Catd_cat (Op_cat K));

assert [K : Cat] (P Q : τ (Psh K)) ⊢
  Hom_cat (@Psh_cat K) P Q
  ≡ @Functord_cat (Op_cat K) P Q;

assert [K : Cat] ⊢
  Psh K
  ≡ Obj (@Catd_cat (Op_cat K));

// Direct proof-time comparison at an abstract base.
assert [K : Cat] ⊢
  @eq_refl Cat_grpd (@Psh_cat K)
  : τ (@= Cat_grpd
      (@Psh_cat K)
      (@Catd_cat (Op_cat K)));

// The same direct comparison survives one visible opposite.
assert [K : Cat] ⊢
  @eq_refl Cat_grpd (@Psh_cat (Op_cat K))
  : τ (@= Cat_grpd
      (@Psh_cat (Op_cat K))
      (@Catd_cat K));

// Opposite involution does not obstruct the nested-opposite presentation.
assert [K : Cat] ⊢
  @eq_refl Cat_grpd (@Psh_cat (Op_cat (Op_cat K)))
  : τ (@= Cat_grpd
      (@Psh_cat (Op_cat (Op_cat K)))
      (@Catd_cat (Op_cat K)));

// The proof-time comparison does not erase the runtime facade.
assertnot [K : Cat] ⊢
  @Psh_cat K
  ≡ @Catd_cat (Op_cat K);

// Nor does it identify an abstract base with its opposite.
assertnot [K : Cat] ⊢
  @eq_refl Cat_grpd (@Psh_cat K)
  : τ (@= Cat_grpd
      (@Psh_cat K)
      (@Catd_cat K));

assert [A B : Cat] (F : τ (Functor A B)) ⊢
  @Psh_pullback_func A B F
  : τ (Functor (@Psh_cat B) (@Psh_cat A));

// Restriction object action is the existing Catd pullback along F^op.
assert [A B : Cat]
  (F : τ (Functor A B))
  (P : τ (Psh B)) ⊢
  @fapp0
    (@Psh_cat B)
    (@Psh_cat A)
    (@Psh_pullback_func A B F)
    P
  ≡ @Pullback_catd
      (Op_cat A)
      (Op_cat B)
      P
      (@Op_func A B F);

// Its arrow action is inherited from the one generic functor-action owner.
assert [A B : Cat]
  (F : τ (Functor A B))
  (P Q : τ (Psh B))
  (eta : τ (@Functord (Op_cat B) P Q)) ⊢
  @fapp1_fapp0
    (@Psh_cat B)
    (@Psh_cat A)
    (@Psh_pullback_func A B F)
    P Q eta
  : τ (@Functord
      (Op_cat A)
      (@Pullback_catd (Op_cat A) (Op_cat B) P (@Op_func A B F))
      (@Pullback_catd (Op_cat A) (Op_cat B) Q (@Op_func A B F)));
/* End of the PSSS-01 presheaf diagnostics. */

// catalog-area: Yoneda, slices, and Cat-valued higher sieves
// Yoneda is the existing contravariant internal hom at the identity functor.
assert [K : Cat] (U V : τ (Obj K)) ⊢
  Fibre_cat (@yoneda_psh K U) V
  ≡ Hom_cat K V U;

assert [K : Cat] ⊢
  @yoneda_psh_func K
  : τ (Functor K (@Psh_cat K));

assert [K : Cat]
  (V U : τ (Obj K))
  (p : τ (Hom K V U)) ⊢
  @fapp1_fapp0
    K
    (@Psh_cat K)
    (@yoneda_psh_func K)
    V U p
  ≡ @hom_con_int_postcomp_func K K (@id_func K) V U p;

// Pointwise, the facade-level Yoneda action is ordinary postcomposition.
assert [K : Cat]
  (V U W : τ (Obj K))
  (p : τ (Hom K V U)) ⊢
  @tapp0_fapp0
    (Op_cat K)
    Cat_cat
    (@yoneda_psh K V)
    (@yoneda_psh K U)
    W
    (@fapp1_fapp0
      K
      (@Psh_cat K)
      (@yoneda_psh_func K)
      V U p)
  ≡ @hom_postcomp_func
      K K (@id_func K)
      W V U p;

// The restriction-oriented total is opposite to the conventional slice.
assert [K : Cat] (U : τ (Obj K)) ⊢
  @Into_restr_cat K U
  ≡ @Sigma_cat (Op_cat K) (@yoneda_psh K U);

assert [K : Cat]
  (V U : τ (Obj K))
  (p : τ (Hom K V U)) ⊢
  @fapp1_fapp0
    K
    Cat_cat
    (@arrow_into_catd K)
    V U p
  ≡ @sigma_map_func
      (Op_cat K)
      (@yoneda_psh K V)
      (@yoneda_psh K U)
      (@hom_con_int_postcomp_func K K (@id_func K) V U p);

assert [K : Cat] (U : τ (Obj K)) ⊢
  @Slice_cat K U
  ≡ Op_cat (@Sigma_cat (Op_cat K) (@yoneda_psh K U));

// Both higher-sieve presentations compare to this stable Catd intermediary.
assert [K : Cat] (U : τ (Obj K)) ⊢
  @eq_refl Cat_grpd (@HigherSieve_cat K U)
  : τ (@= Cat_grpd
      (@HigherSieve_cat K U)
      (@Catd_cat (@Into_restr_cat K U)));

assert [K : Cat] (U : τ (Obj K)) ⊢
  @eq_refl Cat_grpd (@Psh_cat (@Slice_cat K U))
  : τ (@= Cat_grpd
      (@Psh_cat (@Slice_cat K U))
      (@Catd_cat (@Into_restr_cat K U)));

// Experimental unifiers are not transitively chained at runtime.
assertnot [K : Cat] (U : τ (Obj K)) ⊢
  @HigherSieve_cat K U
  ≡ @Psh_cat (@Slice_cat K U);

// Restriction of higher sieves reuses Catd pullback along the arrow-total map.
assert [K : Cat]
  (V U : τ (Obj K))
  (p : τ (Hom K V U)) ⊢
  @fapp1_fapp0
    (Op_cat K)
    Cat_cat
    (@HigherSieveClassifier K)
    U V p
  ≡ @Pullback_catd_func
      (@Into_restr_cat K V)
      (@Into_restr_cat K U)
      (@fapp1_fapp0 K Cat_cat (@arrow_into_catd K) V U p);

assert [K : Cat] (U : τ (Obj K)) ⊢
  @maximal_higher_sieve K U
  ≡ @Terminal_catd (@Into_restr_cat K U);

assert [K : Cat]
  (V U : τ (Obj K))
  (p : τ (Hom K V U)) ⊢
  @fapp0
    (@HigherSieve_cat K U)
    (@HigherSieve_cat K V)
    (@fapp1_fapp0
      (Op_cat K)
      Cat_cat
      (@HigherSieveClassifier K)
      U V p)
    (@maximal_higher_sieve K U)
  ≡ @maximal_higher_sieve K V;
/* End of the PSSS-02 higher-sieve diagnostics. */

// catalog-area: Ordinary subterminal sieves and pullback
// Subterminal means proposition-valued objects plus exact groupoidality.
assert [C : Cat] ⊢
  IsSubterminalCat C
  ≡ `Σ_ obj_prop : τ (IsPropGrpd (Obj C)), @IsGroupoidalCat C;

assert [A : Grpd] (h : τ (IsPropGrpd A)) ⊢
  @path_cat_is_subterminal A h
  : τ (IsSubterminalCat (Path_cat A));

assert [C : Cat] (h : τ (IsSubterminalCat C))
  (x y : τ (Obj C)) ⊢
  @subterminal_cat_arrow C h x y
  : τ (Hom C x y);

assert [C : Cat] (h : τ (IsSubterminalCat C)) ⊢
  @subterminal_cat_is_discrete C h
  : τ (IsDiscreteCat C);

// Both the subterminal witness and the pointwise sieve witness are properties.
assert [C : Cat] ⊢
  @is_subterminal_cat_evidence_is_prop C
  : τ (IsPropGrpd (IsSubterminalCat C));

assert [K : Cat] (U : τ (Obj K))
  (S : τ (@HigherSieve K U)) ⊢
  @is_ordinary_sieve_evidence_is_prop K U S
  : τ (IsPropGrpd (@IsOrdinarySieve K U S));

// The named higher-sieve pullback is exactly the classifier's arrow action.
assert [K : Cat]
  (V U : τ (Obj K))
  (p : τ (Hom K V U)) ⊢
  @HigherSieve_pullback_func K V U p
  ≡ @fapp1_fapp0
      (Op_cat K)
      Cat_cat
      (@HigherSieveClassifier K)
      U V p;

// Ordinary pullback reuses that action and selects pointwise evidence.
assert [K : Cat]
  (V U : τ (Obj K))
  (p : τ (Hom K V U))
  (R : τ (@Sieve K U)) ⊢
  @sieve_higher K V (@sieve_pullback K V U p R)
  ≡ @higher_sieve_pullback K V U p (@sieve_higher K U R);

assert [K : Cat]
  (V U : τ (Obj K))
  (p : τ (Hom K V U))
  (R : τ (@Sieve K U)) ⊢
  @sieve_subterminal K V (@sieve_pullback K V U p R)
  : τ (@IsOrdinarySieve K V
      (@higher_sieve_pullback K V U p (@sieve_higher K U R)));

// Retained evidence is propositionally unique, but package eta is not runtime.
assertnot [K : Cat] (U : τ (Obj K))
  (R : τ (@Sieve K U)) ⊢
  @sieve_pullback K U U (@id K U) R
  ≡ R;
/* End of the PSSS-03a ordinary-sieve diagnostics. */

// catalog-area: Direct ordinary-sieve Grothendieck topologies
// Restriction-total objects expose their domain and arrow observations.
assert [K : Cat] (V U : τ (Obj K))
  (p : τ (Hom K V U)) ⊢
  @into_restr_domain K U (Struct_sigma V p)
  ≡ V;

assert [K : Cat] (V U : τ (Obj K))
  (p : τ (Hom K V U)) ⊢
  @into_restr_arrow K U (Struct_sigma V p)
  ≡ p;

// Ordinary-sieve membership and every selected cover predicate are properties.
assert [K : Cat] (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (f : τ (Obj (@Into_restr_cat K U))) ⊢
  @sieve_membership_is_prop K U R f
  : τ (IsPropGrpd (@SieveMembership K U R f));

assert [K : Cat]
  (J : τ (@SieveCoverage K))
  (U : τ (Obj K))
  (R : τ (@Sieve K U)) ⊢
  @covers_is_prop K J U R
  : τ (IsPropGrpd (@Covers K J U R));

// The maximal ordinary sieve is pointwise true and stable under pullback.
assert [K : Cat] (U : τ (Obj K))
  (f : τ (Obj (@Into_restr_cat K U))) ⊢
  @SieveMembership K U (@maximal_sieve K U) f
  ≡ Unit_grpd;

assert [K : Cat] (V U : τ (Obj K))
  (p : τ (Hom K V U)) ⊢
  @sieve_pullback K V U p (@maximal_sieve K U)
  ≡ @maximal_sieve K V;

// Its literal true-value presentation does not identify category heads.
assertnot [K : Cat] (U : τ (Obj K)) ⊢
  @sieve_higher K U (@maximal_sieve K U)
  ≡ @maximal_higher_sieve K U;

// Every sieve covers in the chaotic topology.
assert [K : Cat] (U : τ (Obj K))
  (R : τ (@Sieve K U)) ⊢
  @groth_topology_covers K (@chaotic_groth_topology K) U R
  ≡ Unit_grpd;

// Pullback stability and local character compute to the unique truth witness.
assert [K : Cat] (V U : τ (Obj K))
  (p : τ (Hom K V U))
  (R : τ (@Sieve K U)) ⊢
  (@groth_topology_pullback K (@chaotic_groth_topology K))
    U V p R tt
  ≡ tt;

assert [K : Cat] (U : τ (Obj K))
  (R S : τ (@Sieve K U)) ⊢
  (@groth_topology_local_character K (@chaotic_groth_topology K))
    U R S tt
    (λ f : τ (Obj (@Into_restr_cat K U)),
      λ _ : τ (@SieveMembership K U R f),
      tt)
  ≡ tt;

assert [K : Cat] ⊢
  @chaotic_groth_topology K
  : τ (@GrothTopology K);

// Small direct combinatorial instance.
assert ⊢
  @chaotic_groth_topology Terminal_cat
  : τ (@GrothTopology Terminal_cat);
/* End of the PSSS-04a direct-topology diagnostics. */

// catalog-area: Set-carrier commutative-ring objects
// Operation constructors expose all five fields without a primitive record.
assert [A : Grpd]
  (zero one : τ A)
  (add : τ (@Function_grpd A (@Function_grpd A A)))
  (neg : τ (@Function_grpd A A))
  (mul : τ (@Function_grpd A (@Function_grpd A A))) ⊢
  @comm_ring_ops_zero A
    (@comm_ring_ops_intro A zero one add neg mul)
  ≡ zero;

assert [A : Grpd]
  (zero one : τ A)
  (add : τ (@Function_grpd A (@Function_grpd A A)))
  (neg : τ (@Function_grpd A A))
  (mul : τ (@Function_grpd A (@Function_grpd A A))) ⊢
  @comm_ring_ops_one A
    (@comm_ring_ops_intro A zero one add neg mul)
  ≡ one;

assert [A : Grpd]
  (zero one : τ A)
  (add : τ (@Function_grpd A (@Function_grpd A A)))
  (neg : τ (@Function_grpd A A))
  (mul : τ (@Function_grpd A (@Function_grpd A A)))
  (x y : τ A) ⊢
  @comm_ring_ops_add A
    (@comm_ring_ops_intro A zero one add neg mul) x y
  ≡ add x y;

assert [A : Grpd]
  (zero one : τ A)
  (add : τ (@Function_grpd A (@Function_grpd A A)))
  (neg : τ (@Function_grpd A A))
  (mul : τ (@Function_grpd A (@Function_grpd A A)))
  (x y : τ A) ⊢
  @comm_ring_ops_mul A
    (@comm_ring_ops_intro A zero one add neg mul) x y
  ≡ mul x y;

// Carrier sethood is retained by the SetU package.
assert (R : τ CommRing) ⊢
  @comm_ring_carrier_is_set R
  : τ (IsSetGrpd (@comm_ring_carrier R));

// The concrete zero ring is nonempty and all five observations compute.
assert ⊢ @comm_ring_carrier zero_comm_ring ≡ Unit_grpd;

assert ⊢ @comm_ring_zero zero_comm_ring ≡ tt;

assert ⊢ @comm_ring_one zero_comm_ring ≡ tt;

assert ⊢ @comm_ring_add zero_comm_ring tt tt ≡ tt;

assert ⊢ @comm_ring_neg zero_comm_ring tt ≡ tt;

assert ⊢ @comm_ring_mul zero_comm_ring tt tt ≡ tt;

assert ⊢
  (@comm_ring_add_zero_law zero_comm_ring) tt
  ≡ @eq_refl Unit_grpd tt;

assert ⊢
  (@comm_ring_mul_one_law zero_comm_ring) tt
  ≡ @eq_refl Unit_grpd tt;

// Zero rings are intentionally allowed.
assert ⊢
  @comm_ring_zero zero_comm_ring
  ≡ @comm_ring_one zero_comm_ring;

// Retained carrier/structure packages are not hidden by a broad Sigma eta.
assertnot (R : τ CommRing) ⊢
  R
  ≡ @comm_ring_intro
      (@comm_ring_carrier_package R)
      (@comm_ring_structure R);
/* End of the PSSS-06a commutative-ring object diagnostics. */

// catalog-area: Structured commutative-ring morphisms and category
// The transparent observation is an ordinary carrier function.
assert (R S : τ CommRing)
  (h : τ (@CommRingHom R S)) ⊢
  @comm_ring_hom_function R S h
  : τ (@Function_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S));

assert (R S : τ CommRing)
  (h : τ (@CommRingHom R S))
  (x : τ (@comm_ring_carrier R)) ⊢
  @comm_ring_hom_apply R S h x
  ≡ @comm_ring_hom_function R S h x;

// Preservation evidence is proposition-valued and full maps form a set.
assert (R S : τ CommRing)
  (f : τ (@Function_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S))) ⊢
  @comm_ring_hom_laws_is_prop R S f
  : τ (IsPropGrpd (@CommRingHomLaws R S f));

assert (R S : τ CommRing) ⊢
  @comm_ring_hom_is_set R S
  : τ (IsSetGrpd (@CommRingHom R S));

// The category facade projects directly to the selected classifiers.
assert ⊢ Obj CommRing_cat ≡ CommRing;

assert (R S : τ CommRing) ⊢
  Hom_cat CommRing_cat R S
  ≡ Path_cat (@CommRingHom R S);

assert ⊢ comm_ring_cat_is_one_cat
  : τ (IsNCat (cat_succ cat_zero) CommRing_cat);

// Whole-arrow identity cuts remain at the generic category owner.
assert (R S : τ CommRing)
  (h : τ (@CommRingHom R S)) ⊢
  @comm_ring_hom_comp R R S h (@comm_ring_hom_id R)
  ≡ h;

assert (R S : τ CommRing)
  (h : τ (@CommRingHom R S)) ⊢
  @comm_ring_hom_comp R S S (@comm_ring_hom_id S) h
  ≡ h;

// Neither package eta nor projected generic identity is claimed.
assertnot (R S : τ CommRing)
  (h : τ (@CommRingHom R S)) ⊢
  h
  ≡ @comm_ring_hom_intro
      R S
      (@comm_ring_hom_function R S h)
      (@comm_ring_hom_laws R S h);

assertnot (R : τ CommRing)
  (x : τ (@comm_ring_carrier R)) ⊢
  @comm_ring_hom_apply R R (@comm_ring_hom_id R) x
  ≡ x;
/* End of the PSSS-06b commutative-ring morphism diagnostics. */

// catalog-area: Universal-property commutative-ring localization
// Pointwise carrier equality extends to the structured morphism package.
assert (R S : τ CommRing)
  (h k : τ (@CommRingHom R S))
  (p : τ (@CommRingHomPointwisePath R S h k)) ⊢
  @comm_ring_hom_ext R S h k p
  : τ (h = k);

// Explicit unit constructors expose the chosen inverse and its equation.
assert (R : τ CommRing)
  (x inverse : τ (@comm_ring_carrier R))
  (law : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R x inverse)
      (@comm_ring_one R))) ⊢
  @comm_ring_unit_inverse R x
    (@comm_ring_unit_intro R x inverse law)
  ≡ inverse;

assert (R : τ CommRing)
  (x inverse : τ (@comm_ring_carrier R))
  (law : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R x inverse)
      (@comm_ring_one R))) ⊢
  @comm_ring_unit_law R x
    (@comm_ring_unit_intro R x inverse law)
  ≡ law;

assert (R : τ CommRing)
  (x : τ (@comm_ring_carrier R)) ⊢
  @comm_ring_unit_evidence_is_prop R x
  : τ (IsPropGrpd (@CommRingUnitEvidence R x));

assert (R : τ CommRing)
  (x : τ (@comm_ring_carrier R))
  (u v : τ (@CommRingUnitEvidence R x)) ⊢
  @comm_ring_unit_inverse_unique R x u v
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_unit_inverse R x u)
      (@comm_ring_unit_inverse R x v));

// Pointwise factor triangles are proposition-valued because target carriers
// are sets.
assert (R L S : τ CommRing)
  (localization_map : τ (@CommRingHom R L))
  (factor : τ (@CommRingHom L S))
  (h : τ (@CommRingHom R S)) ⊢
  @comm_ring_localization_agreement_is_prop
    R L S localization_map factor h
  : τ (IsPropGrpd
      (@CommRingLocalizationAgreement R L S localization_map factor h));

// Factor constructors expose both retained observations.
assert (R L S : τ CommRing)
  (localization_map : τ (@CommRingHom R L))
  (factor : τ (@CommRingHom L S))
  (h : τ (@CommRingHom R S))
  (agreement : τ (@CommRingLocalizationAgreement
      R L S localization_map factor h)) ⊢
  @comm_ring_localization_factor_map
    R L S localization_map h
    (@comm_ring_localization_factor_intro
      R L S localization_map h factor agreement)
  ≡ factor;

assert (R L S : τ CommRing)
  (localization_map : τ (@CommRingHom R L))
  (factor : τ (@CommRingHom L S))
  (h : τ (@CommRingHom R S))
  (agreement : τ (@CommRingLocalizationAgreement
      R L S localization_map factor h)) ⊢
  @comm_ring_localization_factor_agreement
    R L S localization_map h
    (@comm_ring_localization_factor_intro
      R L S localization_map h factor agreement)
  ≡ agreement;

// Chosen localization constructors expose target, map, and universal data.
assert (R L : τ CommRing)
  (f : τ (@comm_ring_carrier R))
  (localization_map : τ (@CommRingHom R L))
  (property : τ (@IsCommRingLocalizationAt
      R f L localization_map)) ⊢
  @comm_ring_localization_target R f
    (@comm_ring_localization_intro R f L localization_map property)
  ≡ L;

assert (R L : τ CommRing)
  (f : τ (@comm_ring_carrier R))
  (localization_map : τ (@CommRingHom R L))
  (property : τ (@IsCommRingLocalizationAt
      R f L localization_map)) ⊢
  @comm_ring_localization_map R f
    (@comm_ring_localization_intro R f L localization_map property)
  ≡ localization_map;

assert (R L : τ CommRing)
  (f : τ (@comm_ring_carrier R))
  (localization_map : τ (@CommRingHom R L))
  (property : τ (@IsCommRingLocalizationAt
      R f L localization_map)) ⊢
  @comm_ring_localization_property R f
    (@comm_ring_localization_intro R f L localization_map property)
  ≡ property;

// Opaque chosen localizations retain their Sigma evidence; no broad eta fold.
assertnot (R : τ CommRing)
  (f : τ (@comm_ring_carrier R))
  (localization : τ (@CommRingLocalizationAt R f)) ⊢
  localization
  ≡ @comm_ring_localization_intro
      R f
      (@comm_ring_localization_target R f localization)
      (@comm_ring_localization_map R f localization)
      (@comm_ring_localization_property R f localization);
/* End of the PSSS-07a localization diagnostics. */

// catalog-area: Identity localization at a unit
// One is canonically a unit, with itself as the selected inverse.
assert (R : τ CommRing) ⊢
  @comm_ring_unit_inverse
    R (@comm_ring_one R) (@comm_ring_one_unit R)
  ≡ @comm_ring_one R;

// The identity factorization space is constructively contractible.
assert (R S : τ CommRing)
  (h : τ (@CommRingHom R S)) ⊢
  @comm_ring_unit_localization_factor_is_contr R S h
  : τ (IsContr (@CommRingLocalizationFactor
      R R S (@comm_ring_hom_id_pointwise R) h));

// Every ring has the selected universal-property localization at one.
assert (R : τ CommRing) ⊢
  @comm_ring_identity_localization_at_one R
  : τ (@CommRingLocalizationAt R (@comm_ring_one R));

// Its target and carrier action compute through the pointwise identity.
assert (R : τ CommRing) ⊢
  @comm_ring_localization_target
    R (@comm_ring_one R) (@comm_ring_identity_localization_at_one R)
  ≡ R;

assert (R : τ CommRing)
  (x : τ (@comm_ring_carrier R)) ⊢
  @comm_ring_hom_apply
    R R
    (@comm_ring_localization_map
      R (@comm_ring_one R) (@comm_ring_identity_localization_at_one R))
    x
  ≡ x;
/* End of the PSSS-08c0F unit-localization diagnostics. */

// catalog-area: Localization at zero in the zero ring
// Multiplication by zero is derived from distributivity and additive inverses.
assert (R : τ CommRing)
  (x : τ (@comm_ring_carrier R)) ⊢
  @comm_ring_mul_zero_right R x
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R x (@comm_ring_zero R))
      (@comm_ring_zero R));

// Invertible zero constructively forces zero=one in the target.
assert (R : τ CommRing)
  (unit : τ (@CommRingUnitEvidence R (@comm_ring_zero R))) ⊢
  @comm_ring_zero_unit_zero_one R unit
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_zero R)
      (@comm_ring_one R));

// Every admissible structured map has a contractible factorization through 0.
assert (R S : τ CommRing)
  (h : τ (@CommRingHom R S))
  (zero_one : τ (@= (@comm_ring_carrier S)
      (@comm_ring_zero S)
      (@comm_ring_one S))) ⊢
  @comm_ring_zero_localization_factor_is_contr R S h zero_one
  : τ (IsContr (@CommRingLocalizationFactor
      R zero_comm_ring S (@comm_ring_hom_to_zero R) h));

// The selected universal-property localization at zero is always available.
assert (R : τ CommRing) ⊢
  @comm_ring_zero_localization R
  : τ (@CommRingLocalizationAt R (@comm_ring_zero R));

// Its target and carrier action compute to the zero ring and its unique point.
assert (R : τ CommRing) ⊢
  @comm_ring_localization_target
    R (@comm_ring_zero R) (@comm_ring_zero_localization R)
  ≡ zero_comm_ring;

assert (R : τ CommRing)
  (x : τ (@comm_ring_carrier R)) ⊢
  @comm_ring_hom_apply
    R zero_comm_ring
    (@comm_ring_localization_map
      R (@comm_ring_zero R) (@comm_ring_zero_localization R))
    x
  ≡ tt;
/* End of the PSSS-08c0F zero-localization diagnostics. */

// catalog-area: Localization at an idempotent through its fixed image
// The fixed-point subtype remains a set and inherits a computing ring.
assert (R : τ CommRing)
  (e : τ (@comm_ring_carrier R)) ⊢
  @comm_ring_idempotent_image_carrier_is_set R e
  : τ (IsSetGrpd (@CommRingIdempotentImageCarrier R e));

assert (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e)) ⊢
  @comm_ring_idempotent_image_element R e
    (@comm_ring_one (@comm_ring_idempotent_image R e idempotent))
  ≡ e;

// Its structure map is the executable scaling operation x |-> e*x.
assert (R : τ CommRing)
  (e x : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e)) ⊢
  @comm_ring_idempotent_image_element R e
    (@comm_ring_hom_apply
      R
      (@comm_ring_idempotent_image R e idempotent)
      (@comm_ring_idempotent_image_localization_map R e idempotent)
      x)
  ≡ @comm_ring_mul R e x;

// Invertibility of the mapped idempotent selects a contractible factor space.
assert (R S : τ CommRing)
  (h : τ (@CommRingHom R S))
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e))
  (unit : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S h e))) ⊢
  @comm_ring_idempotent_image_factor_is_contr
    R e idempotent S h unit
  : τ (IsContr (@CommRingLocalizationFactor
      R
      (@comm_ring_idempotent_image R e idempotent)
      S
      (@comm_ring_idempotent_image_localization_map R e idempotent)
      h));

// The selected package computes to the fixed-image target and scaling map.
assert (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e)) ⊢
  @comm_ring_localization_target
    R e
    (@comm_ring_idempotent_image_localization R e idempotent)
  ≡ @comm_ring_idempotent_image R e idempotent;

assert (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e)) ⊢
  @comm_ring_localization_map
    R e
    (@comm_ring_idempotent_image_localization R e idempotent)
  ≡ @comm_ring_idempotent_image_localization_map R e idempotent;
/* End of the PSSS-08c0G idempotent-localization diagnostics. */

// catalog-area: Product rings and split-idempotent affine restriction
// The public product carrier and its structured arrow action compute by pairs.
assert (R S : τ CommRing) ⊢
  @comm_ring_carrier (@comm_ring_product R S)
  ≡ @Product_grpd (@comm_ring_carrier R) (@comm_ring_carrier S);

assert (R R' S S' : τ CommRing)
  (h : τ (@CommRingHom R R'))
  (k : τ (@CommRingHom S S'))
  (x : τ (@comm_ring_carrier (@comm_ring_product R S))) ⊢
  @comm_ring_hom_apply
    (@comm_ring_product R S)
    (@comm_ring_product R' S')
    (@comm_ring_product_map R R' S S' h k)
    x
  ≡ @Product_pair_grpd
      (@comm_ring_carrier R')
      (@comm_ring_carrier S')
      (@comm_ring_hom_apply R R' h (sigma_Fst x))
      (@comm_ring_hom_apply S S' k (sigma_Snd x));

// Whole structured-map composition is derived without a product-specific rule.
assert (R0 R1 R2 S0 S1 S2 : τ CommRing)
  (gR : τ (@CommRingHom R1 R2))
  (fR : τ (@CommRingHom R0 R1))
  (gS : τ (@CommRingHom S1 S2))
  (fS : τ (@CommRingHom S0 S1)) ⊢
  @comm_ring_product_map_comp_path
    R0 R1 R2 S0 S1 S2 gR fR gS fS
  : τ (@=
      (@CommRingHom
        (@comm_ring_product R0 S0)
        (@comm_ring_product R2 S2))
      (@comm_ring_product_map
        R0 R2 S0 S2
        (@comm_ring_hom_comp_pointwise R0 R1 R2 gR fR)
        (@comm_ring_hom_comp_pointwise S0 S1 S2 gS fS))
      (@comm_ring_hom_comp_pointwise
        (@comm_ring_product R0 S0)
        (@comm_ring_product R1 S1)
        (@comm_ring_product R2 S2)
        (@comm_ring_product_map R1 R2 S1 S2 gR gS)
        (@comm_ring_product_map R0 R1 S0 S1 fR fS)));

// F2 is closed reusable algebraic input for the non-endpoint witness.
assert ⊢ f2_comm_ring : τ CommRing;

assert ⊢ f2_split_idempotent_path
  : τ (@=
      (@comm_ring_carrier f2_split_comm_ring)
      (@comm_ring_mul
        f2_split_comm_ring
        f2_split_idempotent
        f2_split_idempotent)
      f2_split_idempotent);

// The selected idempotent is constructively distinct from both endpoints.
assert ⊢ f2_split_idempotent_not_zero
  : τ (@Function_grpd
      (@= (@comm_ring_carrier f2_split_comm_ring)
        f2_split_idempotent
        (@comm_ring_zero f2_split_comm_ring))
      Empty_grpd);

assert ⊢ f2_split_idempotent_not_one
  : τ (@Function_grpd
      (@= (@comm_ring_carrier f2_split_comm_ring)
        f2_split_idempotent
        (@comm_ring_one f2_split_comm_ring))
      Empty_grpd);

// The affine arrow exposes the fixed-image target selected by localization.
assert ⊢ sigma_Fst f2_split_basic_open_arrow
  ≡ @comm_ring_idempotent_image
      f2_split_comm_ring
      f2_split_idempotent
      f2_split_idempotent_path;

// Its carrier restriction executes as the nontrivial projection (x,y) |-> (x,0).
assert (x y : τ Bool_grpd) ⊢
  @comm_ring_idempotent_image_element
    f2_split_comm_ring
    f2_split_idempotent
    (@comm_ring_hom_apply
      f2_split_comm_ring
      (@comm_ring_idempotent_image
        f2_split_comm_ring
        f2_split_idempotent
        f2_split_idempotent_path)
      (sigma_Snd f2_split_basic_open_arrow)
      (@Product_pair_grpd Bool_grpd Bool_grpd x y))
  ≡ @Product_pair_grpd Bool_grpd Bool_grpd x false;
/* End of the PSSS-08c0H split-idempotent affine diagnostics. */

// catalog-area: Computational affine Cartier glue
// The affine structure presheaf computes to the original ring and map.
assert (R : τ CommRing) ⊢
  @comm_ring_psh_value
    (Op_cat CommRing_cat)
    affine_comm_ring_psh
    R
  ≡ R;

assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S)) ⊢
  @comm_ring_psh_restriction_hom
    (Op_cat CommRing_cat)
    affine_comm_ring_psh
    S R h
  ≡ h;

// Every selected affine localization constructively supplies the full
// componentwise Cartier-glue package.
assert [R : τ CommRing]
  [s : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R s)) ⊢
  @affine_localization_matching_glue R s localization
  : τ (@CommRingPshLocalizationGlue
      (Op_cat CommRing_cat)
      affine_comm_ring_psh
      R s localization);

// The closed non-endpoint split localization reaches that complete package.
assert ⊢
  @affine_localization_matching_glue
    f2_split_comm_ring
    f2_split_idempotent
    f2_split_idempotent_localization
  : τ (@CommRingPshLocalizationGlue
      (Op_cat CommRing_cat)
      affine_comm_ring_psh
      f2_split_comm_ring
      f2_split_idempotent
      f2_split_idempotent_localization);
/* End of the PSSS-08c0I affine Cartier-glue diagnostics. */

// catalog-area: Iterated commutative-ring localization comparison
// Stable structured composition exposes its selected carrier action.
assert (R S T : τ CommRing)
  (g : τ (@CommRingHom S T))
  (f : τ (@CommRingHom R S))
  (x : τ (@comm_ring_carrier R)) ⊢
  @comm_ring_hom_apply R T
    (@comm_ring_hom_comp_pointwise R S T g f) x
  ≡ @comm_ring_hom_apply S T g
      (@comm_ring_hom_apply R S f x);

// Typed reflexivity exercises comparison with generic category composition.
assert (R S T : τ CommRing)
  (g : τ (@CommRingHom S T))
  (f : τ (@CommRingHom R S)) ⊢
  @comm_ring_hom_comp_pointwise_path R S T g f
  : τ (@= (@CommRingHom R T)
      (@comm_ring_hom_comp R S T g f)
      (@comm_ring_hom_comp_pointwise R S T g f));

// Generic whole-map application remains outside runtime reduction.
assertnot (R S T : τ CommRing)
  (g : τ (@CommRingHom S T))
  (f : τ (@CommRingHom R S))
  (x : τ (@comm_ring_carrier R)) ⊢
  @comm_ring_hom_apply R T (@comm_ring_hom_comp R S T g f) x
  ≡ @comm_ring_hom_apply S T g
      (@comm_ring_hom_apply R S f x);

// Unit evidence supports exactly the algebra needed by the overlap consumer.
assert (R S : τ CommRing)
  (h : τ (@CommRingHom R S))
  (x : τ (@comm_ring_carrier R))
  (u : τ (@CommRingUnitEvidence R x)) ⊢
  @comm_ring_hom_preserves_unit R S h x u
  : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S h x));

assert (R : τ CommRing)
  (x y : τ (@comm_ring_carrier R))
  (u : τ (@CommRingUnitEvidence R x))
  (v : τ (@CommRingUnitEvidence R y)) ⊢
  @comm_ring_unit_mul R x y u v
  : τ (@CommRingUnitEvidence R (@comm_ring_mul R x y));

assert (R : τ CommRing)
  (x y : τ (@comm_ring_carrier R))
  (u : τ (@CommRingUnitEvidence R (@comm_ring_mul R x y))) ⊢
  @comm_ring_unit_mul_left R x y u
  : τ (@CommRingUnitEvidence R x);

assert (R : τ CommRing)
  (x y : τ (@comm_ring_carrier R))
  (u : τ (@CommRingUnitEvidence R (@comm_ring_mul R x y))) ⊢
  @comm_ring_unit_mul_right R x y u
  : τ (@CommRingUnitEvidence R y);

// Two chosen stages produce a structure map that inverts f*g.
assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R)) ⊢
  @CommRingIteratedLocalizationAt R f g
  : Grpd;

assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R))
  (iterated : τ (@CommRingIteratedLocalizationAt R f g)) ⊢
  @comm_ring_iterated_localization_inverts_product R f g iterated
  : τ (@CommRingUnitEvidence
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_hom_apply
        R
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_iterated_localization_map R f g iterated)
        (@comm_ring_mul R f g)));

// Universal properties construct the forward and staged reverse factors.
assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R))
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))) ⊢
  @comm_ring_iterated_localization_comparison
    R f g iterated product_localization
  : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization);

assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R))
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))) ⊢
  @comm_ring_iterated_localization_comparison_forward_factor
    R f g iterated product_localization
    (@comm_ring_iterated_localization_comparison
      R f g iterated product_localization)
  ≡ @comm_ring_iterated_localization_forward_factor
      R f g iterated product_localization;

assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R))
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))) ⊢
  @comm_ring_iterated_localization_comparison_reverse_factor
    R f g iterated product_localization
    (@comm_ring_iterated_localization_comparison
      R f g iterated product_localization)
  ≡ @comm_ring_iterated_localization_reverse_factor
      R f g iterated product_localization;
/* End of the PSSS-07b localization-comparison diagnostics. */

// catalog-area: Whole internal iterated-localization overlap
// Universal-property uniqueness gives whole cancellation on the product side.
assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R))
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization)) ⊢
  @comm_ring_iterated_localization_comparison_left_law
    R f g iterated product_localization comparison
  : τ (@=
      (@CommRingHom
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization))
      (@comm_ring_hom_comp
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_iterated_localization_comparison_reverse_map
          R f g iterated product_localization comparison)
        (@comm_ring_iterated_localization_comparison_forward_map
          R f g iterated product_localization comparison))
      (@comm_ring_hom_id
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)));

// Sequential uniqueness through both stages gives the opposite whole law.
assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R))
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization)) ⊢
  @comm_ring_iterated_localization_comparison_right_law
    R f g iterated product_localization comparison
  : τ (@=
      (@CommRingHom
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_iterated_localization_target R f g iterated))
      (@comm_ring_hom_comp
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_iterated_localization_comparison_forward_map
          R f g iterated product_localization comparison)
        (@comm_ring_iterated_localization_comparison_reverse_map
          R f g iterated product_localization comparison))
      (@comm_ring_hom_id
        (@comm_ring_iterated_localization_target R f g iterated)));

// The fixed-forward classifier is the semantic owner of the overlap.
assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R))
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization)) ⊢
  @comm_ring_iterated_localization_comparison_omega_equiv_along
    R f g iterated product_localization comparison
  : τ (@OmegaEquivAlong
      CommRing_cat
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_iterated_localization_comparison_forward_map
        R f g iterated product_localization comparison));

// Both inverse observations compute to the selected staged reverse map.
assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R))
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization)) ⊢
  @omega_equiv_along_left_inv
    CommRing_cat
    (@comm_ring_localization_target
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_iterated_localization_comparison_forward_map
      R f g iterated product_localization comparison)
    (@comm_ring_iterated_localization_comparison_omega_equiv_along
      R f g iterated product_localization comparison)
  ≡ @comm_ring_iterated_localization_comparison_reverse_map
      R f g iterated product_localization comparison;

// The first-class facade retains the forward comparison computation.
assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R))
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization)) ⊢
  @omega_equiv_to
    CommRing_cat
    (@comm_ring_localization_target
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_iterated_localization_comparison_omega_equiv
      R f g iterated product_localization comparison)
  ≡ @comm_ring_iterated_localization_comparison_forward_map
      R f g iterated product_localization comparison;
/* End of the PSSS-08c0F localization-overlap diagnostics. */

// catalog-area: Finite commutative-ring cover presentations
// Formation and visible constructor computation.
assert [A : Grpd] ⊢ @FiniteFamily A zero ≡ Unit_grpd;

assert [A : Grpd] (n : τ Nat_grpd) ⊢
  @FiniteFamily A (succ n)
  ≡ @Σ_ A (λ _ : τ A, @FiniteFamily A n);

assertnot [A : Grpd] (n : τ Nat_grpd) ⊢
  @FiniteFamily A (succ n)
  ≡ @Product_grpd A (@FiniteFamily A n);

assertnot [A : Grpd]
  (xs : τ (@FiniteFamily A zero)) ⊢
  xs ≡ @finite_family_nil A;

assert [A B : Grpd]
  (f : τ (@Function_grpd A B))
  (n : τ Nat_grpd)
  (x : τ A)
  (xs : τ (@FiniteFamily A n)) ⊢
  @finite_family_map A B f (succ n)
    (@finite_family_cons A n x xs)
  ≡ @finite_family_cons B n (f x)
      (@finite_family_map A B f n xs);

assert (R : τ CommRing) ⊢
  @comm_ring_finite_sum R zero (@finite_family_nil (@comm_ring_carrier R))
  ≡ @comm_ring_zero R;

assert (R : τ CommRing)
  (n : τ Nat_grpd)
  (x : τ (@comm_ring_carrier R))
  (xs : τ (@FiniteFamily (@comm_ring_carrier R) n)) ⊢
  @comm_ring_finite_sum R (succ n)
    (@finite_family_cons (@comm_ring_carrier R) n x xs)
  ≡ @comm_ring_add R x (@comm_ring_finite_sum R n xs);

assert (R : τ CommRing)
  (n : τ Nat_grpd)
  (a f : τ (@comm_ring_carrier R))
  (as0 fs0 : τ (@FiniteFamily (@comm_ring_carrier R) n)) ⊢
  @comm_ring_finite_dot R (succ n)
    (@finite_family_cons (@comm_ring_carrier R) n a as0)
    (@finite_family_cons (@comm_ring_carrier R) n f fs0)
  ≡ @comm_ring_add R
      (@comm_ring_mul R a f)
      (@comm_ring_finite_dot R n as0 fs0);

assert (A : Grpd)
  (A_is_set : τ (IsSetGrpd A))
  (n : τ Nat_grpd) ⊢
  @finite_family_is_set A A_is_set n
  : τ (IsSetGrpd (@FiniteFamily A n));

assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (n : τ Nat_grpd)
  (xs : τ (@FiniteFamily (@comm_ring_carrier R) n)) ⊢
  @comm_ring_hom_finite_sum_path R S h n xs
  : τ (@= (@comm_ring_carrier S)
      (@comm_ring_hom_apply R S h
        (@comm_ring_finite_sum R n xs))
      (@comm_ring_finite_sum S n
        (@finite_family_map
          (@comm_ring_carrier R)
          (@comm_ring_carrier S)
          (@comm_ring_hom_function R S h)
          n xs)));

assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (n : τ Nat_grpd)
  (as0 fs0 : τ (@FiniteFamily (@comm_ring_carrier R) n)) ⊢
  @comm_ring_hom_finite_dot_path R S h n as0 fs0
  : τ (@= (@comm_ring_carrier S)
      (@comm_ring_hom_apply R S h
        (@comm_ring_finite_dot R n as0 fs0))
      (@comm_ring_finite_dot S n
        (@finite_family_map
          (@comm_ring_carrier R)
          (@comm_ring_carrier S)
          (@comm_ring_hom_function R S h)
          n as0)
        (@finite_family_map
          (@comm_ring_carrier R)
          (@comm_ring_carrier S)
          (@comm_ring_hom_function R S h)
          n fs0)));

assert [R : τ CommRing]
  (n : τ Nat_grpd)
  (generators : τ (@FiniteFamily (@comm_ring_carrier R) n)) ⊢
  @comm_ring_unimodular_is_set R n generators
  : τ (IsSetGrpd (@CommRingUnimodularPresentation R n generators));

assert (R : τ CommRing) ⊢
  @comm_ring_zariski_cover_is_set R
  : τ (IsSetGrpd (@CommRingZariskiCoverPresentation R));

assert (R : τ CommRing) ⊢
  @comm_ring_zariski_cover_length R (@comm_ring_unit_zariski_cover R)
  ≡ succ zero;

assert (R : τ CommRing) ⊢
  @comm_ring_zariski_cover_generators R (@comm_ring_unit_zariski_cover R)
  ≡ @finite_family_singleton
      (@comm_ring_carrier R)
      (@comm_ring_one R);

assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (cover : τ (@CommRingZariskiCoverPresentation R)) ⊢
  @comm_ring_zariski_cover_map R S h cover
  : τ (@CommRingZariskiCoverPresentation S);

assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (cover : τ (@CommRingZariskiCoverPresentation R)) ⊢
  @comm_ring_zariski_cover_length S
    (@comm_ring_zariski_cover_map R S h cover)
  ≡ @comm_ring_zariski_cover_length R cover;

assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (cover : τ (@CommRingZariskiCoverPresentation R)) ⊢
  @comm_ring_zariski_cover_generators S
    (@comm_ring_zariski_cover_map R S h cover)
  ≡ @finite_family_map
      (@comm_ring_carrier R)
      (@comm_ring_carrier S)
      (@comm_ring_hom_function R S h)
      (@comm_ring_zariski_cover_length R cover)
      (@comm_ring_zariski_cover_generators R cover);

// The generic singleton [1] is an actual nonempty cover presentation.
assert (R : τ CommRing) ⊢
  @comm_ring_unimodular_coefficients
    R
    (succ zero)
    (@finite_family_singleton
      (@comm_ring_carrier R)
      (@comm_ring_one R))
    (@comm_ring_unit_unimodular R)
  ≡ @finite_family_singleton
      (@comm_ring_carrier R)
      (@comm_ring_one R);

assert (R : τ CommRing) ⊢
  @comm_ring_unimodular_law
    R
    (succ zero)
    (@finite_family_singleton
      (@comm_ring_carrier R)
      (@comm_ring_one R))
    (@comm_ring_unit_unimodular R)
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_finite_dot
        R
        (succ zero)
        (@finite_family_singleton
          (@comm_ring_carrier R)
          (@comm_ring_one R))
        (@finite_family_singleton
          (@comm_ring_carrier R)
          (@comm_ring_one R)))
      (@comm_ring_one R));

assert (R : τ CommRing) ⊢
  @comm_ring_zariski_cover_unimodular
    R
    (@comm_ring_unit_zariski_cover R)
  : τ (@CommRingUnimodularPresentation
      R
      (succ zero)
      (@finite_family_singleton
        (@comm_ring_carrier R)
        (@comm_ring_one R)));

// The binary helper consumes the correct unit-ideal equation a*f+b*g=1.
assert [R : τ CommRing]
  (f g a b : τ (@comm_ring_carrier R))
  (law : τ (@= (@comm_ring_carrier R)
      (@comm_ring_add R
        (@comm_ring_mul R a f)
        (@comm_ring_mul R b g))
      (@comm_ring_one R))) ⊢
  @comm_ring_binary_zariski_cover R f g a b law
  : τ (@CommRingZariskiCoverPresentation R);
/* End of the PSSS-07c finite-cover-presentation diagnostics. */

// catalog-area: Polynomial-algebra universal property
// The consumer-selected rigid identity computes on carriers.
assert (R : τ CommRing)
  (x : τ (@comm_ring_carrier R)) ⊢
  @comm_ring_hom_apply R R (@comm_ring_hom_id_pointwise R) x
  ≡ x;

assert (R : τ CommRing) ⊢
  @comm_ring_hom_id_pointwise_path R
  : τ (@= (@CommRingHom R R)
      (@comm_ring_hom_id R)
      (@comm_ring_hom_id_pointwise R));

// Generic whole-identity application remains outside runtime reduction.
assertnot (R : τ CommRing)
  (x : τ (@comm_ring_carrier R)) ⊢
  @comm_ring_hom_apply R R (@comm_ring_hom_id R) x
  ≡ x;

assert (R P S : τ CommRing)
  (base_map : τ (@CommRingHom R P))
  (factor : τ (@CommRingHom P S))
  (h : τ (@CommRingHom R S)) ⊢
  @CommRingPolynomialBaseAgreement R P S base_map factor h
  : Grpd;

assert (R P S : τ CommRing)
  (base_map : τ (@CommRingHom R P))
  (factor : τ (@CommRingHom P S))
  (h : τ (@CommRingHom R S)) ⊢
  @comm_ring_polynomial_base_agreement_is_prop
    R P S base_map factor h
  : τ (IsPropGrpd
      (@CommRingPolynomialBaseAgreement R P S base_map factor h));

assert (X : Grpd)
  (P S : τ CommRing)
  (variables : τ (@Function_grpd X (@comm_ring_carrier P)))
  (factor : τ (@CommRingHom P S))
  (valuation : τ (@Function_grpd X (@comm_ring_carrier S))) ⊢
  @CommRingPolynomialVariableAgreement X P S variables factor valuation
  : Grpd;

assert (X : Grpd)
  (P S : τ CommRing)
  (variables : τ (@Function_grpd X (@comm_ring_carrier P)))
  (factor : τ (@CommRingHom P S))
  (valuation : τ (@Function_grpd X (@comm_ring_carrier S))) ⊢
  @comm_ring_polynomial_variable_agreement_is_prop
    X P S variables factor valuation
  : τ (IsPropGrpd
      (@CommRingPolynomialVariableAgreement
        X P S variables factor valuation));

assert (R P S : τ CommRing)
  (X : Grpd)
  (base_map : τ (@CommRingHom R P))
  (variables : τ (@Function_grpd X (@comm_ring_carrier P)))
  (factor : τ (@CommRingHom P S))
  (h : τ (@CommRingHom R S))
  (valuation : τ (@Function_grpd X (@comm_ring_carrier S))) ⊢
  @comm_ring_polynomial_factor_agreement_is_prop
    R P S X base_map variables factor h valuation
  : τ (IsPropGrpd (@CommRingPolynomialFactorAgreement
      R P S X base_map variables factor h valuation));

assert (R P S : τ CommRing)
  (X : Grpd)
  (base_map : τ (@CommRingHom R P))
  (variables : τ (@Function_grpd X (@comm_ring_carrier P)))
  (h : τ (@CommRingHom R S))
  (valuation : τ (@Function_grpd X (@comm_ring_carrier S))) ⊢
  @CommRingPolynomialFactor R P S X base_map variables h valuation
  : Grpd;

assert (R P S : τ CommRing)
  (X : Grpd)
  (base_map : τ (@CommRingHom R P))
  (variables : τ (@Function_grpd X (@comm_ring_carrier P)))
  (h : τ (@CommRingHom R S))
  (valuation : τ (@Function_grpd X (@comm_ring_carrier S)))
  (factor : τ (@CommRingHom P S))
  (agreement : τ (@CommRingPolynomialFactorAgreement
      R P S X base_map variables factor h valuation)) ⊢
  @comm_ring_polynomial_factor_map
    R P S X base_map variables h valuation
    (@comm_ring_polynomial_factor_intro
      R P S X base_map variables h valuation factor agreement)
  ≡ factor;

assert (R P S : τ CommRing)
  (X : Grpd)
  (base_map : τ (@CommRingHom R P))
  (variables : τ (@Function_grpd X (@comm_ring_carrier P)))
  (h : τ (@CommRingHom R S))
  (valuation : τ (@Function_grpd X (@comm_ring_carrier S)))
  (factor : τ (@CommRingPolynomialFactor
      R P S X base_map variables h valuation)) ⊢
  @comm_ring_polynomial_factor_base
    R P S X base_map variables h valuation factor
  : τ (@CommRingPolynomialBaseAgreement
      R P S base_map
      (@comm_ring_polynomial_factor_map
        R P S X base_map variables h valuation factor)
      h);

assert (R P S : τ CommRing)
  (X : Grpd)
  (base_map : τ (@CommRingHom R P))
  (variables : τ (@Function_grpd X (@comm_ring_carrier P)))
  (h : τ (@CommRingHom R S))
  (valuation : τ (@Function_grpd X (@comm_ring_carrier S)))
  (factor : τ (@CommRingPolynomialFactor
      R P S X base_map variables h valuation)) ⊢
  @comm_ring_polynomial_factor_variables
    R P S X base_map variables h valuation factor
  : τ (@CommRingPolynomialVariableAgreement
      X P S variables
      (@comm_ring_polynomial_factor_map
        R P S X base_map variables h valuation factor)
      valuation);

assert (R P : τ CommRing)
  (X : Grpd)
  (base_map : τ (@CommRingHom R P))
  (variables : τ (@Function_grpd X (@comm_ring_carrier P))) ⊢
  @IsCommRingPolynomialAlgebra R X P base_map variables
  : Grpd;

assert (R : τ CommRing)
  (X : Grpd) ⊢
  @CommRingPolynomialAlgebra R X
  : Grpd;

assert (R P : τ CommRing)
  (X : Grpd)
  (base_map : τ (@CommRingHom R P))
  (variables : τ (@Function_grpd X (@comm_ring_carrier P)))
  (property : τ (@IsCommRingPolynomialAlgebra
      R X P base_map variables)) ⊢
  @comm_ring_polynomial_target R X
    (@comm_ring_polynomial_intro
      R X P base_map variables property)
  ≡ P;

assert (R P : τ CommRing)
  (X : Grpd)
  (base_map : τ (@CommRingHom R P))
  (variables : τ (@Function_grpd X (@comm_ring_carrier P)))
  (property : τ (@IsCommRingPolynomialAlgebra
      R X P base_map variables)) ⊢
  @comm_ring_polynomial_base_map R X
    (@comm_ring_polynomial_intro
      R X P base_map variables property)
  ≡ base_map;

assert (R P : τ CommRing)
  (X : Grpd)
  (base_map : τ (@CommRingHom R P))
  (variables : τ (@Function_grpd X (@comm_ring_carrier P)))
  (property : τ (@IsCommRingPolynomialAlgebra
      R X P base_map variables)) ⊢
  @comm_ring_polynomial_variables R X
    (@comm_ring_polynomial_intro
      R X P base_map variables property)
  ≡ variables;

// Chosen packages retain honest Sigma structure without broad package eta.
assertnot (R : τ CommRing)
  (X : Grpd)
  (polynomial : τ (@CommRingPolynomialAlgebra R X)) ⊢
  polynomial
  ≡ @comm_ring_polynomial_intro
      R X
      (@comm_ring_polynomial_target R X polynomial)
      (@comm_ring_polynomial_base_map R X polynomial)
      (@comm_ring_polynomial_variables R X polynomial)
      (@comm_ring_polynomial_property R X polynomial);
/* End of the PSSS-07d polynomial-algebra diagnostics. */

// catalog-area: CommRing-valued presheaves and invertibility support
// The generic typed identity view is stable under later source specialization.
assert [A B : Cat]
  (F : τ (Functor A B))
  (X : τ (Obj A)) ⊢
  @fapp1_id_path A B F X
  : τ (@=
      (Hom B (@fapp0 A B F X) (@fapp0 A B F X))
      (@fapp1_fapp0 A B F X X (@id A X))
      (@id B (@fapp0 A B F X)));

// CommRing-valued presheaves are a transparent functor category.
assert (K : Cat) ⊢
  @CommRingPsh_cat K
  ≡ @Functor_cat (Op_cat K) CommRing_cat;

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K)) ⊢
  @comm_ring_psh_value K O U
  ≡ @fapp0 (Op_cat K) CommRing_cat O U;

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [V U : τ (Obj K)]
  (f : τ (Hom K V U)) ⊢
  @comm_ring_psh_restriction_hom K O V U f
  ≡ @fapp1_fapp0 (Op_cat K) CommRing_cat O U V f;

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [V U : τ (Obj K)]
  (f : τ (Hom K V U))
  (s : τ (@CommRingPshSection K O U)) ⊢
  @comm_ring_psh_restrict K O V U f s
  ≡ @comm_ring_hom_apply
      (@comm_ring_psh_value K O U)
      (@comm_ring_psh_value K O V)
      (@comm_ring_psh_restriction_hom K O V U f)
      s;

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U)) ⊢
  @comm_ring_psh_restrict_id_path K O U s
  : τ (@= (@CommRingPshSection K O U)
      (@comm_ring_psh_restrict K O U U (@id K U) s)
      s);

// Whole CommRing_cat identity stays opaque at the carrier boundary.
assertnot [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U)) ⊢
  @comm_ring_psh_restrict K O U U (@id K U) s
  ≡ s;

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [W V U : τ (Obj K)]
  (f : τ (Hom K V U))
  (g : τ (Hom K W V)) ⊢
  @comm_ring_psh_restriction_comp_pointwise_path K O W V U f g
  : τ (@= (@CommRingHom
      (@comm_ring_psh_value K O U)
      (@comm_ring_psh_value K O W))
      (@comm_ring_psh_restriction_hom K O W U
        (@comp_fapp0 K W V U f g))
      (@comm_ring_hom_comp_pointwise
        (@comm_ring_psh_value K O U)
        (@comm_ring_psh_value K O V)
        (@comm_ring_psh_value K O W)
        (@comm_ring_psh_restriction_hom K O W V g)
        (@comm_ring_psh_restriction_hom K O V U f)));

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [W V U : τ (Obj K)]
  (f : τ (Hom K V U))
  (g : τ (Hom K W V))
  (s : τ (@CommRingPshSection K O U)) ⊢
  @comm_ring_psh_restrict_comp_path K O W V U f g s
  : τ (@= (@CommRingPshSection K O W)
      (@comm_ring_psh_restrict K O W U
        (@comp_fapp0 K W V U f g) s)
      (@comm_ring_psh_restrict K O W V g
        (@comm_ring_psh_restrict K O V U f s)));

// Whole CommRing_cat composition likewise stays opaque on carrier elements.
assertnot [K : Cat]
  (O : τ (@CommRingPsh K))
  [W V U : τ (Obj K)]
  (f : τ (Hom K V U))
  (g : τ (Hom K W V))
  (s : τ (@CommRingPshSection K O U)) ⊢
  @comm_ring_psh_restrict K O W U
    (@comp_fapp0 K W V U f g) s
  ≡ @comm_ring_psh_restrict K O W V g
      (@comm_ring_psh_restrict K O V U f s);

// Unit preservation has a concrete mapped-inverse normal form.
assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  [x : τ (@comm_ring_carrier R)]
  (u : τ (@CommRingUnitEvidence R x)) ⊢
  @comm_ring_unit_inverse
    S
    (@comm_ring_hom_apply R S h x)
    (@comm_ring_hom_preserves_unit R S h x u)
  ≡ @comm_ring_hom_apply R S h
      (@comm_ring_unit_inverse R x u);

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [V U : τ (Obj K)]
  (f : τ (Hom K V U))
  (s : τ (@CommRingPshSection K O U)) ⊢
  @CommRingPshInvertibleAlong K O U s V f
  ≡ @CommRingUnitEvidence
      (@comm_ring_psh_value K O V)
      (@comm_ring_psh_restrict K O V U f s);

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [V U : τ (Obj K)]
  (f : τ (Hom K V U))
  (s : τ (@CommRingPshSection K O U)) ⊢
  @comm_ring_psh_invertible_along_is_prop K O U s V f
  : τ (IsPropGrpd (@CommRingPshInvertibleAlong K O U s V f));

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [W V U : τ (Obj K)]
  (f : τ (Hom K V U))
  (g : τ (Hom K W V))
  (s : τ (@CommRingPshSection K O U))
  (u : τ (@CommRingPshInvertibleAlong K O U s V f)) ⊢
  @comm_ring_psh_invertible_along_restrict K O W V U f g s u
  : τ (@CommRingPshInvertibleAlong K O U s W
      (@comp_fapp0 K W V U f g));
/* End of the PSSS-08a CommRing-presheaf diagnostics. */

// catalog-area: CommRing-valued presheaf invertibility sieve
// The selected carrier functor exposes ring carriers at objects.
assert (R : τ CommRing) ⊢
  @fapp0 CommRing_cat Grpd_cat comm_ring_carrier_func R
  ≡ @comm_ring_carrier R;

// Its full hom action retains the iterable path-map functor.
assert [R S : τ CommRing] ⊢
  @fapp1_func CommRing_cat Grpd_cat comm_ring_carrier_func R S
  ≡ @path_map_func
      (@CommRingHom R S)
      (@Function_grpd
        (@comm_ring_carrier R)
        (@comm_ring_carrier S))
      (λ h : τ (@CommRingHom R S),
        @comm_ring_hom_function R S h);

// No competing direct capped carrier-action beta is selected.
assertnot [R S : τ CommRing]
  (h : τ (@CommRingHom R S)) ⊢
  @fapp1_fapp0 CommRing_cat Grpd_cat
    comm_ring_carrier_func R S h
  ≡ @comm_ring_hom_function R S h;

// Capping the selected full action uses the existing path-map projection.
assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S)) ⊢
  @fapp0
    (Path_cat (@CommRingHom R S))
    (Path_cat (@Function_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S)))
    (@fapp1_func CommRing_cat Grpd_cat
      comm_ring_carrier_func R S)
    h
  ≡ @comm_ring_hom_function R S h;

assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (x : τ (@comm_ring_carrier R)) ⊢
  (@fapp0
    (Path_cat (@CommRingHom R S))
    (Path_cat (@Function_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S)))
    (@fapp1_func CommRing_cat Grpd_cat
      comm_ring_carrier_func R S)
    h) x
  ≡ @comm_ring_hom_apply R S h x;

assert (R : τ CommRing) ⊢
  @Fibre_cat CommRing_cat comm_ring_carrier_catd R
  ≡ Path_cat (@comm_ring_carrier R);

// Literal total ring elements expose Path_cat-valued unit evidence.
assert (R : τ CommRing)
  (x : τ (@comm_ring_carrier R)) ⊢
  @Fibre_cat
    (@Sigma_cat CommRing_cat comm_ring_carrier_catd)
    comm_ring_unit_evidence_total_catd
    (Struct_sigma R x)
  ≡ Path_cat (@CommRingUnitEvidence R x);

assert (R : τ CommRing)
  (x : τ (@comm_ring_carrier R)) ⊢
  Obj
    (@Fibre_cat
      (@Sigma_cat CommRing_cat comm_ring_carrier_catd)
      comm_ring_unit_evidence_total_catd
      (Struct_sigma R x))
  ≡ @CommRingUnitEvidence R x;

// Displayed covariance reaches the structured map's actual carrier action.
assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (x : τ (@comm_ring_carrier R)) ⊢
  @fapp0
    (Path_cat (@CommRingHom R S))
    (Path_cat (@comm_ring_carrier S))
    (@fib_cov_tapp0_func
      CommRing_cat comm_ring_carrier_catd R S x)
    h
  ≡ @comm_ring_hom_apply R S h x;

// The shaped represented-family comparison fires only during elaboration.
assert [K : Cat]
  (U : τ (Obj K)) ⊢
  @eq_refl
    (Functor (Op_cat K) Cat_cat)
    (@hom_ (Op_cat K) (Op_cat K)
      (@id Cat_cat (Op_cat K)) U)
  : τ (@=
      (Functor (Op_cat K) Cat_cat)
      (@hom_ (Op_cat K) (Op_cat K)
        (@id Cat_cat (Op_cat K)) U)
      (@hom_con K U K (@id Cat_cat K)));

assertnot [K : Cat]
  (U : τ (Obj K)) ⊢
  @hom_ (Op_cat K) (Op_cat K)
    (@id Cat_cat (Op_cat K)) U
  ≡ @hom_con K U K (@id Cat_cat K);

// Owner-position probe for the normalized companion: typed reflexivity must
// invoke proof-time unification after Op(Op(K)) has reduced to K.
assert [K : Cat]
  (U : τ (Obj K)) ⊢
  @eq_refl
    (Functor K Cat_cat)
    (@hom_ K K (@id Cat_cat K) U)
  : τ (@=
      (Functor K Cat_cat)
      (@hom_ K K (@id Cat_cat K) U)
      (@hom_con
        (Op_cat K)
        U
        (Op_cat K)
        (@id Cat_cat (Op_cat K))));

// The proof-time bridge deliberately installs no runtime conversion.
assertnot [K : Cat]
  (U : τ (Obj K)) ⊢
  @hom_ K K (@id Cat_cat K) U
  ≡ @hom_con
      (Op_cat K)
      U
      (Op_cat K)
      (@id Cat_cat (Op_cat K));

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (V : τ (Obj K)) ⊢
  @Fibre_cat
    (Op_cat K)
    (@comm_ring_psh_carrier_catd K O)
    V
  ≡ Path_cat
      (@comm_ring_carrier (@comm_ring_psh_value K O V));

// The total map computes both the ring and restricted-section projections.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U))
  [V : τ (Obj K)]
  (f : τ (Hom K V U)) ⊢
  sigma_Fst
    (@fapp0
      (@Into_restr_cat K U)
      (@Sigma_cat CommRing_cat comm_ring_carrier_catd)
      (@comm_ring_psh_restriction_total_func K O U s)
      (Struct_sigma V f))
  ≡ @comm_ring_psh_value K O V;

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U))
  [V : τ (Obj K)]
  (f : τ (Hom K V U)) ⊢
  sigma_Snd
    (@fapp0
      (@Into_restr_cat K U)
      (@Sigma_cat CommRing_cat comm_ring_carrier_catd)
      (@comm_ring_psh_restriction_total_func K O U s)
      (Struct_sigma V f))
  ≡ @comm_ring_psh_restrict K O V U f s;

// Literal higher-sieve fibres and ordinary membership retain computation.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U))
  [V : τ (Obj K)]
  (f : τ (Hom K V U)) ⊢
  @Fibre_cat
    (@Into_restr_cat K U)
    (@comm_ring_psh_invertibility_higher_sieve K O U s)
    (Struct_sigma V f)
  ≡ Path_cat (@CommRingPshInvertibleAlong K O U s V f);

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U))
  [V : τ (Obj K)]
  (f : τ (Hom K V U)) ⊢
  Obj
    (@Fibre_cat
      (@Into_restr_cat K U)
      (@comm_ring_psh_invertibility_higher_sieve K O U s)
      (Struct_sigma V f))
  ≡ @CommRingPshInvertibleAlong K O U s V f;

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U)) ⊢
  @comm_ring_psh_invertibility_ordinary_evidence K O U s
  : τ (@IsOrdinarySieve K U
      (@comm_ring_psh_invertibility_higher_sieve K O U s));

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U)) ⊢
  @comm_ring_psh_invertibility_sieve K O U s
  : τ (@Sieve K U);

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U))
  [V : τ (Obj K)]
  (f : τ (Hom K V U)) ⊢
  @SieveMembership
    K U
    (@comm_ring_psh_invertibility_sieve K O U s)
    (Struct_sigma V f)
  ≡ @CommRingPshInvertibleAlong K O U s V f;
/* End of the PSSS-08b invertibility-sieve diagnostics. */

// catalog-area: Presented affine Zariski basic opens and base change
// Dependent finite evidence computes on visible family constructors.
assert [A : Grpd]
  (P : τ A → Grpd)
  (n : τ Nat_grpd)
  (x : τ A)
  (xs : τ (@FiniteFamily A n)) ⊢
  @FiniteFamilyAll
    A P (succ n) (@finite_family_cons A n x xs)
  ≡ @Product_grpd (P x) (@FiniteFamilyAll A P n xs);

assert [A : Grpd]
  [P : τ A → Grpd]
  [n : τ Nat_grpd]
  [x : τ A]
  [xs : τ (@FiniteFamily A n)]
  (head : τ (P x))
  (tail : τ (@FiniteFamilyAll A P n xs)) ⊢
  @finite_family_all_head
    A P n (@finite_family_cons A n x xs)
    (@finite_family_all_cons A P n x xs head tail)
  ≡ head;

// Ordinary-sieve pullback exposes membership at canonical postcomposition.
assert [K : Cat]
  [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (Q : τ (@Sieve K U))
  (f : τ (Obj (@Into_restr_cat K V)))
  (member : τ (@SieveMembership
      K U Q (@into_restr_postcompose K V U p f))) ⊢
  @sieve_pullback_membership K V U p Q f member
  : τ (@SieveMembership
      K V (@sieve_pullback K V U p Q) f);

assert (R : τ CommRing)
  (localization : τ (@CommRingLocalizationAt R (@comm_ring_one R))) ⊢
  @comm_ring_zariski_cover_family_length
    R (@comm_ring_unit_zariski_cover_family R localization)
  ≡ succ zero;

// A chosen localization computes to its affine domain and structural map.
assert [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R f)) ⊢
  @into_restr_domain
    (Op_cat CommRing_cat) R
    (@comm_ring_basic_open_arrow R f localization)
  ≡ @comm_ring_localization_target R f localization;

assert [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R f)) ⊢
  @into_restr_arrow
    (Op_cat CommRing_cat) R
    (@comm_ring_basic_open_arrow R f localization)
  ≡ @comm_ring_localization_map R f localization;

// Base-change composition has a literal carrier-action normal form.
assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  [f : τ (@comm_ring_carrier R)]
  (target_localization : τ (@CommRingLocalizationAt
      S (@comm_ring_hom_apply R S h f)))
  (x : τ (@comm_ring_carrier R)) ⊢
  @comm_ring_hom_apply
    R
    (@comm_ring_localization_target
      S
      (@comm_ring_hom_apply R S h f)
      target_localization)
    (@comm_ring_basic_open_base_change_composite
      R S h f target_localization)
    x
  ≡ @comm_ring_hom_apply
      S
      (@comm_ring_localization_target
        S
        (@comm_ring_hom_apply R S h f)
        target_localization)
      (@comm_ring_localization_map
        S
        (@comm_ring_hom_apply R S h f)
        target_localization)
      (@comm_ring_hom_apply R S h x);

assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  [f : τ (@comm_ring_carrier R)]
  (source_localization : τ (@CommRingLocalizationAt R f))
  (target_localization : τ (@CommRingLocalizationAt
      S (@comm_ring_hom_apply R S h f))) ⊢
  @comm_ring_basic_open_base_change_factor_map
    R S h f source_localization target_localization
  : τ (@CommRingHom
      (@comm_ring_localization_target R f source_localization)
      (@comm_ring_localization_target
        S
        (@comm_ring_hom_apply R S h f)
        target_localization));

assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  [f : τ (@comm_ring_carrier R)]
  (source_localization : τ (@CommRingLocalizationAt R f))
  (target_localization : τ (@CommRingLocalizationAt
      S (@comm_ring_hom_apply R S h f))) ⊢
  @comm_ring_basic_open_base_change_triangle
    R S h f source_localization target_localization
  : τ (@=
      (@CommRingHom
        R
        (@comm_ring_localization_target
          S
          (@comm_ring_hom_apply R S h f)
          target_localization))
      (@comm_ring_hom_comp
        R
        (@comm_ring_localization_target R f source_localization)
        (@comm_ring_localization_target
          S
          (@comm_ring_hom_apply R S h f)
          target_localization)
        (@comm_ring_basic_open_base_change_factor_map
          R S h f source_localization target_localization)
        (@comm_ring_localization_map R f source_localization))
      (@comm_ring_basic_open_base_change_composite
        R S h f target_localization));

assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  [f : τ (@comm_ring_carrier R)]
  (source_localization : τ (@CommRingLocalizationAt R f))
  (target_localization : τ (@CommRingLocalizationAt
      S (@comm_ring_hom_apply R S h f))) ⊢
  @comm_ring_basic_open_base_change_into_arrow
    R S h f source_localization target_localization
  : τ (Hom
      (@Into_restr_cat (Op_cat CommRing_cat) R)
      (@comm_ring_basic_open_arrow R f source_localization)
      (Struct_sigma
        (@comm_ring_localization_target
          S
          (@comm_ring_hom_apply R S h f)
          target_localization)
        (@comm_ring_basic_open_base_change_composite
          R S h f target_localization)));

// Pointwise composition and canonical slice action meet only propositionally.
assertnot [R S T : τ CommRing]
  (h : τ (@CommRingHom R S))
  (g : τ (@CommRingHom S T)) ⊢
  @into_restr_postcompose
    (Op_cat CommRing_cat)
    S R h
    (Struct_sigma T g)
  ≡ @Struct_sigma
      (Obj CommRing_cat)
      (λ L : τ (Obj CommRing_cat),
        Obj (@Fibre_cat
          CommRing_cat
          (@yoneda_psh (Op_cat CommRing_cat) R)
          L))
      T
      (@comm_ring_hom_comp_pointwise R S T g h);

// Elementwise localization-generated membership is stable under pullback.
assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  [f : τ (@comm_ring_carrier R)]
  (source_localization : τ (@CommRingLocalizationAt R f))
  (target_localization : τ (@CommRingLocalizationAt
      S (@comm_ring_hom_apply R S h f)))
  (Q : τ (@Sieve (Op_cat CommRing_cat) R))
  (member : τ (@SieveMembership
      (Op_cat CommRing_cat)
      R Q
      (@comm_ring_basic_open_arrow R f source_localization))) ⊢
  @comm_ring_basic_open_pullback_membership
    R S h f source_localization target_localization Q member
  : τ (@SieveMembership
      (Op_cat CommRing_cat)
      S
      (@sieve_pullback
        (Op_cat CommRing_cat)
        S R h Q)
      (@comm_ring_basic_open_arrow
        S
        (@comm_ring_hom_apply R S h f)
        target_localization));
/* End of the PSSS-09a presented basic-open diagnostics. */

// catalog-area: Finite selected Zariski containment and base change
// Dependent evidence over selected evidence computes by Nat/Sigma recursion.
assert [A : Grpd]
  (P : τ A → Grpd)
  (Q : Π x : τ A, τ (P x) → Grpd)
  (n : τ Nat_grpd)
  (x : τ A)
  (xs : τ (@FiniteFamily A n))
  (px : τ (P x))
  (evidence : τ (@FiniteFamilyAll A P n xs)) ⊢
  @FiniteFamilyAllOver
    A P Q
    (succ n)
    (@finite_family_cons A n x xs)
    (@finite_family_all_cons A P n x xs px evidence)
  ≡ @Product_grpd
      (Q x px)
      (@FiniteFamilyAllOver A P Q n xs evidence);

assert [A B : Grpd]
  (map : τ (@Function_grpd A B))
  [P : τ A → Grpd]
  [P2 : τ B → Grpd]
  [Q : Π x : τ A, τ (P x) → Grpd]
  [Q2 : Π y : τ B, τ (P2 y) → Grpd]
  (step : Π x : τ A,
    Π px : τ (P x),
    Π py : τ (P2 (map x)),
      τ (Q x px) → τ (Q2 (map x) py))
  (n : τ Nat_grpd) ⊢
  @finite_family_all_over_map
    A B map P P2 Q Q2 step n
  : τ (@FiniteFamilyAllOverMap
      A B map P P2 Q Q2 n);

// Cover base change retains the mapped algebra and explicit target choices.
assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (family : τ (@CommRingZariskiCoverFamily R))
  (target_localizations : τ (@CommRingLocalizationFamily
      S
      (@comm_ring_zariski_cover_family_length R family)
      (@finite_family_map
        (@comm_ring_carrier R)
        (@comm_ring_carrier S)
        (@comm_ring_hom_function R S h)
        (@comm_ring_zariski_cover_family_length R family)
        (@comm_ring_zariski_cover_family_generators R family)))) ⊢
  @comm_ring_zariski_cover_family_map
    R S h family target_localizations
  : τ (@CommRingZariskiCoverFamily S);

// Finite containment retains literal membership at every selected basic open.
assert [R : τ CommRing]
  (n : τ Nat_grpd)
  (generators : τ (@FiniteFamily (@comm_ring_carrier R) n))
  (localizations : τ (@CommRingLocalizationFamily R n generators))
  (Q : τ (@Sieve (Op_cat CommRing_cat) R)) ⊢
  @CommRingBasicOpenFamilyMembership
    R n generators localizations Q
  : Grpd;

assert [R : τ CommRing]
  (family : τ (@CommRingZariskiCoverFamily R))
  (Q : τ (@Sieve (Op_cat CommRing_cat) R)) ⊢
  @CommRingZariskiCoverFamilyMembership R family Q
  : Grpd;

// The bounded nonempty consumer assembles returned pullback membership.
assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (source_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_one R)))
  (target_localization : τ (@CommRingLocalizationAt
      S (@comm_ring_hom_apply R S h (@comm_ring_one R))))
  (Q : τ (@Sieve (Op_cat CommRing_cat) R))
  (member : τ (@SieveMembership
      (Op_cat CommRing_cat)
      R Q
      (@comm_ring_basic_open_arrow
        R (@comm_ring_one R) source_localization))) ⊢
  @comm_ring_unit_basic_open_family_pullback_membership
    R S h source_localization target_localization Q member
  : τ (@CommRingBasicOpenFamilyMembership
      S
      (succ zero)
      (@finite_family_singleton
        (@comm_ring_carrier S)
        (@comm_ring_hom_apply R S h (@comm_ring_one R)))
      (@comm_ring_localization_family_singleton
        S
        (@comm_ring_hom_apply R S h (@comm_ring_one R))
        target_localization)
      (@sieve_pullback (Op_cat CommRing_cat) S R h Q));
/* End of the PSSS-09b1 finite-containment diagnostics. */

// catalog-area: Supplied Zariski-compatible topology
// Compatibility is proposition-valued while presentations remain explicit.
assert [T : τ (@GrothTopology (Op_cat CommRing_cat))]
  [R : τ CommRing]
  (family : τ (@CommRingZariskiCoverFamily R)) ⊢
  @comm_ring_zariski_presentation_covers_is_prop T R family
  : τ (IsPropGrpd (@CommRingZariskiPresentationCovers T R family));

assert [T : τ (@GrothTopology (Op_cat CommRing_cat))] ⊢
  @is_comm_ring_zariski_compatible_topology_is_prop T
  : τ (IsPropGrpd (@IsCommRingZariskiCompatibleTopology T));

// Package projections compute through the ordinary Sigma owners.
assert [T : τ (@GrothTopology (Op_cat CommRing_cat))]
  (compatible : τ (@IsCommRingZariskiCompatibleTopology T)) ⊢
  @comm_ring_zariski_compatible_topology_topology
    (@comm_ring_zariski_compatible_topology_intro T compatible)
  ≡ T;

assert [T : τ (@GrothTopology (Op_cat CommRing_cat))]
  (compatible : τ (@IsCommRingZariskiCompatibleTopology T)) ⊢
  @comm_ring_zariski_compatible_topology_compatible
    (@comm_ring_zariski_compatible_topology_intro T compatible)
  ≡ compatible;

// The direct chaotic model is nonempty and its cover consumer computes.
assert ⊢
  chaotic_comm_ring_zariski_compatible_topology
  : τ CommRingZariskiCompatibleTopology;

assert [R : τ CommRing]
  (family : τ (@CommRingZariskiCoverFamily R))
  (Q : τ (@Sieve (Op_cat CommRing_cat) R))
  (members : τ (@CommRingZariskiCoverFamilyMembership R family Q)) ⊢
  @comm_ring_zariski_compatible_topology_covers
    chaotic_comm_ring_zariski_compatible_topology
    R family Q members
  ≡ tt;
/* End of the PSSS-09cZ1 supplied-topology diagnostics. */

// catalog-area: Invertibility-cover locality and localization factors
// The topology view is transparent and remains proposition-valued.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U)) ⊢
  @CommRingPshInvertibilityCover K T O U s
  ≡ @groth_topology_covers
      K T U (@comm_ring_psh_invertibility_sieve K O U s);

assert [K : Cat]
  (T : τ (@GrothTopology K))
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U)) ⊢
  @comm_ring_psh_invertibility_cover_is_prop K T O U s
  : τ (IsPropGrpd (@CommRingPshInvertibilityCover K T O U s));

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U)) ⊢
  @chaotic_comm_ring_psh_invertibility_cover K O U s
  ≡ tt;

// Literal D(s) membership selects a universal localization factor.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  [V : τ (Obj K)]
  (f : τ (Hom K V U))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f))) ⊢
  @comm_ring_psh_localization_factor_at_member
    K O U s localization V f member
  : τ (@CommRingPshLocalizationFactorAlong
      K O U s localization V f);

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  [V : τ (Obj K)]
  (f : τ (Hom K V U))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f)))
  (x : τ (@CommRingPshSection K O U)) ⊢
  @comm_ring_psh_localization_factor_triangle_at
    K O U s localization V f member x
  : τ (@= (@CommRingPshSection K O V)
      (@comm_ring_hom_apply
        (@comm_ring_localization_target
          (@comm_ring_psh_value K O U) s localization)
        (@comm_ring_psh_value K O V)
        (@comm_ring_psh_localization_factor_map_at_member
          K O U s localization V f member)
        (@comm_ring_hom_apply
          (@comm_ring_psh_value K O U)
          (@comm_ring_localization_target
            (@comm_ring_psh_value K O U) s localization)
          (@comm_ring_localization_map
            (@comm_ring_psh_value K O U) s localization)
          x))
      (@comm_ring_psh_restrict K O V U f x));

// The internal value diagram reaches O(V) at the readable sieve element.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [U V : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (f : τ (Hom K V U))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f))) ⊢
  @fapp0
    (@CommRingPshInvertibilityElements_cat K O U s)
    CommRing_cat
    (@comm_ring_psh_invertibility_value_diagram K O U s)
    (@comm_ring_psh_invertibility_element K O U s V f member)
  ≡ @comm_ring_psh_value K O V;

// The internal cone component is the selected universal localization factor.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [U V : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  (f : τ (Hom K V U))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f))) ⊢
  @tapp0_fapp0
    (@CommRingPshInvertibilityElements_cat K O U s)
    CommRing_cat
    (@Const_func
      (@CommRingPshInvertibilityElements_cat K O U s)
      CommRing_cat
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization))
    (@comm_ring_psh_invertibility_value_diagram K O U s)
    (@comm_ring_psh_invertibility_element K O U s V f member)
    (@comm_ring_psh_localization_factor_cone K O U s localization)
  ≡ @comm_ring_psh_localization_factor_map_at_member
      K O U s localization V f member;

// Every total-category arrow has one internal off-diagonal cone component.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  [x y : τ (Obj (@CommRingPshInvertibilityElements_cat K O U s))]
  (a : τ (Hom (@CommRingPshInvertibilityElements_cat K O U s) x y)) ⊢
  @tapp1_fapp0
    (@CommRingPshInvertibilityElements_cat K O U s)
    CommRing_cat
    (@Const_func
      (@CommRingPshInvertibilityElements_cat K O U s)
      CommRing_cat
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization))
    (@comm_ring_psh_invertibility_value_diagram K O U s)
    x y
    (@comm_ring_psh_localization_factor_cone K O U s localization)
    a
  : τ (Hom
      CommRing_cat
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization)
      (@fapp0
        (@CommRingPshInvertibilityElements_cat K O U s)
        CommRing_cat
        (@comm_ring_psh_invertibility_value_diagram K O U s)
        y));

// Following a factor by another restriction gives a competing direct factor.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  [W V : τ (Obj K)]
  (f : τ (Hom K V U))
  (g : τ (Hom K W V))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f))) ⊢
  @comm_ring_psh_localization_factor_after_restriction
    K O U s localization W V f g member
  : τ (@CommRingPshLocalizationFactorAlong
      K O U s localization W (@comp_fapp0 K W V U f g));

// Contractible-factor uniqueness supplies the objectwise cone equation.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  [W V : τ (Obj K)]
  (f : τ (Hom K V U))
  (g : τ (Hom K W V))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f))) ⊢
  @comm_ring_psh_localization_factor_restriction_path
    K O U s localization W V f g member
  : τ (@=
      (@CommRingHom
        (@comm_ring_localization_target
          (@comm_ring_psh_value K O U) s localization)
        (@comm_ring_psh_value K O W))
      (@comm_ring_psh_localization_factor_map_at_member
        K O U s localization W (@comp_fapp0 K W V U f g)
        (@comm_ring_psh_invertible_along_restrict
          K O W V U f g s member))
      (@comm_ring_hom_comp_pointwise
        (@comm_ring_localization_target
          (@comm_ring_psh_value K O U) s localization)
        (@comm_ring_psh_value K O V)
        (@comm_ring_psh_value K O W)
        (@comm_ring_psh_restriction_hom K O W V g)
        (@comm_ring_psh_localization_factor_map_at_member
          K O U s localization V f member)));
/* End of the PSSS-08c0/PSSS-08c0C internal locality-cone diagnostics. */

// catalog-area: Localization matching restriction
// A literal matching fibre is the Path-valued carrier of O(V).
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [V U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (f : τ (Hom K V U))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f))) ⊢
  @Fibre_cat
    (@CommRingPshInvertibilityElements_cat K O U s)
    (@comm_ring_psh_localization_matching_catd K O U s)
    (@comm_ring_psh_invertibility_element K O U s V f member)
  ≡ Path_cat (@comm_ring_carrier (@comm_ring_psh_value K O V));

// The coherent section computes pointwise by the selected localization factor.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [V U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  (f : τ (Hom K V U))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f)))
  (x : τ (@comm_ring_carrier
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization))) ⊢
  @piapp0
    (@CommRingPshInvertibilityElements_cat K O U s)
    (@comm_ring_psh_localization_matching_catd K O U s)
    (@comm_ring_psh_localization_matching_section
      K O U s localization x)
    (@comm_ring_psh_invertibility_element K O U s V f member)
  ≡ @comm_ring_hom_apply
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization)
      (@comm_ring_psh_value K O V)
      (@comm_ring_psh_localization_factor_map_at_member
        K O U s localization V f member)
      x;

// PathLift exposes the selected section as the functor's object action.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  (x : τ (@comm_ring_carrier
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization))) ⊢
  @fapp0
    (Path_cat (@comm_ring_carrier
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization)))
    (@CommRingPshLocalizationMatching_cat K O U s)
    (@comm_ring_psh_localization_matching_restriction_func
      K O U s localization)
    x
  ≡ @comm_ring_psh_localization_matching_section
      K O U s localization x;

// Functor application followed by Pi evaluation preserves literal computation.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [V U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  (f : τ (Hom K V U))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f)))
  (x : τ (@comm_ring_carrier
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization))) ⊢
  @piapp0
    (@CommRingPshInvertibilityElements_cat K O U s)
    (@comm_ring_psh_localization_matching_catd K O U s)
    (@fapp0
      (Path_cat (@comm_ring_carrier
        (@comm_ring_localization_target
          (@comm_ring_psh_value K O U) s localization)))
      (@CommRingPshLocalizationMatching_cat K O U s)
      (@comm_ring_psh_localization_matching_restriction_func
        K O U s localization)
      x)
    (@comm_ring_psh_invertibility_element K O U s V f member)
  ≡ @comm_ring_hom_apply
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization)
      (@comm_ring_psh_value K O V)
      (@comm_ring_psh_localization_factor_map_at_member
        K O U s localization V f member)
      x;

// Equality-path action is internal and lands between coherent Pi sections.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  (x y : τ (@comm_ring_carrier
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization)))
  (p : τ (@=
      (@comm_ring_carrier
        (@comm_ring_localization_target
          (@comm_ring_psh_value K O U) s localization))
      x y)) ⊢
  @fapp1_fapp0
    (Path_cat (@comm_ring_carrier
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization)))
    (@CommRingPshLocalizationMatching_cat K O U s)
    (@comm_ring_psh_localization_matching_restriction_func
      K O U s localization)
    x y p
  : τ (Hom
      (@CommRingPshLocalizationMatching_cat K O U s)
      (@comm_ring_psh_localization_matching_section
        K O U s localization x)
      (@comm_ring_psh_localization_matching_section
        K O U s localization y));
/* End of the PSSS-08c0D localization-matching diagnostics. */

// catalog-area: Localization glue
// The selected localization carrier remains the actual ring carrier.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s)) ⊢
  @CommRingPshLocalizationCarrier K O U s localization
  ≡ @comm_ring_carrier
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization);

// Constructor projection preserves the complete selected glue functor.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  (glue_func : τ (@CommRingPshLocalizationGlueFunctor
      K O U s localization))
  (glue_restrict : τ (@CommRingPshLocalizationGlueRestrictLaw
      K O U s localization glue_func))
  (restrict_glue : τ
      (@CommRingPshLocalizationRestrictGlueComponentLaw
        K O U s localization glue_func)) ⊢
  @comm_ring_psh_localization_glue_func
    K O U s localization
    (@comm_ring_psh_localization_glue_intro
      K O U s localization glue_func glue_restrict restrict_glue)
  ≡ glue_func;

// Glue carries matching-arrow action internally through its functor package.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  (glue : τ (@CommRingPshLocalizationGlue K O U s localization))
  (m n : τ (Obj (@CommRingPshLocalizationMatching_cat K O U s)))
  (eta : τ (Hom (@CommRingPshLocalizationMatching_cat K O U s) m n)) ⊢
  @fapp1_fapp0
    (@CommRingPshLocalizationMatching_cat K O U s)
    (Path_cat (@CommRingPshLocalizationCarrier K O U s localization))
    (@comm_ring_psh_localization_glue_func K O U s localization glue)
    m n eta
  : τ (Hom
      (Path_cat (@CommRingPshLocalizationCarrier K O U s localization))
      (@comm_ring_psh_localization_glue
        K O U s localization glue m)
      (@comm_ring_psh_localization_glue
        K O U s localization glue n));

// The selected left-inverse law is available at every localization element.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  (glue : τ (@CommRingPshLocalizationGlue K O U s localization))
  (x : τ (@CommRingPshLocalizationCarrier K O U s localization)) ⊢
  @comm_ring_psh_localization_glue_restrict_path
    K O U s localization glue x
  : τ (@=
      (@CommRingPshLocalizationCarrier K O U s localization)
      (@comm_ring_psh_localization_glue
        K O U s localization glue
        (@comm_ring_psh_localization_matching_section
          K O U s localization x))
      x);

// Literal member observation is the computational Cartier factor equation.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [V U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  (glue : τ (@CommRingPshLocalizationGlue K O U s localization))
  (matching : τ (Obj
      (@CommRingPshLocalizationMatching_cat K O U s)))
  (f : τ (Hom K V U))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f))) ⊢
  @comm_ring_psh_localization_glue_at_member_path
    K O V U s localization glue matching f member
  : τ (@=
      (@comm_ring_carrier (@comm_ring_psh_value K O V))
      (@comm_ring_hom_apply
        (@comm_ring_localization_target
          (@comm_ring_psh_value K O U) s localization)
        (@comm_ring_psh_value K O V)
        (@comm_ring_psh_localization_factor_map_at_member
          K O U s localization V f member)
        (@comm_ring_psh_localization_glue
          K O U s localization glue matching))
      (@piapp0
        (@CommRingPshInvertibilityElements_cat K O U s)
        (@comm_ring_psh_localization_matching_catd K O U s)
        matching
        (@comm_ring_psh_invertibility_element K O U s V f member)));
/* End of the PSSS-08c0E localization-glue diagnostics. */

// catalog-area: Computational affine Spec slice
// Coordinate rings are an actual presheaf on the conventional big slice.
assert (R : τ CommRing) ⊢
  @affine_spec_coordinate_psh R
  : τ (@CommRingPsh (@AffineSpecBigSlice_cat R));

// The whole and selected basic-open chart values compute at the Sigma owner.
assert (R : τ CommRing) ⊢
  @comm_ring_psh_value
    (@AffineSpecBigSlice_cat R)
    (@affine_spec_coordinate_psh R)
    (@affine_spec_whole_chart R)
  ≡ R;

assert [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R f)) ⊢
  @comm_ring_psh_value
    (@AffineSpecBigSlice_cat R)
    (@affine_spec_coordinate_psh R)
    (@affine_spec_basic_open_chart R f localization)
  ≡ @comm_ring_localization_target R f localization;

// Both geometric overlap arrows retain their whole coordinate-ring maps.
assert [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))) ⊢
  @comm_ring_psh_restriction_hom
    (@AffineSpecBigSlice_cat R)
    (@affine_spec_coordinate_psh R)
    (@affine_spec_iterated_basic_open_chart R f g iterated)
    (@affine_spec_basic_open_chart
      R (@comm_ring_mul R f g) product_localization)
    (@affine_spec_overlap_forward_chart_arrow
      R f g iterated product_localization)
  ≡ @comm_ring_iterated_localization_comparison_forward_map
      R f g iterated product_localization
      (@comm_ring_iterated_localization_comparison
        R f g iterated product_localization);

assert [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))) ⊢
  @comm_ring_psh_restriction_hom
    (@AffineSpecBigSlice_cat R)
    (@affine_spec_coordinate_psh R)
    (@affine_spec_basic_open_chart
      R (@comm_ring_mul R f g) product_localization)
    (@affine_spec_iterated_basic_open_chart R f g iterated)
    (@affine_spec_overlap_reverse_chart_arrow
      R f g iterated product_localization)
  ≡ @comm_ring_iterated_localization_comparison_reverse_map
      R f g iterated product_localization
      (@comm_ring_iterated_localization_comparison
        R f g iterated product_localization);

// The scheme-facing overlap facade preserves the native whole CommRing
// equivalence; it does not assert equality of functors or invoke univalence.
assert [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))) ⊢
  @affine_spec_overlap_coordinate_omega_equiv
    R f g iterated product_localization
  : τ (@OmegaEquiv
      CommRing_cat
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_target R f g iterated));
/* End of the PSSS-10a computational affine-Spec diagnostics. */
