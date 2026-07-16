/*
  m- / emdash3.2 diagnostic/assertion checks.

  The implementation lives in emdash3_2.lp; this module owns executable
  diagnostic and regression `assert` commands. Assertions remain grouped by
  the architecture they exercise, while the generated reviewer-facing area
  map lives in reports/REPORT_EMDASH_CHECK_CATALOG.md.

  Do not use source line numbers as durable identifiers. Prefer a mathematical
  area comment, the checked head, and normalized/type-aware search.
*/

flag "eta_equality" on;
flag "print_implicits" on;
flag "print_contexts" on;
flag "print_domains" on;
flag "print_meta_args" on;

require open emdash.emdash3_2;

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
  @idtoequiv_cat
    (Path_cat Nat_grpd) zero zero (@eq_refl Nat_grpd zero)
  ≡ @omega_equiv_refl (Path_cat Nat_grpd) zero;

assert (n : τ Nat_grpd) ⊢
  @idtoequiv_cat
    (Path_cat Nat_grpd)
    (succ n) (succ n) (@eq_refl Nat_grpd (succ n))
  ≡ @omega_equiv_refl (Path_cat Nat_grpd) (succ n);

assertnot ⊢
  @idtoequiv_cat (Path_cat Nat_grpd) zero zero tt
  ≡ @omega_equiv_refl (Path_cat Nat_grpd) zero;

assertnot (n : τ Nat_grpd) ⊢
  @idtoequiv_cat
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
  @idtoequiv_cat
    (Path_cat Unit_grpd) tt tt (@eq_refl Unit_grpd tt)
  ≡ @omega_equiv_refl (Path_cat Unit_grpd) tt;

assertnot ⊢
  @idtoiso_cat (Path_cat Unit_grpd) tt tt tt
  ≡ @iso_evidence_refl (Path_cat Unit_grpd) tt;

assertnot ⊢
  @idtoequiv_cat (Path_cat Unit_grpd) tt tt tt
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

// Both categorical equality encoders retain their generic reflexivity beta.
assert ⊢
  @idtoiso_cat
    (Path_cat Bool_grpd) false false (@eq_refl Bool_grpd false)
  ≡ @iso_evidence_refl (Path_cat Bool_grpd) false;

assert ⊢
  @idtoiso_cat
    (Path_cat Bool_grpd) true true (@eq_refl Bool_grpd true)
  ≡ @iso_evidence_refl (Path_cat Bool_grpd) true;

assert ⊢
  @idtoequiv_cat
    (Path_cat Bool_grpd) false false (@eq_refl Bool_grpd false)
  ≡ @omega_equiv_refl (Path_cat Bool_grpd) false;

assert ⊢
  @idtoequiv_cat
    (Path_cat Bool_grpd) true true (@eq_refl Bool_grpd true)
  ≡ @omega_equiv_refl (Path_cat Bool_grpd) true;

assertnot ⊢
  @idtoiso_cat (Path_cat Bool_grpd) false false tt
  ≡ @iso_evidence_refl (Path_cat Bool_grpd) false;

assertnot ⊢
  @idtoequiv_cat (Path_cat Bool_grpd) false false tt
  ≡ @omega_equiv_refl (Path_cat Bool_grpd) false;

// Open Boolean values retain the generic classifier and reflexivity typing.
assertnot (b : τ Bool_grpd) ⊢
  @= Bool_grpd b b
  ≡ Unit_grpd;

assertnot (b : τ Bool_grpd) ⊢
  @eq_refl Bool_grpd b
  : τ Unit_grpd;

// catalog-area: auto

// General binary sum: decoding, introductions, dependent elimination, and
// constructor beta. Non-collapse is only a conversion control, not a
// no-confusion, canonicity, normalization, or observational-identity theorem.
assert [A B : Grpd] ⊢
  τ (Sum_grpd A B)
  ≡ SumData A B;

assert [A B : Grpd]
  (a : τ A) ⊢
  @sum_inl A B a
  : τ (Sum_grpd A B);

assert [A B : Grpd]
  (b : τ B) ⊢
  @sum_inr A B b
  : τ (Sum_grpd A B);

assert [A B : Grpd]
  (P : τ (Sum_grpd A B) → Grpd)
  (u_inl : Π a : τ A, τ (P (@sum_inl A B a)))
  (u_inr : Π b : τ B, τ (P (@sum_inr A B b)))
  (s : τ (Sum_grpd A B)) ⊢
  @sum_elim A B P u_inl u_inr s
  : τ (P s);

assert [A B : Grpd]
  (P : τ (Sum_grpd A B) → Grpd)
  (u_inl : Π a : τ A, τ (P (@sum_inl A B a)))
  (u_inr : Π b : τ B, τ (P (@sum_inr A B b)))
  (a : τ A) ⊢
  @sum_elim A B P u_inl u_inr (@sum_inl A B a)
  ≡ u_inl a;

assert [A B : Grpd]
  (P : τ (Sum_grpd A B) → Grpd)
  (u_inl : Π a : τ A, τ (P (@sum_inl A B a)))
  (u_inr : Π b : τ B, τ (P (@sum_inr A B b)))
  (b : τ B) ⊢
  @sum_elim A B P u_inl u_inr (@sum_inr A B b)
  ≡ u_inr b;

assertnot [A B : Grpd]
  (a : τ A)
  (b : τ B) ⊢
  @sum_inl A B a
  ≡ @sum_inr A B b;

// catalog-area: Sum observational equality
// Equal tags recurse to component equality; distinct tags expose Empty.
assert [A B : Grpd]
  (a0 a1 : τ A) ⊢
  @= (Sum_grpd A B)
    (@sum_inl A B a0) (@sum_inl A B a1)
  ≡ @= A a0 a1;

assert [A B : Grpd]
  (a : τ A)
  (b : τ B) ⊢
  @= (Sum_grpd A B)
    (@sum_inl A B a) (@sum_inr A B b)
  ≡ Empty_grpd;

assert [A B : Grpd]
  (a : τ A)
  (b : τ B) ⊢
  @= (Sum_grpd A B)
    (@sum_inr A B b) (@sum_inl A B a)
  ≡ Empty_grpd;

assert [A B : Grpd]
  (b0 b1 : τ B) ⊢
  @= (Sum_grpd A B)
    (@sum_inr A B b0) (@sum_inr A B b1)
  ≡ @= B b0 b1;

assert [B : Grpd]
  (n m : τ Nat_grpd) ⊢
  @= (Sum_grpd Nat_grpd B)
    (@sum_inl Nat_grpd B (succ n))
    (@sum_inl Nat_grpd B (succ m))
  ≡ @= Nat_grpd n m;

assert [A : Grpd] ⊢
  @= (Sum_grpd A Bool_grpd)
    (@sum_inr A Bool_grpd false)
    (@sum_inr A Bool_grpd true)
  ≡ Empty_grpd;

// Outer sum reflexivity and component reflexivity inhabit the reduced
// classifier but remain distinct runtime and proof-time presentations.
assert [A B : Grpd]
  (a : τ A) ⊢
  @eq_refl (Sum_grpd A B) (@sum_inl A B a)
  : τ (@= A a a);

assert [A B : Grpd]
  (b : τ B) ⊢
  @eq_refl (Sum_grpd A B) (@sum_inr A B b)
  : τ (@= B b b);

assert [A B : Grpd]
  (a : τ A) ⊢
  @eq_refl A a
  : τ (@=
      (Sum_grpd A B)
      (@sum_inl A B a)
      (@sum_inl A B a));

assert [A B : Grpd]
  (b : τ B) ⊢
  @eq_refl B b
  : τ (@=
      (Sum_grpd A B)
      (@sum_inr A B b)
      (@sum_inr A B b));

assertnot [A B : Grpd]
  (a : τ A) ⊢
  (λ p : τ (@=
      (Sum_grpd A B)
      (@sum_inl A B a)
      (@sum_inl A B a)), p)
    (@eq_refl (Sum_grpd A B) (@sum_inl A B a))
  ≡
  (λ p : τ (@=
      (Sum_grpd A B)
      (@sum_inl A B a)
      (@sum_inl A B a)), p)
    (@eq_refl A a);

assertnot [A B : Grpd]
  (a : τ A) ⊢
  @eq_refl
    (@= A a a)
    (@eq_refl (Sum_grpd A B) (@sum_inl A B a))
  : τ (@=
      (@= A a a)
      (@eq_refl (Sum_grpd A B) (@sum_inl A B a))
      (@eq_refl A a));

assertnot [A B : Grpd]
  (b : τ B) ⊢
  @eq_refl
    (@= B b b)
    (@eq_refl (Sum_grpd A B) (@sum_inr A B b))
  : τ (@=
      (@= B b b)
      (@eq_refl (Sum_grpd A B) (@sum_inr A B b))
      (@eq_refl B b));

// Generic J computes only on exactly matching outer reflexivity.
assert [A B : Grpd]
  (a : τ A)
  (P : Π s : τ (Sum_grpd A B),
    τ (@= (Sum_grpd A B) s (@sum_inl A B a)) → Grpd)
  (u : τ (P
    (@sum_inl A B a)
    (@eq_refl (Sum_grpd A B) (@sum_inl A B a)))) ⊢
  @ind_eqr
    (Sum_grpd A B)
    (@sum_inl A B a)
    P u
    (@sum_inl A B a)
    (@eq_refl (Sum_grpd A B) (@sum_inl A B a))
  ≡ u;

assert [A B : Grpd]
  (b : τ B)
  (P : Π s : τ (Sum_grpd A B),
    τ (@= (Sum_grpd A B) s (@sum_inr A B b)) → Grpd)
  (u : τ (P
    (@sum_inr A B b)
    (@eq_refl (Sum_grpd A B) (@sum_inr A B b)))) ⊢
  @ind_eqr
    (Sum_grpd A B)
    (@sum_inr A B b)
    P u
    (@sum_inr A B b)
    (@eq_refl (Sum_grpd A B) (@sum_inr A B b))
  ≡ u;

assertnot [A B : Grpd]
  (a : τ A) ⊢
  @ind_eqr
    (Sum_grpd A B)
    (@sum_inl A B a)
    (λ s : τ (Sum_grpd A B),
      λ _ : τ (@=
        (Sum_grpd A B) s (@sum_inl A B a)), Unit_grpd)
    tt
    (@sum_inl A B a)
    (@eq_refl A a)
  ≡ tt;

assertnot [A B : Grpd]
  (b : τ B) ⊢
  @ind_eqr
    (Sum_grpd A B)
    (@sum_inr A B b)
    (λ s : τ (Sum_grpd A B),
      λ _ : τ (@=
        (Sum_grpd A B) s (@sum_inr A B b)), Unit_grpd)
    tt
    (@sum_inr A B b)
    (@eq_refl B b)
  ≡ tt;

// Endpoint-guarded path consumers compute on outer reflexivity only.
assert [A B : Grpd]
  (a : τ A) ⊢
  @path_sym
    (Sum_grpd A B)
    (@sum_inl A B a)
    (@sum_inl A B a)
    (@eq_refl (Sum_grpd A B) (@sum_inl A B a))
  ≡ @eq_refl (Sum_grpd A B) (@sum_inl A B a);

assert [A B : Grpd]
  (b : τ B) ⊢
  @path_sym
    (Sum_grpd A B)
    (@sum_inr A B b)
    (@sum_inr A B b)
    (@eq_refl (Sum_grpd A B) (@sum_inr A B b))
  ≡ @eq_refl (Sum_grpd A B) (@sum_inr A B b);

assert [A B : Grpd]
  (a : τ A) ⊢
  @path_to_hom
    (Path_cat (Sum_grpd A B))
    (@sum_inl A B a)
    (@sum_inl A B a)
    (@eq_refl (Sum_grpd A B) (@sum_inl A B a))
  ≡ @id (Path_cat (Sum_grpd A B)) (@sum_inl A B a);

assert [A B : Grpd]
  (b : τ B) ⊢
  @path_to_hom
    (Path_cat (Sum_grpd A B))
    (@sum_inr A B b)
    (@sum_inr A B b)
    (@eq_refl (Sum_grpd A B) (@sum_inr A B b))
  ≡ @id (Path_cat (Sum_grpd A B)) (@sum_inr A B b);

assertnot [A B : Grpd]
  (a : τ A) ⊢
  (λ p : τ (@=
      (Sum_grpd A B)
      (@sum_inl A B a)
      (@sum_inl A B a)), p)
    (@path_sym
      (Sum_grpd A B)
      (@sum_inl A B a)
      (@sum_inl A B a)
      (@eq_refl A a))
  ≡
  (λ p : τ (@=
      (Sum_grpd A B)
      (@sum_inl A B a)
      (@sum_inl A B a)), p)
    (@eq_refl A a);

assertnot [A B : Grpd]
  (b : τ B) ⊢
  @path_to_hom
    (Path_cat (Sum_grpd A B))
    (@sum_inr A B b)
    (@sum_inr A B b)
    (@eq_refl B b)
  ≡ @id (Path_cat (Sum_grpd A B)) (@sum_inr A B b);

// Both path-category unit orientations retain the outer proof owner.
assert [A B : Grpd]
  (a : τ A)
  (s : τ (Sum_grpd A B))
  (p : τ (@=
    (Sum_grpd A B) (@sum_inl A B a) s)) ⊢
  @comp_fapp0
    (Path_cat (Sum_grpd A B))
    (@sum_inl A B a) (@sum_inl A B a) s
    p (@eq_refl (Sum_grpd A B) (@sum_inl A B a))
  ≡ p;

assert [A B : Grpd]
  (a : τ A)
  (s : τ (Sum_grpd A B))
  (p : τ (@=
    (Sum_grpd A B) s (@sum_inl A B a))) ⊢
  @comp_fapp0
    (Path_cat (Sum_grpd A B))
    s (@sum_inl A B a) (@sum_inl A B a)
    (@eq_refl (Sum_grpd A B) (@sum_inl A B a)) p
  ≡ p;

assert [A B : Grpd]
  (b : τ B)
  (s : τ (Sum_grpd A B))
  (p : τ (@=
    (Sum_grpd A B) (@sum_inr A B b) s)) ⊢
  @comp_fapp0
    (Path_cat (Sum_grpd A B))
    (@sum_inr A B b) (@sum_inr A B b) s
    p (@eq_refl (Sum_grpd A B) (@sum_inr A B b))
  ≡ p;

assert [A B : Grpd]
  (b : τ B)
  (s : τ (Sum_grpd A B))
  (p : τ (@=
    (Sum_grpd A B) s (@sum_inr A B b))) ⊢
  @comp_fapp0
    (Path_cat (Sum_grpd A B))
    s (@sum_inr A B b) (@sum_inr A B b)
    (@eq_refl (Sum_grpd A B) (@sum_inr A B b)) p
  ≡ p;

// Categorical encoders compute only from outer reflexivity.
assert [A B : Grpd]
  (a : τ A) ⊢
  @idtoiso_cat
    (Path_cat (Sum_grpd A B))
    (@sum_inl A B a)
    (@sum_inl A B a)
    (@eq_refl (Sum_grpd A B) (@sum_inl A B a))
  ≡ @iso_evidence_refl
      (Path_cat (Sum_grpd A B)) (@sum_inl A B a);

assert [A B : Grpd]
  (b : τ B) ⊢
  @idtoiso_cat
    (Path_cat (Sum_grpd A B))
    (@sum_inr A B b)
    (@sum_inr A B b)
    (@eq_refl (Sum_grpd A B) (@sum_inr A B b))
  ≡ @iso_evidence_refl
      (Path_cat (Sum_grpd A B)) (@sum_inr A B b);

assert [A B : Grpd]
  (a : τ A) ⊢
  @idtoequiv_cat
    (Path_cat (Sum_grpd A B))
    (@sum_inl A B a)
    (@sum_inl A B a)
    (@eq_refl (Sum_grpd A B) (@sum_inl A B a))
  ≡ @omega_equiv_refl
      (Path_cat (Sum_grpd A B)) (@sum_inl A B a);

assert [A B : Grpd]
  (b : τ B) ⊢
  @idtoequiv_cat
    (Path_cat (Sum_grpd A B))
    (@sum_inr A B b)
    (@sum_inr A B b)
    (@eq_refl (Sum_grpd A B) (@sum_inr A B b))
  ≡ @omega_equiv_refl
      (Path_cat (Sum_grpd A B)) (@sum_inr A B b);

assertnot [A B : Grpd]
  (a : τ A) ⊢
  @idtoiso_cat
    (Path_cat (Sum_grpd A B))
    (@sum_inl A B a)
    (@sum_inl A B a)
    (@eq_refl A a)
  ≡ @iso_evidence_refl
      (Path_cat (Sum_grpd A B)) (@sum_inl A B a);

assertnot [A B : Grpd]
  (b : τ B) ⊢
  @idtoequiv_cat
    (Path_cat (Sum_grpd A B))
    (@sum_inr A B b)
    (@sum_inr A B b)
    (@eq_refl B b)
  ≡ @omega_equiv_refl
      (Path_cat (Sum_grpd A B)) (@sum_inr A B b);

// Open sum endpoints retain primitive equality/reflexivity. These controls do
// not establish sum canonicity, normalization, or metatheoretic no-confusion.
assertnot [A B : Grpd]
  (s : τ (Sum_grpd A B)) ⊢
  @= (Sum_grpd A B) s s
  ≡ Unit_grpd;

assertnot [A B : Grpd]
  (s : τ (Sum_grpd A B)) ⊢
  @eq_refl (Sum_grpd A B) s
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

// Both categorical equality encoders register the shaped head.
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
  @idtoequiv_cat
    (Path_cat (PathRecord_grpd A))
    r r
    (@eq_refl (PathRecord_grpd A) r)
  ≡ @omega_equiv_refl (Path_cat (PathRecord_grpd A)) r;

assert [A : Grpd]
  (r : τ (PathRecord_grpd A)) ⊢
  @idtoequiv_cat
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
  @iso_evidence_path C x x (@iso_evidence_refl C x)
  ≡ @eq_refl (Obj C) x;

assert [C : Cat] (x : τ (Obj C)) ⊢
  @iso_evidence_to C x x (@idtoiso_cat C x x (eq_refl x))
  ≡ @id C x;

assert [C : Cat]
  [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y)) ⊢
  @isotoid_cat C (cat_iso_univalence C) x y i
  : τ (x = y);

assert ⊢
  cat_iso_univalence Cat_cat
  : τ (CatIsoUnivalence Cat_cat);

assert ⊢
  cat_iso_univalence_by_decoder Cat_cat
  : τ (CatIsoUnivalenceByDecoder Cat_cat);

// Candidate D0 fixed-arrow evidence, Sigma package, and recursive reflexivity.
assert [C : Cat]
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @OmegaEquivAlong_D0 C x y f
  : Grpd;

assert [C : Cat]
  (x y : τ (Obj C)) ⊢
  OmegaEquiv_D0 C x y
  : Grpd;

assert [C : Cat]
  [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @Struct_sigma
    (Hom C x y)
    (λ g : τ (Hom C x y), @OmegaEquivAlong_D0 C x y g)
    f
    u
  : τ (OmegaEquiv_D0 C x y);

assert [C : Cat]
  [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @omega_equiv_to_D0 C x y
    (@Struct_sigma
      (Hom C x y)
      (λ g : τ (Hom C x y), @OmegaEquivAlong_D0 C x y g)
      f
      u)
  ≡ f;

assert [C : Cat]
  [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @omega_equiv_evidence_D0 C x y
    (@Struct_sigma
      (Hom C x y)
      (λ g : τ (Hom C x y), @OmegaEquivAlong_D0 C x y g)
      f
      u)
  ≡ u;

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @omega_equiv_along_left_inv_D0 C x y f u
  : τ (Hom C y x);

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @omega_equiv_along_right_inv_D0 C x y f u
  : τ (Hom C y x);

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @omega_equiv_along_left_cell_D0 C x y f u
  : τ (OmegaEquiv_D0
      (Hom_cat C x x)
      (@comp_fapp0 C x y x
        (@omega_equiv_along_left_inv_D0 C x y f u)
        f)
      (@id C x));

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @omega_equiv_along_right_cell_D0 C x y f u
  : τ (OmegaEquiv_D0
      (Hom_cat C y y)
      (@comp_fapp0 C y x y
        f
        (@omega_equiv_along_right_inv_D0 C x y f u))
      (@id C y));

assert [C : Cat]
  (x : τ (Obj C)) ⊢
  @omega_equiv_along_refl_D0 C x
  : τ (@OmegaEquivAlong_D0 C x x (@id C x));

assert [C : Cat]
  (x : τ (Obj C)) ⊢
  @omega_equiv_refl_D0 C x
  : τ (OmegaEquiv_D0 C x x);

assert [C : Cat]
  (x : τ (Obj C)) ⊢
  @omega_equiv_to_D0 C x x (@omega_equiv_refl_D0 C x)
  ≡ @id C x;

assert [C : Cat]
  (x : τ (Obj C)) ⊢
  @omega_equiv_evidence_D0 C x x (@omega_equiv_refl_D0 C x)
  ≡ @omega_equiv_along_refl_D0 C x;

assert [C : Cat]
  (x : τ (Obj C)) ⊢
  @omega_equiv_along_left_inv_D0
    C x x (@id C x)
    (@omega_equiv_evidence_D0 C x x (@omega_equiv_refl_D0 C x))
  ≡ @id C x;

assert [C : Cat]
  (x : τ (Obj C)) ⊢
  @omega_equiv_along_right_inv_D0
    C x x (@id C x)
    (@omega_equiv_evidence_D0 C x x (@omega_equiv_refl_D0 C x))
  ≡ @id C x;

assert [C : Cat]
  (x : τ (Obj C)) ⊢
  @omega_equiv_along_left_cell_D0
    C x x (@id C x)
    (@omega_equiv_along_refl_D0 C x)
  ≡ @omega_equiv_refl_D0
      (Hom_cat C x x)
      (@id C x);

assert [C : Cat]
  (x : τ (Obj C)) ⊢
  @omega_equiv_along_right_cell_D0
    C x x (@id C x)
    (@omega_equiv_along_refl_D0 C x)
  ≡ @omega_equiv_refl_D0
      (Hom_cat C x x)
      (@id C x);

// One recursive next-hom rung: project the left reflexive cell's certificate,
// then observe its own left cell.
assert [C : Cat]
  (x : τ (Obj C)) ⊢
  @omega_equiv_along_left_cell_D0
    (Hom_cat C x x)
    (@id C x)
    (@id C x)
    (@id (Hom_cat C x x) (@id C x))
    (@omega_equiv_evidence_D0
      (Hom_cat C x x)
      (@id C x)
      (@id C x)
      (@omega_equiv_along_left_cell_D0
        C x x (@id C x)
        (@omega_equiv_along_refl_D0 C x)))
  ≡ @omega_equiv_refl_D0
      (Hom_cat (Hom_cat C x x) (@id C x) (@id C x))
      (@id (Hom_cat C x x) (@id C x));

// The Sigma package remains intensional: no open package eta is installed.
assertnot [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv_D0 C x y)) ⊢
  @Struct_sigma
    (Hom C x y)
    (λ f : τ (Hom C x y), @OmegaEquivAlong_D0 C x y f)
    (@omega_equiv_to_D0 C x y e)
    (@omega_equiv_evidence_D0 C x y e)
  ≡ e;

// Higher inverse evidence does not strictify either composite to identity.
assertnot [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @comp_fapp0 C x y x
    (@omega_equiv_along_left_inv_D0 C x y f u)
    f
  ≡ @id C x;

assertnot [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @comp_fapp0 C y x y
    f
    (@omega_equiv_along_right_inv_D0 C x y f u)
  ≡ @id C y;

// Candidate D0b variable-evidence Cat hom action and endpoint repair.
assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  @omega_equiv_along_fapp1_D0 A B F u x y
  : τ (@OmegaEquivAlong_D0
      Cat_cat
      (Hom_cat A x y)
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (@fapp1_func A B F x y));

assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  @Struct_sigma
    (Functor
      (Hom_cat A x y)
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y)))
    (λ G : τ (Functor
      (Hom_cat A x y)
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))),
      @OmegaEquivAlong_D0
        Cat_cat
        (Hom_cat A x y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        G)
    (@fapp1_func A B F x y)
    (@omega_equiv_along_fapp1_D0 A B F u x y)
  : τ (OmegaEquiv_D0
      Cat_cat
      (Hom_cat A x y)
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y)));

assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  @omega_equiv_to_D0
    Cat_cat
    (Hom_cat A x y)
    (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
    (@Struct_sigma
      (Functor
        (Hom_cat A x y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y)))
      (λ G : τ (Functor
        (Hom_cat A x y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))),
        @OmegaEquivAlong_D0
          Cat_cat
          (Hom_cat A x y)
          (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
          G)
      (@fapp1_func A B F x y)
      (@omega_equiv_along_fapp1_D0 A B F u x y))
  ≡ @fapp1_func A B F x y;

assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  @omega_equiv_evidence_D0
    Cat_cat
    (Hom_cat A x y)
    (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
    (@Struct_sigma
      (Functor
        (Hom_cat A x y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y)))
      (λ G : τ (Functor
        (Hom_cat A x y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))),
        @OmegaEquivAlong_D0
          Cat_cat
          (Hom_cat A x y)
          (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
          G)
      (@fapp1_func A B F x y)
      (@omega_equiv_along_fapp1_D0 A B F u x y))
  ≡ @omega_equiv_along_fapp1_D0 A B F u x y;

assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F)) ⊢
  omega_equiv_along_left_functor_D0 u
  : τ (Functor B A);

assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F)) ⊢
  omega_equiv_along_right_functor_D0 u
  : τ (Functor B A);

assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x : τ (Obj A)) ⊢
  omega_equiv_along_left_from_component_D0 u x
  : τ (Hom A
      x
      (@fapp0 B A
        (omega_equiv_along_left_functor_D0 u)
        (@fapp0 A B F x)));

assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (y : τ (Obj A)) ⊢
  omega_equiv_along_left_to_component_D0 u y
  : τ (Hom A
      (@fapp0 B A
        (omega_equiv_along_left_functor_D0 u)
        (@fapp0 A B F y))
      y);

assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x : τ (Obj A)) ⊢
  omega_equiv_along_fapp1_right_source_D0 u x
  : τ (Hom A
      x
      (@fapp0 B A
        (omega_equiv_along_right_functor_D0 u)
        (@fapp0 A B F x)));

assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (y : τ (Obj A)) ⊢
  omega_equiv_along_fapp1_right_target_D0 u y
  : τ (Hom A
      (@fapp0 B A
        (omega_equiv_along_right_functor_D0 u)
        (@fapp0 A B F y))
      y);

assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  omega_equiv_along_fapp1_left_inv_D0 u x y
  : τ (Functor
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (Hom_cat A x y));

assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  omega_equiv_along_fapp1_right_inv_D0 u x y
  : τ (Functor
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (Hom_cat A x y));

// Raw hom action of either inverse functor retains the wrong endpoints.
assertnot [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  @fapp1_func
    B A
    (omega_equiv_along_left_functor_D0 u)
    (@fapp0 A B F x)
    (@fapp0 A B F y)
  : τ (Functor
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (Hom_cat A x y));

assertnot [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  @fapp1_func
    B A
    (omega_equiv_along_right_functor_D0 u)
    (@fapp0 A B F x)
    (@fapp0 A B F y)
  : τ (Functor
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (Hom_cat A x y));

// Both selected inverse observations compute to the conjugated functors.
assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  omega_equiv_along_left_inv_D0
    (@omega_equiv_along_fapp1_D0 A B F u x y)
  ≡ omega_equiv_along_fapp1_left_inv_D0 u x y;

assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  omega_equiv_along_right_inv_D0
    (@omega_equiv_along_fapp1_D0 A B F u x y)
  ≡ omega_equiv_along_fapp1_right_inv_D0 u x y;

// Object projections expose the inverse-functor action after endpoint repair.
assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A))
  (h : τ (Hom B (@fapp0 A B F x) (@fapp0 A B F y))) ⊢
  fapp0 (omega_equiv_along_fapp1_left_inv_D0 u x y) h
  ≡ @Hom_fapp0
      A
      (@fapp0 B A
        (omega_equiv_along_left_functor_D0 u)
        (@fapp0 A B F x))
      x
      (@fapp0 B A
        (omega_equiv_along_left_functor_D0 u)
        (@fapp0 A B F y))
      y
      (omega_equiv_along_left_from_component_D0 u x)
      (omega_equiv_along_left_to_component_D0 u y)
      (@fapp1_fapp0
        B A
        (omega_equiv_along_left_functor_D0 u)
        (@fapp0 A B F x)
        (@fapp0 A B F y)
        h);

assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A))
  (h : τ (Hom B (@fapp0 A B F x) (@fapp0 A B F y))) ⊢
  fapp0 (omega_equiv_along_fapp1_right_inv_D0 u x y) h
  ≡ @Hom_fapp0
      A
      (@fapp0 B A
        (omega_equiv_along_right_functor_D0 u)
        (@fapp0 A B F x))
      x
      (@fapp0 B A
        (omega_equiv_along_right_functor_D0 u)
        (@fapp0 A B F y))
      y
      (omega_equiv_along_fapp1_right_source_D0 u x)
      (omega_equiv_along_fapp1_right_target_D0 u y)
      (@fapp1_fapp0
        B A
        (omega_equiv_along_right_functor_D0 u)
        (@fapp0 A B F x)
        (@fapp0 A B F y)
        h);

// Both recursive cell observations compute to transparent next-hom packages.
assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  omega_equiv_along_left_cell_D0
    (@omega_equiv_along_fapp1_D0 A B F u x y)
  ≡ omega_equiv_along_fapp1_left_cell_D0 u x y;

assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  omega_equiv_along_right_cell_D0
    (@omega_equiv_along_fapp1_D0 A B F u x y)
  ≡ omega_equiv_along_fapp1_right_cell_D0 u x y;

assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  omega_equiv_to_D0
    (omega_equiv_along_left_cell_D0
      (@omega_equiv_along_fapp1_D0 A B F u x y))
  ≡ omega_equiv_along_fapp1_left_cell_to_D0 u x y;

assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  omega_equiv_evidence_D0
    (omega_equiv_along_left_cell_D0
      (@omega_equiv_along_fapp1_D0 A B F u x y))
  ≡ omega_equiv_along_fapp1_left_cell_evidence_D0 u x y;

assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  omega_equiv_to_D0
    (omega_equiv_along_right_cell_D0
      (@omega_equiv_along_fapp1_D0 A B F u x y))
  ≡ omega_equiv_along_fapp1_right_cell_to_D0 u x y;

assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  omega_equiv_evidence_D0
    (omega_equiv_along_right_cell_D0
      (@omega_equiv_along_fapp1_D0 A B F u x y))
  ≡ omega_equiv_along_fapp1_right_cell_evidence_D0 u x y;

// One more observation at each returned cell confirms recursive iterability.
assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  omega_equiv_along_left_inv_D0
    (omega_equiv_evidence_D0
      (omega_equiv_along_left_cell_D0
        (@omega_equiv_along_fapp1_D0 A B F u x y)))
  : τ (Hom
      (Functor_cat (Hom_cat A x y) (Hom_cat A x y))
      (@id_func (Hom_cat A x y))
      (@comp_cat_fapp0
        (Hom_cat A x y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (Hom_cat A x y)
        (omega_equiv_along_fapp1_left_inv_D0 u x y)
        (@fapp1_func A B F x y)));

assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  omega_equiv_along_right_inv_D0
    (omega_equiv_evidence_D0
      (omega_equiv_along_right_cell_D0
        (@omega_equiv_along_fapp1_D0 A B F u x y)))
  : τ (Hom
      (Functor_cat
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y)))
      (@id_func
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y)))
      (@comp_cat_fapp0
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (Hom_cat A x y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (@fapp1_func A B F x y)
        (omega_equiv_along_fapp1_right_inv_D0 u x y)));

// D1 public fixed-map normal form and categorical decoder.
// catalog-area: Public fixed-map omega-equivalence and categorical decoder
assert [C : Cat]
  [x y : τ (Obj C)] ⊢
  OmegaEquiv C x y
  ≡ `Σ_ f : τ (Hom C x y), @OmegaEquivAlong C x y f;

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)] ⊢
  @OmegaEquivAlong C x y f
  ≡ @OmegaEquivAlong_D0 C x y f;

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f)) ⊢
  @omega_equiv_from_along C x y f u
  : τ (OmegaEquiv C x y);

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f)) ⊢
  @omega_equiv_to C x y
    (@omega_equiv_from_along C x y f u)
  ≡ f;

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f)) ⊢
  @omega_equiv_evidence C x y
    (@omega_equiv_from_along C x y f u)
  ≡ u;

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f)) ⊢
  @omega_equiv_left_inv C x y
    (@omega_equiv_from_along C x y f u)
  ≡ @omega_equiv_along_left_inv_D0 C x y f u;

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f)) ⊢
  @omega_equiv_right_inv C x y
    (@omega_equiv_from_along C x y f u)
  ≡ @omega_equiv_along_right_inv_D0 C x y f u;

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f)) ⊢
  @omega_equiv_left_cell C x y
    (@omega_equiv_from_along C x y f u)
  ≡ @omega_equiv_along_left_cell_D0 C x y f u;

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f)) ⊢
  @omega_equiv_right_cell C x y
    (@omega_equiv_from_along C x y f u)
  ≡ @omega_equiv_along_right_cell_D0 C x y f u;

// The semantic fibre comparison is a one-sided retraction, not package eta.
assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f)) ⊢
  @omega_equiv_along_to_fibre C x y f u
  : τ (@OmegaEquivFibre C x y f);

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f)) ⊢
  @omega_equiv_fibre_to_along C x y f
    (@omega_equiv_along_to_fibre C x y f u)
  ≡ u;

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f)) ⊢
  @omega_equiv_along_fibre_retract C x y f u
  ≡ eq_refl u;

assertnot [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y)) ⊢
  @omega_equiv_from_along
    C x y
    (@omega_equiv_to C x y e)
    (@omega_equiv_evidence C x y e)
  ≡ e;

assertnot [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (h : τ (@OmegaEquivFibre C x y f)) ⊢
  @omega_equiv_along_to_fibre C x y f
    (@omega_equiv_fibre_to_along C x y f h)
  ≡ h;

// Opposite closure is evidence-owned, including its decoder square.
assert [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y)) ⊢
  @omega_equiv_evidence
    (Op_cat C) y x (@omega_equiv_op C x y e)
  ≡ @omega_equiv_along_op_D1
      C x y
      (@omega_equiv_to C x y e)
      (@omega_equiv_evidence C x y e);

assert [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y)) ⊢
  @omega_equiv_path
    (Op_cat C) y x (@omega_equiv_op C x y e)
  ≡ @path_sym
      (Obj C)
      x
      y
      (@omega_equiv_path C x y e);

assert [C : Cat]
  (x : τ (Obj C)) ⊢
  @omega_equiv_evidence
    (Op_cat C)
    x
    x
    (@omega_equiv_op C x x (@omega_equiv_refl C x))
  ≡ @omega_equiv_along_refl_D0 (Op_cat C) x;

// Both reduction orders join for opposite evidence specialized to reflexivity.
assert [C : Cat]
  (x : τ (Obj C)) ⊢
  @omega_equiv_along_left_inv_D0
    (Op_cat C) x x (@id C x)
    (@omega_equiv_along_op_D1
      C x x (@id C x) (@omega_equiv_along_refl_D0 C x))
  ≡ @omega_equiv_along_left_inv_D0
      (Op_cat C) x x (@id C x)
      (@omega_equiv_along_refl_D0 (Op_cat C) x);

assert [C : Cat]
  (x : τ (Obj C)) ⊢
  @omega_equiv_along_right_inv_D0
    (Op_cat C) x x (@id C x)
    (@omega_equiv_along_op_D1
      C x x (@id C x) (@omega_equiv_along_refl_D0 C x))
  ≡ @omega_equiv_along_right_inv_D0
      (Op_cat C) x x (@id C x)
      (@omega_equiv_along_refl_D0 (Op_cat C) x);

assert [C : Cat]
  (x : τ (Obj C)) ⊢
  @omega_equiv_along_left_cell_D0
    (Op_cat C) x x (@id C x)
    (@omega_equiv_along_op_D1
      C x x (@id C x) (@omega_equiv_along_refl_D0 C x))
  ≡ @omega_equiv_along_left_cell_D0
      (Op_cat C) x x (@id C x)
      (@omega_equiv_along_refl_D0 (Op_cat C) x);

assert [C : Cat]
  (x : τ (Obj C)) ⊢
  @omega_equiv_along_right_cell_D0
    (Op_cat C) x x (@id C x)
    (@omega_equiv_along_op_D1
      C x x (@id C x) (@omega_equiv_along_refl_D0 C x))
  ≡ @omega_equiv_along_right_cell_D0
      (Op_cat C) x x (@id C x)
      (@omega_equiv_along_refl_D0 (Op_cat C) x);

assert [C : Cat]
  (x : τ (Obj C)) ⊢
  @omega_equiv_along_path_D1
    (Op_cat C) x x (@id C x)
    (@omega_equiv_along_op_D1
      C x x (@id C x) (@omega_equiv_along_refl_D0 C x))
  ≡ @omega_equiv_along_path_D1
      (Op_cat C) x x (@id C x)
      (@omega_equiv_along_refl_D0 (Op_cat C) x);

// catalog-area: Product reflexivity provenance
// Product closure retains the component evidence in one fixed-map owner.
assert [A B : Cat]
  [x0 x1 : τ (Obj A)]
  [y0 y1 : τ (Obj B)]
  (eA : τ (OmegaEquiv A x0 x1))
  (eB : τ (OmegaEquiv B y0 y1)) ⊢
  @omega_equiv_evidence
    (Product_cat A B)
    (Struct_sigma x0 y0)
    (Struct_sigma x1 y1)
    (@omega_equiv_product A B x0 x1 y0 y1 eA eB)
  ≡ @omega_equiv_along_product_D1
      A B x0 x1 y0 y1
      (@omega_equiv_to A x0 x1 eA)
      (@omega_equiv_to B y0 y1 eB)
      (@omega_equiv_evidence A x0 x1 eA)
      (@omega_equiv_evidence B y0 y1 eB);

assert [A B : Cat]
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  @omega_equiv_evidence
    (Product_cat A B)
    (Struct_sigma x y)
    (Struct_sigma x y)
    (@omega_equiv_product
      A B x x y y
      (@omega_equiv_refl A x)
      (@omega_equiv_refl B y))
  ≡ @omega_equiv_along_product_D1
      A B x x y y
      (@id A x) (@id B y)
      (@omega_equiv_along_refl_D0 A x)
      (@omega_equiv_along_refl_D0 B y);

// Componentwise Product evidence no longer collapses to generic reflexivity.
assertnot [A B : Cat]
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  @omega_equiv_evidence
    (Product_cat A B)
    (Struct_sigma x y)
    (Struct_sigma x y)
    (@omega_equiv_product
      A B x x y y
      (@omega_equiv_refl A x)
      (@omega_equiv_refl B y))
  ≡ @omega_equiv_along_refl_D0
      (Product_cat A B)
      (Struct_sigma x y);

// Inverse-arrow projections still join with generic Product reflexivity.
assert [A B : Cat]
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  omega_equiv_along_left_inv_D0
    (@omega_equiv_along_product_D1
      A B x x y y
      (@id A x) (@id B y)
      (@omega_equiv_along_refl_D0 A x)
      (@omega_equiv_along_refl_D0 B y))
  ≡ omega_equiv_along_left_inv_D0
      (@omega_equiv_along_refl_D0
        (Product_cat A B) (Struct_sigma x y));

assert [A B : Cat]
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  omega_equiv_along_right_inv_D0
    (@omega_equiv_along_product_D1
      A B x x y y
      (@id A x) (@id B y)
      (@omega_equiv_along_refl_D0 A x)
      (@omega_equiv_along_refl_D0 B y))
  ≡ omega_equiv_along_right_inv_D0
      (@omega_equiv_along_refl_D0
        (Product_cat A B) (Struct_sigma x y));

assert [A B : Cat]
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  omega_equiv_along_left_cell_D0
    (@omega_equiv_along_product_D1
      A B x x y y
      (@id A x) (@id B y)
      (@omega_equiv_along_refl_D0 A x)
      (@omega_equiv_along_refl_D0 B y))
  ≡ omega_equiv_product
      (omega_equiv_along_left_cell_D0
        (@omega_equiv_along_refl_D0 A x))
      (omega_equiv_along_left_cell_D0
        (@omega_equiv_along_refl_D0 B y));

assert [A B : Cat]
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  omega_equiv_along_right_cell_D0
    (@omega_equiv_along_product_D1
      A B x x y y
      (@id A x) (@id B y)
      (@omega_equiv_along_refl_D0 A x)
      (@omega_equiv_along_refl_D0 B y))
  ≡ omega_equiv_product
      (omega_equiv_along_right_cell_D0
        (@omega_equiv_along_refl_D0 A x))
      (omega_equiv_along_right_cell_D0
        (@omega_equiv_along_refl_D0 B y));

assertnot [A B : Cat]
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  omega_equiv_along_left_cell_D0
    (@omega_equiv_along_product_D1
      A B x x y y
      (@id A x) (@id B y)
      (@omega_equiv_along_refl_D0 A x)
      (@omega_equiv_along_refl_D0 B y))
  ≡ omega_equiv_along_left_cell_D0
      (@omega_equiv_along_refl_D0
        (Product_cat A B) (Struct_sigma x y));

assert [A B : Cat]
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  sigma_Fst
    (omega_equiv_along_path_D1
      (@omega_equiv_along_product_D1
        A B x x y y
        (@id A x) (@id B y)
        (@omega_equiv_along_refl_D0 A x)
        (@omega_equiv_along_refl_D0 B y)))
  ≡ @eq_refl (Obj A) x;

assert [A B : Cat]
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  sigma_Snd
    (omega_equiv_along_path_D1
      (@omega_equiv_along_product_D1
        A B x x y y
        (@id A x) (@id B y)
        (@omega_equiv_along_refl_D0 A x)
        (@omega_equiv_along_refl_D0 B y)))
  ≡ @const_pathover
      (Obj A)
      (Obj B)
      x x y y
      (@eq_refl (Obj A) x)
      (@eq_refl (Obj B) y);

assertnot [A B : Cat]
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  omega_equiv_along_path_D1
    (@omega_equiv_along_product_D1
      A B x x y y
      (@id A x) (@id B y)
      (@omega_equiv_along_refl_D0 A x)
      (@omega_equiv_along_refl_D0 B y))
  ≡ @eq_refl
      (Obj (Product_cat A B))
      (Struct_sigma x y);

// catalog-area: auto

// The canonical decoder capability owns both propositional round trips.
assert [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (x = y)) ⊢
  @omega_equiv_path_idtoequiv_cat C x y p
  : τ (
      @omega_equiv_path C x y (@idtoequiv_cat C x y p)
      = p);

assert [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y)) ⊢
  @idtoequiv_cat_omega_equiv_path C x y e
  : τ (
      @idtoequiv_cat C x y (@omega_equiv_path C x y e)
      = e);

assert [C : Cat] ⊢
  @cat_univalence_from_decoder C
  : τ (CatUnivalence C);

assert [C : Cat]
  (x y : τ (Obj C)) ⊢
  @cat_univalence_type_equiv C x y
  : τ (TypeEquiv (@= (Obj C) x y) (OmegaEquiv C x y));

assert [C : Cat]
  (x y : τ (Obj C))
  (p : τ (x = y)) ⊢
  @type_equiv_to
    (@= (Obj C) x y)
    (OmegaEquiv C x y)
    (@cat_univalence_type_equiv C x y)
    p
  ≡ @idtoequiv_cat C x y p;

assert [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y)) ⊢
  @cat_univalence_selected_path C x y e
  ≡ @omega_equiv_path C x y e;

assert [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y)) ⊢
  @equivtoid_cat C
    (@cat_univalence_from_decoder C)
    x y e
  ≡ @omega_equiv_path C x y e;

// The Core path square is propositional; no open runtime fold is installed.
assert [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (x = y)) ⊢
  @idtoequiv_cat_path_to_hom C x y p
  : τ (
      @omega_equiv_to C x y (@idtoequiv_cat C x y p)
      = @path_to_hom C x y p);

assert [C : Cat]
  (x : τ (Obj C)) ⊢
  @idtoequiv_cat_path_to_hom C x x (eq_refl x)
  ≡ eq_refl (@id C x);

assertnot [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (x = y)) ⊢
  @omega_equiv_to C x y (@idtoequiv_cat C x y p)
  ≡ @path_to_hom C x y p;

assertnot [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (x = y)) ⊢
  @omega_equiv_path C x y (@idtoequiv_cat C x y p)
  ≡ p;

assertnot [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y)) ⊢
  @idtoequiv_cat C x y (@omega_equiv_path C x y e)
  ≡ e;

// A category path produces an iterable next-hom omega-equivalence via D0b.
assert [A B : Cat]
  (p : τ (@= (Obj Cat_cat) A B)) ⊢
  @idtoequiv_cat_functor_D1 A B p
  : τ (Functor A B);

assert [A B : Cat]
  (p : τ (@= (Obj Cat_cat) A B))
  (x y : τ (Obj A)) ⊢
  @idtoequiv_cat_fapp1_along_D1 A B p x y
  : τ (@OmegaEquivAlong
      Cat_cat
      (Hom_cat A x y)
      (Hom_cat B
        (@fapp0 A B (idtoequiv_cat_functor_D1 p) x)
        (@fapp0 A B (idtoequiv_cat_functor_D1 p) y))
      (@fapp1_func A B (idtoequiv_cat_functor_D1 p) x y));

assert [A B : Cat]
  (p : τ (@= (Obj Cat_cat) A B))
  (x y : τ (Obj A)) ⊢
  @omega_equiv_to
    Cat_cat
    (Hom_cat A x y)
    (Hom_cat B
      (@fapp0 A B (idtoequiv_cat_functor_D1 p) x)
      (@fapp0 A B (idtoequiv_cat_functor_D1 p) y))
    (@idtoequiv_cat_fapp1_D1 A B p x y)
  ≡ @fapp1_func A B (idtoequiv_cat_functor_D1 p) x y;

assert [A B : Cat]
  (p : τ (@= (Obj Cat_cat) A B))
  (x y : τ (Obj A)) ⊢
  @omega_equiv_evidence
    Cat_cat
    (Hom_cat A x y)
    (Hom_cat B
      (@fapp0 A B (idtoequiv_cat_functor_D1 p) x)
      (@fapp0 A B (idtoequiv_cat_functor_D1 p) y))
    (@idtoequiv_cat_fapp1_D1 A B p x y)
  ≡ @idtoequiv_cat_fapp1_along_D1 A B p x y;

assert [A B : Cat]
  (p : τ (@= (Obj Cat_cat) A B))
  (x y : τ (Obj A)) ⊢
  @omega_equiv_left_cell
    Cat_cat
    (Hom_cat A x y)
    (Hom_cat B
      (@fapp0 A B (idtoequiv_cat_functor_D1 p) x)
      (@fapp0 A B (idtoequiv_cat_functor_D1 p) y))
    (@idtoequiv_cat_fapp1_D1 A B p x y)
  : τ (OmegaEquiv
      (Functor_cat (Hom_cat A x y) (Hom_cat A x y))
      (@comp_cat_fapp0
        (Hom_cat A x y)
        (Hom_cat B
          (@fapp0 A B (idtoequiv_cat_functor_D1 p) x)
          (@fapp0 A B (idtoequiv_cat_functor_D1 p) y))
        (Hom_cat A x y)
        (@omega_equiv_left_inv
          Cat_cat
          (Hom_cat A x y)
          (Hom_cat B
            (@fapp0 A B (idtoequiv_cat_functor_D1 p) x)
            (@fapp0 A B (idtoequiv_cat_functor_D1 p) y))
          (@idtoequiv_cat_fapp1_D1 A B p x y))
        (@fapp1_func A B (idtoequiv_cat_functor_D1 p) x y))
      (@id_func (Hom_cat A x y)));

// catalog-area: auto
// Phase 9 discrete-category core and homwise adequacy.
// catalog-area: Discrete category core-inclusion adequacy
assert [C : Cat] ⊢
  IsDiscreteCat C
  ≡ @Product_grpd
      (IsSetGrpd (Obj C))
      (@OmegaEquivAlong
        Cat_cat
        (Core_cat C)
        C
        (Core_incl_func C));

assert [C : Cat]
  (obj_set : τ (IsSetGrpd (Obj C)))
  (core_equiv : τ (@OmegaEquivAlong
      Cat_cat (Core_cat C) C (Core_incl_func C))) ⊢
  @discrete_cat_intro C obj_set core_equiv
  : τ (IsDiscreteCat C);

assert [C : Cat]
  (obj_set : τ (IsSetGrpd (Obj C)))
  (core_equiv : τ (@OmegaEquivAlong
      Cat_cat (Core_cat C) C (Core_incl_func C))) ⊢
  @is_discrete_cat_obj_set C
    (@discrete_cat_intro C obj_set core_equiv)
  ≡ obj_set;

assert [C : Cat]
  (obj_set : τ (IsSetGrpd (Obj C)))
  (core_equiv : τ (@OmegaEquivAlong
      Cat_cat (Core_cat C) C (Core_incl_func C))) ⊢
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
  ≡ @omega_equiv_along_fapp1_D0
      (Core_cat C)
      C
      (Core_incl_func C)
      (is_discrete_cat_core_equiv d)
      x y;

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
  @discrete_core_hom_left_cell C d x y
  : τ (OmegaEquiv
      (Functor_cat
        (Path_cat (@= (Obj C) x y))
        (Path_cat (@= (Obj C) x y)))
      (@comp_cat_fapp0
        (Path_cat (@= (Obj C) x y))
        (Hom_cat C x y)
        (Path_cat (@= (Obj C) x y))
        (@discrete_core_hom_inv_func C d x y)
        (@core_incl_hom_func C x y))
      (@id_func (Path_cat (@= (Obj C) x y))));

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

// The two round trips are carried by recursive cells, not runtime cancellation.
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

// catalog-area: auto
assert [C : Cat] (x : τ (Obj C)) ⊢
  omega_equiv_to (@omega_equiv_refl C x)
  ≡ @id C x;

assert [C : Cat] (x : τ (Obj C)) ⊢
  omega_equiv_left_inv (@omega_equiv_refl C x)
  ≡ @id C x;

assert [C : Cat] (x : τ (Obj C)) ⊢
  omega_equiv_right_inv (@omega_equiv_refl C x)
  ≡ @id C x;

assert [C : Cat] (x : τ (Obj C)) ⊢
  omega_equiv_left_cell (@omega_equiv_refl C x)
  ≡ @omega_equiv_refl (Hom_cat C x x) (@id C x);

assert [C : Cat] (x : τ (Obj C)) ⊢
  omega_equiv_right_cell (@omega_equiv_refl C x)
  ≡ @omega_equiv_refl (Hom_cat C x x) (@id C x);

assert [A : Grpd] (x : τ A) ⊢
  @path_cat_omega_path A x x
    (@omega_equiv_refl (Path_cat A) x)
  ≡ eq_refl x;

assert [A : Grpd] (x : τ A) ⊢
  @path_cat_iso_path A x x
    (@iso_evidence_refl (Path_cat A) x)
  ≡ eq_refl x;

assert [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y)) ⊢
  @omega_equiv_op C x y e
  : τ (OmegaEquiv (Op_cat C) y x);

assert [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y)) ⊢
  @id (Hom_cat (Op_cat C) y x)
    (@omega_equiv_to (Op_cat C) y x (@omega_equiv_op C x y e))
  ≡ @id (Hom_cat (Op_cat C) y x)
    (@omega_equiv_to C x y e);

assert [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y)) ⊢
  @id (Hom_cat (Op_cat C) x y)
    (@omega_equiv_left_inv (Op_cat C) y x (@omega_equiv_op C x y e))
  ≡ @id (Hom_cat (Op_cat C) x y)
    (@omega_equiv_right_inv C x y e);

assert [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y)) ⊢
  @id (Hom_cat (Op_cat C) x y)
    (@omega_equiv_right_inv (Op_cat C) y x (@omega_equiv_op C x y e))
  ≡ @id (Hom_cat (Op_cat C) x y)
    (@omega_equiv_left_inv C x y e);

assert [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y)) ⊢
  @id
    (Path_cat
      (OmegaEquiv
        (Hom_cat C y y)
        (@comp_fapp0 C y x y
          (@omega_equiv_to C x y e)
          (@omega_equiv_right_inv C x y e))
        (@id C y)))
    (@omega_equiv_left_cell (Op_cat C) y x (@omega_equiv_op C x y e))
  ≡ @id
    (Path_cat
      (OmegaEquiv
        (Hom_cat C y y)
        (@comp_fapp0 C y x y
          (@omega_equiv_to C x y e)
          (@omega_equiv_right_inv C x y e))
        (@id C y)))
    (@omega_equiv_right_cell C x y e);

assert [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y)) ⊢
  @id
    (Path_cat
      (OmegaEquiv
        (Hom_cat C x x)
        (@comp_fapp0 C x y x
          (@omega_equiv_left_inv C x y e)
          (@omega_equiv_to C x y e))
        (@id C x)))
    (@omega_equiv_right_cell (Op_cat C) y x (@omega_equiv_op C x y e))
  ≡ @id
    (Path_cat
      (OmegaEquiv
        (Hom_cat C x x)
        (@comp_fapp0 C x y x
          (@omega_equiv_left_inv C x y e)
          (@omega_equiv_to C x y e))
        (@id C x)))
    (@omega_equiv_left_cell C x y e);

assert [C : Cat] (x : τ (Obj C)) ⊢
  @omega_equiv_op C x x (@omega_equiv_refl C x)
  ≡ @omega_equiv_refl (Op_cat C) x;

assert [C : Cat] (x : τ (Obj C)) ⊢
  omega_equiv_to (@omega_equiv_op C x x (@omega_equiv_refl C x))
  ≡ @id (Op_cat C) x;

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
  (iA : τ (IsoEvidence A x0 x1))
  (iB : τ (IsoEvidence B y0 y1)) ⊢
  sigma_Fst
    (@iso_evidence_path
      (Product_cat A B)
      (Struct_sigma x0 y0)
      (Struct_sigma x1 y1)
      (@iso_evidence_product A B x0 x1 y0 y1 iA iB))
  ≡ @iso_evidence_path A x0 x1 iA;

assert [A B : Cat]
  [x0 x1 : τ (Obj A)]
  [y0 y1 : τ (Obj B)]
  (iA : τ (IsoEvidence A x0 x1))
  (iB : τ (IsoEvidence B y0 y1)) ⊢
  sigma_Snd
    (@iso_evidence_path
      (Product_cat A B)
      (Struct_sigma x0 y0)
      (Struct_sigma x1 y1)
      (@iso_evidence_product A B x0 x1 y0 y1 iA iB))
  ≡ @const_pathover
      (Obj A)
      (Obj B)
      x0
      x1
      y0
      y1
      (@iso_evidence_path A x0 x1 iA)
      (@iso_evidence_path B y0 y1 iB);

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

assert [A B : Cat]
  [x0 x1 : τ (Obj A)]
  [y0 y1 : τ (Obj B)]
  (eA : τ (OmegaEquiv A x0 x1))
  (eB : τ (OmegaEquiv B y0 y1)) ⊢
  @omega_equiv_product A B x0 x1 y0 y1 eA eB
  : τ (OmegaEquiv
      (Product_cat A B)
      (Struct_sigma x0 y0)
      (Struct_sigma x1 y1));

assert [A B : Cat]
  [x0 x1 : τ (Obj A)]
  [y0 y1 : τ (Obj B)]
  (eA : τ (OmegaEquiv A x0 x1))
  (eB : τ (OmegaEquiv B y0 y1)) ⊢
  sigma_Fst
    (@omega_equiv_to
      (Product_cat A B)
      (Struct_sigma x0 y0)
      (Struct_sigma x1 y1)
      (@omega_equiv_product A B x0 x1 y0 y1 eA eB))
  ≡ @omega_equiv_to A x0 x1 eA;

assert [A B : Cat]
  [x0 x1 : τ (Obj A)]
  [y0 y1 : τ (Obj B)]
  (eA : τ (OmegaEquiv A x0 x1))
  (eB : τ (OmegaEquiv B y0 y1)) ⊢
  sigma_Snd
    (@omega_equiv_to
      (Product_cat A B)
      (Struct_sigma x0 y0)
      (Struct_sigma x1 y1)
      (@omega_equiv_product A B x0 x1 y0 y1 eA eB))
  ≡ @omega_equiv_to B y0 y1 eB;

assert [A B : Cat]
  [x0 x1 : τ (Obj A)]
  [y0 y1 : τ (Obj B)]
  (eA : τ (OmegaEquiv A x0 x1))
  (eB : τ (OmegaEquiv B y0 y1)) ⊢
  sigma_Fst
    (@omega_equiv_left_inv
      (Product_cat A B)
      (Struct_sigma x0 y0)
      (Struct_sigma x1 y1)
      (@omega_equiv_product A B x0 x1 y0 y1 eA eB))
  ≡ @omega_equiv_left_inv A x0 x1 eA;

assert [A B : Cat]
  [x0 x1 : τ (Obj A)]
  [y0 y1 : τ (Obj B)]
  (eA : τ (OmegaEquiv A x0 x1))
  (eB : τ (OmegaEquiv B y0 y1)) ⊢
  sigma_Snd
    (@omega_equiv_right_inv
      (Product_cat A B)
      (Struct_sigma x0 y0)
      (Struct_sigma x1 y1)
    (@omega_equiv_product A B x0 x1 y0 y1 eA eB))
  ≡ @omega_equiv_right_inv B y0 y1 eB;

assert [A B : Cat]
  [x0 x1 : τ (Obj A)]
  [y0 y1 : τ (Obj B)]
  (eA : τ (OmegaEquiv A x0 x1))
  (eB : τ (OmegaEquiv B y0 y1)) ⊢
  sigma_Fst
    (@omega_equiv_path
      (Product_cat A B)
      (Struct_sigma x0 y0)
      (Struct_sigma x1 y1)
      (@omega_equiv_product A B x0 x1 y0 y1 eA eB))
  ≡ @omega_equiv_path A x0 x1 eA;

assert [A B : Cat]
  [x0 x1 : τ (Obj A)]
  [y0 y1 : τ (Obj B)]
  (eA : τ (OmegaEquiv A x0 x1))
  (eB : τ (OmegaEquiv B y0 y1)) ⊢
  sigma_Snd
    (@omega_equiv_path
      (Product_cat A B)
      (Struct_sigma x0 y0)
      (Struct_sigma x1 y1)
      (@omega_equiv_product A B x0 x1 y0 y1 eA eB))
  ≡ @const_pathover
      (Obj A)
      (Obj B)
      x0
      x1
      y0
      y1
      (@omega_equiv_path A x0 x1 eA)
      (@omega_equiv_path B y0 y1 eB);

assert [A B : Cat]
  [x0 x1 : τ (Obj A)]
  [y0 y1 : τ (Obj B)]
  (pA : τ (x0 = x1))
  (pB : τ (@PathOver (Obj A) (λ _ : τ (Obj A), Obj B) x0 x1 pA y0 y1)) ⊢
  @idtoequiv_cat
    (Product_cat A B)
    (Struct_sigma x0 y0)
    (Struct_sigma x1 y1)
    (@Struct_sigma
      (@= (Obj A) x0 x1)
      (λ p : τ (@= (Obj A) x0 x1),
        @PathOver (Obj A) (λ _ : τ (Obj A), Obj B) x0 x1 p y0 y1)
      pA
      pB)
  ≡ @omega_equiv_product
      A
      B
      x0
      x1
      y0
      y1
      (@idtoequiv_cat A x0 x1 pA)
      (@idtoequiv_cat
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
  @idtoequiv_cat
    (Product_cat A B)
    (Struct_sigma x y)
    (Struct_sigma x y)
    (@Struct_sigma
      (@= (Obj A) x x)
      (λ p : τ (@= (Obj A) x x),
        @PathOver (Obj A) (λ _ : τ (Obj A), Obj B) x x p y y)
      (eq_refl x)
      (@pathover_refl (Obj A) (λ _ : τ (Obj A), Obj B) x y))
  ≡ @omega_equiv_product
      A B x x y y
      (@omega_equiv_refl A x)
      (@omega_equiv_refl B y);

assertnot [A B : Cat]
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  @omega_equiv_product
    A
    B
    x
    x
    y
    y
    (@omega_equiv_refl A x)
    (@omega_equiv_refl B y)
  ≡ @omega_equiv_refl
      (Product_cat A B)
      (Struct_sigma x y);

// catalog-area: auto

assert [A B : Cat]
  [x0 x1 : τ (Obj A)]
  [y0 y1 : τ (Obj B)]
  (eA : τ (OmegaEquiv A x0 x1))
  (eB : τ (OmegaEquiv B y0 y1)) ⊢
  @omega_equiv_left_cell
    (Product_cat A B)
    (Struct_sigma x0 y0)
    (Struct_sigma x1 y1)
    (@omega_equiv_product A B x0 x1 y0 y1 eA eB)
  ≡ @omega_equiv_product
      (Hom_cat A x0 x0)
      (Hom_cat B y0 y0)
      (@comp_fapp0
        A
        x0
        x1
        x0
        (@omega_equiv_left_inv A x0 x1 eA)
        (@omega_equiv_to A x0 x1 eA))
      (@id A x0)
      (@comp_fapp0
        B
        y0
        y1
        y0
        (@omega_equiv_left_inv B y0 y1 eB)
        (@omega_equiv_to B y0 y1 eB))
      (@id B y0)
      (@omega_equiv_left_cell A x0 x1 eA)
      (@omega_equiv_left_cell B y0 y1 eB);

assert [A B : Cat]
  [x0 x1 : τ (Obj A)]
  [y0 y1 : τ (Obj B)]
  (eA : τ (OmegaEquiv A x0 x1))
  (eB : τ (OmegaEquiv B y0 y1)) ⊢
  @omega_equiv_right_cell
    (Product_cat A B)
    (Struct_sigma x0 y0)
    (Struct_sigma x1 y1)
    (@omega_equiv_product A B x0 x1 y0 y1 eA eB)
  ≡ @omega_equiv_product
      (Hom_cat A x1 x1)
      (Hom_cat B y1 y1)
      (@comp_fapp0
        A
        x1
        x0
        x1
        (@omega_equiv_to A x0 x1 eA)
        (@omega_equiv_right_inv A x0 x1 eA))
      (@id A x1)
      (@comp_fapp0
        B
        y1
        y0
        y1
        (@omega_equiv_to B y0 y1 eB)
        (@omega_equiv_right_inv B y0 y1 eB))
      (@id B y1)
      (@omega_equiv_right_cell A x0 x1 eA)
      (@omega_equiv_right_cell B y0 y1 eB);

assert [C : Cat] (x : τ (Obj C)) ⊢
  @idtoequiv_cat C x x (eq_refl x)
  ≡ @omega_equiv_refl C x;

assert [C : Cat] (x : τ (Obj C)) ⊢
  @omega_equiv_path C x x (@omega_equiv_refl C x)
  ≡ @eq_refl (Obj C) x;

assert [C : Cat] (x : τ (Obj C)) ⊢
  omega_equiv_to (@idtoequiv_cat C x x (eq_refl x))
  ≡ @id C x;

assert [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y)) ⊢
  @equivtoid_cat C (cat_univalence C) x y e
  : τ (x = y);

assert ⊢
  cat_univalence Cat_cat
  : τ (CatUnivalence Cat_cat);

assert ⊢
  cat_univalence_by_decoder Cat_cat
  : τ (CatUnivalenceByDecoder Cat_cat);

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

// catalog-area: Registered observational path action
assert [A B : Grpd]
  (f : τ A → τ B) ⊢
  @ObsAction A B f
  ≡ @Σ_ (@ObsActionMap A B f)
      (λ act : τ (@ObsActionMap A B f),
        @ObsActionCoherence A B f act);

assert [A B : Grpd]
  [f : τ A → τ B]
  (act : τ (@ObsActionMap A B f))
  (coherence : τ (@ObsActionCoherence A B f act)) ⊢
  @obs_action_intro A B f act coherence
  : τ (@ObsAction A B f);

assert [A B : Grpd]
  [f : τ A → τ B]
  (act : τ (@ObsActionMap A B f))
  (coherence : τ (@ObsActionCoherence A B f act)) ⊢
  @obs_action_map A B f (@obs_action_intro A B f act coherence)
  ≡ act;

assert [A B : Grpd]
  [f : τ A → τ B]
  (act : τ (@ObsActionMap A B f))
  (coherence : τ (@ObsActionCoherence A B f act))
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @obs_action_apply A B f
    (@obs_action_intro A B f act coherence) x y p
  ≡ act x y p;

assert [A B : Grpd]
  [f : τ A → τ B]
  (act : τ (@ObsActionMap A B f))
  (coherence : τ (@ObsActionCoherence A B f act))
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @obs_action_agrees A B f
    (@obs_action_intro A B f act coherence) x y p
  ≡ coherence x y p;

assert [A B : Grpd]
  (f : τ A → τ B)
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @obs_action_apply A B f (@obs_action_from_function A B f) x y p
  ≡ @eq_ap A B f x y p;

assert [A B : Grpd]
  (f : τ A → τ B)
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @obs_action_agrees A B f (@obs_action_from_function A B f) x y p
  ≡ @eq_refl
      (@= B (f x) (f y))
      (@eq_ap A B f x y p);

assert [A : Grpd]
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @eq_ap_id A x y p
  : τ (@= (@= A x y)
      p
      (@eq_ap A A (λ z : τ A, z) x y p));

assert [A : Grpd]
  (x : τ A) ⊢
  @eq_ap_id A x x (@eq_refl A x)
  ≡ @eq_refl (@= A x x) (@eq_refl A x);

assert [A : Grpd] ⊢
  @obs_action_id A
  : τ (@ObsAction A A (λ z : τ A, z));

assert [A : Grpd]
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @obs_action_apply A A (λ z : τ A, z)
    (@obs_action_id A) x y p
  ≡ p;

assert [A B C : Grpd]
  (f : τ A → τ B)
  (g : τ B → τ C)
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @eq_ap_comp A B C f g x y p
  : τ (@= (@= C (g (f x)) (g (f y)))
      (@eq_ap B C g (f x) (f y) (@eq_ap A B f x y p))
      (@eq_ap A C (λ z : τ A, g (f z)) x y p));

assert [A B C : Grpd]
  (f : τ A → τ B)
  (g : τ B → τ C)
  (x : τ A) ⊢
  @eq_ap_comp A B C f g x x (@eq_refl A x)
  ≡ @eq_refl
      (@= C (g (f x)) (g (f x)))
      (@eq_refl C (g (f x)));

assert [A B C : Grpd]
  [f : τ A → τ B]
  [g : τ B → τ C]
  (u : τ (@ObsAction A B f))
  (v : τ (@ObsAction B C g)) ⊢
  @obs_action_comp A B C f g u v
  : τ (@ObsAction A C (λ z : τ A, g (f z)));

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

assert [A : Grpd]
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @obs_action_apply
    A A (λ z : τ A, z)
    (@obs_action_comp
      A A A
      (λ z : τ A, z)
      (λ z : τ A, z)
      (@obs_action_id A)
      (@obs_action_id A))
    x y p
  ≡ p;

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
  (s : Π x : τ A, τ (P x)) ⊢
  @ObsDAction A P s
  ≡ @Σ_ (@ObsDActionMap A P s)
      (λ act : τ (@ObsDActionMap A P s),
        @ObsDActionCoherence A P s act);

assert [A : Grpd]
  [P : τ A → Grpd]
  [s : Π x : τ A, τ (P x)]
  (act : τ (@ObsDActionMap A P s))
  (coherence : τ (@ObsDActionCoherence A P s act)) ⊢
  @obs_daction_intro A P s act coherence
  : τ (@ObsDAction A P s);

assert [A : Grpd]
  [P : τ A → Grpd]
  [s : Π x : τ A, τ (P x)]
  (act : τ (@ObsDActionMap A P s))
  (coherence : τ (@ObsDActionCoherence A P s act))
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @obs_daction_apply A P s
    (@obs_daction_intro A P s act coherence) x y p
  ≡ act x y p;

assert [A : Grpd]
  [P : τ A → Grpd]
  [s : Π x : τ A, τ (P x)]
  (act : τ (@ObsDActionMap A P s))
  (coherence : τ (@ObsDActionCoherence A P s act))
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @obs_daction_agrees A P s
    (@obs_daction_intro A P s act coherence) x y p
  ≡ coherence x y p;

assert [A : Grpd]
  [P : τ A → Grpd]
  (s : Π x : τ A, τ (P x))
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @obs_daction_apply A P s (@obs_daction_from_section A P s) x y p
  ≡ @eq_apd A P s x y p;

assert [A : Grpd]
  [P : τ A → Grpd]
  (s : Π x : τ A, τ (P x))
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @obs_daction_agrees A P s (@obs_daction_from_section A P s) x y p
  ≡ @eq_refl
      (@PathOver A P x y p (s x) (s y))
      (@eq_apd A P s x y p);

assert [A B : Grpd]
  [f : τ (PathRecord_grpd A) → τ (PathRecord_grpd B)]
  (u : τ (@ObsAction (PathRecord_grpd A) (PathRecord_grpd B) f))
  [r s : τ (PathRecord_grpd A)]
  (p : τ (@PathRecordPathView A r s)) ⊢
  @path_record_action A B f u r s p
  : τ (@PathRecordPathView B (f r) (f s));

assert [A B : Grpd]
  (f : τ (PathRecord_grpd A) → τ (PathRecord_grpd B))
  [r s : τ (PathRecord_grpd A)]
  (p : τ (@PathRecordPathView A r s)) ⊢
  @path_record_action A B f
    (@obs_action_from_function (PathRecord_grpd A) (PathRecord_grpd B) f)
    r s p
  ≡ @eq_ap
      (PathRecord_grpd A)
      (PathRecord_grpd B)
      f r s p;

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

assert [A : Grpd] ⊢
  @path_record_witness_daction A
  : τ (@ObsDAction
      (PathRecord_grpd A)
      (λ r : τ (PathRecord_grpd A),
        @= A (path_record_src r) (path_record_dst r))
      (λ r : τ (PathRecord_grpd A), path_record_witness r));

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

// Agreement is propositional data, not runtime equality for arbitrary packages.
assertnot [A B : Grpd]
  [f : τ A → τ B]
  (u : τ (@ObsAction A B f))
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @obs_action_apply A B f u x y p
  ≡ @eq_ap A B f x y p;

assertnot [A : Grpd]
  [P : τ A → Grpd]
  [s : Π x : τ A, τ (P x)]
  (u : τ (@ObsDAction A P s))
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @obs_daction_apply A P s u x y p
  ≡ @eq_apd A P s x y p;

// Registered action packages retain their coherence evidence and have no eta.
assertnot [A B : Grpd]
  [f : τ A → τ B]
  (u : τ (@ObsAction A B f)) ⊢
  u
  ≡ @obs_action_intro A B f
      (@obs_action_map A B f u)
      (sigma_Snd u);

// An arbitrary selected loop action does not collapse to shaped reflexivity.
assertnot [A B : Grpd]
  [f : τ (PathRecord_grpd A) → τ (PathRecord_grpd B)]
  (u : τ (@ObsAction (PathRecord_grpd A) (PathRecord_grpd B) f))
  (r : τ (PathRecord_grpd A))
  (p : τ (@PathRecordPathView A r r)) ⊢
  @path_record_action A B f u r r p
  ≡ @PathRecordPathRefl B (f r);

// Action data alone does not grant arbitrary-constructor dependent-J beta.
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

assert [A : Cat] ⊢
  @omega_equiv_along_obj_path
    A A (@id_func A) (@omega_equiv_along_refl_D0 Cat_cat A)
  ≡ @eq_refl Grpd_grpd (Obj A);

assert [A : Cat] ⊢
  @omega_equiv_along_obj_type_equiv
    A A (@id_func A) (@omega_equiv_along_refl_D0 Cat_cat A)
  ≡ @type_equiv_refl (Obj A);

assert (n : TruncLevel)
  [A : Cat] ⊢
  @is_obj_trunc_cat_equiv_type_equiv
    n A A (@id_func A) (@omega_equiv_along_refl_D0 Cat_cat A)
  ≡ @type_equiv_refl (IsObjTruncCat n A);

assert (n : TruncLevel)
  [A : Cat]
  (h : τ (IsObjTruncCat n A)) ⊢
  @is_obj_trunc_cat_equiv_to
    n A A (@id_func A) (@omega_equiv_along_refl_D0 Cat_cat A) h
  ≡ h;

assert (n : TruncLevel)
  [A : Cat]
  (h : τ (IsObjTruncCat n A)) ⊢
  @is_obj_trunc_cat_equiv_from
    n A A (@id_func A) (@omega_equiv_along_refl_D0 Cat_cat A) h
  ≡ h;

assert (n : TruncLevel)
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (h : τ (IsObjTruncCat n B)) ⊢
  type_equiv_right (@is_obj_trunc_cat_equiv_type_equiv n A B F u) h
  : τ (
      @is_obj_trunc_cat_equiv_to n A B F u
        (@is_obj_trunc_cat_equiv_from n A B F u h)
      = h);

assert (n : TruncLevel)
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (h : τ (IsObjTruncCat n A)) ⊢
  type_equiv_left (@is_obj_trunc_cat_equiv_type_equiv n A B F u) h
  : τ (
      @is_obj_trunc_cat_equiv_from n A B F u
        (@is_obj_trunc_cat_equiv_to n A B F u h)
      = h);

// Decoder-induced object equivalence does not runtime expose the functor map.
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
  ≡ @SigmaPathView A (λ _ : τ A, B) p q;

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

// catalog-area: Categorical-universe direct identity

// Public category-universe equality has the finite fixed-map package normal form.
assert [A B : Cat] ⊢
  @= (Obj Cat_cat) A B
  ≡ @CatPathView A B;

assert [A B : Cat] ⊢
  @CatPathView A B
  ≡ OmegaEquiv Cat_cat A B;

assert [A B : Cat]
  (e : τ (@CatPathView A B)) ⊢
  e
  : τ (@= (Obj Cat_cat) A B);

assert [A B : Cat]
  (p : τ (@= (Obj Cat_cat) A B)) ⊢
  @cat_path_functor A B p
  : τ (Functor A B);

// Canonical package reflexivity is usable as equality but remains distinct
// from the generic proof normal form required by literal J/eq_ap beta.
assert [A : Cat] ⊢
  @cat_path_refl A
  ≡ @omega_equiv_refl Cat_cat A;

assert [A : Cat] ⊢
  @cat_path_refl A
  : τ (@= (Obj Cat_cat) A A);

assert [A : Cat] ⊢
  @eq_refl (Obj Cat_cat) A
  : τ (@CatPathView A A);

assert [A : Cat] ⊢
  @cat_path_functor A A (@cat_path_refl A)
  ≡ @id_func A;

assert [A : Cat] ⊢
  @cat_path_evidence A A (@cat_path_refl A)
  ≡ @omega_equiv_along_refl_D0 Cat_cat A;

// The existing encoder/decoder own both directions and reflexive computation.
assert [A : Cat] ⊢
  @cat_path_encode A A (@eq_refl (Obj Cat_cat) A)
  ≡ @cat_path_refl A;

assert [A : Cat] ⊢
  @cat_path_decode A A (@cat_path_refl A)
  ≡ @eq_refl (Obj Cat_cat) A;

assert [A B : Cat]
  (p : τ (@= (Obj Cat_cat) A B)) ⊢
  @cat_path_decode_encode A B p
  : τ (
      @cat_path_decode A B (@cat_path_encode A B p)
      = p);

assert [A B : Cat]
  (e : τ (@CatPathView A B)) ⊢
  @cat_path_encode_decode A B e
  : τ (
      @cat_path_encode A B (@cat_path_decode A B e)
      = e);

assert [A B : Cat]
  (p : τ (@= (Obj Cat_cat) A B)) ⊢
  @cat_path_encode_functor A B p
  : τ (
      @cat_path_functor A B (@cat_path_encode A B p)
      = @path_to_hom Cat_cat A B p);

assert [A : Cat] ⊢
  @cat_path_encode_functor
    A A (@eq_refl (Obj Cat_cat) A)
  ≡ @eq_refl (Obj (Functor_cat A A)) (@id_func A);

// Product action decodes, applies generic action, and re-encodes exactly once.
assert [A B : Cat] ⊢
  @cat_path_product
    A A B B (@cat_path_refl A) (@cat_path_refl B)
  ≡ @cat_path_refl (Product_cat A B);

assert [A B : Cat] ⊢
  @cat_path_functor
    (Product_cat A B)
    (Product_cat A B)
    (@cat_path_product
      A A B B (@cat_path_refl A) (@cat_path_refl B))
  ≡ @id_func (Product_cat A B);

// Direct fixed-map evidence remains iterable at the next hom level.
assert [A B : Cat]
  (e : τ (@CatPathView A B))
  (x y : τ (Obj A)) ⊢
  @cat_path_fapp1_along A B e x y
  : τ (@OmegaEquivAlong
      Cat_cat
      (Hom_cat A x y)
      (Hom_cat B
        (@fapp0 A B (cat_path_functor e) x)
        (@fapp0 A B (cat_path_functor e) y))
      (@fapp1_func A B (cat_path_functor e) x y));

assert [A B : Cat]
  (e : τ (@CatPathView A B))
  (x y : τ (Obj A)) ⊢
  @cat_path_fapp1 A B e x y
  : τ (OmegaEquiv
      Cat_cat
      (Hom_cat A x y)
      (Hom_cat B
        (@fapp0 A B (cat_path_functor e) x)
        (@fapp0 A B (cat_path_functor e) y)));

assert [A : Cat]
  (x y : τ (Obj A)) ⊢
  @omega_equiv_to
    Cat_cat
    (Hom_cat A x y)
    (Hom_cat A x y)
    (@cat_path_fapp1 A A (@cat_path_refl A) x y)
  ≡ @id_func (Hom_cat A x y);

// The unstratified self-universe normal form is finite at the opaque-evidence boundary.
assert ⊢
  @cat_path_refl Cat_cat
  : τ (@CatPathView Cat_cat Cat_cat);

// Literal reflexivity keeps the guarded generic-J beta.
assert [A : Cat] ⊢
  @ind_eqr
    (Obj Cat_cat)
    A
    (λ X : Cat, λ _ : τ (@= (Obj Cat_cat) X A), Unit_grpd)
    tt
    A
    (@eq_refl (Obj Cat_cat) A)
  ≡ tt;

// Provenance/runtime boundaries selected by the direct classifier-only rule.
assertnot [A : Cat] ⊢
  @eq_refl (Obj Cat_cat) A
  ≡ @cat_path_refl A;

assertnot [A : Cat] ⊢
  @omega_equiv_to
    Cat_cat A A (@eq_refl (Obj Cat_cat) A)
  ≡ @id_func A;

assertnot [A B : Cat]
  (p : τ (@= (Obj Cat_cat) A B)) ⊢
  @cat_path_decode A B (@cat_path_encode A B p)
  ≡ p;

assertnot [A B : Cat]
  (e : τ (@CatPathView A B)) ⊢
  @cat_path_encode A B (@cat_path_decode A B e)
  ≡ e;

assertnot [A B : Cat]
  (p : τ (@= (Obj Cat_cat) A B)) ⊢
  @cat_path_encode A B p
  ≡ p;

assertnot [A B : Cat]
  (e : τ (@CatPathView A B)) ⊢
  @cat_path_decode A B e
  ≡ e;

assertnot [A : Cat] ⊢
  @ind_eqr
    (Obj Cat_cat)
    A
    (λ X : Cat, λ _ : τ (@= (Obj Cat_cat) X A), Unit_grpd)
    tt
    A
    (@cat_path_refl A)
  ≡ tt;

assertnot [A : Cat]
  (x y : τ (Obj A)) ⊢
  @cat_path_fapp1 A A (@cat_path_refl A) x y
  ≡ @omega_equiv_refl Cat_cat (Hom_cat A x y);

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
