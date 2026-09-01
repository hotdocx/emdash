/*
  Concatenation and splitting of Nat-indexed finite families.

  `FiniteFamily(A,n)` and `nat_add(m,n)` both recurse from the left. This
  module therefore defines transparent append, left-prefix, and left-drop
  operations with the expected constructor computation. The inverse and
  empty-right laws are theorem-level Nat inductions; no rewrite or unification
  rule and no second list/Fin representation is introduced.
*/

require open emdash.emdash3_2_finite_families;

// Concatenation `A^m × A^n -> A^(m+n)`, recursively owned by `m`.
symbol finite_family_append
  [A : Grpd]
  (m n : τ Nat_grpd)
  (xs : τ (@FiniteFamily A m))
  (ys : τ (@FiniteFamily A n))
  : τ (@FiniteFamily A (@nat_add m n))
≔ (@nat_elim
    (λ m0 : τ Nat_grpd,
      @Function_grpd
        (@FiniteFamily A m0)
        (@Function_grpd
          (@FiniteFamily A n)
          (@FiniteFamily A (@nat_add m0 n))))
    (λ _ : τ (@FiniteFamily A zero),
      λ ys0 : τ (@FiniteFamily A n), ys0)
    (λ m0 : τ Nat_grpd,
      λ rec : τ (@Function_grpd
        (@FiniteFamily A m0)
        (@Function_grpd
          (@FiniteFamily A n)
          (@FiniteFamily A (@nat_add m0 n)))),
      λ xs0 : τ (@FiniteFamily A (succ m0)),
      λ ys0 : τ (@FiniteFamily A n),
        @finite_family_cons
          A (@nat_add m0 n)
          (@finite_family_head A m0 xs0)
          (rec (@finite_family_tail A m0 xs0) ys0))
    m) xs ys;

// Recover the first `m` entries of a family of length `m+n`.
symbol finite_family_take_left
  [A : Grpd]
  (m n : τ Nat_grpd)
  (zs : τ (@FiniteFamily A (@nat_add m n)))
  : τ (@FiniteFamily A m)
≔ (@nat_elim
    (λ m0 : τ Nat_grpd,
      @Function_grpd
        (@FiniteFamily A (@nat_add m0 n))
        (@FiniteFamily A m0))
    (λ _ : τ (@FiniteFamily A n), @finite_family_nil A)
    (λ m0 : τ Nat_grpd,
      λ rec : τ (@Function_grpd
        (@FiniteFamily A (@nat_add m0 n))
        (@FiniteFamily A m0)),
      λ zs0 : τ (@FiniteFamily A (@nat_add (succ m0) n)),
        @finite_family_cons
          A m0
          (@finite_family_head A (@nat_add m0 n) zs0)
          (rec (@finite_family_tail A (@nat_add m0 n) zs0)))
    m) zs;

// Drop the first `m` entries of a family of length `m+n`.
symbol finite_family_drop_left
  [A : Grpd]
  (m n : τ Nat_grpd)
  (zs : τ (@FiniteFamily A (@nat_add m n)))
  : τ (@FiniteFamily A n)
≔ (@nat_elim
    (λ m0 : τ Nat_grpd,
      @Function_grpd
        (@FiniteFamily A (@nat_add m0 n))
        (@FiniteFamily A n))
    (λ zs0 : τ (@FiniteFamily A n), zs0)
    (λ m0 : τ Nat_grpd,
      λ rec : τ (@Function_grpd
        (@FiniteFamily A (@nat_add m0 n))
        (@FiniteFamily A n)),
      λ zs0 : τ (@FiniteFamily A (@nat_add (succ m0) n)),
        rec (@finite_family_tail A (@nat_add m0 n) zs0))
    m) zs;

// Taking the left block after append recovers the first family.
symbol finite_family_take_append_path
  [A : Grpd]
  (m n : τ Nat_grpd)
  (xs : τ (@FiniteFamily A m))
  (ys : τ (@FiniteFamily A n))
  : τ (@= (@FiniteFamily A m)
      (@finite_family_take_left A m n
        (@finite_family_append A m n xs ys))
      xs)
≔ (@nat_elim
    (λ m0 : τ Nat_grpd,
      @Pi_grpd (@FiniteFamily A m0)
        (λ xs0 : τ (@FiniteFamily A m0),
          @Pi_grpd (@FiniteFamily A n)
            (λ ys0 : τ (@FiniteFamily A n),
              @= (@FiniteFamily A m0)
                (@finite_family_take_left A m0 n
                  (@finite_family_append A m0 n xs0 ys0))
                xs0)))
    (λ xs0 : τ (@FiniteFamily A zero),
      λ _ : τ (@FiniteFamily A n),
        (sigma_Snd unit_is_contr) xs0)
    (λ m0 : τ Nat_grpd,
      λ ih : Π xs0 : τ (@FiniteFamily A m0),
        Π ys0 : τ (@FiniteFamily A n),
          τ (@= (@FiniteFamily A m0)
            (@finite_family_take_left A m0 n
              (@finite_family_append A m0 n xs0 ys0))
            xs0),
      λ xs0 : τ (@FiniteFamily A (succ m0)),
      λ ys0 : τ (@FiniteFamily A n),
        @eq_ap
          (@FiniteFamily A m0)
          (@FiniteFamily A (succ m0))
          (λ tail : τ (@FiniteFamily A m0),
            @finite_family_cons A m0
              (@finite_family_head A m0 xs0) tail)
          (@finite_family_take_left A m0 n
            (@finite_family_append A m0 n
              (@finite_family_tail A m0 xs0) ys0))
          (@finite_family_tail A m0 xs0)
          (ih (@finite_family_tail A m0 xs0) ys0))
    m) xs ys;

// Dropping the left block after append recovers the second family.
symbol finite_family_drop_append_path
  [A : Grpd]
  (m n : τ Nat_grpd)
  (xs : τ (@FiniteFamily A m))
  (ys : τ (@FiniteFamily A n))
  : τ (@= (@FiniteFamily A n)
      (@finite_family_drop_left A m n
        (@finite_family_append A m n xs ys))
      ys)
≔ (@nat_elim
    (λ m0 : τ Nat_grpd,
      @Pi_grpd (@FiniteFamily A m0)
        (λ xs0 : τ (@FiniteFamily A m0),
          @Pi_grpd (@FiniteFamily A n)
            (λ ys0 : τ (@FiniteFamily A n),
              @= (@FiniteFamily A n)
                (@finite_family_drop_left A m0 n
                  (@finite_family_append A m0 n xs0 ys0))
                ys0)))
    (λ _ : τ (@FiniteFamily A zero),
      λ ys0 : τ (@FiniteFamily A n),
        @eq_refl (@FiniteFamily A n) ys0)
    (λ m0 : τ Nat_grpd,
      λ ih : Π xs0 : τ (@FiniteFamily A m0),
        Π ys0 : τ (@FiniteFamily A n),
          τ (@= (@FiniteFamily A n)
            (@finite_family_drop_left A m0 n
              (@finite_family_append A m0 n xs0 ys0))
            ys0),
      λ xs0 : τ (@FiniteFamily A (succ m0)),
      λ ys0 : τ (@FiniteFamily A n),
        ih (@finite_family_tail A m0 xs0) ys0)
    m) xs ys;

// Appending the two selected splits reconstructs the original family.
symbol finite_family_append_split_path
  [A : Grpd]
  (m n : τ Nat_grpd)
  (zs : τ (@FiniteFamily A (@nat_add m n)))
  : τ (@= (@FiniteFamily A (@nat_add m n))
      (@finite_family_append A m n
        (@finite_family_take_left A m n zs)
        (@finite_family_drop_left A m n zs))
      zs)
≔ (@nat_elim
    (λ m0 : τ Nat_grpd,
      @Pi_grpd (@FiniteFamily A (@nat_add m0 n))
        (λ zs0 : τ (@FiniteFamily A (@nat_add m0 n)),
          @= (@FiniteFamily A (@nat_add m0 n))
            (@finite_family_append A m0 n
              (@finite_family_take_left A m0 n zs0)
              (@finite_family_drop_left A m0 n zs0))
            zs0))
    (λ zs0 : τ (@FiniteFamily A n),
      @eq_refl (@FiniteFamily A n) zs0)
    (λ m0 : τ Nat_grpd,
      λ ih : Π zs0 : τ (@FiniteFamily A (@nat_add m0 n)),
        τ (@= (@FiniteFamily A (@nat_add m0 n))
          (@finite_family_append A m0 n
            (@finite_family_take_left A m0 n zs0)
            (@finite_family_drop_left A m0 n zs0))
          zs0),
      λ zs0 : τ (@FiniteFamily A (@nat_add (succ m0) n)),
        @eq_ap
          (@FiniteFamily A (@nat_add m0 n))
          (@FiniteFamily A (@nat_add (succ m0) n))
          (λ tail : τ (@FiniteFamily A (@nat_add m0 n)),
            @finite_family_cons A (@nat_add m0 n)
              (@finite_family_head A (@nat_add m0 n) zs0) tail)
          (@finite_family_append A m0 n
            (@finite_family_take_left A m0 n
              (@finite_family_tail A (@nat_add m0 n) zs0))
            (@finite_family_drop_left A m0 n
              (@finite_family_tail A (@nat_add m0 n) zs0)))
          (@finite_family_tail A (@nat_add m0 n) zs0)
          (ih (@finite_family_tail A (@nat_add m0 n) zs0)))
    m) zs;

// Appending the empty family on the right is propositionally the identity.
symbol finite_family_append_zero_right_path
  [A : Grpd]
  (m : τ Nat_grpd)
  (xs : τ (@FiniteFamily A m))
  : τ (@= (@FiniteFamily A m)
      (@finite_family_append A m zero xs (@finite_family_nil A))
      xs)
≔ (@nat_elim
    (λ m0 : τ Nat_grpd,
      @Pi_grpd (@FiniteFamily A m0)
        (λ xs0 : τ (@FiniteFamily A m0),
          @= (@FiniteFamily A m0)
            (@finite_family_append A m0 zero xs0
              (@finite_family_nil A))
            xs0))
    (λ xs0 : τ (@FiniteFamily A zero),
      (sigma_Snd unit_is_contr) xs0)
    (λ m0 : τ Nat_grpd,
      λ ih : Π xs0 : τ (@FiniteFamily A m0),
        τ (@= (@FiniteFamily A m0)
          (@finite_family_append A m0 zero xs0
            (@finite_family_nil A))
          xs0),
      λ xs0 : τ (@FiniteFamily A (succ m0)),
        @eq_ap
          (@FiniteFamily A m0)
          (@FiniteFamily A (succ m0))
          (λ tail : τ (@FiniteFamily A m0),
            @finite_family_cons A m0
              (@finite_family_head A m0 xs0) tail)
          (@finite_family_append A m0 zero
            (@finite_family_tail A m0 xs0) (@finite_family_nil A))
          (@finite_family_tail A m0 xs0)
          (ih (@finite_family_tail A m0 xs0)))
    m) xs;
