/*
  Boundary and horn sieves of the standard two-simplex.

  Three Boolean omission observations are computed structurally on raw
  skip/keep words and descend through the public set truncation by the active
  restricted recursor. Boundary membership asks that some target vertex is
  omitted; horn k membership asks that some vertex other than k is omitted.

  One kind-indexed whole higher-sieve owner packages the resulting
  proposition-valued fibres. Its generic Catd action owns restriction and
  naturality; the module adds only the fibre projection, not an external
  coherence record. Existing ordinary-sieve pullback, fibrewise extension,
  and whole inclusion owners supply the public sieve operations.

  This module is deliberately fixed at the three-vertex target. It does not
  claim a generic boundary/horn family, decidable equality for arbitrary
  simplex dimensions, degeneracies, a spine, a Kan condition, or fillers.
*/

require open emdash.emdash3_2_simplex_shapes;
require open emdash.emdash3_2_semisimplicial_diagrams;
require open emdash.emdash3_2_sieve_extensions;

// Two-variable Boolean elimination used to prove local Boolean sethood.
symbol simplex_bool_elim2
  (P : τ Bool_grpd → τ Bool_grpd → Grpd)
  (pff : τ (P false false))
  (pft : τ (P false true))
  (ptf : τ (P true false))
  (ptt : τ (P true true))
  (x y : τ Bool_grpd)
  : τ (P x y)
≔ (@bool_elim
      (λ x0 : τ Bool_grpd,
        @Pi_grpd Bool_grpd (λ y0 : τ Bool_grpd, P x0 y0))
      (λ y0 : τ Bool_grpd,
        @bool_elim
          (λ y1 : τ Bool_grpd, P false y1)
          pff pft y0)
      (λ y0 : τ Bool_grpd,
        @bool_elim
          (λ y1 : τ Bool_grpd, P true y1)
          ptf ptt y0)
      x) y;

symbol simplex_bool_is_set
  : τ (IsSetGrpd Bool_grpd)
≔ λ x : τ Bool_grpd,
    λ y : τ Bool_grpd,
      @simplex_bool_elim2
        (λ x0 : τ Bool_grpd,
          λ y0 : τ Bool_grpd,
            IsPropGrpd (@= Bool_grpd x0 y0))
        unit_is_prop empty_is_prop empty_is_prop unit_is_prop
        x y;

symbol simplex_bool_or
  (x y : τ Bool_grpd)
  : τ Bool_grpd
≔ @bool_elim
    (λ _ : τ Bool_grpd, Bool_grpd)
    y true x;

// Boolean truth as a literal Empty/Unit proposition classifier.
symbol simplex_bool_prop
  (b : τ Bool_grpd)
  : Grpd
≔ @bool_elim
    (λ _ : τ Bool_grpd, Grpd_grpd)
    Empty_grpd Unit_grpd b;

symbol simplex_bool_prop_is_prop
  (b : τ Bool_grpd)
  : τ (IsPropGrpd (@simplex_bool_prop b))
≔ @bool_elim
    (λ b0 : τ Bool_grpd,
      IsPropGrpd (@simplex_bool_prop b0))
    empty_is_prop unit_is_prop b;

// Does a raw code omit its final target vertex?
injective symbol raw_face_omits_last
  [p n : τ Nat_grpd]
  (f : τ (@RawFaceCode p (succ n)))
  : τ Bool_grpd;

rule @raw_face_omits_last _ _ (@raw_face_skip _ _ _)
  ↪ true
with @raw_face_omits_last _ _ (@raw_face_keep _ _ _)
  ↪ false;

// Omission of target vertex 1 in a three-vertex target.
injective symbol raw_face_omits_one_three
  [p : τ Nat_grpd]
  (f : τ (@RawFaceCode p (succ (succ (succ zero)))))
  : τ Bool_grpd;

rule @raw_face_omits_one_three _ (@raw_face_skip _ _ $f)
  ↪ @raw_face_omits_last _ _ $f
with @raw_face_omits_one_three _ (@raw_face_keep _ _ $f)
  ↪ @raw_face_omits_last _ _ $f;

// Helper for omission of target vertex 0 in a two-vertex target.
injective symbol raw_face_omits_zero_two
  [p : τ Nat_grpd]
  (f : τ (@RawFaceCode p (succ (succ zero))))
  : τ Bool_grpd;

rule @raw_face_omits_zero_two _ (@raw_face_skip _ _ $f)
  ↪ @raw_face_omits_last _ _ $f
with @raw_face_omits_zero_two _ (@raw_face_keep _ _ $f)
  ↪ @raw_face_omits_last _ _ $f;

// Omission of target vertex 0 in a three-vertex target.
injective symbol raw_face_omits_zero_three
  [p : τ Nat_grpd]
  (f : τ (@RawFaceCode p (succ (succ (succ zero)))))
  : τ Bool_grpd;

rule @raw_face_omits_zero_three _ (@raw_face_skip _ _ $f)
  ↪ @raw_face_omits_zero_two _ $f
with @raw_face_omits_zero_three _ (@raw_face_keep _ _ $f)
  ↪ @raw_face_omits_zero_two _ $f;

// Public omission bits, computed by recursion from visible raw points.
symbol face_omits_zero_three
  [p : τ Nat_grpd]
  (f : τ (@FaceCode p (succ (succ (succ zero)))))
  : τ Bool_grpd
≔ @trunc_rec_ambient
    trunc_zero
    (@RawFaceCode p (succ (succ (succ zero))))
    Bool_grpd
    simplex_bool_is_set
    (λ raw : τ (@RawFaceCode p (succ (succ (succ zero)))),
      @raw_face_omits_zero_three p raw)
    f;

symbol face_omits_one_three
  [p : τ Nat_grpd]
  (f : τ (@FaceCode p (succ (succ (succ zero)))))
  : τ Bool_grpd
≔ @trunc_rec_ambient
    trunc_zero
    (@RawFaceCode p (succ (succ (succ zero))))
    Bool_grpd
    simplex_bool_is_set
    (λ raw : τ (@RawFaceCode p (succ (succ (succ zero)))),
      @raw_face_omits_one_three p raw)
    f;

symbol face_omits_two_three
  [p : τ Nat_grpd]
  (f : τ (@FaceCode p (succ (succ (succ zero)))))
  : τ Bool_grpd
≔ @trunc_rec_ambient
    trunc_zero
    (@RawFaceCode p (succ (succ (succ zero))))
    Bool_grpd
    simplex_bool_is_set
    (λ raw : τ (@RawFaceCode p (succ (succ (succ zero)))),
      @raw_face_omits_last p (succ (succ zero)) raw)
    f;

// Boundary and the three horns form one finite kind-indexed family.
inductive Simplex2SieveKindData : TYPE ≔
| simplex2_boundary_kind : Simplex2SieveKindData
| simplex2_horn_zero_kind : Simplex2SieveKindData
| simplex2_horn_one_kind : Simplex2SieveKindData
| simplex2_horn_two_kind : Simplex2SieveKindData;

injective symbol Simplex2SieveKind : Grpd;

rule τ Simplex2SieveKind
  ↪ Simplex2SieveKindData;

injective symbol simplex2_member_bool
  (kind : τ Simplex2SieveKind)
  [p : τ Nat_grpd]
  (f : τ (@FaceCode p (succ (succ (succ zero)))))
  : τ Bool_grpd;

rule @simplex2_member_bool simplex2_boundary_kind _ $f
  ↪ @simplex_bool_or
      (@face_omits_zero_three _ $f)
      (@simplex_bool_or
        (@face_omits_one_three _ $f)
        (@face_omits_two_three _ $f))
with @simplex2_member_bool simplex2_horn_zero_kind _ $f
  ↪ @simplex_bool_or
      (@face_omits_one_three _ $f)
      (@face_omits_two_three _ $f)
with @simplex2_member_bool simplex2_horn_one_kind _ $f
  ↪ @simplex_bool_or
      (@face_omits_zero_three _ $f)
      (@face_omits_two_three _ $f)
with @simplex2_member_bool simplex2_horn_two_kind _ $f
  ↪ @simplex_bool_or
      (@face_omits_zero_three _ $f)
      (@face_omits_one_three _ $f);

symbol Simplex2SieveMember
  (kind : τ Simplex2SieveKind)
  [p : τ Nat_grpd]
  (f : τ (@FaceCode p (succ (succ (succ zero)))))
  : Grpd
≔ @simplex_bool_prop (@simplex2_member_bool kind p f);

symbol simplex2_sieve_member_is_prop
  (kind : τ Simplex2SieveKind)
  [p : τ Nat_grpd]
  (f : τ (@FaceCode p (succ (succ (succ zero)))))
  : τ (IsPropGrpd (@Simplex2SieveMember kind p f))
≔ @simplex_bool_prop_is_prop (@simplex2_member_bool kind p f);

/*
  One whole higher-sieve owner. The fibre rule exposes the selected
  proposition; generic fapp1/tapp action remains the unique naturality owner.
*/
injective symbol simplex2_higher_sieve
  (kind : τ Simplex2SieveKind)
  : τ (@HigherSieve
      SemiDeltaPlus_cat
      (succ (succ (succ zero))));

rule @fapp0 _ _ (@simplex2_higher_sieve $kind) $q
  ↪ Path_cat
      (@Simplex2SieveMember
        $kind
        (@into_restr_domain
          SemiDeltaPlus_cat (succ (succ (succ zero))) $q)
        (@into_restr_arrow
          SemiDeltaPlus_cat (succ (succ (succ zero))) $q));

symbol simplex2_ordinary_evidence
  (kind : τ Simplex2SieveKind)
  : τ (@IsOrdinarySieve
      SemiDeltaPlus_cat
      (succ (succ (succ zero)))
      (@simplex2_higher_sieve kind))
≔ λ q : τ (Obj (@Into_restr_cat
      SemiDeltaPlus_cat (succ (succ (succ zero))))),
    @path_cat_is_subterminal
      (@Simplex2SieveMember
        kind
        (@into_restr_domain
          SemiDeltaPlus_cat (succ (succ (succ zero))) q)
        (@into_restr_arrow
          SemiDeltaPlus_cat (succ (succ (succ zero))) q))
      (@simplex2_sieve_member_is_prop
        kind
        (@into_restr_domain
          SemiDeltaPlus_cat (succ (succ (succ zero))) q)
        (@into_restr_arrow
          SemiDeltaPlus_cat (succ (succ (succ zero))) q));

symbol simplex2_sieve
  (kind : τ Simplex2SieveKind)
  : τ (@Sieve
      SemiDeltaPlus_cat
      (succ (succ (succ zero))))
≔ @sieve_intro
    SemiDeltaPlus_cat
    (succ (succ (succ zero)))
    (@simplex2_higher_sieve kind)
    (@simplex2_ordinary_evidence kind);

// Readable boundary and horn sieve aliases.
symbol simplex2_boundary_sieve
  : τ (@Sieve
      SemiDeltaPlus_cat (succ (succ (succ zero))))
≔ @simplex2_sieve simplex2_boundary_kind;

symbol simplex2_horn_zero_sieve
  : τ (@Sieve
      SemiDeltaPlus_cat (succ (succ (succ zero))))
≔ @simplex2_sieve simplex2_horn_zero_kind;

symbol simplex2_horn_one_sieve
  : τ (@Sieve
      SemiDeltaPlus_cat (succ (succ (succ zero))))
≔ @simplex2_sieve simplex2_horn_one_kind;

symbol simplex2_horn_two_sieve
  : τ (@Sieve
      SemiDeltaPlus_cat (succ (succ (succ zero))))
≔ @simplex2_sieve simplex2_horn_two_kind;

// Generic pullback of any of the four selected sieves.
symbol simplex2_sieve_pullback
  (kind : τ Simplex2SieveKind)
  [q : τ Nat_grpd]
  (r : τ (@FaceCode q (succ (succ (succ zero)))))
  : τ (@Sieve SemiDeltaPlus_cat q)
≔ @sieve_pullback
    SemiDeltaPlus_cat q (succ (succ (succ zero))) r
    (@simplex2_sieve kind);

// Existing fibrewise extension and whole inclusion, specialized readably.
symbol simplex2_sieve_extension_psh
  (kind : τ Simplex2SieveKind)
  : τ (@Psh SemiDeltaPlus_cat)
≔ @ordinary_sieve_extension_psh
    SemiDeltaPlus_cat
    (succ (succ (succ zero)))
    (@simplex2_sieve kind);

symbol simplex2_sieve_inclusion
  (kind : τ Simplex2SieveKind)
  : τ (Hom
      (@Psh_cat SemiDeltaPlus_cat)
      (@simplex2_sieve_extension_psh kind)
      (@StandardSimplex (succ (succ (succ zero)))))
≔ @ordinary_sieve_extension_inclusion
    SemiDeltaPlus_cat
    (succ (succ (succ zero)))
    (@simplex2_sieve kind);
