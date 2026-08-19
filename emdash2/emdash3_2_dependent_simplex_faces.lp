/*
  Whole nonempty-face action for intrinsic dependent-simplex codes.

  A result packages the target dependent code together with a whole functor
  from the source decoded category. Raw face action recurses simultaneously on
  the flagged code and the existing skip/keep word:

    skip alpha       selects a face of the fixed flag (constant functor),
    keep (skip a)    selects the matching face of the target simplex,
    keep (keep a)    maps the outgoing path by the recursive face functor.

  The middle case is the mixed-variance step missing from a naive PathOut-map
  recursion: it precomposes the recursive target face with `Sigma_proj1_func`.
  Public action decodes the existing set-truncated `FaceCode`; no second face
  syntax or external simplicial equation family is introduced. The action is
  whole and retains generic hom action. Its direct/sequential composition
  comparison remains a normal-form question and receives no rewrite or
  proof-time unifier here.
*/

require open emdash.emdash3_2_dependent_simplex_code_map;

// Target dependent code and whole functor selected by one nonempty face.
symbol DependentSimplexFaceResult
  [C : Cat]
  (p : τ Nat_grpd)
  (K : Cat)
  : Grpd
≔ `Σ_ target : τ (@DependentSimplexCode C p),
    @Functor K (@dependent_simplex_code_decode_cat C p target);

symbol dependent_simplex_face_result
  [C : Cat]
  [p : τ Nat_grpd]
  [K : Cat]
  (target : τ (@DependentSimplexCode C p))
  (face : τ (Functor K
    (@dependent_simplex_code_decode_cat C p target)))
  : τ (@DependentSimplexFaceResult C p K)
≔ Struct_sigma target face;

// Structural face action at the intrinsically decoded raw category index.
injective symbol raw_dependent_simplex_face
  [C : Cat]
  [p n : τ Nat_grpd]
  [K : Cat]
  (c : τ (@RawDependentSimplexCode C n K))
  (alpha : τ (@RawFaceCode (succ p) (succ n)))
  : τ (@DependentSimplexFaceResult C p K);

// The unique face of a vertex is the identity whole functor.
rule @raw_dependent_simplex_face
      _ _ _ _
      (@raw_dependent_simplex_zero $C)
      (@raw_face_keep zero zero raw_face_nil)
  ↪ @dependent_simplex_face_result
      $C zero $C
      (@dependent_simplex_code_zero $C)
      (@id_func $C)

// Omitting the newest vertex selects a face of the fixed flag.
with @raw_dependent_simplex_face
      _ _ _ _
      (@raw_dependent_simplex_step $C $n $K $c $x)
      (@raw_face_skip (succ $p) (succ $n) $alpha)
  ↪ @dependent_simplex_face_result
      $C $p (@PathOut_cat $K $x)
      (sigma_Fst
        (@raw_dependent_simplex_face
          $C $p $n $K $c $alpha))
      (@Const_func
        (@PathOut_cat $K $x)
        (@dependent_simplex_code_decode_cat
          $C $p
          (sigma_Fst
            (@raw_dependent_simplex_face
              $C $p $n $K $c $alpha)))
        (@fapp0
          $K
          (@dependent_simplex_code_decode_cat
            $C $p
            (sigma_Fst
              (@raw_dependent_simplex_face
                $C $p $n $K $c $alpha)))
          (sigma_Snd
            (@raw_dependent_simplex_face
              $C $p $n $K $c $alpha))
          $x))

// Keeping the newest vertex after omitting its predecessor selects the same
// face of the target simplex, exposed by the PathOut first projection.
with @raw_dependent_simplex_face
      _ _ _ _
      (@raw_dependent_simplex_step $C $n $K $c $x)
      (@raw_face_keep $p (succ $n)
        (@raw_face_skip $p $n $alpha))
  ↪ @dependent_simplex_face_result
      $C $p (@PathOut_cat $K $x)
      (sigma_Fst
        (@raw_dependent_simplex_face
          $C $p $n $K $c
          (@raw_face_keep $p $n $alpha)))
      (@comp_cat_fapp0
        (@PathOut_cat $K $x)
        $K
        (@dependent_simplex_code_decode_cat
          $C $p
          (sigma_Fst
            (@raw_dependent_simplex_face
              $C $p $n $K $c
              (@raw_face_keep $p $n $alpha))))
        (sigma_Snd
          (@raw_dependent_simplex_face
            $C $p $n $K $c
            (@raw_face_keep $p $n $alpha)))
        (@Sigma_proj1_func $K (@Rep_catd $K $x)))

// Keeping both newest vertices maps the whole outgoing path by the recursively
// selected lower face functor.
with @raw_dependent_simplex_face
      _ _ _ _
      (@raw_dependent_simplex_step $C $n $K $c $x)
      (@raw_face_keep (succ $p) (succ $n)
        (@raw_face_keep $p $n $alpha))
  ↪ @dependent_simplex_face_result
      $C (succ $p) (@PathOut_cat $K $x)
      (@dependent_simplex_code_step
        $C $p
        (sigma_Fst
          (@raw_dependent_simplex_face
            $C $p $n $K $c
            (@raw_face_keep $p $n $alpha)))
        (@fapp0
          $K
          (@dependent_simplex_code_decode_cat
            $C $p
            (sigma_Fst
              (@raw_dependent_simplex_face
                $C $p $n $K $c
                (@raw_face_keep $p $n $alpha))))
          (sigma_Snd
            (@raw_dependent_simplex_face
              $C $p $n $K $c
              (@raw_face_keep $p $n $alpha)))
          $x))
      (@pathout_map_func
        $K
        (@dependent_simplex_code_decode_cat
          $C $p
          (sigma_Fst
            (@raw_dependent_simplex_face
              $C $p $n $K $c
              (@raw_face_keep $p $n $alpha))))
        (sigma_Snd
          (@raw_dependent_simplex_face
            $C $p $n $K $c
            (@raw_face_keep $p $n $alpha)))
        $x);

// Public action through the existing set-truncated face-code decoder.
symbol dependent_simplex_face
  [C : Cat]
  [p n : τ Nat_grpd]
  (c : τ (@DependentSimplexCode C n))
  (alpha : τ (@DependentSimplexFaceRef p n))
  : τ (@DependentSimplexFaceResult
      C p (@dependent_simplex_code_decode_cat C n c))
≔ @raw_dependent_simplex_face
    C p n
    (@dependent_simplex_code_decode_cat C n c)
    (@dependent_simplex_code_raw C n c)
    (@face_code_raw (succ p) (succ n) alpha);

symbol dependent_simplex_face_target
  [C : Cat]
  [p n : τ Nat_grpd]
  (c : τ (@DependentSimplexCode C n))
  (alpha : τ (@DependentSimplexFaceRef p n))
  : τ (@DependentSimplexCode C p)
≔ sigma_Fst (@dependent_simplex_face C p n c alpha);

symbol dependent_simplex_face_func
  [C : Cat]
  [p n : τ Nat_grpd]
  (c : τ (@DependentSimplexCode C n))
  (alpha : τ (@DependentSimplexFaceRef p n))
  : τ (Functor
      (@dependent_simplex_code_decode_cat C n c)
      (@dependent_simplex_code_decode_cat
        C p (@dependent_simplex_face_target C p n c alpha)))
≔ sigma_Snd (@dependent_simplex_face C p n c alpha);
