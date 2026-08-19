/*
  Functorial mapped decoding of intrinsic dependent-simplex codes.

  Mapping a raw code along F:C->D returns both the target D-code and a whole
  functor from the source decoded category to the target decoded category.
  Zero returns `(code0(D),F)`. A successor recursively maps its previous code,
  maps the stored flag object, and returns the existing `pathout_map_func`.

  Thus code action does not duplicate the native maps: selected codes reduce
  to `dependent_simplex1_map` through `dependent_simplex4_map`, and another hom
  action remains the generic `fapp1_func`. Endpoint views map by the decoded
  functor's object function and ordinary equality action. The two runtime
  clauses recurse structurally on raw code constructors; no proof-time unifier
  or constructor-specific functoriality law is added.
*/

require open emdash.emdash3_2_dependent_simplex_codes;

// Result of mapped decoding: target code plus its whole decoded map.
symbol DependentSimplexCodeMapResult
  [D : Cat]
  (n : τ Nat_grpd)
  (K : Cat)
  : Grpd
≔ `Σ_ target : τ (@DependentSimplexCode D n),
    @Functor K (@dependent_simplex_code_decode_cat D n target);

symbol dependent_simplex_code_map_result
  [D : Cat]
  [n : τ Nat_grpd]
  [K : Cat]
  (target : τ (@DependentSimplexCode D n))
  (map : τ (Functor K
    (@dependent_simplex_code_decode_cat D n target)))
  : τ (@DependentSimplexCodeMapResult D n K)
≔ Struct_sigma target map;

// Structural mapped decoding at the raw intrinsic index.
injective symbol raw_dependent_simplex_code_map
  [C D : Cat]
  (F : τ (Functor C D))
  [n : τ Nat_grpd]
  [K : Cat]
  (c : τ (@RawDependentSimplexCode C n K))
  : τ (@DependentSimplexCodeMapResult D n K);

// lhs-audit: keep 2 -- the target category is required by the RHS package.
rule @raw_dependent_simplex_code_map
      _ $D $F _ _ (@raw_dependent_simplex_zero $C)
  ↪ @dependent_simplex_code_map_result
      $D zero $C
      (@dependent_simplex_code_zero $D)
      $F
with @raw_dependent_simplex_code_map
      _ $D $F _ _
      (@raw_dependent_simplex_step $C $n $K $c $x)
  ↪ @dependent_simplex_code_map_result
      $D (succ $n) (@PathOut_cat $K $x)
      (@dependent_simplex_code_step
        $D $n
        (sigma_Fst
          (@raw_dependent_simplex_code_map $C $D $F $n $K $c))
        (@fapp0
          $K
          (@dependent_simplex_code_decode_cat
            $D $n
            (sigma_Fst
              (@raw_dependent_simplex_code_map $C $D $F $n $K $c)))
          (sigma_Snd
            (@raw_dependent_simplex_code_map $C $D $F $n $K $c))
          $x))
      (@pathout_map_func
        $K
        (@dependent_simplex_code_decode_cat
          $D $n
          (sigma_Fst
            (@raw_dependent_simplex_code_map $C $D $F $n $K $c)))
        (sigma_Snd
          (@raw_dependent_simplex_code_map $C $D $F $n $K $c))
        $x);

// Public mapped decoder for an existentially packaged code.
symbol dependent_simplex_code_map
  [C D : Cat]
  (F : τ (Functor C D))
  [n : τ Nat_grpd]
  (c : τ (@DependentSimplexCode C n))
  : τ (@DependentSimplexCodeMapResult
      D n (@dependent_simplex_code_decode_cat C n c))
≔ @raw_dependent_simplex_code_map
    C D F n
    (@dependent_simplex_code_decode_cat C n c)
    (@dependent_simplex_code_raw C n c);

symbol dependent_simplex_code_map_target
  [C D : Cat]
  (F : τ (Functor C D))
  [n : τ Nat_grpd]
  (c : τ (@DependentSimplexCode C n))
  : τ (@DependentSimplexCode D n)
≔ sigma_Fst (@dependent_simplex_code_map C D F n c);

symbol dependent_simplex_code_map_func
  [C D : Cat]
  (F : τ (Functor C D))
  [n : τ Nat_grpd]
  (c : τ (@DependentSimplexCode C n))
  : τ (Functor
      (@dependent_simplex_code_decode_cat C n c)
      (@dependent_simplex_code_decode_cat D n
        (@dependent_simplex_code_map_target C D F n c)))
≔ sigma_Snd (@dependent_simplex_code_map C D F n c);

// Functorial image of a formal/readable endpoint view.
symbol dependent_simplex_endpoint_view_map
  [C D : Cat]
  (F : τ (Functor C D))
  [n : τ Nat_grpd]
  (c : τ (@DependentSimplexCode C n))
  (v : τ (@DependentSimplexEndpointView C n c))
  : τ (@DependentSimplexEndpointView
      D n (@dependent_simplex_code_map_target C D F n c))
≔ @dependent_simplex_endpoint_view
    D n
    (@dependent_simplex_code_map_target C D F n c)
    (@fapp0
      _ _
      (@dependent_simplex_code_map_func C D F n c)
      (sigma_Fst v))
    (@fapp0
      _ _
      (@dependent_simplex_code_map_func C D F n c)
      (sigma_Fst (sigma_Snd v)))
    (@eq_ap
      (Obj (@dependent_simplex_code_decode_cat C n c))
      (Obj (@dependent_simplex_code_decode_cat
        D n (@dependent_simplex_code_map_target C D F n c)))
      (@functor_object_function
        (@dependent_simplex_code_decode_cat C n c)
        (@dependent_simplex_code_decode_cat
          D n (@dependent_simplex_code_map_target C D F n c))
        (@dependent_simplex_code_map_func C D F n c))
      (sigma_Fst v)
      (sigma_Fst (sigma_Snd v))
      (sigma_Snd (sigma_Snd v)));
