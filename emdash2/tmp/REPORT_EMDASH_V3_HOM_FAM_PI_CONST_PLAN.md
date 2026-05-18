# emdash v3 Hom-Family and Pi/Constant Infrastructure Plan

## Status

Draft planning report for the next `emdash3_1.lp` iteration. This document
consolidates the design review around `Hom_fam`, `Transf_fam`,
`Functor_fam`, constant families, opposite families, and `Pi_cat`.

The active source remains `emdash3_1.lp`, guided by
`REPORT_EMDASH_V3_CONSOLIDATED.md`. This report should be iterated before
implementation.

## Current Facts From v3.1

- Directed families are ordinary functors into `Cat_cat`:
  `Fam_cat K := Functor_cat K Cat_cat`.
- `Fam_app_cat E k` is currently a defined projection:
  `Fam_app_cat E k := fapp0 E k`.
- `Const_fam K A` is currently a defined composite through
  `Obj_func A` and `Terminal_func K`. It computes pointwise, but it is not a
  stable rewrite head that future rules can reliably match.
- `Terminal_fam K` is currently a defined special case of `Const_fam`.
- `Pi_cat E` is currently represented as
  `Transf_cat (Terminal_fam K) E`.
- `piapp0` is already a primitive projection head, even though `Pi_cat` is
  represented through `Transf_cat`.
- `op_val_func K` and `Homd_source_fam E` are defined expressions, not stable
  constructor heads. Operationally, `Homd_source_fam E` is the pointwise
  opposite family of `E`.
- `Functor_fam A B` is a stable family constructor whose fibre computes:
  `(Functor_fam A B)[k] = Functor_cat (A[k]) (B[k])`.
- `Functor_mix_fam_func K` packages `Functor_fam` as a functorial two-argument
  constructor:
  `Op(Fam(Op K)) -> (Fam K -> Fam K)`.
- `homd_ E x u y v` already expresses the dependent hom family over base
  arrows:
  `f : x -> y |-> Hom_{E[y]}(E(f)(u), v)`.

## Lessons From v2

- v2 distinguishes fibrewise displayed constructors from actual displayed
  transformations.
- `Functor_catd` and `Transf_catd` are fibrewise only: their fibres compute to
  ordinary functor and transfor categories, but they do not by themselves give
  full displayed naturality data.
- `Transfd_cat` is the stronger v2 structure: it is the category of displayed
  transfors, with `tdapp0_func`, `tdapp0_fapp0`, `Fibre_transf`, and
  modification packaging.
- v3 should not reintroduce `Catd`/`Catdd`, but the distinction matters:
  a future `Transf_fam` as a `Hom_fam` specialization is analogous to the
  fibrewise `Transf_catd` layer, not yet to full v2 `Transfd_cat`.
- v2 repeatedly uses stable projection heads instead of large definitional
  expansions. This remains the correct discipline for v3.

## Design Conclusions

### 1. Do not add `Hom_fam` directly on top of current definitions

The current definitions are semantically suggestive but operationally too
reducible:

- `Const_fam` is not matchable as a constructor head.
- `op_val_func` and `Homd_source_fam` are not matchable as constructor heads.
- `Pi_cat` is represented by `Transf_cat`, while `piapp0` is already primitive.
- There is no `piapp1`-style projection layer parallel to `tapp*`.

Adding `Hom_fam` now would likely typecheck as a fibre formula but create
fragile rule LHSs and force later rewrites to match through large composites.

### 2. `Const_fam` should become a stable head

`Const_fam K A` should be a primitive or rewrite-capable stable constructor.
Pointwise object computation should remain:

```text
Fam_app_cat (Const_fam K A) k
  --> A
```

The constant action must be omega-aware. A capped rule such as:

```text
fapp1_fapp0 (Const_fam K A) f
  --> id_func A
```

is not enough by itself. Prefer a functor-level constant action.

Introduce or expose a general constant functor head:

```text
Const_func [A B : Cat] (b : Obj B) : Functor A B
```

with object and higher-action rules shaped so that constant families can reduce
through `fapp1_func`, not only through `fapp1_fapp0`.

Then the family action should reduce at the functor level:

```text
fapp1_func (Const_fam K A) x y
  --> Const_func (id_func A)
```

The exact implicit arguments should be chosen after a small Lambdapi probe, but
the important point is functor-level computation first, capped object-level
computation second.

### 3. Add stable opposite-family infrastructure

The operational role currently played by `op_val_func K` should be exposed as a
stable family constructor:

```text
Op_fam [K : Cat] (E : Fam K) : Fam K
```

with fibre rule:

```text
Fam_app_cat (Op_fam E) k
  --> Op_cat (Fam_app_cat E k)
```

and constant-family compatibility:

```text
Op_fam (Const_fam K A)
  --> Const_fam K (Op_cat A)
```

`Homd_source_fam E` should either become a stable alias of `Op_fam E`, or its
operational uses should be replaced by `Op_fam E`. Future rules should not rely
on matching the current defined expression for `Homd_source_fam`.

### 4. Make `Pi_cat` a stable head

`Pi_cat E` should be promoted from a definition to a primitive stable head.
The current representation:

```text
Transf_cat (Terminal_fam K) E
```

is semantically correct, but operationally it conflicts with primitive
`piapp0`. We should make the section category itself a stable surface.

The likely fold is:

```text
Transf_cat (Terminal_fam K) E
  --> Pi_cat E
```

This requires changing `Transf_cat` from `constant symbol` to a rewrite-capable
symbol, likely `injective symbol`, and then rechecking the existing
`Transf_cat` unification helpers and `Hom_cat (Functor_cat _ _)` rule.

If relaxing `Transf_cat` proves too risky, keep the semantic representation
temporarily but still treat `Pi_cat`/`piapp*` as stable heads and avoid adding
new rules that depend on expanding `Pi_cat`.

### 5. Direct non-dependent Pi reduction is preferable

If `Pi_cat` and `Const_fam` are both stable heads, prefer a direct rule:

```text
Pi_cat (Const_fam K A)
  --> Functor_cat K A
```

This states the non-dependent Pi principle directly:
a section of the constant family at `A` is a functor `K -> A`.

Then projection rules should align with ordinary functor application:

```text
piapp0 F k
  --> fapp0 F k
```

for `F : Obj (Pi_cat (Const_fam K A))`, after the source category reduces to
`Functor_cat K A`.

The same principle should extend to the next projection layer:

```text
piapp1_fapp0 F f
  --> fapp1_fapp0 F f
```

This is better than introducing an object-only bridge such as
`Pi_const_to_func`, because the category itself reduces and the ordinary
functor-category infrastructure remains available.

### 6. `homd_` should supply section-over-arrow targets

Do not introduce an isolated object-level projection like:

```text
piapp_base f s
```

The category in which a section's arrow component should live is already
expressed by `homd_`.

For:

```text
E : Fam K
s : Obj (Pi_cat E)
x y : Obj K
f : Hom_K x y
```

the section arrow component should be an object of:

```text
fapp0 (homd_ E x (piapp0 s x) y (piapp0 s y)) f
```

which reduces to:

```text
Hom_cat (E[y]) (E(f)(s[x])) (s[y])
```

Thus the next Pi projection layer should be shaped around `homd_`, for example:

```text
piapp1_fapp0 s f
  : Obj (fapp0 (homd_ E x (piapp0 s x) y (piapp0 s y)) f)
```

and preferably an iterable section-level/functor-level head should accompany
it, rather than only this capped object projection.

The exact functor-level shape remains an open design point, but it should
parallel the `tapp0_func` / `tapp0_fapp0` discipline.

### 7. `Hom_fam` should use `Op_fam`, not `Homd_source_fam`

After the stable infrastructure pass, define:

```text
Hom_fam [K : Cat]
  (E : Fam K)
  (X : Obj (Pi_cat (Op_fam E)))
  (Y : Obj (Pi_cat E))
  : Fam K
```

with fibre rule:

```text
Fam_app_cat (Hom_fam E X Y) k
  --> Hom_cat (Fam_app_cat E k)
        (piapp0 X k)
        (piapp0 Y k)
```

The source endpoint is a section of `Op_fam E` because source position is
contravariant. Since `Obj (Op_cat A)` reduces to `Obj A`, this still gives an
object of the original fibre at each point.

The base-arrow action of `Hom_fam` should be expressed using the future
`piapp1*` projections and `homd_`, not by inventing a separate transport head.

### 8. `Functor_fam` is a constant-`Cat_cat` instance of `Hom_fam`

Semantically:

```text
Functor_fam A B
  ~= Hom_fam (Const_fam K Cat_cat) A B
```

After non-dependent Pi reduction, the precise bridge should be possible
without special source/target section constructors.

For:

```text
X : Obj (Pi_cat (Op_fam (Const_fam K Cat_cat)))
Y : Obj (Pi_cat (Const_fam K Cat_cat))
```

the reductions should give:

```text
X : Obj (Functor_cat K (Op_cat Cat_cat))
Y : Obj (Functor_cat K Cat_cat)
```

Then `Op_func X` has type:

```text
Functor (Op_cat K) Cat_cat
```

so the bridge can be:

```text
Hom_fam (Const_fam K Cat_cat) X Y
  --> Functor_fam (Op_func X) Y
```

The exact LHS should use stable heads and keep inferred arguments implicit.

### 9. `Transf_fam` is a `Hom_fam` specialization

This bridge is more direct:

```text
Transf_fam A B FF GG
  := Hom_fam (Functor_fam A B) FF GG
```

or as a stable fold:

```text
Hom_fam (Functor_fam A B) FF GG
  --> Transf_fam A B FF GG
```

where:

```text
A  : Fam (Op_cat K)
B  : Fam K
FF : Obj (Pi_cat (Op_fam (Functor_fam A B)))
GG : Obj (Pi_cat (Functor_fam A B))
```

Fibrewise:

```text
(Transf_fam A B FF GG)[k]
  --> Transf_cat (piapp0 FF k) (piapp0 GG k)
```

because:

```text
Hom_cat (Functor_cat (A[k]) (B[k])) FF[k] GG[k]
  --> Transf_cat FF[k] GG[k]
```

This `Transf_fam` is the v3 analogue of a fibrewise transformation-family
constructor. It is not yet the full v2-style `Transfd_cat` analogue for
displayed natural transformations between covariant sections.

## Proposed Implementation Order

### Phase 0: Baseline and probes

- Keep the current file typechecking before each phase:
  `lambdapi check -w emdash3_1.lp`.
- Add temporary assertions only as needed to probe Lambdapi elaboration, then
  keep the useful ones as regression checks.
- Avoid any rewrite whose LHS spells large reducible expressions in inferred
  positions.

### Phase 1: Stable constant infrastructure

- Convert `Const_fam` from a definition into a stable symbol.
- Decide whether `Terminal_fam` remains a separate stable symbol or becomes a
  rewrite-normal special case of `Const_fam K Terminal_cat`.
- Introduce or expose `Const_func` for omega-aware constant functors.
- Add functor-level constant action rules before capped `fapp1_fapp0` rules.
- Restore existing assertions:
  `Fam_app_cat (Const_fam K A) k == A`.

### Phase 2: Stable opposite-family infrastructure

- Add `Op_fam` and optionally `Op_fam_func`.
- Add object/fibre rule:
  `Fam_app_cat (Op_fam E) k == Op_cat (Fam_app_cat E k)`.
- Add constant compatibility:
  `Op_fam (Const_fam K A) == Const_fam K (Op_cat A)`.
- Refactor `Homd_source_fam` to use or alias `Op_fam`.
- Ensure existing `homd_int` projection assertions still typecheck.

### Phase 3: Stable Pi infrastructure

- Promote `Pi_cat` to a stable head.
- Add or preserve `Pi_func` object-action:
  `fapp0 (Pi_func K) E == Pi_cat E`.
- Investigate changing `Transf_cat` from `constant symbol` to
  `injective symbol`, then add:
  `Transf_cat (Terminal_fam K) E --> Pi_cat E`.
- Add `piapp0_func` as the functorial projection at an object, if feasible:
  `fapp0 (piapp0_func k) s --> piapp0 s k`.
- Add the first `piapp1*` projection layer through `homd_`.

### Phase 4: Non-dependent Pi

- Add:
  `Pi_cat (Const_fam K A) --> Functor_cat K A`.
- Add projection compatibility:
  `piapp0 F k --> fapp0 F k`.
- Add arrow/higher projection compatibility:
  `piapp1_fapp0 F f --> fapp1_fapp0 F f`, plus functor-level variants if the
  `piapp1` design supports them.
- Keep these rules targeted to stable constant-family heads to avoid broad
  conversion surprises.

### Phase 5: `Hom_fam`

- Add `Hom_fam E X Y` with `X : Pi_cat (Op_fam E)` and `Y : Pi_cat E`.
- Add fibre computation only at first.
- Add sanity assertions for:
  ordinary fibre computation,
  constant-family specialization,
  source object typing through `Obj (Op_cat _)`.
- Delay full base-arrow action rules until the `piapp1` layer is stable.

### Phase 6: Bridges to existing constructors

- Add the constant-`Cat_cat` bridge:
  `Hom_fam (Const_fam K Cat_cat) X Y --> Functor_fam (Op_func X) Y`.
- Add `Transf_fam` as the `Hom_fam (Functor_fam A B)` specialization.
- Add fibre assertion:
  `(Transf_fam A B FF GG)[k] == Transf_cat FF[k] GG[k]`.

## Validation Plan

After each phase, run:

```bash
lambdapi check -w emdash3_1.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

For every new stable head, add at least one assertion exercising its intended
normal form. For every rewrite involving `Const_fam`, `Op_fam`, `Pi_cat`, or
`Hom_fam`, add one assertion in the generic case and one assertion in the
constant-family case.

If a typecheck hangs, inspect the most recent rewrite LHS first, especially
rules that mention `Transf_cat`, `Pi_cat`, `Const_fam`, `Op_fam`, or
`Functor_fam`.

## Open Design Questions

- Should `Terminal_fam` be a separate canonical head, or should
  `Const_fam K Terminal_cat` be the canonical normal form?
- Can `Transf_cat` safely be changed from `constant symbol` to
  `injective symbol` in v3.1 without disturbing current `tapp0_fapp0` rules?
- What is the best functor-level shape for `piapp1`, beyond the capped
  projection into `homd_`?
- Should `Homd_source_fam` remain as a readability alias, or should all future
  internal types use `Op_fam` directly?
- Should `Transf_fam` be a defined alias of `Hom_fam (Functor_fam A B)` or a
  separate stable head with a fold from the `Hom_fam` specialization?

