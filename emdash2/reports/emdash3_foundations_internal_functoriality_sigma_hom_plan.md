# Plan Draft: v3 Foundations, Internal Functoriality, and Sigma Hom

## Summary

This draft supersedes the previous Functord-first wording. The corrected v3 foundation keeps `Pi_cat` primitive and keeps fibrewise constructors such as `Functor_catd` primitive. The missing general principle is the displayed pointwise hom, currently represented by `PiHom_catd`, which should be promoted/renamed to the generic `Hom_catd`.

For Sigma homs, the corrected source of truth is not a new primitive `SigmaHom_catd`. It is a directed displayed transport/induction section over the existing edge context `Edge_catd`, followed by the generic displayed hom `Hom_catd`.

Documentation consolidation is also in scope: before or alongside implementation, the stable v3 decisions should be summarized in a single consolidated report so older planning reports can be retired without losing useful context.

The intended hierarchy is:

```text
Pi_cat        primitive
Functor_catd  primitive
Hom_catd      primitive/generic pointwise displayed hom

Functord_cat E D := Pi_cat (Functor_catd E D)

Transf_catd FF GG := stable canonical specialization of
  Hom_catd (Functor_catd E D) FF GG

Transfd_cat FF GG := Pi_cat (Transf_catd FF GG)
```

`Transf_catd` should remain a stable primitive head, not just a definitional alias. The canonical normalization should be a rule from the generic pointwise hom of a `Functor_catd` to this stable head:

```text
Hom_catd (Functor_catd E D) FF GG ↪ Transf_catd FF GG
```

## Core Architecture

- Promote `PiHom_catd` to `Hom_catd`.
  - Current `PiHom_catd E s t` is already essentially the desired operation.
  - Rename it or add a compatibility alias only temporarily.
  - Fibre rule:
    ```text
    Fibre_cat (Hom_catd E s t) z
      ↪ Hom_cat (Fibre_cat E z) (piapp0 s z) (piapp0 t z)
    ```
  - Pi hom rule:
    ```text
    Hom_cat (Pi_cat E) s t ↪ Pi_cat (Hom_catd E s t)
    ```

- Keep `Functor_catd` primitive.
  - `Functor_catd E D` remains the fibrewise displayed functor-category constructor.
  - `Functord_cat E D` remains a definition:
    ```text
    Functord_cat E D := Pi_cat (Functor_catd E D)
    ```
  - Therefore the hom of displayed functors is obtained from the generic Pi hom rule and the `Hom_catd (Functor_catd ...)` specialization.

- Keep `Transf_catd` as a stable primitive head.
  - Add or preserve:
    ```text
    Transf_catd [Z] [E D : Catd Z] (FF GG : Functord E D) : Catd Z
    ```
  - Its fibre rule should use extracted fibre functors:
    ```text
    Fibre_cat (Transf_catd FF GG) z
      ↪ Transf_cat (Fibre_func FF z) (Fibre_func GG z)
    ```
  - Add canonical normalization:
    ```text
    Hom_catd (Functor_catd E D) FF GG ↪ Transf_catd FF GG
    ```

- Define `Transfd_cat` by Pi, not as an independent level.
  - Use:
    ```text
    Transfd_cat FF GG := Pi_cat (Transf_catd FF GG)
    ```
  - Then:
    ```text
    Hom_cat (Functord_cat E D) FF GG
      ↪ Transfd_cat FF GG
    ```
    should either follow by unfolding plus the generic rules, or be added as a shortcut that joins the same normal form.

## Sigma/Pi/Weakening Adjunction Clarification

The current plan needs a sharper distinction between:

```text
Sigma_cat E : Cat
```

and the relative logical operation:

```text
Sigma_π : Catd (Sigma_cat E) -> Catd Z
```

where `π = Sigma_proj1_func E : Functor (Sigma_cat E) Z`.

`Sigma_cat E` is the context extension / total category for one displayed category `E : Catd Z`. It is not itself the whole left adjoint in the relative adjunction

```text
Sigma_π  ⊣  π*  ⊣  Pi_π.
```

In the current v3 kernel, the middle functor `π*` is already represented by pullback:

```text
Pullback_catd D (Sigma_proj1_func E)
```

for `D : Catd Z`. The relative `Sigma_π` and `Pi_π` constructors can be added later as displayed-category-level operations over `Z`. Their fibre rules should be expressed by restricting a family over `Sigma_cat E` to the fibre inclusion over each base object:

```text
fibre_intro_func E z : Functor (Fibre_cat E z) (Sigma_cat E)
fapp0 (fibre_intro_func E z) u ↪ Struct_sigma z u

Fibre_cat (Sigma_proj_catd E D) z
  ↪ Sigma_cat (Pullback_catd D (fibre_intro_func E z))

Fibre_cat (Pi_proj_catd E D) z
  ↪ Pi_cat (Pullback_catd D (fibre_intro_func E z))
```

These relative constructors are not required before the Sigma-hom slice, but the plan should avoid describing `Sigma_cat` alone as the adjoint `Sigma_π`.

The fragments needed immediately are the terminal/base-global adjunction fragments:

```text
Sigma_!  ⊣  !*  ⊣  Pi_!
```

where `!* A` is `Const_catd Z A`, `Sigma_! E` is `Sigma_cat E`, and `Pi_! E` is `Pi_cat E`.

Add or at least document the following generic stable heads before adding edge-specific helpers:

```text
sigma_intro_functord E
  : Functord E (Const_catd Z (Sigma_cat E))

fdapp0 (sigma_intro_functord E) z u
  ↪ Struct_sigma z u
```

This is the unit of `Sigma_! ⊣ !*`, i.e. Sigma introduction in context. It also packages all fibre inclusions internally. The fixed-endpoint edge map should be only a derived component:

```text
edge_at_func x y
  := piapp0 (sigma_intro_functord (Edge_catd Z x)) y

edge_at_func x y
  : Functor (Fibre_cat (Edge_catd Z x) y)
            (Sigma_cat (Edge_catd Z x))
```

and the existing fibre rule for `Edge_catd` then gives the desired source:

```text
Fibre_cat (Edge_catd Z x) y ↪ Op_cat (Hom_cat Z x y).
```

For `Pi_cat`, keep `piapp0` as the primitive eliminator/evaluation head, but identify it as the counit of `!* ⊣ Pi_!` by adding a displayed functor packaging:

```text
pi_eval_functord E
  : Functord (Const_catd Z (Pi_cat E)) E

fdapp0 (pi_eval_functord E) z s
  ↪ piapp0 s z
```

The dual unit is the constant-section operation:

```text
const_section_func Z A
  : Functor A (Pi_cat (Const_catd Z A))

piapp0 (fapp0 (const_section_func Z A) a) z
  ↪ a
```

This is the general source of any fixed-family constant section. Therefore `edge_const_sec` should not be foundational. It should either be a temporary alias or be replaced by a generic compatibility bridge saying that pulling `π*E` back along Sigma introduction is constant:

```text
Pullback_catd
  (Pullback_catd E (Sigma_proj1_func H))
  (piapp0 (sigma_intro_functord H) z)

  behaves as

Const_catd (Fibre_cat H z) (Fibre_cat E z).
```

More precisely, this should follow from three generic computation principles:

```text
Pullback_catd (Pullback_catd E F) G
  ↪ Pullback_catd E (comp_cat_fapp0 F G)

comp_cat_fapp0
  (Sigma_proj1_func H)
  (piapp0 (sigma_intro_functord H) z)
  ↪ const_func (Fibre_cat H z) Z z

Pullback_catd E (const_func A Z z)
  ↪ Const_catd A (Fibre_cat E z)
```

where `const_func A Z z : Functor A Z` is the ordinary constant functor at `z`. It can be implemented as a stable head or as the composite `Obj_func z ∘ Terminal_func A`, but a stable head may make the pullback rule easier to match.

If a direct rewrite from the pullback expression to `Const_catd` is too aggressive for Lambdapi, keep a generic stable head for this compatibility case, but make it generic in `H`, `E`, and `z`; do not introduce an edge-only primitive.

Similarly, section restriction should be a functoriality/substitution operation for `Pi_cat`, not an edge-specific construction:

```text
section_pullback_func F E
  : Functor (Pi_cat E) (Pi_cat (Pullback_catd E F))

piapp0 (fapp0 (section_pullback_func F E) s) a
  ↪ piapp0 s (fapp0 F a)
```

The fixed-endpoint transport section used in Sigma hom is then:

```text
transport_xy
  := fapp0
       (section_pullback_func (edge_at_func x y)
                              (Pullback_catd E (Sigma_proj1_func (Edge_catd Z x))))
       (transportd_sec E x u)
```

This keeps the Sigma-hom construction internal: `edge_at_func`, constant sections, and section restriction all come from generic Sigma/Pi/weakening primitives.

## Omega-Iteration Principle

Do not introduce a fresh Lambdapi category constructor for each higher cell level, such as `Modf_catd`, `Modfd_cat`, `4Cell_catd`, etc.

Higher cells are ordinary homs in already-formed categories:

```text
modifications between eps eps' : Transfd_cat FF GG
  are Hom_cat (Transfd_cat FF GG) eps eps'
```

When these higher homs must be used functorially, they should be repackaged by operation-level heads into `Transfd_cat`-shaped data, following the emdash2 pattern:

```text
Hom_cat (Transfd_cat FF GG) eps eps'
  --operation-level repackaging-->
Transfd_cat (component_functor eps) (component_functor eps')
```

This is the role of later `tapp1_fapp1_func` / `tdapp1_fapp1_func`-style operations. They are stable heads for functorial operations, not new primitive cell levels. This preserves omega iteration without requiring an infinite sequence of Lambdapi symbols.

## Documentation Consolidation

- Add `reports/REPORT_EMDASH_V3_CONSOLIDATED.md`.
  - Summarize `PRD_EMDASH_V3_INITIAL_IDEA.md`, the emdash2 lessons that still matter, the accepted v3 architecture in this plan, and the next implementation sequence.
  - Include a superseded-reports index for existing `reports/*` files, distinguishing still-relevant references from outdated drafts.
  - Do not read, summarize, or reference `.scratchpad/`.
  - Treat `reports/emdash3_foundations_internal_functoriality_sigma_hom_plan.md` as the source of truth until the consolidated report exists.

## Internal Functoriality Work Still in Scope

- Internalize pullback in the displayed-category argument.
  - Add `Pullback_catd_func F : Functor (Catd_cat B) (Catd_cat A)`.
  - Object action:
    ```text
    fapp0 (Pullback_catd_func F) E ↪ Pullback_catd E F
    ```
  - Hom action should fold to `Pullback_funcd F`.

- Internalize ordinary composition more fully.
  - Add a functorial composition package in the functor being postcomposed:
    ```text
    comp_cat_func [X Y Z]
      : Functor
          (Functor_cat Y Z)
          (Functor_cat (Functor_cat X Y) (Functor_cat X Z))
    ```
  - Keep `comp_cat_cov_func G` as the object-action / stable postcomposition head.
  - Object action should compute as:
    ```text
    fapp0 (fapp0 comp_cat_func G) F ↪ comp_cat_fapp0 G F
    ```
  - Once this is stable, update `op_val_func` and similar internal pipelines to use the general functorial composition package rather than ad hoc postcomposition-only plumbing.

- Internalize `Catdd` constructors when needed.
  - Current `Catdd`, `Pullback_catdd`, `Functor_catdd`, and `Pi_catdd` remain useful.
  - Add functor-object versions for constructors whose morphism action matters:
    ```text
    Pullback_catdd_func F
    Functor_catdd_func B
    ```
  - Keep current `Pullback_catdd` and `Functor_catdd` as object-action aliases / stable object-level heads.
  - `Const_catdd [I Z] E` means weakening both `Z` and `E` into the extra `I` context.

- Make `Totald_catd` functorial in the displayed category variable.
  - The current fibre-only form is useful but semantically incomplete.
  - Keep `Total_intro_func` as the stable head for the induced functor on total categories:
    ```text
    Total_intro_func xy FF : Functor (Total_cat E) (Total_cat D)
    ```
    where `FF : Functord E (Pullback_catd D xy)`.
  - Keep `Total_intro_func_func xy` as the functor-object packaging in the displayed-functor argument:
    ```text
    fapp0 (Total_intro_func_func xy) FF ↪ Total_intro_func xy FF
    ```
  - A later `Totald_func Z : Functor (Catd_cat Z) Cat_cat` should have object action `H ↦ Sigma_cat H`.
  - Its hom action should be induced by the existing total-introduction package:
    ```text
    fapp1_func (Totald_func Z) H K
      ↪ Total_intro_func_func (id_func Z)
    ```
  - This should be paired with the identity-pullback normalization:
    ```text
    Pullback_catd K (id_func Z) ↪ K
    ```
    so the domain of `Total_intro_func_func (id_func Z)` is definitionally `Functord_cat H K`.
  - Once `Totald_func Z` exists, prefer defining or normalizing:
    ```text
    Totald_catd Z ↦ Fibration_cov_catd (Totald_func Z)
    ```
    rather than keeping `Totald_catd Z` as only a bare fibre rule.
  - Keep `Total_proj1_functord Z : Functord (Totald_catd Z) (ConstZ_catd Z)`.
    Its fibre functor should continue to compute to the ordinary projection:
    ```text
    Fibre_func (Total_proj1_functord Z) H ↪ Total_proj1_func H
    ```
    This remains important for `PredPi_catd` and for later generalized `Sigma`/weakening-pullback adjunction machinery.

## Older Draft Material Intentionally Not Restored

The older saved draft contains two major decisions that should remain superseded:

- Do not restore the Functord-first foundation.
  - `Functord_cat` should not become primitive again merely to make `Pi_cat` a terminal displayed-functor instance.
  - Current decision:
    ```text
    Pi_cat primitive
    Functor_catd primitive
    Functord_cat E D := Pi_cat (Functor_catd E D)
    ```
  - `piapp0` can still later be related to general displayed-functor evaluation, but this should not force the foundation back to the older primitive `Functord_cat` plan.

- Do not restore primitive `SigmaHom_catd`.
  - The older draft used:
    ```text
    SigmaHom_catd E x u y v : Catd (Op_cat (Hom_cat Z x y))
    ```
  - Current decision: Sigma hom must be expressed by `transportd_sec`, restriction along the edge context, constant sections, and `Hom_catd`.
  - A named endpoint head is allowed later only as a derived normal form for that expression.

## Directed Displayed Transport

The transport primitive should be global over the edge context. Do not introduce a parallel `HomFrom_catd`; reuse the existing edge family:

```text
Edge_catd Z x : Catd Z
Fibre_cat (Edge_catd Z x) y ≡ Op_cat (Hom_cat Z x y)
```

Introduce a directed displayed transport/induction section:

```text
transportd_sec [Z] (E : Catd Z)
  (x : Obj Z) (u : E[x])
  : Obj
      (Pi_cat
        (Pullback_catd E
          (Total_proj1_func (Edge_catd Z x))))
```

Read this as:

```text
transportd_sec E x u [y, f : x -> y] : E[y]
```

For the Grothendieck case, add the beta rule:

```text
piapp0
  (transportd_sec (Fibration_cov_catd M) x u)
  (Struct_sigma y f)
↪ fib_cov_tapp0_fapp0 M f u
```

This is the directed analogue of HoTT transport/J for displayed categories. It is primitive for general `E : Catd Z`, with computation rules only for structured constructors such as `Fibration_cov_catd M`. It should not be derived from `homd_curry`; rather, `homd_curry` is later higher/off-diagonal packaging related to transport plus fibrewise hom.

For fixed endpoint `y`, the old fixed-target section is only a restriction of this global section. The endpoint inclusion should be obtained from generic Sigma introduction:

```text
edge_at_func x y :
  Functor (Op_cat (Hom_cat Z x y))
          (Sigma_cat (Edge_catd Z x))

edge_at_func x y
  := piapp0 (sigma_intro_functord (Edge_catd Z x)) y

edge_at_func x y f = Struct_sigma y f
```

If `edge_at_func` remains as a named symbol during implementation, it should be a compatibility alias for this component, not a new primitive concept.

The section-level helper needed to use this restriction is the generic pullback/substitution operation for sections:

```text
section_pullback_func F E
  : Functor (Pi_cat E) (Pi_cat (Pullback_catd E F))
```

where `s : Obj (Pi_cat E)` and `F : Functor A B`, with beta behavior:

```text
piapp0 (fapp0 (section_pullback_func F E) s) a
  ↪ piapp0 s (fapp0 F a)
```

The fixed-target section over the restricted family should come from the generic `const_section_func` plus the Sigma-introduction/pullback compatibility rule:

```text
edge_const_sec E x y v
  : Obj
      (Pi_cat
        (Pullback_catd
          (Pullback_catd E (Total_proj1_func (Edge_catd Z x)))
          (edge_at_func x y)))
```

with beta behavior:

```text
piapp0 (edge_const_sec E x y v) f ↪ v
```

As with `edge_at_func`, `edge_const_sec` may remain temporarily as a readable alias, but the source of truth should be the generic constant-section/unit operation. If the required pullback does not normalize all the way to `Const_catd`, introduce a generic compatibility head for this Sigma-introduction pullback case rather than an edge-only primitive.

## Sigma Hom Direction

The temporary endpoint heads `homd_eval_func` / `Homd_func` should not be treated as the v3 foundation. They may remain briefly as compatibility/debug heads, but the intended source of truth is:

```text
transportd_sec + section restriction + const_section + Hom_catd + Sigma_cat
```

For fixed endpoints `(x,u)` and `(y,v)`, define the restricted displayed family over the base-arrow category:

```text
Dxy :=
  Pullback_catd
    (Pullback_catd E (Total_proj1_func (Edge_catd Z x)))
    (edge_at_func x y)
```

Using pullback composition, projection-after-Sigma-introduction cancellation, and pullback-along-constant normalization, this family should reduce to:

```text
Dxy
  ↪ Const_catd
      (Fibre_cat (Edge_catd Z x) y)
      (Fibre_cat E y)

  ↪ Const_catd
      (Op_cat (Hom_cat Z x y))
      (Fibre_cat E y)
```

This does not make the transport section constant. It only says that all fibres of the indexed family are the same category `Fibre_cat E y`. The transport section can still vary with the arrow `f : x -> y`, which is exactly the intended Grothendieck behaviour.

Construct two sections over `Dxy`:

```text
transport_xy : Obj (Pi_cat Dxy)
const_v_xy   : Obj (Pi_cat Dxy)
```

where:

```text
transport_xy :=
  fapp0
    (section_pullback_func
      (edge_at_func x y)
      (Pullback_catd E (Total_proj1_func (Edge_catd Z x))))
    (transportd_sec E x u)

const_v_xy :=
  edge_const_sec E x y v
  -- eventually: generic constant section after Sigma-introduction pullback compatibility
```

After `Dxy` normalizes to the constant family, the second line should become simply:

```text
const_v_xy :=
  fapp0
    (const_section_func
      (Fibre_cat (Edge_catd Z x) y)
      (Fibre_cat E y))
    v
```

Then the Sigma hom classifier is the generic displayed hom:

```text
Hom_catd Dxy transport_xy const_v_xy
```

and the Sigma hom rule should be:

```text
Hom_cat (Sigma_cat E) (Struct_sigma x u) (Struct_sigma y v)
  ↪ Op_cat (Sigma_cat (Hom_catd Dxy transport_xy const_v_xy))
```

The current orientation convention is to keep the fixed-arrow base as `Op_cat (Hom_cat Z x y)`, matching the existing `Edge_catd` and `Homd_func` orientation. This can be revisited only if the full Sigma hom normal form is changed consistently.

For the Grothendieck probe case, the fibre of the displayed hom should compute to:

```text
Fibre_cat
  (Hom_catd Dxy transport_xy const_v_xy)
  f
↪ Hom_cat (M y) (fib_cov_tapp0_fapp0 M f u) v
```

No primitive `SigmaHom_catd` should be added for this meaning. If a stable endpoint head is useful later, it must be a derived normal form for this `Hom_catd` expression, not an independent primitive hom concept.

## Implementation Sequence

1. Consolidate documentation into `reports/REPORT_EMDASH_V3_CONSOLIDATED.md`, using this plan as the current source of truth and marking older reports as superseded where appropriate.
2. Promote `PiHom_catd` to `Hom_catd`, add the `Hom_catd (Functor_catd ...) ↪ Transf_catd ...` specialization, and verify `Transfd_cat` remains a Pi-defined level.
3. Add the generic Sigma/Pi/weakening adjunction fragments: `const_func`, `sigma_intro_functord`, `pi_eval_functord`, `const_section_func`, `section_pullback_func`, pullback-composition normalization, and only generic compatibility heads needed for pullback along Sigma introduction.
4. Add the internal functor-object versions of pullback, composition, `Catdd` constructors, and totalization, including the `Total_intro_func_func`-based hom action for `Totald_func`.
5. Add directed displayed transport over `Edge_catd`, derive `edge_at_func` from `sigma_intro_functord`, derive or alias the fixed constant section from the generic constant-section machinery, and add the Sigma hom rule expressed through `Hom_catd`.
6. Remove or demote `homd_eval_func` / `Homd_func` only after the new Sigma hom path has equivalent Grothendieck beta coverage.

## Test Plan

- Run after each implementation slice:
  - `lambdapi check -w emdash3.lp`
- Final validation:
  - `EMDASH_TYPECHECK_TIMEOUT=60s make check`

Required assertions for this foundation:

- `Fibre_cat (Hom_catd E s t) z ≡ Hom_cat (Fibre_cat E z) (piapp0 s z) (piapp0 t z)`.
- `Hom_cat (Pi_cat E) s t ≡ Pi_cat (Hom_catd E s t)`.
- `Hom_catd (Functor_catd E D) FF GG ≡ Transf_catd FF GG`.
- `Fibre_cat (Transf_catd FF GG) z ≡ Transf_cat (Fibre_func FF z) (Fibre_func GG z)`.
- `Transfd_cat FF GG ≡ Pi_cat (Transf_catd FF GG)`.
- `Hom_cat (Functord_cat E D) FF GG ≡ Transfd_cat FF GG`.
- `fdapp0 (sigma_intro_functord E) z u ≡ Struct_sigma z u`.
- `fdapp0 (pi_eval_functord E) z s ≡ piapp0 s z`.
- `piapp0 (fapp0 (const_section_func Z A) a) z ≡ a`.
- `piapp0 (fapp0 (section_pullback_func F E) s) a ≡ piapp0 s (fapp0 F a)`.
- `piapp0 (sigma_intro_functord (Edge_catd Z x)) y` has the fixed-endpoint `edge_at_func` type.
- `comp_cat_fapp0 (Sigma_proj1_func H) (piapp0 (sigma_intro_functord H) z) ≡ const_func (Fibre_cat H z) Z z`.
- `Pullback_catd E (const_func A Z z) ≡ Const_catd A (Fibre_cat E z)`.
- `fapp0 (Pullback_catd_func F) E ≡ Pullback_catd E F`.
- `fapp1_fapp0 (Pullback_catd_func F) FF ≡ Pullback_funcd F FF`.
- `fapp0 (fapp0 comp_cat_func G) F ≡ comp_cat_fapp0 G F`.
- `Fibre_cat (Totald_catd Z) H ≡ Sigma_cat H`.
- `fapp1_func (Totald_func Z) H K ≡ Total_intro_func_func (id_func Z)`.
- `Fibre_cat (Edge_catd Z x) y ≡ Op_cat (Hom_cat Z x y)`.
- `piapp0 (transportd_sec (Fibration_cov_catd M) x u) (Struct_sigma y f) ≡ fib_cov_tapp0_fapp0 M f u`.
- Restricting `transportd_sec E x u` along `edge_at_func x y` yields a section over the fixed-arrow family `Dxy`.
- The fixed-endpoint Sigma hom normalizes through `Hom_catd Dxy transport_xy const_v_xy`.
- In the Grothendieck case, the Sigma hom fibre computes to `Hom_cat (M y) (fib_cov_tapp0_fapp0 M f u) v`.
- No `Modf_catd` / `Modfd_cat` symbols are introduced.
- No primitive `SigmaHom_catd` is introduced for the foundational meaning.
- Existing `hom2_int`, `hom_`, `hom_con`, `Functor_catd`, `Catdd`, `PredPi_catd`, `Edge_catd`, and Groth transport sanity checks still pass.

## Assumptions

- `emdash3.lp` is allowed to break compatibility with temporary v3 names from earlier iterations.
- `emdash2.lp` remains read-only reference material.
- `Pi_cat` and `Functor_catd` remain primitive in v3.
- `Hom_catd` is the generic pointwise displayed hom; current `PiHom_catd` is its prototype.
- `Transf_catd` is a stable primitive head with a canonical rule from `Hom_catd (Functor_catd ...)`.
- The older proposal to make `Functord_cat` primitive again is superseded by the current decision: `Functord_cat E D := Pi_cat (Functor_catd E D)`.
- `Sigma_cat E` is context extension/totalization; the relative `Sigma_π` and `Pi_π` adjoints to pullback along `Sigma_proj1_func E` are separate displayed-category-level operations to add later if needed.
- `const_func`, `sigma_intro_functord`, `pi_eval_functord`, `const_section_func`, and `section_pullback_func` are the immediate computational fragments of the Sigma/Pi/weakening adjunctions.
- `transportd_sec` is a primitive directed displayed transport/induction operation for general `Catd`, with beta rules for `Fibration_cov_catd`.
- `Edge_catd` is the existing source of the edge context; do not introduce a duplicate `HomFrom_catd`.
- `edge_at_func` is provisional notation for the fixed-endpoint restriction map; it should be the `y`-component of `sigma_intro_functord (Edge_catd Z x)`, not a primitive.
- `edge_const_sec` is provisional notation for a constant section over the Sigma-introduction pullback; it should come from `const_section_func` plus generic compatibility, not an edge-only primitive.
- Sigma hom is expressed by `Hom_catd` after restricting transport and adding a constant section, not by a primitive `SigmaHom_catd`.
- Higher cells are represented by ordinary homs in existing categories and are made iterable by operation-level repackaging heads, not by an infinite family of new cell constructors.
- Old reports will not be moved by this implementation; a future consolidated report will make them safe for the user to retire afterward.
