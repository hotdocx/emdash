# REPORT_EMDASH_TYPESCRIPT_ELABORATION.md

Date: 2026-02-09

## 0. Purpose

This report redesigns the TypeScript elaboration architecture in light of the current `emdash2.lp`
status.

Primary target:

- define a practical, implementable syntax+elaboration plan that matches current kernel reality,
- keep the report as the reference for the next TS elaboration iteration.

Secondary target:

- align the surface document (`docs/SYNTAX_SURFACE.md`) with the same decisions.

---

## 1. Ground Truth From Current `emdash2.lp`

### 1.1 Computational today (relevant to elaboration design)

- Stable-head discipline is central (`fapp1_fapp0`, `tapp0_fapp0`, `tapp1_fapp0`, `tdapp0_fapp0`, etc.).
- `Total_cat` object layer is always-Sigma:
  - `tau (Obj (Total_cat E))` reduces to Sigma over base object + fibre object.
- Groth bridges exist as first-class heads:
  - `Fibration_cov_func` (object action of Groth construction),
  - `Fibration_cov_fapp1_func` (morphism-action bridge on transfors).
- `homd_` has a concrete Grothendieck/Grothendieck pointwise computation rule.
- `homd_curry` and `Homd_func` are active computational bridges for total homs in Groth-shaped cases.
- Phase-2 draft strict naturality/exchange rules on `tapp1_fapp0` exist and are typechecked.
- Phase-3 draft adjunction triangle rewrite exists and is typechecked.

### 1.2 Explicitly draft/partial

- `homd_int` is mostly interface-level (not full computation).
- Full displayed Groth morphism-action bridge for deriving all external displayed heads is incomplete.
- Adjunction layer still lacks closed regression terms around triangle normalization.

Implication:

- TS elaboration must separate what is canonical+computational now vs what is exposed as draft features.

---

## 2. Problem Statement (Syntax and Elaboration)

We need a surface language that feels mathematical, but elaborates to stable kernel heads where
normalization performs coherence.

The prior gap:

- syntax discussion focused too much on parser-level notation,
- not enough on kernel-intent elaboration objects (`*_int_*`, stable heads, mode-aware context).

Correct framing:

- syntax is a view,
- elaboration chooses canonical kernel heads,
- rewrite/unification in the kernel carries the computational logic.

---

## 3. Design Decisions

### 3.1 Two-layer surface strategy

We adopt two surface tiers:

1. Default ergonomic tier:
- keep silent forms (`F[x]`, `E[z]`, `eps[x]`, `eps[e]`),
- keep explicit off-diagonal forms (`eps_(f)`, `eps_(sigma)`).

2. Explicit diagnostic tier:
- allow explicit arrow-action notations (`F1[f]`, `FF1[sigma]`) as aliases,
- elaborate them directly to stable heads (`fapp1_fapp0`, `fdapp1_*` family),
- use this tier for debugging, tests, and documentation clarity.

This removes the current asymmetry where `eps_(f)` is explicit but `F1[f]` is unavailable.

### 3.2 Context entries carry mode + controller

Do not introduce special variable term constructors (`CVar`, `FVar`, etc.).

Instead, each context binding stores:

- variable name,
- underlying type/category,
- variation mode,
- controlling category (for arrow-indexed action discipline).

Minimal mode set:

- `functorial` (default `x : A`),
- `object_only` (`x :^o A`),
- `contravariant` (`x :^- A`),
- `natural_intro` (elaboration-only discipline for transfor introduction; optional surface syntax).

Note:

- `natural_intro` is not a replacement for `functorial`; it is a formation/intro discipline.
- compatibility with `EMAIL.md` wording:
  - `:^f` maps to our functorial mode,
  - `:^n` maps to the natural-intro discipline plus context-specific object/arrow roles.
- for arrow-indexed dependent contexts, default base-binder intent is `:^f` (functorial);
  `:^o` is explicit/specialized.

### 3.3 Canonical heads policy

Elaboration always picks canonical stable heads, not expanded expressions.

Examples:

- arrow action: elaborate to `fapp1_fapp0`, not `fapp0 (fapp1_func ...) ...`,
- transfor component: elaborate to `tapp0_fapp0`,
- off-diagonal component: elaborate to `tapp1_fapp0`,
- displayed analogues similarly (`tdapp0_fapp0`, `tdapp1_*` heads).

### 3.4 Feature flags for draft kernel regions

Expose draft computational regions behind explicit elaboration flags:

- `strict_naturality_phase2`,
- `adjunction_phase3`,
- `homd_int_experimental`.

Default behavior:

- allow terms and typing,
- do not promise strong normalization behavior beyond currently computational kernel regions.

---

## 4. Proposed Surface Redesign

### 4.1 Keep existing base notation

- `x : A`, `x :^o A`, `x :^- A`,
- `F[x]`, `E[z]`,
- `eps[x]`, `eps[e]`,
- `eps_(f)`, `eps_(sigma)`.

### 4.2 Add explicit arrow-action forms (new)

Recommended additions:

- `F1[f]`  as explicit ordinary functor arrow-action,
- `FF1[sigma]` as explicit displayed functor dependent arrow-action (where available),
- optional `eps1[alpha]` alias if needed for higher-level readability (desugars to `tapp1_*` usage).

These are aliases, not new kernel primitives.

### 4.3 Optional natural-intro binder syntax (new, optional)

To make transfor introduction readable, allow:

- `x :^n A` in intro blocks that build transfors from diagonal data.

If omitted, elaborator can infer this in transfor-intro contexts.

---

## 5. Elaboration Architecture (TypeScript)

### 5.1 Core data updates (`emdash1/src/types.ts`)

Add:

- `BinderMode` enum:
  - `Functorial`,
  - `ObjectOnly`,
  - `Contravariant`,
  - `NaturalIntro`.
- `ContextEntry` extension with:
  - `mode`,
  - `controllerCat` (term id or normalized descriptor).

Add/ensure stable-head term constructors exist for:

- `fapp1_fapp0`,
- `tapp0_fapp0`,
- `tapp1_fapp0`,
- displayed counterparts (`tdapp0_fapp0`, `tdapp1_*` wrappers),
- optional explicit aliases (`F1`, etc.) as syntax nodes that desugar immediately.

### 5.2 Elaboration phases

Phase A: Parse to neutral CST/AST.

Phase B: Scope + context mode assignment.

Phase C: Desugar silent/explicit aliases to canonical kernel-headed AST.

Phase D: Bidirectional typing with mode checks.

Phase E: Insert implicit coercions/bridges only where policy allows:

- Groth coercion style (`D0 : Z -> Cat` to displayed usage points),
- no global aggressive coercions in draft regions.

Phase F: Normalize/check via kernel conversion.

### 5.3 Mode checks (key rules)

- `object_only` variables cannot be implicitly transported along arbitrary base arrows.
- `contravariant` variables are permitted in off-diagonal accumulation contexts.
- `natural_intro` only appears in transfor-introduction contexts and discharges to transfor terms.

---

## 6. Introduction and Elimination Plan

### 6.1 Functor intro (already known pattern)

Keep `MkFunctorTerm` style intro (or renamed equivalent):

- accepts object action + arrow action skeleton,
- coherence checked by normalization.

### 6.2 Add transfor intro (new required kernel object in TS layer)

Add `MkTransfTerm` (name placeholder):

- input: diagonal component family under `natural_intro` discipline,
- elaborates to canonical transfor object,
- off-diagonal behavior is accessed by eliminators (`tapp1` pipeline), not required as intro input.

This matches current emdash2 design intent: coherence from computation, not separate user lemmas.

### 6.3 Displayed transfor intro (next step after ordinary transfor)

Analogous constructor for displayed transfors:

- diagonal displayed components as intro data,
- off-diagonal displayed components through `tdapp1_*` eliminators.

---

## 7. Mapping to Current `emdash2.lp` Heads

### 7.1 Ordinary

- `F[x]` -> `fapp0 F x`
- `F1[f]` -> `fapp1_fapp0 F f`
- `eps[x]` -> `tapp0_fapp0 x eps`
- `eps_(f)` -> `tapp1_fapp0 eps f`

### 7.2 Displayed

- `FF[e]` -> `fdapp0 FF z e` (with inferred `z`)
- `eps[e]` -> `tdapp0_fapp0 z e eps`
- `eps_(sigma)` -> `tdapp1_*` path (chosen canonical head by elaborator policy)

### 7.3 Dependent hom layer

Use two distinct elaboration routes:

- computational route (preferred where applicable):
  - `homd_` + `homd_curry` + `Homd_func` for total-hom shaped terms.
  - in TS milestone M1, `Cat[b]` is represented through a dedicated constant displayed family
    `CatConst_catd` (temporary hardcoded weakening surrogate; do not overload `Catd_cat` naming).
- interface route:
  - `homd_int` family where no strong computation is guaranteed yet.

---

## 8. Potential Solution to the Syntax Question

Recommended answer:

1. Keep current concise syntax as default.
2. Add explicit arrow-action syntax (`F1[f]`, displayed analogues) as first-class aliases.
3. Adopt mode-aware context as mandatory elaboration infrastructure.
4. Treat `*_int_*` as elaboration targets (named discharge/abstraction operators), not parser sugar.
5. Keep draft kernel regions behind feature flags in elaboration behavior.

This yields:

- user-readable terms,
- predictable normalization (stable heads),
- no artificial variable taxonomy,
- architecture aligned with `emdash2.lp` as it exists today.

---

## 9. Implementation Plan (Incremental)

M0:

- add mode/controller in context,
- no syntax changes yet,
- ensure old tests pass.

M1:

- add explicit alias syntax forms `F1[f]` (and parser mapping),
- desugar to canonical heads,
- add unit tests for equivalence with silent forms.

M2:

- add `MkTransfTerm` intro path,
- implement diagonal-only intro elaboration,
- projection/elimination checks through `tapp0/tapp1` heads.

M3:

- add displayed transfor intro path,
- enable explicit displayed off-diagonal alias where feasible.

M4:

- add draft feature flags (`strict_naturality_phase2`, `adjunction_phase3`, `homd_int_experimental`),
- test matrix by feature profile.

---

## 10. Test Strategy

### 10.1 Elaboration tests

- silent vs explicit alias equivalence:
  - `F[x]` and `F1[id_x]`-related scenarios,
  - `eps[x]` vs `eps_(id_x)` bridge behavior where available.

- mode safety:
  - reject illegal arrow transport from `object_only`.

### 10.2 Normalization-facing tests

- transfor off-diagonal accumulation (phase-2 enabled).
- representable exchange sanity shape.
- adjunction triangle rewrite shape (phase-3 enabled).

### 10.3 Regression gates

- maintain compatibility with current `emdash2.lp` conversion behavior.
- avoid introducing elaboration rewrites that assume unimplemented `homd_int` computation.

---

## 11. Updates Needed in `docs/SYNTAX_SURFACE.md`

Minimum sync updates:

- document explicit alias forms (`F1[f]`, displayed equivalent) as optional/debug-tier syntax,
- clarify that `homd_curry`/`Homd_func` are active computational bridges while `homd_int` remains partial,
- clarify draft status of strict naturality/exchange and adjunction triangle regions.

---

## 12. Final Recommendation

Adopt the two-tier syntax + mode-aware elaboration architecture now, with canonical stable-head output
and explicit draft feature flags.

This is the shortest path that is:

- faithful to current `emdash2.lp`,
- implementable in the TypeScript kernel,
- compatible with future completion of the `homd_int` and displayed bridge story.
