# emdash3 Clean Executable Skeleton

## Summary

Build `emdash3.lp` as a fresh, typechecking Lambdapi kernel that keeps v2's stable-head rewrite discipline but reorganizes the theory around HoTT-style categorical type formers:

- `Σ_cat` for context extension / totals.
- `Π_cat` for dependent sections.
- A uniform binary internal hom `hom2_int` for `Hom(G ~, F -)`.
- A curried dependent hom `Homd_func` for arrows over base arrows.
- `Functord_cat` and `Transfd_cat` derived from `Π_cat`, not treated as primary primitives.
- `Cat_cat` remains the directed universe: `Hom_cat Cat_cat A B ↪ Functor_cat A B`.

The first deliverable is an executable skeleton, not a full v2 port.

## Key Interfaces

- Keep foundational v2 heads: `Grpd`, `τ`, equality into `Grpd`, `Cat`, `Obj`, `Hom_cat`, `Hom`, `id`, `comp_fapp0`, `Op_cat`, `Path_cat`, `Functor_cat`, `fapp0`, `fapp1_func`, `fapp1_fapp0`, `Cat_cat`.
- Add binary internal hom:
  - `hom2_int G F : Op_cat I → (J → Cat_cat)` for `G : I → A`, `F : J → A`.
  - β-rule: `hom2_int(G,F)(i)(j) ↪ Hom_cat A (G i) (F j)`.
  - Define unary compatibility aliases `hom_` and `hom_con` from `hom2_int`, not as independent architecture.
- Add categorical type formers:
  - `Sigma_cat E : Cat` for `E : Catd Z`; keep `Total_cat` only as alias.
  - `Pi_cat E : Cat` for `E : Catd Z`; objects are sections.
  - `piapp0 s z : Fibre E z` for section evaluation.
  - `PiHom_catd E s t : Catd Z`, with fibre `Hom_cat (E[z]) (s[z]) (t[z])`.
  - Rule: `Hom_cat (Pi_cat E) s t ↪ Pi_cat (PiHom_catd E s t)`.
- Re-express displayed functors:
  - `Functor_catd E D : Catd Z`, fibrewise `Functor_cat (E[z]) (D[z])`.
  - `Functord_cat E D ≔ Pi_cat (Functor_catd E D)`.
  - `fdapp0 FF z u ≔ fapp0 (piapp0 FF z) u`.
  - `Transf_catd FF GG : Catd Z`, fibrewise pointwise transfors.
  - `Transfd_cat FF GG ≔ Pi_cat (Transf_catd FF GG)`.
- Add iteration helper:
  - `Catd_catd E : Catd Z`.
  - Fibre rule: `Fibre_cat (Catd_catd E) z ↪ Catd_cat (Fibre_cat E z)`.
- Replace v2's total/product dependent hom pipeline with a direct curried head:
  - `Homd_func E x u y v : Functor (Op_cat (Hom_cat Z x y)) Cat_cat`.
  - Groth rule: for `E = Fibration_cov_catd M`, object action at `f : x → y` computes to `Hom_cat (M y) (f_! u) v`.
  - Σ arrow characterization: `Hom_cat (Sigma_cat E) (x,u) (y,v)` computes through `Homd_func`.

## Implementation Order

1. Scaffold `emdash3.lp` with flags, comments, and the stable-head design notes from v2 in shortened form.
2. Add the core category layer: `Grpd`, equality, `Cat`, `Obj`, `Hom_cat`, identity, composition, opposites, `Path_cat`.
3. Add ordinary functors and `Cat_cat`, including `id_func`, `comp_cat_fapp0`, `Op_func`, and basic β-rules.
4. Add products only as needed for Σ objects and compatibility helpers.
5. Add `hom2_int`, then derive `hom_` and `hom_con` aliases.
6. Add `Catd`, `Fibre_cat`, `Catd_cat`, `Catd_catd`, `Terminal_catd`, `Fibration_cov_catd`, and Groth object transport.
7. Add `Sigma_cat`/`Total_cat` and projection rules.
8. Add `Pi_cat`, `piapp0`, `PiHom_catd`, and the Π-arrow characterization.
9. Define `Functor_catd`, `Functord_cat`, `fdapp0`, `Transf_catd`, and `Transfd_cat` from Π.
10. Add `Homd_func` and the Groth computation rule; connect Σ homs to `Homd_func`.
11. Defer v2's strict naturality, adjunction, univalence witness, and `tapp/tdapp` layers until this kernel typechecks cleanly.

## Test Plan

- After each implementation block, run `lambdapi check -w emdash3.lp`.
- Add small `assert` checks for:
  - `Path_cat` object/hom/id/comp computation.
  - `Cat_cat` homs reducing to `Functor_cat`.
  - `hom2_int` object-action reducing to `Hom_cat`.
  - `hom_` and `hom_con` aliases reducing through `hom2_int`.
  - `Sigma_cat` object layer reducing to a Σ over fibres.
  - `Pi_cat` homs reducing to pointwise Π homs.
  - `Functord_cat E D` reducing to `Pi_cat (Functor_catd E D)`.
  - `fdapp0` reducing through `piapp0`.
  - Groth `Homd_func` reducing to `Hom_cat (M y) (f_! u) v`.
- Keep `make check` behavior unchanged initially unless we explicitly decide to switch repository-wide checks from `emdash2.lp` to `emdash3.lp`.

## Assumptions

- v3 prioritizes a clean executable skeleton over porting all v2 features immediately.
- `Π_cat` and `Σ_cat` are public conceptual names; v2 names like `Total_cat` remain compatibility aliases only.
- The binary hom design is the default foundation; unary representables are derived views.
- Non-directed univalence, equivalence/isomorphism internals, pushouts/HITs, adjunction cut rules, and full lax naturality are deferred until the Π/Σ/homd foundation is stable.
