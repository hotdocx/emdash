# Appendix — next internal steps (recorded discussion)

This appendix records the agreed design points for continuing the “more internal” development,
as discussed after implementing `homd_cov_int`, `tapp1_func_transf`, and `fapp1_transf`.

It is intended as a handover note for the next implementation steps; it is not executable code.

---

## A) Relative dimension (comment convention)

When we use phrases like “1-cell / 2-cell / 3-cell” in this development, the dimension is always
**relative to the ambient category** `A : Cat`.

- A “1-cell in `A`” is an object of `Hom_cat A X Y`.
- A “2-cell in `A`” is a morphism in that hom-category, i.e. a 1-cell in `Hom_cat A X Y`.
- And so on, iterating globularly.

Semantically, the ambient `A` can itself encode higher structure (e.g. `A = Total_cat E`), so a
“1-cell relative to `A`” may correspond to a higher-dimensional cell in an “absolute” semantics.

---

## B) Globular vs simplicial (key interface distinction)

### `fapp1_func` vs `fapp1_fib_funcd`

- `fapp1_func` is the **globular** action: it acts on the hom-category `Hom_cat A X Y`.
  In the intended globular reading, morphisms in `Hom_cat A X Y` are higher (2-)arrows “over” an
  identity 1-arrow (they compare parallel 1-cells with fixed boundary `(X,Y)`).

- `fapp1_fib_funcd` is the **simplicial/Grothendieck packaging** of (a piece of) the same action,
  using representables and Grothendieck totals to present higher arrows “over” a chosen base 1-cell.
  The difference between `fapp1_func` and `fapp1_fib_funcd` is therefore presentation (globular vs simplicial),
  not a change of relative dimension.

### “1/2 vs 2/3” slogan (relative)

- `fapp1_fib_funcd` (built from `hom_cov`) presents “(relative) 1-cells as objects + (relative) 2-cells as arrows”
  in a simplicial style (2-simplex level).

- `fdapp1_funcd` (built from `homd_cov`) is the next simplicial iteration: it presents “(relative) 2-cells as objects
  + (relative) 3-cells as arrows” (surface/triangle classifier; 3-simplex level).

---

## C) Strict functors and “laxness evidence becomes identity” (deferred rule)

We introduced `StrictFunctor_cat` with an injective forgetful map:

- `forget_strict : StrictFunctor_cat(A,B) → Functor_cat(A,B)`

and strictness rewrite rules for identities and composition on 1-cells:

- `F(id_X) ↪ id_{F(X)}`
- `F(g∘f) ↪ F(g)∘F(f)`

However, this is only the prerequisite. For a strict functor `F = forget_strict Fs`, we also want the
**simplicial packaging** `fapp1_fib_funcd` to be *cartesian* in the sense that it maps the canonical/cartesian
2-arrow (over a base edge) to an **identity** 2-arrow. Equivalently: the usual “laxness evidence”
2-cell that would witness non-commutativity / non-strictness should reduce to an identity 2-cell.

This cartesianness step is deferred to a later milestone.

---

## D) Internalization via nested transfors (ordinary case)

We now have a very-internal ordinary “superscript component packaging”:

- `tapp1_func_transf` (outer index internalized via nested `Transf_cat`)

and a derived stable head:

- `fapp1_transf`, obtained by specializing `tapp1_func_transf` at the identity transfor.

The older external-index packaging `fapp1_fib_funcd` is intended to become **derived** later, once we add the
Grothendieck morphism-action bridge that turns a transfor `E ⇒ D` into a displayed functor `∫E ⟶ ∫D`.

---

## E) Displayed “very internal tdapp1” (restricted plan)

The outline’s Step F (nested `Transfd_cat`, non-circular) is considered correct.

Key implementation refinements:

1) **Probe restriction (simple, not a new “probe notion”)**
   To align with the current `homd_cov_int` discipline, restrict the domain displayed category to be Grothendieck:

   - `E := FibrationOp_catd E0` for some `E0 : Z ⟶ Cat_cat`.
   - Then `GG : Functord_cat (FibrationOp_catd E0) D` matches the intended “computational probe into D”.

2) **Need displayed opposite and composition**
   For the Step F form

   - `… (homd_cov_int Id) … ((homd_cov_int GG) ∘ (FF^op)) …`

   we need:

   - a displayed opposite on slice-style displayed functors:
     `Op_funcd : Functord_cat(E,D) → Functord_cat(Op_catd E, Op_catd D)`
     (cf. `cartierSolution13.lp`, adapted to our slice-style setting with implicit base identity).

   - a clean composition operator for displayed functors, ideally paralleling ordinary composition by
     instantiating the ordinary `comp_func` story at a category `Catd_cat Z` (to be introduced later if needed).
     In the short term, we can use the existing term-level `comp_funcd`.

3) The nested-`Transfd_cat` target is already the displayed analogue of “internalizing the outer index”.
   The remaining missing pieces are the displayed `^op` and displayed composition packaging.

---

## F) Future categorification candidates (parked idea)

There is a plausible future `Catd_cat Z : Cat` (objects `Catd Z`, homs `Functord_cat`) and a base-variance functor
`Catd_func : Functor_cat (Cat_cat^op) Cat_cat`, analogous in spirit to the existing fibration classifier `Fib_func`.

We also expect an embedding of (op)fibrations into isofibrations (details deferred):

- `isofib_of_fib : Fib_func → Catd_func`

This is recorded as a plausible direction, but it is not required for the immediate nested-`Transfd_cat` step.

