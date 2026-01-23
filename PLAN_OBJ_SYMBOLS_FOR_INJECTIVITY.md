# PLAN: Stable `Grpd` heads to regain injectivity (without making `Obj` injective)

This note records the proposed approach for improving inference/readability in `emdash2.lp` while keeping the design choice:

> `Obj : Cat → Grpd` is intentionally **not injective**, to allow definitional equalities like `Obj (Op_cat A) ↪ Obj A` without collapsing `Op_cat A ≡ A`.

The idea is to introduce *injective stable heads* at the `Grpd`-classifier level for selected category constructors, and add fold rules of the form:

```
rule Obj (K_cat …) ↪ K …
```

so that occurrences of `τ (Obj (K_cat …))` normalize to `τ (K …)` where the head `K` *is* injective.

This is analogous to existing stable-head patterns already used in `emdash2.lp`:
- `rule Obj Cat_cat ↪ Cat_grpd;` with `τ Cat_grpd ↪ Cat`,
- `rule Obj (Catd_cat Z) ↪ Catd_grpd Z;` with `τ (Catd_grpd Z) ↪ Catd Z`,
- `rule Obj (Product_cat A1 A2) ↪ Σ_ …`.

---

## 1) Why not “make `Obj` injective and replace definitional equalities by coercions”?

An alternative is:
- delete (or avoid) rules like:
  - `rule Obj (Op_cat A) ↪ Obj A;`
  - `rule @Hom_cat (Op_cat A) X Y ↪ @Hom_cat A Y X;`
- instead add explicit maps/coercions/isomorphisms (e.g. `Obj_op_to : τ (Obj (Op_cat A)) → τ (Obj A)`),
- and then declare `injective symbol Obj : Cat → Grpd;`.

This is *conceptually viable*, but it is a **major redesign** with large practical consequences:

- **You lose definitional transport**. Many existing rewrite rules/proofs rely on definitional equalities
  to keep types literally identical. Without `Obj (Op_cat A) ↪ Obj A`, a term `X : τ (Obj (Op_cat A))`
  cannot be re-used where `τ (Obj A)` is expected without inserting explicit coercions/transport.

- **You must thread coercions everywhere**. For instance, even a rule like:
  `rule @id (Op_cat A) X ↪ @id A X;`
  would stop typechecking (since the RHS expects `X : τ (Obj A)`).
  Every such rule would need a coerced endpoint, and those coercions would need their own computation rules.

- **You reintroduce coherence obligations**. Once you make “opposite” an isomorphism rather than definitional equality,
  you need coherence data showing these coercions behave functorially and involutively, and you must decide which of
  those laws are definitional vs propositional vs unification hints. This becomes especially heavy in the ω-setting.

- **Rewrite matching becomes more brittle**. Many rewrite rules currently match on simple stable heads like `Op_cat`,
  `Hom_cat`, `comp_fapp0`, etc. Inserting coercions/transport tends to obscure those heads, making rewriting and
  normalization harder and more expensive.

Conclusion: making `Obj` injective by replacing definitional equalities with coercions is likely **more complicated and less convenient**
than the “stable `Grpd` heads” plan, and risks turning into a long refactor with degraded computational behavior.

---

## 2) Proposed architecture: “stable `Grpd` heads” + fold rules

### Principle

For selected constructors producing a `Cat` (or producing a `Cat` indexed by data), add a corresponding `Grpd`-level classifier symbol
whose head is injective, and a fold rule from `Obj`:

```
constant injective symbol K : …, Grpd;
rule Obj (K_cat …) ↪ K …;
```

Then:

```
τ (Obj (K_cat …))   ↪*   τ (K …)
```

and type inference can recover parameters from `K …` by injectivity, without requiring `Obj` itself to be injective.

### Safety constraint (important)

Avoid adding “invariance” rewrite rules on these new injective heads, e.g.
`K (Op_cat A) … ↪ K A …`.
Such rules would, together with injectivity, risk forcing unwanted definitional equalities between parameters.

Instead, keep explicit dualization maps like the existing `Op_func`, `Op_funcd`, etc.

---

## 3) First-batch proposal: symbols and fold rules

### 3.1 Functor classifiers

Goal: make `τ (Obj (Functor_cat A B))` normalize to `τ (Functor A B)` with `Functor` injective.

Proposed:

```
constant injective symbol Functor : Π (A B : Cat), Grpd;
rule Obj (Functor_cat $A $B) ↪ Functor $A $B;
```

Then you can gradually rewrite signatures from:
`τ (Obj (Functor_cat A B))`
to:
`τ (Functor A B)`
purely for readability (the old form still normalizes to the new one).

Same pattern for strict functors:

```
constant injective symbol StrictFunctor : Π (A B : Cat), Grpd;
rule Obj (StrictFunctor_cat $A $B) ↪ StrictFunctor $A $B;
```

### 3.2 Displayed functor classifiers

```
constant injective symbol Functord : Π [B : Cat], Π (E D : Catd B), Grpd;
rule Obj (@Functord_cat $B $E $D) ↪ @Functord $B $E $D;
```

(Name note: `Functord` is the `Grpd` classifier; `Functord_cat` stays the `Cat` of displayed functors.)

### 3.3 Transformation classifiers

Ordinary transformations:

```
constant injective symbol Transf : Π [A B : Cat], Π (F G : τ (Functor A B)), Grpd;
rule Obj (@Transf_cat $A $B $F $G) ↪ @Transf $A $B $F $G;
```

Displayed transformations:

```
constant injective symbol Transfd : Π [Z : Cat], Π [E D : Catd Z],
  Π (FF GG : τ (Functord E D)), Grpd;
rule Obj (@Transfd_cat $Z $E $D $FF $GG) ↪ @Transfd $Z $E $D $FF $GG;
```

These are particularly useful because `Transf_cat` / `Transfd_cat` appear all over the projection infrastructure (`tapp*`, `tdapp*`).

### 3.4 “Objects of hom-categories” and “objects of fibres”

These are high-impact because they govern the types of 1-cells and fibre objects.

Hom objects:

```
constant injective symbol Hom : Π [A : Cat] (X Y : τ (Obj A)), Grpd;
rule Obj (@Hom_cat $A $X $Y) ↪ @Hom $A $X $Y;
```

Fibre objects:

Recommended naming to avoid confusion with `Fibre_cat`:

```
constant injective symbol FibreObj : Π [B : Cat] (E : Catd B) (X : τ (Obj B)), Grpd;
rule Obj (Fibre_cat $E $X) ↪ FibreObj $E $X;
```

(Alternative name if preferred: `Fibre` instead of `FibreObj`, but it is easy to confuse with `Fibre_cat` in prose.)

---

## 4) Interaction with existing rules (what must be updated when implementing)

### 4.1 Rules targeting `τ (Obj (@Hom_cat Grpd_cat …))`

There is currently a computation rule:

```
rule τ (Obj (@Hom_cat Grpd_cat $X $Y)) ↪ (τ $X → τ $Y);
```

After adding `rule Obj (@Hom_cat …) ↪ Hom …`, the LHS above will no longer match once the fold happens.

So, when implementing, either:
- rewrite that rule to target `τ (@Hom Grpd_cat X Y)`, or
- delay adding the `Hom` fold until all such `τ(Obj(Hom_cat …))` rules are adjusted.

### 4.2 Existing `unif_rule Obj (…_cat …) ≡ Obj (…_cat …) ↪ …`

Current examples in `emdash2.lp`:
- `Functor_cat` (domain/codomain inference),
- `StrictFunctor_cat`,
- `Functord_cat`.

Once `Obj (…_cat …)` folds to an injective head, these unification rules become **optional**:
- they may become redundant logically,
- but can still be kept if they speed up elaboration in practice.

---

## 5) Migration strategy (incremental, with typechecking at each step)

1. Add new `Grpd` heads + fold rules only (no refactors yet).
2. Re-typecheck (`make check`).
3. Gradually refactor high-traffic signatures for readability:
   - change `τ (Obj (Functor_cat A B))` → `τ (Functor A B)` (etc).
4. Optionally refactor existing `unif_rule`/`rule` LHS patterns to target the new heads (especially the `Hom Grpd_cat` decoding rule).
5. Optionally remove redundant `unif_rule`s after confirming no regressions in inference/timeouts.

---

## 6) Automation: balanced-parentheses rewrite helper

For bulk in-place refactors, use a small Python script (not regex) that:

- scans the file and replaces selected patterns with balanced-paren parsing, e.g.
  - `Obj (Functor_cat <A> <B>)` → `Functor <A> <B>`
  - `Obj (@Hom_cat <A> <X> <Y>)` → `Hom <A> <X> <Y>`
  - `Obj (Fibre_cat <E> <X>)` → `FibreObj <E> <X>`
- avoids changing occurrences in comments/code fences if desired (optional, but recommended).

The safe workflow is: run the script once, then typecheck, then iterate.

