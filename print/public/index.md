---
title: "emdash: Computational ω-Category Theory via Dependent Arrow Categories in Lambdapi"
authors: m— / emdash project
---

# Abstract

`emdash2.lp` is an experiment in *functorial programming* for strict/lax $\\omega$-categories inside the Lambdapi logical framework. The guiding principle is proof-theoretic: many categorical equalities (units, associativity, triangle identities, functoriality laws) are best treated as *normalization* (“cut-elimination”) rather than as external propositions. The technical focus of this paper is a *dependent arrow/comma (dependent hom)* construction for a dependent category $E$ over a base category $Z$. In the kernel this appears as `homd_cov` and its more internal, base-parametrized variant `homd_cov_int`. These constructions organize “cells over a base arrow” in a simplicial (triangle/surface) manner, and they serve as the substrate for computational treatments of higher structure such as lax naturality and adjunctions. We explain the design of the emdash kernel, relate it to standard category-theoretic and type-theoretic notions, and show how (a draft of) adjunction triangle identities becomes a rewrite rule.

# 1. Introduction (what problem are we solving?)

Higher category theory is hard to formalize for two intertwined reasons:

1. *Size of coherence*: weak $n$-categories and especially weak $\\omega$-categories come with an explosion of coherence data.
2. *Where equalities live*: in proof assistants, equalities are propositions to be proved, while in category theory many equalities are “structural” and ought to compute away.

The emdash project explores a kernel design in which:

- “Category theory” is internal: we work *inside* a dependent type theory that has a classifier `Cat` of categories and a classifier `Grpd` of (∞-)groupoids.
- Many categorical laws are definitional: they are enforced by rewrite rules and unification hints, so that normalization *is* diagram chasing.

This paper is a narrative tour of the current `emdash2.lp` kernel. It aims to be readable to a non-specialist, while staying faithful to the code. When we mention a kernel identifier (e.g. `homd_cov_int_base`) we also provide a traditional reading.

# 2. Why Lambdapi, and why rewriting?

Lambdapi is a logical framework with user-defined rewrite rules and a higher-order unification engine. This matters because emdash wants two things simultaneously:

- **Internal definitions**: a functor is not a meta-level function; it is an *object* of a functor category.
- **Computation**: categorical equalities are implemented as *rewrites on stable head symbols*, so they are available during typechecking.

In standard proof assistants you typically have:

- definitional equality: β/δ/ι/ζ reductions;
- propositional equality: theorems you rewrite with.

In emdash we deliberately push a large part of the “categorical equational theory” into definitional equality, using Lambdapi’s rewriting and (carefully!) its unification rules.

# 3. The kernel in one page: `Grpd`, `Cat`, and homs-as-categories

## 3.1 Two classifiers: groupoids vs directed structure

The kernel separates:

- `Grpd : TYPE` — codes for (∞-)groupoids (types with paths);
- `Cat : TYPE` — codes for (strict/lax) $\\omega$-categories.

Equality is valued in `Grpd` (so “paths form a groupoid”):

```lambdapi
constant symbol = : Π [a: Grpd], τ a → τ a → Grpd;
constant symbol eq_refl : Π [a: Grpd], Π x: τ a, τ (x = x);
symbol ind_eq : Π [a: Grpd], Π [x: τ a], Π [y: τ a], τ (x = y) → Π p: (τ a → Grpd), τ (p y) → τ (p x);
```

## 3.2 Objects are groupoidal

Every category has an object classifier:

```lambdapi
symbol Obj : Cat → Grpd;
```

This is an explicit design choice: object “equality” in a category is *not* a primitive directed notion; it is a path in the object groupoid.

## 3.3 Hom is recursive: homs are categories

Instead of `Hom_C(x,y)` being a set/type, in emdash it is a category:

```lambdapi
injective symbol Hom_cat : Π [A : Cat] (X_A Y_A : τ (Obj A)), Cat;
```

So a “1-cell” $f:x\\to y$ is an *object* of `Hom_cat C x y`. A “2-cell” between parallel 1-cells is then a 1-cell *in that hom-category*, etc. This is the standard globular iteration, but the rest of the paper emphasizes a *simplicial* reorganization of this data.

# 4. Functorial programming: functors and transfors as objects

## 4.1 Functors are objects of a functor category

For categories $A,B : \\texttt{Cat}$, the category of functors is `Functor_cat A B : Cat`.

```lambdapi
constant symbol Functor_cat : Π (A B : Cat), Cat;
symbol fapp0 : Π [A B : Cat], Π (F : τ (Obj (Functor_cat A B))), τ (Obj A) → τ (Obj B);
symbol fapp1_func : Π [A B : Cat], Π (F : τ (Obj (Functor_cat A B))),
  Π [X Y : τ (Obj A)],
  τ (Obj (Functor_cat (Hom_cat A X Y) (Hom_cat B (fapp0 F X) (fapp0 F Y))));
```

Here `fapp0` is the object action $F_0$, and `fapp1_func` is the induced functor on hom-categories $F_1$ (so it already “knows” about higher cells).

## 4.2 Stability by “rewrite heads”

In `emdash2.lp`, many operations are *declared* as symbols (not definitional abbreviations) so that rewrite rules can canonically fold large expressions into small stable heads. For example, applying `fapp1_func` and then `fapp0` is folded into a stable head `fapp1_fapp0`:

```lambdapi
symbol fapp1_fapp0 : Π [A B : Cat], Π (F : τ (Obj (Functor_cat A B))),
  Π [X Y : τ (Obj A)], Π (f : τ (Obj (Hom_cat A X Y))),
  τ (Obj (Hom_cat B (fapp0 F X) (fapp0 F Y)));
```

This “stable head discipline” is crucial for performance and for avoiding brittle matching against huge expanded terms.

## 4.3 Transfors (transformations) and components

Morphisms in a functor category are transfors (natural transformations / higher analogues). In emdash they live in a category `Transf_cat F G`. A key operation is component extraction: given $\\epsilon : F \\Rightarrow G$ and $Y \\in A$, we want a 1-cell
$$
\\epsilon_Y : \\mathrm{Hom}_B(FY, GY).
$$
In the kernel this is a *primitive head* `tapp0_fapp0` with rewrite rules connecting it to the internal packaging:

```lambdapi
symbol tapp0_fapp0 : Π [A B : Cat], Π [F G : τ (Obj (Functor_cat A B))],
  Π (Y : τ (Obj A)), Π (ϵ : τ (Obj (Transf_cat F G))),
  τ (Obj (Hom_cat B (fapp0 F Y) (fapp0 G Y)));
```

The philosophy is: *do not bake “components” into a record definition of transfors*. Instead, compute components by normalization of projection heads.

# 5. Dependent categories (`Catd`) and Grothendieck constructions

## 5.1 Displayed categories as isofibrations

The kernel has a classifier `Catd Z` of dependent categories over a base category $Z$ (intended to model isofibrations / displayed categories).

```lambdapi
constant symbol Catd : Π (Z : Cat), TYPE;
```

In the paper we write $E : \\texttt{Catd}\\;Z$ and read it as a fibration-like structure $p : \\int E \\to Z$ whose fibre over $z$ is a category $E[z]$.

## 5.2 The Grothendieck constructor as computation

For an honest Cat-valued functor $M : Z \\to \\mathbf{Cat}$, emdash provides a displayed category `Fibration_cov_catd M : Catd Z` (think “the Grothendieck construction” $\\int M$), and in this special case fibres compute definitionally:

```lambdapi
constant symbol Fibration_cov_catd : Π [Z : Cat], τ (Obj (Functor_cat Z Cat_cat)) → Catd Z;
```

This is the main place where the kernel commits to concrete computations for `Catd`: general displayed categories are abstract, but Grothendieck ones compute.

### Figure 1: Grothendieck morphisms lie over base arrows

<div class="arrowgram">
{
  "version": 1,
  "nodes": [
    { "name": "b",  "left": 140, "top": 80,  "label": "$b$" },
    { "name": "bp", "left": 460, "top": 80,  "label": "$b'$" },
    { "name": "be", "left": 140, "top": 240, "label": "$(b,e)$" },
    { "name": "bx", "left": 460, "top": 240, "label": "$(b',x)$" }
  ],
  "arrows": [
    { "from": "b",  "to": "bp", "label": "$f$" },
    { "from": "be", "to": "bx", "label": "$(f,\\sigma)$" },
    { "from": "be", "to": "b",  "label": "$p$", "style": { "body": { "name": "dashed" } } },
    { "from": "bx", "to": "bp", "label": "$p$", "style": { "body": { "name": "dashed" } } }
  ]
}
</div>

Here $(f,\\sigma)$ is the usual Grothendieck idea: a morphism in the total category contains a base arrow $f$ plus a fibre morphism $\\sigma$ with the correct transported source.

# 6. The dependent arrow/comma construction: `homd_cov` and `homd_cov_int`

This section is the technical center of the paper. It explains the kernel constructions that we use to model “cells over a base arrow” without starting from a raw globular presentation.

## 6.1 Classical picture: dependent hom / comma object

Let:

- $Z$ be a category,
- $E$ be a dependent category over $Z$ (morally $E : Z \\to \\mathbf{Cat}$),
- $W \\in Z$ be a chosen base object, and $w \\in E(W)$ be a chosen fibre object.

Given a base arrow $f : W \\to z$ and an object $x \\in E(z)$, we want the category of “arrows from the transport of $w$ along $f$ to $x$”. In textbook fibration language this is:
$$
\\mathrm{Hom}_{E(z)}(f_!w, x).
$$

This is a *dependent arrow category*: its objects are “triangles” with base edge $f$ and a displayed edge in the fibre.

## 6.2 What `homd_cov` computes (in the Grothendieck case)

The kernel symbol `homd_cov` is declared abstractly, but it has a key computation rule when the displayed categories involved are Grothendieck constructions. In words:

> if $E = \\int E_0$ and $D = \\int D_0$ are Grothendieck displayed categories, then `homd_cov` evaluated at a triple $(z,d,f)$ reduces to the hom-category in the fibre $E_0(z)$ from the transported $w$ to the image of $d$ under the displayed functor.

This is precisely the “dependent arrow/comma” intuition.

### Figure 2: a displayed arrow over a base arrow

<div class="arrowgram">
{
  "version": 1,
  "nodes": [
    { "name": "e",  "left": 120, "top": 80,  "label": "$e\\in E(b)$" },
    { "name": "x",  "left": 520, "top": 80,  "label": "$x\\in E(b')$" },
    { "name": "b",  "left": 120, "top": 240, "label": "$b$" },
    { "name": "bp", "left": 520, "top": 240, "label": "$b'$" }
  ],
  "arrows": [
    { "from": "b",  "to": "bp", "label": "$f$" },
    { "from": "e",  "to": "x",  "label": "$\\sigma : f_!e \\to x$", "curve": 40 },
    { "from": "e",  "to": "b",  "label": "$p$", "style": { "body": { "name": "dashed" } } },
    { "from": "x",  "to": "bp", "label": "$p$", "style": { "body": { "name": "dashed" } } }
  ]
}
</div>

The slogan is: *a 2-cell is a 1-cell in a dependent arrow category*.

## 6.3 The “more internal” pipeline: `homd_cov_int_base`

The file `emdash2.lp` contains a more internal version of the dependent hom construction, designed to be composed with other internal operations without exploding rewriting. It is built from stable-head building blocks (pointwise opposite, pointwise product, totalization, etc.). The key helper is:

```lambdapi
symbol homd_cov_int_base [Z : Cat] (D0 : τ (Obj (Functor_cat Z Cat_cat)))
  : τ (Obj (Functor_cat (Op_cat Z) Cat_cat));
```

Conceptually, `homd_cov_int_base D0` is a Cat-valued functor on $Z^{op}$ whose value at $z$ packages:

- a representable $\\mathrm{Hom}_Z(-,z)$ (built via `hom_cov_int` and then dualized),
- paired with the probe family $D0[z]$ (via `prodFib`),
- then “totalized” (via `Total_func`) so that later constructions can range over *base arrows* explicitly.

The point is not the exact combinatorics but the *shape*: we are building a simplicial indexing category (objects $z$ together with base edges into $z$) in a way that remains computationally stable.

<div class="mermaid">
flowchart LR
  Zop["Z^op"] --> H["representable (hom_cov_int)"]
  H --> Op["pointwise op (op_val_func)"]
  D0["probe D0: Z -> Cat"] --> Prod["pointwise product (prodFib)"]
  Op --> Prod
  Prod --> Tot["totalization (Total_func)"]
  Tot --> Base["homd_cov_int_base(D0): Z^op -> Cat"]
</div>

## 6.4 `homd_cov_int` as a displayed functor (current status)

The kernel exposes `homd_cov_int` as a displayed functor object (currently without computation rules). Informally it packages:

- a probe displayed category $\\int D0$,
- a displayed functor $FF : \\int D0 \\to E$,
- and returns a displayed functor over $E^{op}$ whose fibre over $(z,e)$ classifies arrows “from $e$ to $FF(d)$ over a base arrow”.

In the source:

```lambdapi
constant symbol homd_cov_int : Π [Z : Cat], Π [E : Catd Z],
  Π (D0 : τ (Obj (Functor_cat Z Cat_cat))),
  Π (FF : τ (Obj (Functord_cat (Fibration_cov_catd D0) E))),
  τ (Obj (Functord_cat (Op_catd E) ... ));
```

The important message for the reader is: *emdash organizes higher cells by iterating dependent arrow categories*; `homd_cov_int` is the internalized, compositional version of the triangle classifier.

# 7. From globes to simplices: triangles, surfaces, and “stacking”

Classically, $\\omega$-categories are presented globularly: $0$-cells, $1$-cells, $2$-cells between $1$-cells, etc. emdash keeps the globular core (homs are categories), but it tries to *use simplicial indexing for computation*:

- a 2-cell is a triangle over a base edge;
- a 3-cell is a tetrahedron over a base triangle;
- and so on.

The kernel contains the beginnings of this “simplicial engine”:

- `homd_cov` (triangle/surface classifier),
- and draft operations like `fdapp1_funcd` (dependent action on morphisms), intended to iterate the construction.

### Figure 3: a lax naturality triangle as a 2-cell over a base edge

<div class="arrowgram">
{
  "version": 1,
  "nodes": [
    { "name": "X", "left": 120, "top": 120, "label": "$X$" },
    { "name": "Y", "left": 420, "top": 120, "label": "$Y$" },
    { "name": "Z", "left": 270, "top": 320, "label": "$Z$" }
  ],
  "arrows": [
    { "from": "X", "to": "Y", "label": "$f$" },
    { "from": "Y", "to": "Z", "label": "$g$" },
    { "from": "X", "to": "Z", "label": "$g\\circ f$", "label_alignment": "left" },
    { "from": "X", "to": "Z", "label": "$\\alpha$", "style": { "mode": "arrow", "level": 2 }, "label_alignment": "over", "shift": 18 }
  ]
}
</div>

This is the common 2-categorical picture (a 2-cell between parallel composites). The kernel aim is to recover such cells as objects of a dependent hom construction, so that “stacking” and exchange laws can be derived from functoriality of the indexing.

# 8. Computational adjunctions: triangle identities as cut-elimination

The `emdash2.lp` file contains a draft interface for adjunctions inspired by Došen–Petrić’s proof-theoretic view of categories.

## 8.1 Adjunction data as first-class terms

An adjunction is represented by:

- categories $R,L$,
- functors $LAdj : R\\to L$ and $RAdj : L\\to R$,
- transfors (unit and counit)
  $$
  \\eta : \\mathrm{Id}_R \\Rightarrow RAdj\\circ LAdj,
  \\qquad
  \\epsilon : LAdj\\circ RAdj \\Rightarrow \\mathrm{Id}_L.
  $$

In the kernel this is a type former:

```lambdapi
constant symbol adj :
  Π [R L : Cat],
  Π (LAdj : τ (Obj (Functor_cat R L))),
  Π (RAdj : τ (Obj (Functor_cat L R))),
  Π (η : τ (Obj (Transf_cat (id_func R) (comp_cat_fapp0 RAdj LAdj)))),
  Π (ϵ : τ (Obj (Transf_cat (comp_cat_fapp0 LAdj RAdj) (id_func L)))),
  TYPE;
```

## 8.2 The triangle law as a rewrite rule

One of the most concrete successes of this approach is that a triangle identity can be oriented as a rewrite rule (“cut-elimination”). Very roughly (omitting indices), the rule has the shape:
$$
\\epsilon_f \\circ L(\\eta_g) \\;\\rightsquigarrow\\; f \\circ L(g).
$$

This matches the abstract’s goal: make the triangle identity a *definitional computation step* rather than a lemma.

### Figure 4: the familiar triangle identity (as reduction)

<div class="arrowgram">
{
  "version": 1,
  "nodes": [
    { "name": "LA",   "left": 120, "top": 160, "label": "$L(A)$" },
    { "name": "LRLA", "left": 330, "top": 80,  "label": "$L(R(L(A)))$" },
    { "name": "LA2",  "left": 540, "top": 160, "label": "$L(A)$" }
  ],
  "arrows": [
    { "from": "LA",   "to": "LRLA", "label": "$L(\\eta_A)$" },
    { "from": "LRLA", "to": "LA2",  "label": "$\\epsilon_{L(A)}$" },
    { "from": "LA",   "to": "LA2",  "label": "$\\mathrm{id}$", "style": { "body": { "name": "dashed" } }, "shift": 18 }
  ]
}
</div>

In `emdash2.lp` the rule is implemented at the level of the stable heads for composition (`comp_fapp0`), functor action on morphisms (`fapp1_fapp0`), and arrow-indexed transfor components (`tapp1_fapp0`). The result is that normalizing a composite term *performs* the triangle reduction.

## 8.3 Why the dependent arrow category matters for adjunctions

Adjunction identities are 2-dimensional: they compare composites of 2-cells (unit/counit whiskered by functors) with 1-cells. In an $\\omega$-setting, the correct statement is not only about components at identities (the $\\epsilon_{L(A)}\\circ L(\\eta_A)$ triangle), but also about how these components behave over non-identity base arrows.

This is exactly where the dependent arrow construction enters:

- it provides a place where “whiskering along a 1-cell” is represented as a displayed morphism over that 1-cell;
- it sets up the infrastructure needed for higher triangle/exchange laws as further normalizations.

The current kernel contains only the first cut-elimination rule, but it is designed to scale as the simplicial machinery (`homd_cov`, `fdapp1_funcd`, …) is completed.

# 9. Engineering notes: unification rules, rewrite hygiene, and timeouts

The file `emdash2.lp` contains extensive comments about “rewrite hygiene”. The short version is:

1. **Prefer stable heads**: introduce a named symbol (a rewrite head) for the normal form you want, and add a canonicalization rule folding big redexes into that head.
2. **Keep LHS implicit arguments minimal**: over-specifying implicit arguments in rule left-hand sides forces expensive conversion work and may cause timeouts.
3. **Use unification rules for inference, not computation**: when an equation is a *typing/elaboration hint* (e.g. identifying the component at an identity with the object-indexed component), encode it as `unif_rule` rather than `rule` to keep normal forms stable.

This is also why the repo’s recommended workflow uses short timeouts for typechecking: a hung typecheck is treated as a signal of a rewrite/unification loop.

# 10. Implementation status and roadmap (January 2026 snapshot)

The kernel is intentionally “small but sharp”. Some parts compute definitionally today; others are interfaces intended to be refined.

- **Computational today** (examples): opposites (`Op_cat`), products, Grothendieck fibres for `Fibration_cov_catd`, pointwise computation for `homd_cov` in the Grothendieck–Grothendieck case, pointwise component extraction for transfors (`tapp0_fapp0`), and a draft triangle cut-elimination rule for adjunctions.
- **Abstract / TODO** (examples): full computation rules for general displayed categories `E : Catd Z`, full simplicial iteration (`fdapp1_funcd` depends on more `homd_cov` infrastructure), and the user-facing surface syntax/elaboration layer (variance-aware binders, implicit coercions).

This division is deliberate: the kernel tries to avoid committing to heavy encodings (Σ-records for functors/transfors) until the rewrite story is stable.

# 11. Related ideas and influences

emdash draws on three complementary threads:

1. **Proof-theoretic categories** (Došen–Petrić): treat categorical equalities as cut-elimination / normalization steps.
2. **Type-theoretic higher categories** (e.g. Finster–Mimram): define weak $\\omega$-categories by internal type-theoretic structure.
3. **Parametricity-inspired internalization** (e.g. “bridge types”): avoid explicit interval objects while retaining internal reasoning principles reminiscent of parametricity.

Our distinctive emphasis is *computational organization of higher cells over base arrows* via a dependent arrow/comma construction inside a rewrite-based kernel.

# 12. Conclusion

emdash is an attempt to make a small computational kernel in which:

- higher categorical structure is *internal* (functors and transformations are first-class objects),
- equalities are *operational* (rewrite rules),
- and higher cells are organized *simplicially* via dependent arrow categories (`homd_cov`, `homd_cov_int`).

The most concrete result so far is a faithful computational core for (parts of) Grothendieck-style dependent categories and a first computational adjunction rule. The next step is to finish the simplicial iteration so that exchange/stacking laws and higher triangle identities can also become normalization steps.

# References (informal)

1. F. Blanqui et al. *The Lambdapi Logical Framework*.
2. K. Došen and Z. Petrić. *Cut-Elimination in Categories*.
3. E. Finster and S. Mimram. *A Type-Theoretical Definition of Weak $\\omega$-Categories*.
4. T. Altenkirch, Y. Chamoun, A. Kaposi, M. Shulman. *Internal Parametricity, without an Interval*.
5. H. Herbelin, R. Ramachandra. *Parametricity-based formalizations of semi-simplicial / semi-cubical structures*.

# Appendix A. Reading guide to the code (kernel identifiers → math)

- `Cat`, `Obj`, `Hom_cat`: category classifier, object groupoid, hom-category (iterated for higher cells).
- `Functor_cat`, `fapp0`, `fapp1_func`, `fapp1_fapp0`: functors as objects; object and hom action; stable-head application.
- `Transf_cat`, `tapp0_fapp0`, `tapp1_fapp0`: transfors; object-indexed and arrow-indexed components (lax naturality lives “off-diagonal”).
- `Catd`, `Fibre_cat`, `Functord_cat`: displayed categories (isofibrations); fibres; displayed functors over a fixed base.
- `Fibration_cov_catd`: Grothendieck construction $\\int M$ for $M:Z\\to\\mathbf{Cat}$ (this is where definitional computation for fibres exists).
- `hom_cov`, `hom_cov_int`: (co)representables / internalized hom functors.
- `homd_cov`: dependent arrow/comma construction (triangle classifier), with a computation rule in the Grothendieck case.
- `homd_cov_int_base`, `homd_cov_int`: internalized pipeline and displayed packaging for the same idea.
- `adj` and the triangle rewrite: adjunction data and (draft) cut-elimination rule.
