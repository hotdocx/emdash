---
title: Functorial Programming for Strict/Lax $\omega$-Categories in Lambdapi
authors: m— / emdash project
---

# Abstract

We report on an ongoing experiment, `emdash`, whose goal is a new **type-theoretical** definition of $\omega$-categories that is both **internal** (expressed inside dependent type theory) and **computational** (amenable to normalization by rewriting). The implementation target is the **Lambdapi** logical framework, and the broader methodological inspiration is the proof-theoretic viewpoint that categorical equalities should be presented as normalization steps ("cut-elimination"). In this sense, the Lambdapi specification itself behaves like a small programming language and proof assistant for $\omega$-categories: the theory is formulated internally, and computations are performed by normalization; what remains is chiefly elaboration and user-facing syntax.

# 1. Introduction

The formalization of higher category theory is notoriously difficult. Traditional approaches often flounder in the "coherence hell" of infinite hierarchies of equations (pentagons, hexagons, and beyond). When defining weak $\omega$-categories, one must typically postulate an infinite set of coherence cells and equations governing them. In a standard proof assistant, managing these hierarchies manually is intractable.

Our approach, implemented in the `emdash2.lp` kernel, sidesteps this by adopting a **functorial programming** paradigm. Instead of building categories out of raw sets and imposing axioms, we define a universe of categories where the primary objects of study are **functors** and **transformations** (transfors).

The key design choices are:
1.  **Internalization**: We do not define "a category" as a structure *within* a type theory (like a record of sets and functions). Instead, we define a universe `Cat` *of* categories.
2.  **Strict 1-Skeleton**: We impose **strict** definitional equalities for the 1-categorical layer (functor composition is associative on the nose). This provides a rigid scaffold.
3.  **Weakness via Fibrations**: We represent higher weak structures (laxness) not as properties, but as *data* carried by the fibers of **dependent categories** (simplicial objects).
4.  **Computation**: We use the rewriting engine of Lambdapi to operationalize categorical equalities. For instance, the triangle identities of an adjunction are not axioms to be proved, but reduction rules that simplify terms.

This paper outlines the type-theoretic foundations of `emdash`, the simplicial mechanism for higher cells ("dependent homs"), and the computational treatment of adjunctions.

# 2. The Internal Type Theory

The core of `emdash` is built on a few primitive classifiers (universes). We distinguish sharply between "types/sets" (which form $\infty$-groupoids) and "directed categories".

## 2.1 Universes: Grpd and Cat

We posit two universes:
*   `Grpd`: The classifier of $\infty$-groupoids (types). This is where "equality" lives.
*   `Cat`: The classifier of $\omega$-categories.

Crucially, the "objects" of a category $C$ do not form a Set, but a Groupoid.

```lambdapi
constant symbol Cat : TYPE;
symbol Obj : Cat → Grpd;
```

This reflects the $\infty$-categorical principle that one should never talk about equality of objects, only paths or isomorphisms. If $x, y$ are objects of $C$, the type $x = y$ is a path in `Grpd`.

## 2.2 Recursive Hom-Structure

The hom-structure is recursive. For any category $C$ and objects $x, y$, the collection of arrows between them is itself an $\omega$-category:

$$ 
\text{Hom\\_cat}\_C(x, y) : \text{Cat} 
$$ 

A 1-cell $f : x \to y$ is an object of this hom-category. A 2-cell $\alpha : f \Rightarrow g$ is an object of the hom-category of the hom-category, $\text{Hom}\_\text{Hom}(x,y)(f, g)$, and so on. This inductive definition naturally captures the globular structure of $\omega$-categories, though as we shall see, we essentially treat them simplicially using dependent sums.

## 2.3 Functors as First-Class Citizens

In `emdash`, a functor is not a meta-level map between types. It is an object of a dedicated functor category.

$$ 
F : \text{Obj}(\text{Functor\\_cat}(A, B)) 
$$ 

The application of a functor to objects ($F_0$) and homs ($F_1$) are derived operations, `fapp0` and `fapp1`.

<div class="arrowgram">
{
  "version": 1,
  "nodes": [
    { "name": "A", "left": 150, "top": 150, "label": "A" },
    { "name": "B", "left": 450, "top": 150, "label": "B" },
    { "name": "C", "left": 300, "top": 350, "label": "C" }
  ],
  "arrows": [
    { "from": "A", "to": "B", "label": "F" },
    { "from": "B", "to": "C", "label": "G" },
    { "from": "A", "to": "C", "label": "G $\\circ$ F" }
  ]
}
</div>

By using rewrite rules, we enforce strictness at the 1-categorical level. The composition $G \circ F$ is defined such that its action on an object $x$ reduces definitionally:

$$ (G \circ F)(x) \hookrightarrow G(F(x)) 
$$ 

This eliminates the need to carry "associators" for 1-cell composition, significantly simplifying the higher coherence handling.

# 3. Dependent Categories: The Simplicial Engine

To handle higher dimensions without getting lost in globular coordinates, we rely heavily on **Dependent Categories** (also known as Displayed Categories or Fibrations). This is the "simplicial engine" of `emdash`.

A dependent category $E$ over a base $Z$ (denoted $E : \text{Catd}(Z)$) can be thought of as a family of categories indexed by $Z$. Geometrically, it is a bundle $p: E \to Z$.

## 3.1 The Grothendieck Construction

The bridge between the internal world (functors $Z \to \text{Cat}$) and the external world (fibrations) is the Grothendieck construction. Given a functor $M : Z \to \text{Cat}$, we construct a displayed category $\int M$.

*   **Fibre**: The category over an object $z : Z$ is definitionally $M(z)$.
*   **Total Space**: The total category $\text{Total\\_cat}(\int M)$ has pairs $(z, u)$ as objects, where $u \in \text{Obj}(M(z))$.

<div class="arrowgram">
{
  "version": 1,
  "nodes": [
    { "name": "Total", "left": 300, "top": 100, "label": "$\\int M$" },
    { "name": "Base", "left": 300, "top": 300, "label": "Z" },
    { "name": "Fibre", "left": 500, "top": 200, "label": "M(z)" }
  ],
  "arrows": [
    { "from": "Total", "to": "Base", "label": "$\\pi$", "style": { "tail": { "name": "maps_to" } } },
    { "from": "Fibre", "to": "Total", "label": "incl", "style": { "body": { "name": "dashed" }, "tail": { "name": "hook" } } }
  ]
}
</div>

The morphism structure in the total category is what gives us the simplicial "shape". A morphism in $\int M$ from $(x, u)$ to $(y, v)$ lying over $f : x \to y$ corresponds to a morphism in the fibre $M(y)$:
$$ 
\alpha : M(f)(u) \longrightarrow v 
$$ 
Here, $M(f)(u)$ represents the transport of $u$ along $f$.

## 3.2 The Dependent Hom (`homd_cov`)

The central innovation in `emdash` for representing higher cells is the **dependent hom** construction, `homd_cov`.

In a simplicial set, a 2-simplex is a triangle bounded by three edges ($f, g, h$) and filled by a surface. In `emdash`, we internalize this via a classifier for "morphisms over a base arrow".

Given:
*   A base category $Z$ (often itself a total category of a lower dimension).
*   A base arrow $f : x \to y$ in $Z$.
*   A displayed category $E$ over $Z$.
*   A starting object $u$ in the fibre $E(x)$.

We construct a functor (which classifies the fibre categories):
$$ 
\text{homd\\_cov}(u) : \text{Hom}\_Z(x, -) \longrightarrow \text{Cat} 
$$ 

The value of this functor at a target object $z$ and an arrow $g : x \to z$ is the category of "lifts of $g$ starting at $u$". More specifically, it classifies triangles.

```lambdapi
constant symbol homd_cov : Π [Z : Cat], Π [E : Catd Z], Π [W_Z : τ (Obj Z)] ...
```

This construction is iterated. A 2-cell $\alpha: f \Rightarrow g$ is not a primitive "globe"; it is a section of this dependent hom fibration.

<div class="arrowgram">
{
  "version": 1,
  "nodes": [
    { "name": "X", "left": 200, "top": 100, "label": "x" },
    { "name": "Y", "left": 400, "top": 100, "label": "y" },
    { "name": "Z", "left": 300, "top": 300, "label": "z" }
  ],
  "arrows": [
    { "from": "X", "to": "Y", "label": "f" },
    { "from": "Y", "to": "Z", "label": "g" },
    { "from": "X", "to": "Z", "label": "h", "label_alignment": "left" },
    { "from": "X", "to": "Z", "label": "$\\alpha$", "style": { "mode": "arrow", "level": 2 }, "label_alignment": "over", "shift": 15 }
  ]
}
</div>

By taking the Grothendieck construction of `homd_cov`, we effectively build the "space of triangles" over the base category. A section of this bundle picks out a consistent choice of 2-cells.

# 4. Transfors and Lax Naturality

We use the term **Transfor** (from "Transformation/Functor") to encompass natural transformations, modifications, and higher mappings.

In `emdash`, a transfor $\epsilon : F \Rightarrow G$ is an object of `Transf_cat(F, G)`. Its components are extracted computationally via a "projection and evaluation" strategy.

1.  **Project to Dependent Functor**: We view $\epsilon$ as a dependent functor parameterized by an external index $X$.
    $$ 
    \epsilon^X : \text{Hom}\_A(X, -) \longrightarrow \text{Hom}\_B(FX, G(-)) 
    $$ 
2.  **Evaluate**: We evaluate this functor at the identity $id_X$ to get the 1-cell component $\epsilon_X : FX \to GX$.

## 4.1 Lax Squares

Crucially, because we work with $\omega$-categories, naturality is **lax**. The square formed by a 1-cell $f: X \to Y$ does not commute on the nose. Instead, there is a non-trivial 2-cell filling it.

<div class="arrowgram">
{
  "version": 1,
  "nodes": [
    { "name": "FX", "left": 200, "top": 200, "label": "FX" },
    { "name": "GX", "left": 400, "top": 200, "label": "GX" },
    { "name": "FY", "left": 200, "top": 400, "label": "FY" },
    { "name": "GY", "left": 400, "top": 400, "label": "GY" }
  ],
  "arrows": [
    { "from": "FX", "to": "GX", "label": "$\\epsilon_X$" },
    { "from": "FX", "to": "FY", "label": "Ff", "label_alignment": "left" },
    { "from": "GX", "to": "GY", "label": "Gf" },
    { "from": "FY", "to": "GY", "label": "$\\epsilon_Y$", "style": { "head": { "side": "top" } } },
    { "from": "FX", "to": "GY", "label": "$\\alpha$", "style": { "mode": "arrow", "level": 2 }, "label_alignment": "over" }
  ]
}
</div>

This 2-cell $\alpha$ (the "laxness witness") is carried by the higher structure of the transfor object. In the strict case, we can impose rewrite rules that force $\alpha$ to be an identity, but the framework is designed to handle the general lax case natively.

# 5. Adjunctions as Computation

Following the philosophy of Došen and Petrić, we treat adjunctions not just as properties but as computational reductions. The triangle identities of an adjunction $(L \dashv R, \eta, \epsilon)$ are oriented as **cut-elimination** rules.

Consider the unit-counit equation:
$$ 
\epsilon_{L(A)} \circ L(\eta_A) = id_{L(A)} 
$$ 

In `emdash`, we implement this as a rewrite rule on the stable head symbols for composition and transfor application.

$$ 
\epsilon_{L(A)} \circ L(\eta_A) \rightsquigarrow id_{L(A)} 
$$ 

<div class="arrowgram">
{
  "version": 1,
  "nodes": [
    { "name": "LA", "left": 100, "top": 200, "label": "L(A)" },
    { "name": "LRLA", "left": 300, "top": 100, "label": "L(R(L(A)))" },
    { "name": "LA2", "left": 500, "top": 200, "label": "L(A)" }
  ],
  "arrows": [
    { "from": "LA", "to": "LRLA", "label": "$L(\\eta_A)$" },
    { "from": "LRLA", "to": "LA2", "label": "$\\epsilon_{L(A)}$" },
    { "from": "LA", "to": "LA2", "label": "id", "style": { "body": { "name": "dashed" } }, "shift": 20 }
  ]
}
</div>

This approach has profound implications for the automation of category theory. Large diagrams involving adjoints can often be simplified automatically by the type checker simply by normalizing the term. The user does not need to manually apply the triangle identities; the system "computes" the simplified form.

# 6. The Univalence Bridge

One of the most challenging aspects of type-theoretic category theory is the treatment of "equality of objects". In `emdash`, we enforce a strict discipline:
*   **Paths**: Equality in `Obj(C)` is a path in the groupoid `Obj(C)`.
*   **Equivalences**: Isomorphism in `C` is a structure in `Hom_cat(C)`.

We are developing a **Univalence Bridge** to connect these two concepts without inducing rewrite loops (a common peril when equating paths and equivalences).

We define a canonical map from paths to equivalences (the "rewrite" direction, $\beta$):
```lambdapi
constant symbol univ_equiv_of_path : Π [C : Cat], Π (x y : τ (Obj C)),
  Π (p : τ (x = y)),
  τ (Obj (@Fibre_cat (@Hom_cat C x y) (isEquiv x y) (@path_to_hom_fapp0 C x y p)));
```

And we use **unification rules** to guide the system in the reverse direction (the "inference" direction, $\eta$), treating equivalences as paths during elaboration where safe.

```lambdapi
// Unification hint
unif_rule @univ_path_of_equiv $C $x $y $f $w ≡ $p
  ↪ [ $f ≡ @path_to_hom_fapp0 $C $x $y $p;
      $w ≡ @univ_equiv_of_path $C $x $y $p ];
```

This ensures that we can "prove" univalence constructively without getting stuck in infinite reduction cycles in the kernel.

# 7. Implementation Status

The current kernel (`emdash2.lp`) successfully implements:
*   The hierarchy of universes (`Grpd`, `Cat`).
*   Strict functor categories with definitional composition.
*   The Grothendieck construction for displayed categories.
*   The simplicial "dependent hom" packaging (`homd_cov`).
*   Pointwise computation of transfor components.
*   Prototype strictness rules for functors (preserving `id` and `comp` on the nose).

The next phase of development focuses on the `Path_cat` infrastructure—treating discrete groupoids as full $\omega$-categories—and populating the `isEquiv` witnesses with higher coherent data.

# 8. Conclusion

`emdash` represents a shift from "checking" category theory to "running" it. By embedding the rules of $\omega$-categories into the computational core of a logical framework, we move closer to the dream of an AI assistant that can not only verify categorical proofs but actively construct them through normalization.

Future work targets the full mechanization of a basic category theory textbook, with the "simplicial nerve" approach providing a robust foundation for the weak higher structures that usually make such a task impossible.