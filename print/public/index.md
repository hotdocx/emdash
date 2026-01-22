---
title: Functorial Programming for Strict/Lax $\omega$-Categories in Lambdapi
authors: m— / emdash project
---

# 1. Introduction

We report on an ongoing experiment, `emdash2.lp`, whose goal is a new **type-theoretical** definition of $\omega$-categories that is both **internal** (expressed inside dependent type theory) and **computational** (amenable to normalization by rewriting). 

The implementation target is the **Lambdapi** logical framework, and the broader methodological inspiration is the proof-theoretic viewpoint that categorical equalities should be presented as normalization steps ("cut-elimination"). In this sense, the Lambdapi specification itself acts as a small programming language and proof assistant for $\omega$-categories: the theory is formulated internally, and computations are performed by the rewrite engine.

Traditional approaches to higher category theory often flounder in the "coherence hell" of infinite hierarchies of equations (pentagons, hexagons, etc.). Our approach sidesteps this by adopting a **functorial programming** paradigm:
1.  We define 1-categorical structures (functors, natural transformations) as first-class citizens (objects in a "category of functors").
2.  We impose strict definitional equalities (via rewrite rules) for the 1-categorical layer.
3.  We represent higher weak structures (laxness) as *data* carried by the fibers of **dependent categories** (simplicial objects), rather than as properties.

# 2. The Internal Type Theory

The core of `emdash` is built on a few primitive classifiers (universes).

## 2.1 Universes: Grpd and Cat

We distinguish between "sets/types" and "categories":

*   `Grpd`: The classifier of $\infty$-groupoids (types). Equality types $x = y$ live here.

*   `Cat`: The classifier of $\omega$-categories.


Unlike standard set-theoretic foundations, objects of a category $C : Cat$ form a groupoid `Obj(C) : Grpd`, not a set. This reflects the $\infty$-categorical principle that one should never talk about equality of objects, only paths/isomorphisms.


The hom-structure is recursive:

$$

\text{Hom}_C(x, y) : \text{Cat}

$$

This means that for any two objects $x, y$, the collection of arrows between them is itself an $\omega$-category.



```lambdapi

// Core primitives in emdash2.lp

constant symbol Cat : TYPE;

symbol Obj : Cat → Grpd;



// Hom-categories are categories themselves (recursive)

symbol Hom_cat : Π [C : Cat] (X Y : Obj C), Cat;



// 1-cells are objects of the Hom-category

// f : x → y

symbol f : Obj (Hom_cat C x y);

```


A 2-cell $\alpha : f \Rightarrow g$ is an object of the hom-category of the hom-category, and so on.


## 2.2 Functors as First-Class Objects

A functor $F : A \to B$ is not a meta-level map, but an object of the functor category:

$$

F : \text{Obj}(\text{Functor\_cat}(A, B))

$$

Its action on objects ($F_0$) and homs ($F_1$) are derived operations `fapp0` and `fapp1`.



```lambdapi

// Functor category classifier

symbol Functor_cat (A B : Cat) : Cat;



// Application on objects (F_0)

symbol fapp0 : Functor_cat A B → Obj A → Obj B;



// Application on homs (F_1) - returns a functor between hom-categories

symbol fapp1 : Π (F : Functor_cat A B) (x y : Obj A),

  Functor_cat (Hom_cat A x y) (Hom_cat B (F x) (F y));

```


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
    { "from": "A", "to": "C", "label": "G \\circ F" }
  ]
}
</div>

Crucially, composition is strict: $G \circ F$ is defined by a rewrite rule such that $(G \circ F)(x)$ definitionally reduces to $G(F(x))$. This strictness at the 1-cell level provides a rigid skeleton upon which weak higher structures can hang.

# 3. Displayed Categories and Simplicial Nerves

To handle higher dimensions without explicit globular coordinates, we use **Dependent Categories** (also known as Displayed Categories or Fibrations).

A dependent category $E$ over a base $Z$ (denoted $E : \text{Catd}(Z)$) can be thought of as a family of categories indexed by $Z$, or geometrically, as a bundle $E \to Z$.

## 3.1 The Grothendieck Construction
The bridge between the internal world (functors $Z \to Cat$) and the external world (fibrations) is the Grothendieck construction.
Given a functor $M : Z \to Cat$, we construct a displayed category $\int M : Catd(Z)$.
*   **Fibre**: The category over an object $z : Z$ is simply $M(z)$.
*   **Total Space**: The total category $\text{Total\_cat}(\int M)$ has pairs $(z, u)$ as objects, where $u \in M(z)$.

<div class="arrowgram">
{
  "version": 1,
  "nodes": [
    { "name": "Total", "left": 300, "top": 100, "label": "$\\int M$" },
    { "name": "Base", "left": 300, "top": 300, "label": "Z" },
    { "name": "Fibre", "left": 500, "top": 200, "label": "M(z)" }
  ],
  "arrows": [
    { "from": "Total", "to": "Base", "label": "$\\pi$", "style": { "head": { "name": "maps_to" } } },
    { "from": "Fibre", "to": "Total", "label": "incl", "style": { "body": { "name": "dashed" }, "head": { "name": "hook" } } }
  ]
}
</div>

## 3.2 The Simplicial Core: Dependent Hom
The central innovation in `emdash` is the **dependent hom** construction, `homd_cov`. Instead of postulating globular cells directly, we construct them simplicially.

Given a base category $Z$ and a displayed category $E$ over it, we define a "triangle classifier". For a base arrow $f : x \to y$ and a fibre object $u \in E(x)$, we form a category of "morphisms over $f$ starting from $u$".

$$ 

\text{Homd}_E(u, -) : E \times (\text{Hom}_Z(x, -))^{\text{op}} \longrightarrow \text{Cat} 

$$ 

This structure classifies **2-simplices** (triangles). By iterating this construction, we obtain higher simplices. A 2-cell is not a globe, but a section of this dependent hom fibration.

```lambdapi
// The "Dependent Hom" / Simplicial Nerve construction
// Classifies "triangles" over a base arrow f: x → y
symbol homd_cov : Π [Z : Cat] [E : Catd Z]
  (u : Fibre_cat E x)     // Source object in fibre
  (D : Catd Z)            // Another displayed category (often E)
  (FF : Functord_cat D E) // Displayed functor (often id)
  → Functor_cat ... Cat_cat; // Returns a Cat-valued functor
```

<div class="arrowgram">{
  "version": 1,
  "nodes": [
    { "name": "X", "left": 200, "top": 100, "label": "x" },
    { "name": "Y", "left": 400, "top": 100, "label": "y" },
    { "name": "Z", "left": 300, "top": 300, "label": "z" }
  ],
  "arrows": [
    { "from": "X", "to": "Y", "label": "f" },
    { "from": "Y", "to": "Z", "label": "g" },
    { "from": "X", "to": "Z", "label": "h", "label_alignment": "left" }
  ]
}
</div>

In the diagram above, the "dependent hom" construction allows us to define the space of "fillers" (2-cells) $\alpha : g \circ f \Rightarrow h$ as objects in a specific fibre.

# 4. Transfors and Lax Naturality

We use the term **Transfor** (from "Transformation/Functor") to encompass natural transformations, modifications, and higher mappings.

In `emdash`, a transfor $\epsilon : F \Rightarrow G$ is an object of `Transf_cat(F, G)`. Its components are extracted computationally:
1.  **Project to Functor**: We view $\epsilon$ as a dependent functor $\epsilon^X : \text{Hom}(X, -) \to \text{Hom}(FX, G-)$.
2.  **Evaluate**: We evaluate this functor at the identity $id_X$ to get the 1-cell component $\epsilon_X : FX \to GX$.

## 4.1 Lax Squares
Crucially, because we work with $\omega$-categories, naturality is **lax**. The square does not commute on the nose; there is a non-trivial 2-cell filling it.

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
    { "from": "FX", "to": "GY", "label": "$\\alpha$", "style": { "mode": "arrow", "body": { "name": "none" }, "level": 2 }, "label_alignment": "over" }
  ]
}
</div>

This 2-cell $\alpha$ (the "laxness witness") is carried by the higher structure of the transfor object. In the strict case, we can impose rewrite rules that force $\alpha$ to be an identity.

# 5. Adjunctions as Computation

Following the philosophy of Došen and Petrić, we treat adjunctions not just as properties but as computational reductions. 

The triangle identities of an adjunction $(L \dashv R, \eta, \epsilon)$ are oriented as **cut-elimination** rules:

$$ 

\epsilon_{L(A)} \circ L(\eta_A) \rightsquigarrow id_{L(A)} 

$$ 

In `emdash`, these are implemented as rewrite rules on the composition of the relevant transfor components. This means that large diagrams involving adjoints can be simplified automatically by the type checker.

<div class="arrowgram">
{
  "version": 1,
  "nodes": [
    { "name": "LA", "left": 100, "top": 200, "label": "L(A)" },
    { "name": "LRLA", "left": 300, "top": 100, "label": "L(R(L(A)))" },
    { "name": "LA2", "left": 500, "top": 200, "label": "L(A)" }
  ],
  "arrows": [
    { "from": "LA", "to": "LRLA", "label": "L(\\eta_A)" },
    { "from": "LRLA", "to": "LA2", "label": "$\\epsilon_{L(A)}$" },
    { "from": "LA", "to": "LA2", "label": "id", "style": { "body": { "name": "dashed" } }, "shift": 20 }
  ]
}
</div>

# 6. Implementation Status

The current kernel (`emdash2.lp`) successfully implements:
*   The hierarchy of universes (`Grpd`, `Cat`).
*   Strict functor categories with definitional composition.
*   The Grothendieck construction for displayed categories.
*   The simplicial "dependent hom" packaging (`homd_cov`).
*   Pointwise computation of transfor components.

Work is ongoing to fully implement the **Univalence Bridge**, which relates the path groupoid in `Obj(C)` to the equivalence 1-cells in `Hom(C)`. This will allow the system to treat "equality of objects" as "isomorphism" in a fully mechanized way.

# 7. Conclusion

`emdash` represents a shift from "checking" category theory to "running" it. By embedding the rules of $\omega$-categories into the computational core of a logical framework, we move closer to the dream of an AI assistant that can not only verify categorical proofs but actively construct them through normalization.

Future work targets the full mechanization of a basic category theory textbook, with the "simplicial nerve" approach providing a robust foundation for the weak higher structures that usually make such a task impossible.
