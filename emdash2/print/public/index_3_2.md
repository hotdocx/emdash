---
title: emdash — Functorial programming for ω-categories in Lambdapi (v3.2 arrow induction, profunctors, and weighted limits)
authors: https://github.com/hotdocx/emdash
---

# Abstract

We present the v3.2 architecture of **emdash**, a Lambdapi specification for a
programming language and prototype proof assistant for strict/lax higher
$\\omega$-categorical structure. The development is fully internalized in
dependent type theory and computational in the proof-theoretic sense:
structural categorical equalities are oriented as normalization, or
cut-elimination, steps.

The basic construction is the directed dependent hom. For a category-valued
family $E : K \\vdash \\mathbf{Cat}$, where $\\vdash$ denotes a functor
category, and fixed data $x : K$ and $u \\in E[x]$, emdash forms a functorial
object

$$
\\mathrm{homd}_E(x,u)
  : \\prod_{y : K^{\\mathrm{op}}}
      \\bigl(E[y^-] \\vdash_{[y]}
        (\\mathrm{Hom}_K(x,y)^{\\mathrm{op}} \\vdash \\mathbf{Cat})\\bigr)
$$

Here $\\vdash_{[y]}$ is the mixed-variance displayed version of $\\vdash$, and
$y^-$ marks that the $E$-argument occurs contravariantly. At a fixed $y$, its
value at $v \\in E[y]$ and $f : x \\to y$ is

$$
\\mathrm{homd}_E(x,u)[y][v][f]
  =
\\mathrm{Hom}_{E[y]}(E[f](u),v).
$$

This is the construction that organizes arrows in Sigma totals:

$$
\\mathrm{Hom}_{\\Sigma E}((x,u),(y,v))
  =
\\Sigma_{f : x \\to y}\\,\\mathrm{Hom}_{E[y]}(E[f](u),v).
$$

The same normalization-first architecture drives this simplicial
$\\omega$-iteration and also covers product/curry structure, computational
adjunctions, structural operations such as weakening/symmetry/contraction, and
ordinary hom-action cut elimination. In the current v3.2 kernel it also
supports a symbolic but checked calculus of Cat-valued profunctors:
representables, reindexing, tensor, co-Yoneda maps, covariant and
contravariant internal homs, weighted limits as representability, preservation
of weighted limits by right adjoints, the dual preservation theorem for left
adjoints and weighted colimits, and a primitive directed-inductive join
category.

The motivating example is the familiar shape of path induction in dependent
type theory, now directed. For a category $Z$ and an object $x : Z$, emdash
uses the outgoing-arrow category, i.e. the coslice/undercategory

$$
\\mathrm{PathOut}_Z(x)
  \\coloneqq x \\downarrow Z
  \\coloneqq
\\Sigma_{y : Z}\\,\\mathrm{Hom}_Z(x,y).
$$

The object $\\iota_x = (x,\\mathrm{id}_x)$ is initial in
$\\mathrm{PathOut}_Z(x)$. For $a = (y,p)$, the canonical arrow
$\\iota_x \\to a$ is the arrow $p$ itself; when a reusable name is needed, we
write it as

$$
\\rho^x_a : \\iota_x \\to a.
$$

Thus, for a motive $E : \\mathrm{PathOut}_Z(x) \\vdash \\mathbf{Cat}$ and
$u \\in E(\\iota_x)$, fixed-source directed induction gives the section

$$
\\mathrm{Ind}_x(E,u)
  : \\prod_{a : \\mathrm{PathOut}_Z(x)} E(a),
\\qquad
\\mathrm{Ind}_x(E,u)(a) = E(\\rho^x_a)(u).
$$

Write $\\mathrm{Rep}_Z(t)$ for the covariant representable
$\\mathrm{Hom}_Z(t,-)$. For the composition motive

$$
E[(y,p)] := \\mathrm{Rep}_Z(y) \\vdash \\mathrm{Rep}_Z(x),
$$

with initial datum $\\mathrm{id} : \\mathrm{Rep}_Z(x) \\vdash
\\mathrm{Rep}_Z(x)$, this computes to ordinary composition:

$$
\\mathrm{Ind}_x(E,\\mathrm{id})[(y,p)][z][q]
  \\rightsquigarrow q \\circ p.
$$

The latest runtime owner for this benchmark is the hom-action normal form
`hom_postcomp_fapp0(id_Z,q,p)`. The ordinary composite `comp_fapp0(q,p)` is
still available as the typed categorical view; the distinction is one example
of the v3.2 boundary between runtime cut-elimination heads and proof-time
convertibility surfaces.

The new phenomenon appears when the source object $x$ itself is internalized.
For an arrow $r : x \\to y$, precomposition gives

$$
\\mathrm{PathOut}_Z(r) : \\mathrm{PathOut}_Z(y) \\vdash
\\mathrm{PathOut}_Z(x),
\\qquad
\\mathrm{PathOut}_Z(r)(z,q : y \\to z) = (z,q \\circ r).
$$

Once induction is internalized as a construction varying in $x$, the target
section-taking construction

$$
x \\mapsto
\\left(E \\mapsto \\prod_{a : \\mathrm{PathOut}_Z(x)} E(a)\\right)
$$

is itself displayed over the moving source object. Its transport/comparison
along $r$ is not the identity; it is the section-pullback functor

$$
\\prod_{a : \\mathrm{PathOut}_Z(x)} E(a)
  \\vdash
\\prod_{b : \\mathrm{PathOut}_Z(y)}
  E(\\mathrm{PathOut}_Z(r)(b)),
\\qquad
s \\mapsto \\bigl(b \\mapsto s(\\mathrm{PathOut}_Z(r)(b))\\bigr).
$$

This is the lax naturality/functoriality layer exposed by the internalized
formulation of directed path induction; the Lambdapi kernel packages the
source-indexed theorem as `PathInd_transfd(Z)`.

The profunctor part of the development follows the same rule. A weighted-limit
theorem is not represented as a single propositional statement detached from
computation. It is a comparison object whose push/pull operations act on
arbitrary incoming profunctor maps and cancel by normalization. This is how the
formalization proves that right adjoints preserve Cat-valued weighted limits,
and how the dual left-adjoint colimit theorem is obtained by opposite
normalization.

# Contents

| Section | Title |
| --- | --- |
| Abstract | Summary of the v3.2 architecture and main checked computations |
| 1 | Introduction |
| 1.1 | What v3.2 Contributes |
| 1.2 | Road Map |
| 1.3 | What "Checked" Means |
| 2 | A Type-Theoretic Foundation For Directed Families |
| 3 | Dependent Hom, Sigma Totals, And Sections |
| 3.1 | Sigma Totals |
| 3.2 | Pi Sections |
| 4 | Outgoing Arrows And The Canonical `rho` Arrow |
| 5 | Arrow Induction |
| 5.1 | The Telescope Theorem |
| 5.2 | The Derived Sigma-Total Presentation |
| 6 | Strictness, Laxity, And Directed Induction |
| 7 | Composition As The Main Computation |
| 8 | Surface Syntax And Kernel Names |
| 9 | Computational Method And Checked Evidence |
| 10 | Cat-Valued Profunctors And Representables |
| 11 | Tensor, Co-Yoneda, And Internal Hom |
| 12 | Weighted Limits, Adjunctions, And Duality |
| 13 | Directed-Inductive Join Categories |
| 14 | Equality, DefIso, And Normalization Boundaries |
| 15 | Formal Artifact And Validation |
| 16 | Conclusion |
| Appendix A | Identifier Glossary |
| Appendix B | Selected Checked Normal Forms |
| Appendix C | Diagram Source Notes |

# 1. Introduction

Higher category theory is hard to mechanize because coherence is not a small
side condition. Every definition carries functoriality, naturality, and
higher-dimensional compatibility data. In ordinary mathematical prose, much of
this data disappears into phrases such as "by functoriality" or "by
naturality." In a proof assistant, those phrases either become explicit proof
terms or they must compute.

The emdash design chooses the second option whenever the equation is structural
enough to be part of the computational theory. Categories, functors,
transformations, category-valued families, dependent sums, dependent products,
and dependent homs are internal objects of the Lambdapi specification.
Coherence facts are oriented as rewrite and unification rules with stable
normal forms.

This paper explains the v3.2 development for a reader who knows dependent type
theory or HoTT, but not the emdash codebase. The central claim is:

```text
category-theoretic arrow induction can be expressed as a computational theorem.
```

The word "arrow" is important. The theorem is not HoTT identity elimination
for paths in a type. It is an induction principle for outgoing directed arrows
inside a category. The construction resembles path induction because every
outgoing arrow $p : x \\to y$ has a canonical comparison from the reflexive
outgoing arrow $(x,\\mathrm{id}_x)$ to $(y,p)$, but that comparison lives in a
Sigma category of arrows, not in an identity type.

## 1.1 What v3.2 Contributes

The v3.2 article focuses on eight checked contributions.

1. **Directed dependent homs.** Homs in total categories and section actions
   are organized by one dependent-hom construction over a base arrow.
2. **Outgoing-arrow categories.** For each object $x : Z$,
   $\\mathrm{PathOut}_Z(x)$ is the Sigma total of the representable family
   $\\mathrm{Hom}_Z(x,-)$.
3. **Synthetic arrow induction.** For
   `x :^n Z ; E :^n (PathOut_Z(x) ⊢ Cat)`, the checked construction has type
   `E[(x,id_x)] ⊢ Π (q :^n PathOut_Z(x)), E[q]`; the kernel packages the
   source-indexed telescope as `PathInd_transfd(Z)`.
4. **Strict and lax directed transport.** General displayed functors carry
   computable transport-comparison cells over base arrows; strict or cartesian
   constructors, including representable precomposition, collapse those cells
   to canonical identities.
5. **Computational composition.** The transitivity benchmark reduces a fully
   expanded path-induction expression to $q \\circ p$. Runtime computation
   exposes the reusable hom-action owner `hom_postcomp_fapp0(id_Z,q,p)`, while
   a typed proof-time view records the ordinary composite `comp_fapp0(q,p)`.
6. **Cat-valued profunctors.** The kernel has a checked facade for
   `Prof(A,B) = A^op × B ⊢ Cat`, representables, reindexing, shaped cells, and
   shaped elements.
7. **Tensor, co-Yoneda, and internal hom.** A symbolic tensor and fixed
   covariant/contravariant implication cores support eval/lambda cancellation,
   fixed co-Yoneda beta/fusion, and functorial fixed-endpoint tensor action.
8. **Weighted limits, duality, and directed induction.** Weighted limits are
   implemented as computational profunctor representability; right adjoints
   preserve them by composing comparisons, left adjoints preserve the dual
   weighted colimits by opposite normalization, and `Join_cat` checks a
   primitive directed-inductive recursor with an internally natural cross cell.

## 1.2 Road Map

The paper has two connected layers. The first layer, Sections 2-9, develops
the directed-family calculus far enough to state and check arrow induction.
Section 2 fixes the basic directed type-theoretic reading of categories,
functors, category-valued families, and section categories. Section 3 explains
dependent homs, Sigma totals, and Pi sections, which are the structural
ingredients used by outgoing-arrow categories. Section 4 defines
`PathOut_Z(x)` and the canonical `rho` arrow. Section 5 packages fixed-source,
source-indexed, and Sigma-total arrow induction. Section 6 explains where
strict and lax transport enter the theorem. Section 7 gives the main
normalization benchmark: applying arrow induction to the composition motive
computes to categorical composition. Sections 8 and 9 then record the surface
syntax and the kernel-evidence discipline used by the checks.

The second layer, Sections 10-14, shows that the same cut-elimination
discipline scales beyond the PathOut theorem. Section 10 introduces the
Cat-valued profunctor facade, representables, reindexing, and shaped cells.
Section 11 adds the symbolic tensor, fixed co-Yoneda maps, and covariant and
contravariant internal homs. Section 12 formulates weighted limits as
profunctor representability, proves right-adjoint preservation by computation,
and obtains the dual left-adjoint colimit theorem by opposite normalization.
Section 13 records the primitive directed-inductive join category. Section 14
separates equality, `DefIso`, profunctor comparison, and the runtime/proof-time
normalization boundary.

Section 15 describes the formal artifact, validation commands, and MathOps
supporting infrastructure. Section 16 concludes. The appendices collect kernel
identifier correspondences and selected checked normal forms.

## 1.3 What "Checked" Means

The paper uses checked in the Lambdapi sense. An assertion

```text
Γ ⊢ left ≡ right
```

is accepted only when `left` and `right` are convertible under beta-reduction,
definitions, rewrite rules, and unification rules. For the arrow-induction
story, the checked evidence has three layers.

1. The theorem interfaces typecheck, including the unfolded telescope
   `E[(x,id_x)] ⊢ Π (q :^n PathOut_Z(x)), E[q]`.
2. Their projections compute; for example, the source-indexed theorem reduces
   at source `x` to the fixed-source construction introduced in Section 5.
3. Fully expanded applications normalize to ordinary categorical terms, for
   example the composition benchmark reduces to $q \\circ p$. The runtime
   normal form is the hom-action cut
   `hom_postcomp_fapp0 Z Z (id_func Z) x y z q p`; the typed ordinary
   composition view remains `comp_fapp0 Z x y z q p`.

Thus the paper is not claiming only that the theorem is mathematically
plausible. The theorem surface, its projections, and the benchmark computation
are part of the same executable rewrite system.

We follow a formula-first convention for implementation names. When the paper
mentions a Lambdapi identifier such as `Sigma_cat` or `PathInd_transfd`, the
surrounding display gives the corresponding mathematical or emdash surface
notation first; Appendix A collects the identifier correspondences.

# 2. A Type-Theoretic Foundation For Directed Families

The surface notation is intentionally close to dependent type theory, but the
base of a family is directed. A category $K$ has real arrows, not just points.
Consequently, a family over $K$ must explain how fibre objects move along base
arrows.

The core reading is:

```text
A : Cat                  a category
x : A                    an object, formally x : Obj(A)
a →^A b                  hom-category Hom_A(a,b)
F : A ⊢ B                ordinary functor
F[x]                     object action
F[f]                     arrow action
E : K ⊢ Cat              category-valued family over K
E[k]                     fibre category at k
E[f](u)                  transport of u along f : k → k'
```

The hom between two objects is itself a category. A 1-cell $f : x \\to y$ is an
object of $\\mathrm{Hom}_A(x,y)$; a 2-cell is an arrow in that hom-category;
higher cells are obtained by iterating the same pattern. This is the
$\\omega$-oriented part of the foundation.

The universe of categories is also a category:

```text
Obj(Cat)      = categories
Hom_Cat(A,B)  = A ⊢ B
```

So a category-valued family is just a functor into `Cat`. The implementation
calls the category of such families `Catd(K)`, but the mathematical reading is:

```text
E : K ⊢ Cat.
```

A morphism of families is a natural family of functors:

```text
FF : k :^n K ; E[k] ⊢ D[k]
FF[k] : E[k] ⊢ D[k].
```

A transformation between such family morphisms is a family of transformations
natural in the same directed base:

```text
ϵ : FF ⇒ GG
ϵ[k] : FF[k] ⇒ GG[k].
```

The notation `:^n` marks an ordinary directed index in the current surface
syntax. The paper uses typographic operators such as `→`, `→_`, `⇒`, and
`⇒_`; the parser-oriented ASCII spellings are recorded in the syntax report.
Mixed variance appears on the family occurrence, for example
`A[z^-] ⊢_[z] B[z]`, not by introducing older binder modes.

# 3. Dependent Hom, Sigma Totals, And Sections

The key construction for v3.2 is the dependent hom over a base arrow. Let

```text
E : K ⊢ Cat
x y : K
u : E[x]
v : E[y].
```

For every base arrow $f : x \\to y$, transport sends $u$ to $E[f](u)$ in the
fibre over $y$. The dependent hom over $f$ is then:

$$
\\mathrm{Hom}_{E[y]}(E[f](u), v).
$$

As a whole, this is not only a pointwise formula. It is a Cat-valued functor
over the base hom:

```text
homd_E(x,u,y,v) : Hom_K(x,y)^op ⊢ Cat
homd_E(x,u,y,v)[f] = Hom_{E[y]}(E[f](u),v).
```

The Lambdapi identifier for this dependent-hom functor is `homd_`.
The opposite on the base hom is an implementation convention that makes the
functorial action line up with the current normal forms. The reader-facing
content is simply: a dependent arrow from $(x,u)$ to $(y,v)$ consists of a base
arrow and a fibre arrow above it.

## 3.1 Sigma Totals

The dependent sum of a directed family is a total category:

```text
Σ_k E[k].
```

Its objects are pairs:

```text
(k,u)       with k : K and u : E[k].
```

The hom category in a total category is organized by the dependent hom. At the
level of 1-cell data it has the familiar dependent-pair shape:

```text
Hom_{ΣE}((x,u),(y,v))
  = Σ f : x →^K y, Hom_{E[y]}(E[f](u),v).
```

The kernel keeps the opposite orientation needed for higher hom-action explicit,
so the checked normal form is an opposite of a Sigma category over the opposite
base hom. This distinction affects higher cells and normal forms, not the
ordinary description of a total arrow.

Equivalently, an arrow in the total category is a pair:

```text
(f, α)
f : x →^K y
α : E[f](u) →^{E[y]} v.
```

The implementation identifier for $\\Sigma_k E[k]$ is `Sigma_cat(E)`;
`sigma_arrow(E,p,α)` names the pair `(p,α)`. The canonical transported total
arrow is `sigma_transport_arrow(E,p,u)`:

```text
sigma_transport_arrow(E,p,u) : (x,u) → (y,E[p](u))
```

whose fibre component is the identity at the transported endpoint.

## 3.2 Pi Sections

The dependent product is the category of sections:

```text
Π_k E[k].
```

An object $s : \\Pi_k E[k]$ assigns a fibre object $s[k] : E[k]$ for every
$k : K$, and it also carries action over base arrows:

```text
s[f] : Hom_{E[y]}(E[f](s[x]), s[y])
```

for $f : x \\to y$. This is the same dependent-hom shape as the Sigma hom,
specialized to the section's endpoints. In v3.2 this shared architecture is
important: total-category arrows and section actions are not independent
features with unrelated computation rules.

The implementation name for the section category is `Pi_cat(E)`. In the
surface notation the article writes:

```text
Π (k :^n K), E[k].
```

Section evaluation is written $s[k]$ in the surface notation; its Lambdapi
projection head is `piapp0(s,k)`.

# 4. Outgoing Arrows And The Canonical `rho` Arrow

Now fix a category $Z$ and an object $x : Z$. The represented family at $x$ is:

```text
Rep_Z(x)[y] = Hom_Z(x,y).
```

Its action along a base arrow $p : x \\to y$ is representable
precomposition:

```text
Rep_transport(p) : Rep_Z(y) ⊢ Rep_Z(x)
Rep_transport(p)[z][q] = q ∘ p.
```

The outgoing-arrow category from $x$ is the Sigma total of this representable:

```text
PathOut_Z(x) = Σ y :^n Z, Rep_Z(x)[y]
             = Σ y :^n Z, Hom_Z(x,y).
```

An object of `PathOut_Z(x)` is a pair `(y,p)` with `p : x →^Z y`. The
distinguished reflexive outgoing arrow is:

```text
reflout_x = (x,id_x).
```

The first diagram shows `PathOut_Z(x)` as a total category over $Z$.

<div class="arrowgram">
{
  "version": 1,
  "nodes": [
    { "name": "x", "left": 100, "top": 80, "label": "$x$" },
    { "name": "y", "left": 330, "top": 80, "label": "$y$" },
    { "name": "z", "left": 560, "top": 80, "label": "$z$" },
    { "name": "refl", "left": 100, "top": 260, "label": "$(x,\\mathrm{id}_x)$" },
    { "name": "yp", "left": 330, "top": 260, "label": "$(y,p)$" },
    { "name": "zqp", "left": 560, "top": 260, "label": "$(z,q\\circ p)$" }
  ],
  "arrows": [
    { "from": "x", "to": "y", "label": "$p$", "label_alignment": "over" },
    { "from": "y", "to": "z", "label": "$q$", "label_alignment": "over" },
    { "from": "x", "to": "z", "label": "$q\\circ p$", "curve": -45, "label_alignment": "left" },
    { "from": "refl", "to": "yp", "label": "$\\rho_{x,y,p}$", "label_alignment": "over" },
    { "from": "yp", "to": "zqp", "label": "$\\mathrm{transport}_q$", "label_alignment": "over" },
    { "from": "refl", "to": "x", "label": "$\\pi_1$", "label_alignment": "right", "style": { "body": { "name": "dashed" } } },
    { "from": "yp", "to": "y", "label": "$\\pi_1$", "label_alignment": "right", "style": { "body": { "name": "dashed" } } },
    { "from": "zqp", "to": "z", "label": "$\\pi_1$", "label_alignment": "right", "style": { "body": { "name": "dashed" } } }
  ]
}
</div>

For every object `(y,p)` of `PathOut_Z(x)`, there is a canonical arrow:

```text
rho_{x,y,p} : reflout_x →^PathOut_Z(x) (y,p).
```

This is not postulated. It is the Sigma transport arrow of the representable
family:

```text
rho_{x,y,p} = sigma_transport_arrow(Rep_Z(x), p, id_x).
```

The endpoint computation is:

```text
Rep_Z(x)[p](id_x) = p.
```

Thus the fibre component of `rho` is the identity at the computed endpoint
$p$.

<div class="arrowgram">
{
  "version": 1,
  "nodes": [
    { "name": "base_x", "left": 130, "top": 250, "label": "$x$" },
    { "name": "base_y", "left": 520, "top": 250, "label": "$y$" },
    { "name": "total_x", "left": 130, "top": 90, "label": "$(x,\\mathrm{id}_x)$" },
    { "name": "total_y", "left": 520, "top": 90, "label": "$(y,p)$" },
    { "name": "fiber_id", "left": 130, "top": 410, "label": "$\\mathrm{id}_x$" },
    { "name": "fiber_p", "left": 520, "top": 410, "label": "$p$" }
  ],
  "arrows": [
    { "from": "base_x", "to": "base_y", "label": "$p$", "label_alignment": "over" },
    { "from": "total_x", "to": "total_y", "label": "$\\rho_{x,y,p}$", "label_alignment": "over" },
    { "from": "total_x", "to": "base_x", "label": "$\\pi_1$", "label_alignment": "right", "style": { "body": { "name": "dashed" } } },
    { "from": "total_y", "to": "base_y", "label": "$\\pi_1$", "label_alignment": "left", "style": { "body": { "name": "dashed" } } },
    { "from": "fiber_id", "to": "fiber_p", "label": "$\\mathrm{Rep}_Z(x)[p]$", "label_alignment": "over" },
    { "from": "base_x", "to": "fiber_id", "label": "$\\mathrm{fibre}$", "label_alignment": "right", "style": { "body": { "name": "dotted" } } },
    { "from": "base_y", "to": "fiber_p", "label": "$\\mathrm{fibre}$", "label_alignment": "left", "style": { "body": { "name": "dotted" } } }
  ]
}
</div>

The `rho` arrows assemble into a section:

```text
pathout_refl_arrow_sec(x)
  : Π q :^n PathOut_Z(x),
      reflout_x →^PathOut_Z(x) q

pathout_refl_arrow_sec(x)[(y,p)] = rho_{x,y,p}.
```

This section is the categorical reason an induction principle is available:
every outgoing arrow has a canonical arrow from the reflexive outgoing arrow.

# 5. Arrow Induction

Let `E : PathOut_Z(x) ⊢ Cat` be a motive over outgoing arrows, and let

```text
u : E[reflout_x].
```

Fixed-source arrow induction constructs a section:

```text
path_ind_sec(Z,x,E,u) : Π q :^n PathOut_Z(x), E[q].
```

Its computation at an outgoing arrow `(y,p)` is:

```text
path_ind_sec(Z,x,E,u)[(y,p)] = E[rho_{x,y,p}](u).
```

In words: to define an element of the motive at every outgoing arrow, it
suffices to define it at the reflexive outgoing arrow and then transport along
the canonical `rho` arrow.

The checked internal version of the same statement uses ordinary fibre
transport in the family `E`. The kernel head `fib_cov_tapp0_func` names the
functor $f \\mapsto E[f](u)$:

```text
piapp0(path_ind_sec(Z,x,E,u),(y,p))
  = fib_cov_tapp0_func(PathOut_Z(x),E,reflout_x,(y,p),u)(rho_{x,y,p}).
```

This fixed-source construction is packaged as a shaped functor:

```text
PathInd_func(Z,x)
  : E :^n (PathOut_Z(x) ⊢ Cat) ;
      E[(x,id_x)] ⊢ Π (q :^n PathOut_Z(x)), E[q]

PathInd_func(Z,x)[E](u) = path_ind_sec(Z,x,E,u).
```

## 5.1 The Telescope Theorem

The primary v3.2 theorem lets the source object vary. In unfolded surface
notation, the theorem is the following source-indexed construction:

```text
x :^n Z ;
E :^n (PathOut_Z(x) ⊢ Cat) ;
E[(x,id_x)] ⊢ Π (q :^n PathOut_Z(x)), E[q].
```

Its value on $u : E[(x,\\mathrm{id}_x)]$ is the section whose component at
`(y,p)` is `E[rho_{x,y,p}](u)`.

The kernel packages this theorem as a transformation between two
source-indexed constructions. For each $x : Z$, the motive category is:

```text
PathOutMotives_Z[x] = PathOut_Z(x) ⊢ Cat.
```

The source and target constructions are:

```text
source[x,E] = E[(x,id_x)]
target[x,E] = Π q :^n PathOut_Z(x), E[q].
```

The implementation names for these are `PathOutReflEval_Z` and `PathOutPi_Z`,
and the packaged theorem is:

```text
PathInd_transfd(Z)
  : x :^n Z ; PathOutReflEval_Z[x] ⇒ PathOutPi_Z[x].
```

This packaging is important to the implementation because naturality in the
moving source object is part of the theorem's type, not a separate external
square.

Along a base arrow $p : x \\to y$, `PathOut` is contravariant in the source.
Precomposition gives a functor

```text
PathOut_Z(p) : PathOut_Z(y) ⊢ PathOut_Z(x)
PathOut_Z(p)[(z,q : y → z)] = (z,q ∘ p).
```

A motive $E$ over `PathOut_Z(x)` is transported by pullback along this action:

```text
p_*E = PathOut_Z(p)^*E : PathOut_Z(y) ⊢ Cat.
```

In Lambdapi this is the expression
`Pullback_catd(E, PathOut_transport_func(p))`. The source-side transport is
concrete:

```text
PathIndSrc_transport(p,E) = E[rho_{x,y,p}]
  : E[(x,id_x)] ⊢ E[(y,p)].
```

The target-side transport is section pullback:

```text
PathIndTgt_transport(p,E)
  : Π q :^n PathOut_Z(x), E[q]
    ⊢ Π q :^n PathOut_Z(y), E[PathOut_transport(p)[q]].
```

<div class="arrowgram">
{
  "version": 1,
  "nodes": [
    { "name": "u0", "left": 120, "top": 90, "label": "$u \\in E[(x,\\mathrm{id}_x)]$" },
    { "name": "u1", "left": 560, "top": 90, "label": "$E[\\rho_{x,y,p}](u) \\in E[(y,p)]$" },
    { "name": "r0", "left": 120, "top": 270, "label": "$(x,\\mathrm{id}_x)$" },
    { "name": "r1", "left": 560, "top": 270, "label": "$(y,p)$" }
  ],
  "arrows": [
    { "from": "u0", "to": "u1", "label": "$E[\\rho_{x,y,p}]$", "label_alignment": "over" },
    { "from": "r0", "to": "r1", "label": "$\\rho_{x,y,p}$", "label_alignment": "over" },
    { "from": "u0", "to": "r0", "label": "$\\in$", "label_alignment": "right", "style": { "body": { "name": "dotted" }, "head": { "name": "none" } } },
    { "from": "u1", "to": "r1", "label": "$\\in$", "label_alignment": "left", "style": { "body": { "name": "dotted" }, "head": { "name": "none" } } }
  ]
}
</div>

## 5.2 The Derived Sigma-Total Presentation

There is also an ordinary total-category presentation of the theorem:

```text
PathInd_funcd(Z)
  : (x,E) :^n Σ x :^n Z, (PathOut_Z(x) ⊢ Cat) ;
      E[(x,id_x)] ⊢ Π (q :^n PathOut_Z(x)), E[q].
```

It is derived, not primitive:

```text
PathInd_funcd(Z) = Sigma_transfd_funcd(PathInd_transfd(Z)).
```

Equivalently, it is the Sigma-totalization of the telescope theorem. Its
component at `(x,E)` reduces back to the object component of the fixed-source
functor:

```text
PathInd_funcd(Z)[(x,E)] = path_ind_func_fapp0(Z,x,E).
```

This distinction is important. The theorem is naturally telescope-shaped; the
Sigma-total form is a useful presentation for ordinary functor-level
applications and expanded regression checks.

<div class="arrowgram">
{
  "version": 1,
  "nodes": [
    { "name": "mot", "left": 100, "top": 230, "label": "$x :^n Z;\\ E : \\mathrm{PathOut}_Z(x) \\to \\mathrm{Cat}$" },
    { "name": "src", "left": 140, "top": 80, "label": "$E[(x,\\mathrm{id}_x)]$" },
    { "name": "tgt", "left": 560, "top": 80, "label": "$\\Pi_q\\ E[q]$" },
    { "name": "sigsrc", "left": 140, "top": 390, "label": "$\\Sigma\\ \\mathrm{source}$" },
    { "name": "sigtgt", "left": 560, "top": 390, "label": "$\\Sigma\\ \\mathrm{target}$" }
  ],
  "arrows": [
    { "from": "src", "to": "tgt", "label": "$\\mathrm{PathInd\\_transfd}(Z)$", "label_alignment": "over" },
    { "from": "src", "to": "mot", "label": "$$", "style": { "body": { "name": "dashed" }, "head": { "name": "none" } } },
    { "from": "tgt", "to": "mot", "label": "$$", "style": { "body": { "name": "dashed" }, "head": { "name": "none" } } },
    { "from": "sigsrc", "to": "sigtgt", "label": "$\\mathrm{PathInd\\_funcd}(Z)$", "label_alignment": "over" },
    { "from": "src", "to": "sigsrc", "label": "$\\Sigma$", "label_alignment": "right", "style": { "body": { "name": "dotted" } } },
    { "from": "tgt", "to": "sigtgt", "label": "$\\Sigma$", "label_alignment": "left", "style": { "body": { "name": "dotted" } } }
  ]
}
</div>

# 6. Strictness, Laxity, And Directed Induction

In ordinary dependent type theory and HoTT, substitution is organized around
variables and identity/path structure. The computation rules for identity
elimination are strict at reflexivity, and many uses of transport are
judgemental only after the relevant path has reduced to `refl`.

In emdash v3.2 the base of a family is a directed category. A family
$E : K \\to \\mathbf{Cat}$ transports fibre objects along actual arrows
$p : x \\to y$:

```text
E[p](u) : E[y].
```

This directed transport is strict for ordinary functoriality: functor actions
are oriented so that composites compute as composites. However, a morphism of
families

```text
FF : k :^n K ; E[k] ⊢ D[k]
```

does not in general preserve canonical transport arrows strictly. Over
$p : x \\to y$ and $u : E[x]$, the two evident endpoints are

```text
D[p](FF[x](u))
FF[y](E[p](u)).
```

A displayed functor therefore has a directed laxity phenomenon at the component
level. We write the associated transport-comparison component as
`χ^{FF}_{p,u}` (read as `cmp(FF,p,u)`), reserving `λ` for lambda abstraction:

```text
χ^{FF}_{p,u} : D[p](FF[x](u)) →^{D[y]} FF[y](E[p](u)).
```

This is useful mathematical notation, but it is not a primitive operation in
the active kernel. The computational owner is the internal displayed
hom-action. Its capped projection has the form

```text
fdapp1_int_hom_fapp0(FF,p,u,α)
  : D[p](FF[x](u)) →^{D[y]} FF[y](v)
```

for a fibre arrow $\\alpha : E[p](u) \\to v$. Thus the Sigma-map action on a
total arrow is represented as

```text
Σ(FF)(p,α) = (p, fdapp1_int_hom_fapp0(FF,p,u,α)).
```

The familiar composite $FF[y][\\alpha] \\circ \\chi^{FF}_{p,u}$ is only a
surface reading of this capped projection. The article does not take it as the
definition, because the active v3.2 design deliberately avoids reconstructing
Sigma maps from a separate whole-comparison operation.

The canonical identity case extracts the component-level cell:

```text
fdapp1_int_hom_fapp0(FF,p,u,id_{E[p](u)})
  = fdapp1_int_cell(FF,p,u).
```

This is the sense in which laxity becomes visible: it is observed through the
internal displayed hom-action and its Sigma-map fibre component, not supplied
as an independent external naturality square.

Strict or cartesian constructors add focused computation rules making the
comparison cell collapse. Representable precomposition is one such strict
case: for $p : x \\to y$, the family morphism

```text
Rep_transport(p) : Rep_Z(y) ⊢ Rep_Z(x)
```

has cartesian behaviour on the canonical identity fibre arrow. Concretely, for
$q : y \\to z$, the comparison component reduces to the identity at the
composite:

```text
χ^{Rep_transport(p)}_{q,id_y} = id_{q ∘ p}.
```

This is why the `PathOut` and composition benchmarks compute strictly even
though the surrounding directed-family theory permits lax displayed
transport.

The formulation of arrow induction follows this discipline. The primary
theorem is the source-indexed telescope:

```text
x :^n Z ;
E :^n (PathOut_Z(x) ⊢ Cat) ;
E[(x,id_x)] ⊢ Π (q :^n PathOut_Z(x)), E[q].
```

Moving the source object along $p : x \\to y$ transports motives by pullback
along `PathOut_Z(p)`. The source side is the concrete map
$E[\\rho_{x,y,p}]$, and the target side is section pullback. The derived
Sigma-total theorem is used to inspect this structure at canonical transported
objects. It should not be read as a claim that arbitrary non-cartesian
Sigma-total arrows preserve the induction structure strictly.

# 7. Composition As The Main Computation

The most concrete application of arrow induction is directed transitivity.
Fix $x : Z$. Define the composition target family:

```text
CompTarget_Z(x)[y] = Rep_Z(y) ⊢ Rep_Z(x).
```

Pull it back along the projection `PathOut_Z(x) → Z`:

```text
CompMotive_Z(x)[(y,p)] = Rep_Z(y) ⊢ Rep_Z(x).
```

Path induction at the identity displayed functor gives:

```text
path_comp_sec(x)
  = path_ind_sec(CompMotive_Z(x), id_Rep_Z(x)).
```

Its first application to $p : x \\to y$ is a functor:

```text
path_comp_func(p) : Rep_Z(y) ⊢ Rep_Z(x).
```

Its action on $q : y \\to z$ computes to ordinary composition:

```text
path_comp_func(p)[z][q] = q ∘ p.
```

The current runtime normal form for this composite is the hom-action cut:

```text
hom_postcomp_fapp0 Z Z (id_func Z) x y z q p.
```

The ordinary categorical composite is still present as the proof-time view
`comp_fapp0 Z x y z q p`. The distinction is intentional: the telescope
`hom_postcomp_*` and `hom_precomp_along_*` heads own runtime cut-elimination,
while `comp_fapp0`, `comp_cat_fapp0`, and `comp_catd_fapp0` remain the
ordinary composition and convertibility surfaces.

<div class="arrowgram">
{
  "version": 1,
  "nodes": [
    { "name": "p", "left": 90, "top": 80, "label": "$p : x \\to y$" },
    { "name": "q", "left": 350, "top": 80, "label": "$q : y \\to z$" },
    { "name": "qp", "left": 610, "top": 80, "label": "$q \\circ p : x \\to z$" },
    { "name": "mot", "left": 90, "top": 280, "label": "$\\mathrm{CompMotive}_Z(x)$" },
    { "name": "ind", "left": 350, "top": 280, "label": "$\\mathrm{PathInd}$" },
    { "name": "nf", "left": 610, "top": 280, "label": "$\\mathrm{hom\\_postcomp\\_fapp0}(\\mathrm{id}_Z,q,p)$" }
  ],
  "arrows": [
    { "from": "p", "to": "q", "label": "$\\mathrm{input}$", "label_alignment": "over", "style": { "body": { "name": "dotted" }, "head": { "name": "none" } } },
    { "from": "q", "to": "qp", "label": "$\\circ$", "label_alignment": "over" },
    { "from": "mot", "to": "ind", "label": "$\\mathrm{id}_{\\mathrm{Rep}_Z(x)}$", "label_alignment": "over" },
    { "from": "ind", "to": "nf", "label": "$\\rightsquigarrow$", "label_alignment": "over" },
    { "from": "p", "to": "mot", "label": "$$", "style": { "body": { "name": "dashed" }, "head": { "name": "none" } } },
    { "from": "q", "to": "ind", "label": "$$", "style": { "body": { "name": "dashed" }, "head": { "name": "none" } } },
    { "from": "qp", "to": "nf", "label": "$$", "style": { "body": { "name": "dashed" }, "head": { "name": "none" } } }
  ]
}
</div>

Both theorem presentations reach this normal form. The primary telescope route
is checked as:

```text
PathInd_transfd(Z)[x][CompMotive_Z(x)](id_Rep_Z(x))[p][z][q]
  = hom_postcomp_fapp0 Z Z (id_func Z) x y z q p.
```

The derived Sigma-total route is checked as:

```text
PathInd_funcd(Z)[(x,CompMotive_Z(x))](id_Rep_Z(x))[p][z][q]
  = hom_postcomp_fapp0 Z Z (id_func Z) x y z q p.
```

The computation is not a special-purpose rewrite for transitivity. It is the
ordinary action of the representable family, reached by applying the general
arrow-induction theorem to the composition motive.

# 8. Surface Syntax And Kernel Names

The paper uses the current v3.2 surface syntax. The syntax distinguishes
ordinary homs, indexed homs, ordinary functor categories, shaped functor
categories, section categories, and displayed transformation categories.

| Surface form | Kernel meaning | Role |
| --- | --- | --- |
| `a →^C b` | `Hom_cat C a b` | ordinary hom with explicit ambient category |
| `a → b` | `Hom_cat C a b` | ordinary hom when `C` is clear |
| `aa[z^-] →_[z]^R bb[z]` | `Hom_catd R aa bb` | indexed/displayed hom |
| `A ⊢ B` | `Functor_cat A B` | ordinary functor/program category |
| `z :^n Z ; E[z] ⊢ D[z]` | `Functord_cat E D` | shaped functor/program category |
| `Π (z :^n Z), D[z]` | `Pi_cat D` | terminal-shape section category |
| `A[z^-] ⊢_[z] B[z]` | `Functor_catd A B` | mixed-variance displayed functor family |
| `F ⇒ G` | `Transf_cat F G` | ordinary transformation category |
| `FF[z^-] ⇒_[z] GG[z]` | `Transf_catd A B FF GG` | indexed/displayed transformation category |

Two notation choices prevent ambiguity.

First, ordinary ambient categories use superscripts:

```text
a →^C b.
```

The operator `→_` is reserved for indexed or displayed homs:

```text
aa[z^-] →_[z]^R bb[z].
```

Second, the shaped category

```text
z :^n Z ; E[z] ⊢ D[z]
```

does not bind an object variable of `E[z]`. The shape `E[z]` is part of the
generalized quantification. If the target depends on an actual object of
`E[z]`, the construction is a Sigma-style telescope.

The nested telescope stress test is:

```text
k :^n K ; C[k] ⊢ (z :^n Z ; E[k^-;z] ⊢ D[k;z]).
```

This is telescope-style notation, not product-base notation. The order `k;z`
is meaningful.

# 9. Computational Method And Checked Evidence

The formalization relies on a small normalization discipline. Constructions
whose projections are used by later theorems are assigned stable semantic
owners; readable helper names are routed through those owners rather than
duplicating their definitions.

For example:

```text
CompTarget_Z(x)[y] = Rep_Z(y) ⊢ Rep_Z(x).
```

The helper for its action on a base arrow routes through `CompTarget_Z(x)`;
it is not a second definition of the same operation.

The stable heads that appear in the evidence have direct mathematical
readings:

```text
fapp0         ordinary functor object action
fapp1_fapp0  ordinary functor arrow action
tapp0_fapp0  transformation component
tdapp0_fapp0 displayed-transformation component
piapp0        section evaluation
```

Rules are installed at the lowest stable head that carries the relevant
discriminator. This is why diagnostic assertions often use canonical forms
such as `Hom_cat`, `Functor_cat`, and `Functord_cat` rather than readability
wrappers.

The formal artifact separates definitions from executable claims:
`emdash3_2.lp` contains the definitions and rewrite rules, while
`emdash3_2_checks.lp` contains the conversion assertions used as regression
evidence.

Representative checked claims:

| Surface | Representative checked claim |
| --- | --- |
| Representable | `Rep_Z(x)[y] = Hom_Z(x,y)` |
| PathOut object layer | `PathOut_Z(x) = Sigma_cat Z (Rep_Z(x))` |
| PathOut transport | `PathOut_Z(p) : PathOut_Z(y) ⊢ PathOut_Z(x)` and `PathOut_Z(p)[(z,q : y → z)] = (z,q ∘ p)` |
| Rho construction | `rho_{x,y,p} = sigma_transport_arrow(Rep_Z(x),p,id_x)` |
| Fixed-source induction | `PathInd_func(Z,x)[E](u) = path_ind_sec(Z,x,E,u)` |
| Telescope theorem | `PathInd_transfd(Z)[x] = PathInd_func(Z,x)` |
| Sigma-total theorem | `PathInd_funcd(Z)[(x,E)] = path_ind_func_fapp0(Z,x,E)` |
| Composition benchmark | `path_comp_func(p)[z][q] = q ∘ p` |

# 10. Cat-Valued Profunctors And Representables

The second arc of the v3.2 development starts from Cat-valued profunctors. For
categories $A$ and $B$, emdash defines the profunctor category by the same
category-valued-family infrastructure used earlier:

```text
Prof(A,B)     = A^op × B ⊢ Cat
Prof_cat(A,B) = Catd_cat(Product_cat(Op_cat A) B)
ProfMap(P,Q)  = Obj(Hom_{Prof_cat(A,B)}(P,Q)).
```

Thus a profunctor is not a new external semantic primitive. It is a directed
family over the product base $A^{\\mathrm{op}} \\times B$, and a vertical
profunctor map is an object of the ordinary hom-category between two such
families, equivalently a displayed transformation in that family category.
This choice keeps identity and vertical composition owned by the existing
`id_funcd` and `comp_catd_fapp0` calculus.

The representable profunctor associated to two functors
$F : A \\vdash X$ and $G : B \\vdash X$ is written:

```text
Hom_prof_along(F,G) : Prof(A,B)
Hom_prof_along(F,G)[a,b] = Hom_X(F[a],G[b]).
```

Its action on an arrow pair $(p : a' \\to a, q : b \\to b')$ is the expected
cut:

```text
h : Hom_X(F[a],G[b])
------------------------------------------------
Hom_prof_along(F,G)[p,q](h) = G[q] ∘ h ∘ F[p].
```

The implementation deliberately routes this computation through the generic
hom-action owners. `hom_postcomp_*`, `hom_precomp_along_*`, and their
`fapp0` projections expose the reusable runtime cuts; `comp_fapp0`,
`comp_cat_fapp0`, and `comp_catd_fapp0` remain the ordinary composition heads
and proof-time comparison surfaces.

Endpoint reindexing is also internal:

```text
Prof_reindex(R,F,G)[a',b'] = R[F[a'],G[b']]
```

with a functorial owner

```text
Prof_reindex_func(F,G) : Prof(A,B) ⊢ Prof(A',B').
```

The checks cover identity endpoint reindexing, nested endpoint reindexing,
representable reindexing, and the semantic agreement with pullback along the
product map. This is the profunctor version of the earlier displayed-family
discipline: a readable operation is allowed, but it must route through one
stable owner.

Two representables receive standard equipment names:

```text
Companion_prof(F) = Hom_prof_along(F,id)
Conjoint_prof(F)  = Hom_prof(F).
```

The internal right-representable embedding

```text
Hom_prof_func(J,B) : (J ⊢ B) ⊢ Prof(B,J)
```

computes on objects to `Hom_prof(G)`. Its body is semantic, built from
ordinary precomposition, internal hom, and uncurrying, but the public head is
opaque so that projection rules do not repeatedly unfold the composite.

The shaped-cell layer is the bridge from vertical profunctor maps to equipment
notation. A cell over endpoint functors $F : A' \\vdash A$ and
$G : B' \\vdash B$ is:

```text
Prof_transf_cat(R',F,R,G)
  = R' ⊢ Prof_reindex(R,F,G).
```

A shaped element is the special case whose source is the unit profunctor on a
shape category $I$:

```text
Prof_hom(I,A,B,F,R,G)
  = Obj(Prof_transf_cat(Unit_prof(I),F,R,G)).
```

The narrow evaluator `Prof_cell_apply` applies one internally natural
profunctor cell to one shaped element. It is intentionally smaller than a full
bicategory-of-profunctors composition operator. Its role is to support the
checked co-Yoneda and join computations below without adding broad
constructor-local functoriality rules.

# 11. Tensor, Co-Yoneda, And Internal Hom

The active tensor is a symbolic profunctor composite:

```text
P : Prof(A,B), Q : Prof(B,X)
--------------------------------
Prof_tensor(P,Q) : Prof(A,X).
```

Mathematically this is the coend-like composite of profunctors. The current
kernel does not yet contain a general coend or coinserter quotient, so
`Prof_tensor` is intentionally opaque. Only the endpoint behavior that is
needed by checked consumers is computational: reindexing distributes over the
two exposed endpoints, while the shared middle category remains fixed.

Fixed-endpoint tensor functoriality is internalized by a bifunctor:

```text
Prof_tensor_func(A,B,X)
  : Prof(A,B) × Prof(B,X) ⊢ Prof(A,X)
```

with projections:

```text
Prof_tensor_func(P,Q) = Prof_tensor(P,Q)
Prof_tensor_func(r,s) = Prof_tensor_map(r,s).
```

This is the current owner for fixed tensor action. The broader
endpoint-changing tensor-transformer names from earlier experiments are not
active core owners; future endpoint-changing tensor theorems should be derived
from reindexing plus this fixed-endpoint map layer once the missing
middle-change/coend compatibility is available.

The co-Yoneda maps are fixed natural transformations from tensoring with the
unit profunctor back to the identity:

```text
Prof_coyoneda_cov_transf(A,B)
  : Prof_tensor_right_unit_func(A,B) ⇒ id_{Prof(A,B)}

Prof_coyoneda_con_transf(A,B)
  : Prof_tensor_left_unit_func(A,B) ⇒ id_{Prof(A,B)}.
```

Their diagonal components are stable projection heads:

```text
Prof_coyoneda_cov_map(P)
  : ProfMap(Prof_tensor(P,Unit_prof(B)), P)

Prof_coyoneda_con_map(P)
  : ProfMap(Prof_tensor(Unit_prof(A),P), P).
```

At shaped elements, the checked beta rules have the expected co-Yoneda shape.
For $p : \\mathrm{Prof\\_hom}(I,A,B,F,P,M)$:

```text
Prof_cell_apply(
  Prof_coyoneda_cov_map(P),
  Prof_tensor_hom_hom(M,p,Prof_func_hom(M)))
  = p.
```

Dually, for $p : \\mathrm{Prof\\_hom}(I,A,B,F,P,G)$:

```text
Prof_cell_apply(
  Prof_coyoneda_con_map(P),
  Prof_tensor_hom_hom(F,Prof_func_hom(F),p))
  = p.
```

Naturality fusion is also checked for arbitrary fixed-endpoint maps. Applying
the `tapp1_fapp0` component of a co-Yoneda transformation to a tensor-shaped
element reduces to applying the chosen map to the original shaped element.
This is the Došen-style reading of co-Yoneda in the kernel: cut with the
co-Yoneda counit eliminates.

The closed structure is represented by covariant and contravariant implication
cores:

```text
Prof_imply_cov(O,Q) : Prof(A,B)
Prof_imply_con(P,O) : Prof(B,X)
```

They are paired with evaluation and lambda maps:

```text
Prof_eval_cov_map
Prof_lambda_cov_map
Prof_eval_con_map
Prof_lambda_con_map.
```

For the covariant side, maps

```text
ProfMap(Prof_tensor(P,Q), O)
```

and

```text
ProfMap(P, Prof_imply_cov(O,Q))
```

convert back and forth by computation. The contravariant side has the dual
pair of conversions. Additional shaped and endpoint-changing views exist where
concrete consumers need them, but the principal article point is simpler:
tensor, co-Yoneda, and internal hom are not detached axioms. They are exposed
as a cut-elimination interface over Cat-valued profunctors.

# 12. Weighted Limits, Adjunctions, And Duality

Weighted limits are formulated as profunctor representability. For
$F : J \\vdash B$ and a weight $W : \\mathrm{Prof}(J',J)$, the weighted-cone
profunctor is:

```text
WeightedCone_prof(F,W)
  = Prof_imply_cov(Hom_prof(F), W).
```

A covariant weighted limit of $F$ by $W$ at
$L : J' \\vdash B$ is a computational comparison:

```text
WeightedLimit_cov(F,W,L)
  = ProfComparison(WeightedCone_prof(F,W), Hom_prof(L)).
```

There is also an ordinary `IsoEvidence` presentation,
`IsWeightedLimit_cov_iso`. The active unsuffixed public name is the stronger
computational comparison, and the ordinary evidence is obtained by projection.
This is a recurring emdash pattern: a proposition-like statement may be useful
for mathematical reading, but the runtime theorem is the pair of operations
that eliminate against arbitrary probes.

Concretely, for any incoming profunctor $R$ and any shaped probe
$M : I \\vdash B$, the comparison supplies inverse operations:

```text
weighted_limit_cov_push
weighted_limit_cov_pull
```

and the checks assert:

```text
pull(push(r)) = r
push(pull(s)) = s.
```

Selected universal and cone maps are exposed as identity applications of these
operations:

```text
weighted_limit_cov_univ_transf
weighted_limit_cov_cone_transf.
```

The preservation theorem for right adjoints is then an actual computation over
these comparisons. Given an adjunction between $A$ and $B$, the representable
mate comparison is:

```text
Adjunction_hom_prof_comparison(adj)
  : Hom_B(left(-),-) ≃ Hom_A(-,right(-)).
```

The theorem

```text
right_adjoint_preserves_weighted_limit_cov
```

is transparently the composition of three comparison steps:

```text
1. use the inverse adjunction mate through fixed-weight implication;
2. reindex the given weighted-limit comparison along the left adjoint;
3. use the adjunction mate at the candidate limit.
```

The ordinary theorem
`right_adjoint_preserves_weighted_limit_cov_iso` is defined in parallel over
`IsoEvidence`, and the computational comparison forgets exactly to this
ordinary evidence. The formal checks include that compatibility.

Duality is handled by opposite normalization rather than by duplicating the
proof. The profunctor duality operation

```text
Op_prof(P) : Prof(Op B, Op A)
```

pulls back along product swap and does not opposite the fibre categories. This
choice is deliberate: with the current hom rule for opposite categories,
pointwise fibre-op would dualize representable hom categories twice.

Contravariant weighted colimits are transparent weighted limits in the
opposite world:

```text
WeightedColimit_con(F,W,L)
  = WeightedLimit_cov(Op_func(F), Op_prof(W), Op_func(L)).
```

The two conversion wrappers `Op_weighted_limit_cov` and
`Op_weighted_colimit_con` are identities after opposite and double-swap
normalization. Consequently,

```text
left_adjoint_preserves_weighted_colimit_con
```

is obtained by applying right-adjoint preservation to `Op_adjunction`. No
second colimit-specific cut calculus is installed.

# 13. Directed-Inductive Join Categories

The first directed-inductive stress test is a primitive join category. For
categories $A$ and $B$, the kernel has:

```text
Join_cat(A,B)
join_fst_func : A ⊢ Join_cat(A,B)
join_snd_func : B ⊢ Join_cat(A,B).
```

The directed cross arrows from the $A$ side to the $B$ side are not represented
as an externally quantified family plus a separate naturality proof. They are
one internally natural profunctor cell:

```text
join_cross_transf
  : Terminal_prof(A,B)
      ⊢ Hom_prof_along(join_fst_func, join_snd_func).
```

The old shaped cross-arrow interface is derived from that cell:

```text
join_cross_hom(a,b)
  = Prof_cell_eval(join_cross_transf,a,b).
```

The nondependent recursor is:

```text
join_elim_func(first,second,cross) : Join_cat(A,B) ⊢ E.
```

It computes on both inclusions:

```text
join_elim_func(first,second,cross) ∘ join_fst_func = first
join_elim_func(first,second,cross) ∘ join_snd_func = second
```

and on the cross cell:

```text
join_elim_cross_transf(first,second,cross) = cross.
```

This is not yet a semantic collage construction and not yet a generic
dependent higher-inductive schema. Its purpose in v3.2 is narrower and useful:
it tests whether directed-inductive data can be expressed using the same
profunctor-cell, shaped-element, and cut-elimination interfaces developed for
the tensor and weighted-limit calculus.

# 14. Equality, DefIso, And Normalization Boundaries

The v3.2 kernel now contains several equality-like layers, and the article
keeps them separate.

The ordinary categorical path/equality layer supports the internal syntax
needed by the directed-family development. Groupoid and univalence-facing
interfaces stage equivalence data:

```text
PathOver
TypeEquiv
GrpdUnivalence
OmegaEquiv
CatUnivalence.
```

These are not advertised here as a completed semantics of all categories.
They are a computational interface for later univalence and higher-categorical
work.

The strict computational isomorphism layer is `DefIso`. It packages selected
forward and backward maps together with cancellation behavior that is meant to
compute. Public profunctor comparisons are now compatibility names:

```text
ProfComparison(P,Q) = DefIso(Prof_cat(A,B),P,Q).
```

Their eliminators are ordinary hom-action cuts:

```text
prof_comparison_push(i,r)
  = hom_postcomp_fapp0(id, defiso_to(i), r)

prof_comparison_pull(i,s)
  = hom_postcomp_fapp0(id, defiso_from(i), s).
```

The cancellation equations for comparison push and pull are therefore inherited
from `DefIso` and `hom_postcomp_fapp0`, not from theorem-specific rewrite
rules. This is the same architectural boundary already visible in the
PathOut composition benchmark:

```text
hom_postcomp_* / hom_precomp_along_* / hom_postcomp_fapp0
  runtime cut-elimination owners

comp_fapp0 / comp_cat_fapp0 / comp_catd_fapp0
  ordinary composition heads and proof-time comparison surfaces.
```

The boundary also explains the treatment of Cat-specialized heads. A
specialization such as a `Cat_cat` or `Catd_cat` hom-action projection is kept
when it exposes data that is only semantically available at that level, for
example `tapp0_fapp0`, `tapp1_func`, or `tapp1_fapp0`. It is not a license to
add a second owner for ordinary functoriality or naturality.

The current limitations are part of the formal claim.

- `Prof_tensor` has no general coend or coinserter semantics yet; only the
  fixed endpoint and co-Yoneda-facing computations are active.
- `Join_cat` is a primitive directed-inductive stress test, not a constructed
  semantic collage.
- Generic dependent join elimination remains future work.
- Full bicategory/equipment coherence is not claimed.
- General dependent adjunctions such as `Σ_F ⊣ F^* ⊣ Π_F` remain future work.
- Arbitrary Sigma-map transport is not claimed to be strict without the
  corresponding strict or cartesian specialization.
- The project is still a strict/lax computational core for higher-categorical
  programming, not a completed formalization of weak $\\omega$-categories.

# 15. Formal Artifact And Validation

The artifact consists of a Lambdapi development, a companion regression module,
project reports, and a reproducible paper-rendering pipeline. The active v3.2
sources are:

- `emdash3_2.lp`: definitions, interfaces, and rewrite rules.
- `emdash3_2_checks.lp`: executable assertions and regression checks.
- `reports/EMDASH_FOUNDATIONS.md`: mathematician-facing foundation guide.
- `reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`:
  notation authority.
- `reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`:
  rewrite/debugging SOP and current-status ledger.
- `reports/REPORT_EMDASH_V3_2_RESEARCH_ARTICLE_ARCHITECTURE_2026-06-05.md`:
  article architecture and update plan.

The development process also includes MathOps/DevOps checks: a generated check
catalog, a health report, warning summaries, rewrite-LHS audits, examples, and
the Infinity Codex final-response archive. The archive is not an authority for
mathematics, but it is useful recovery evidence after interruption or context
compaction; active code, SOP, and reports remain the authority.

The core commands are:

```bash
EMDASH_TYPECHECK_TIMEOUT=60s make check
make examples
make ci
make warning-summary
npm run validate:paper
npm run check:render
```

`make check` typechecks the active Lambdapi development and diagnostics under
a timeout suitable for rewrite-system development. `make ci` adds examples,
catalog freshness, script checks, stale-reference lint, whitespace checks, and
the Infinity Codex hook tests. `npm run validate:paper` checks the Markdown
paper sources and embedded diagram specifications, while `npm run check:render`
builds the print renderer and runs a browser smoke test.

# 16. Conclusion

The v3.2 development shows that directed arrow induction can be expressed as
computational categorical structure. The foundation is a directed dependent
type theory of category-valued families, Sigma totals, Pi sections, and
dependent homs. The outgoing-arrow category is a Sigma total of a
representable; the canonical `rho` arrow is Sigma transport; and the primary
theorem is a source-indexed telescope from the reflexive fibre of a motive to
its section category.

The composition benchmark is the visible payoff. Applying arrow induction to
the composition motive normalizes to ordinary categorical composition, with
`hom_postcomp_fapp0` as the runtime cut-elimination owner and `comp_fapp0` as
the typed ordinary-composition view.

The newer profunctor layer shows that the same method scales beyond the
PathOut theorem. Cat-valued profunctors, tensor, co-Yoneda reductions,
internal homs, weighted limits, adjunction preservation, dual colimits, and a
primitive join category all use the same discipline: put the categorical
operation behind a stable owner, expose the projections needed by downstream
consumers, and make structural coherence compute when it is meant to be a
normal form. That is the emdash design goal in miniature: coherence is not
merely stated; it computes.

# Appendix A. Identifier Glossary

| Mathematical notation | Kernel identifier |
| --- | --- |
| category of categories | `Cat_cat` |
| `E : K ⊢ Cat` | `Catd_cat K` |
| fibre `E[k]` | `Fibre_cat K E k` |
| transport `E[p]` | `catd_transport_func K E x y p` |
| `A ⊢ B` | `Functor_cat A B` |
| `z :^n Z ; E[z] ⊢ D[z]` | `Functord_cat Z E D` |
| `Π (k :^n K), E[k]` | `Pi_cat K E` |
| section evaluation `s[k]` | `piapp0 K E s k` |
| `Σ (k :^n K), E[k]` | `Sigma_cat K E` |
| total arrow `(p,α)` in `ΣE` | `sigma_arrow K E x y u v p α` |
| canonical total transport | `sigma_transport_arrow K E x y p u` |
| Sigma map `Σ(FF)` | `sigma_map_func K E D FF` |
| dependent hom `homd_E(x,u,y,v)` | `homd_ K E E (id_funcd K E) x u y v` |
| motive pullback `F^*E` | `Pullback_catd A B E F` |
| uncurrying a displayed theorem over Sigma | `Sigma_transfd_funcd K R S T η` |
| `Rep_Z(x)` | `Rep_catd Z x` |
| `Rep_transport(p)` | `Rep_transport_func Z x y p` |
| `PathOut_Z(x)` | `PathOut_cat Z x` |
| `PathOut_Z(p)` | `PathOut_transport_func Z x y p` |
| `(y,p)` in `PathOut_Z(x)` | `pathout_obj Z x y p` |
| `(x,id_x)` | `pathout_refl_obj Z x` |
| `rho_{x,y,p}` | `pathout_refl_arrow Z x y p` |
| section of all `rho` arrows | `pathout_refl_arrow_sec Z x` |
| `E[rho_{x,y,p}]` | `pathout_refl_eval_base_func Z x y p E` |
| transported motive `p_*E` | `pathout_motive_transport_obj Z x y p E` |
| `PathOutMotives_Z` | `PathOutMotives_catd Z` |
| `PathOutReflEval_Z` | `PathOutReflEval_funcd Z` |
| `PathOutPi_Z` | `PathOutPi_funcd Z` |
| fixed-source induction source family | `PathInd_src_catd Z x` |
| fixed-source induction target family | `PathInd_tgt_catd Z x` |
| fixed-source component functor | `path_ind_func_fapp0 Z x E` |
| fixed-source path induction | `PathInd_func Z x` |
| telescope path induction | `PathInd_transfd Z` |
| Sigma-total source family | `PathIndSrc_catd Z` |
| Sigma-total target family | `PathIndTgt_catd Z` |
| Sigma-total source transport | `PathIndSrc_transport_func Z x y p E` |
| Sigma-total target transport | `PathIndTgt_transport_func Z x y p E` |
| Sigma-total path induction | `PathInd_funcd Z` |
| composition target | `CompTarget_catd Z x` |
| action of composition target | `CompTarget_fapp1_func Z x a b p` |
| composition motive | `CompMotive_catd Z x` |
| composition section | `path_comp_sec Z x` |
| composition functor for `p` | `path_comp_func Z x y p` |
| fibre transport action `E[f](u)` | `fib_cov_tapp0_func K E x y u` |
| covariant fibre transport | `fib_cov_transf Z D x u` |
| Sigma-map fibre component | `fdapp1_int_hom_fapp0 K E D FF x y p u v α` |
| displayed transport-comparison component `χ^{FF}_{p,u}` | `fdapp1_int_cell K E D FF x y p u` |
| profunctor base `A^op × B` | `Prof_base A B` |
| profunctor category `Prof(A,B)` | `Prof_cat A B` |
| profunctor object sort | `Prof A B` |
| profunctor map `P ⇒ Q` | `ProfMap A B P Q` |
| unit profunctor | `Unit_prof B` |
| representable profunctor `Hom_X(F[-],G[-])` | `Hom_prof_along A B X F G` |
| conjoint/right representable | `Hom_prof B X G` |
| right-representable embedding | `Hom_prof_func J B` |
| endpoint reindexing | `Prof_reindex A A' B B' R F G` |
| profunctor shaped cell category | `Prof_transf_cat A A' B B' R' F R G` |
| profunctor shaped element | `Prof_hom I A B F R G` |
| apply shaped profunctor cell | `Prof_cell_apply ... c r` |
| tensor of profunctors | `Prof_tensor A B X P Q` |
| fixed-endpoint tensor bifunctor | `Prof_tensor_func A B X` |
| fixed-endpoint tensor map | `Prof_tensor_map A B X P P' Q Q' r s` |
| tensor shaped composition | `Prof_tensor_hom_hom I A B X R S F G M r s` |
| covariant co-Yoneda map | `Prof_coyoneda_cov_map A B P` |
| contravariant co-Yoneda map | `Prof_coyoneda_con_map A B P` |
| covariant internal hom | `Prof_imply_cov A B X O Q` |
| contravariant internal hom | `Prof_imply_con A B X P O` |
| covariant eval/lambda maps | `Prof_eval_cov_map`, `Prof_lambda_cov_map` |
| contravariant eval/lambda maps | `Prof_eval_con_map`, `Prof_lambda_con_map` |
| weighted cone profunctor | `WeightedCone_prof B J J' F W` |
| weighted limit comparison | `WeightedLimit_cov B J J' F W L` |
| weighted limit push/pull | `weighted_limit_cov_push`, `weighted_limit_cov_pull` |
| adjunction hom comparison | `Adjunction_hom_prof_comparison A B adj` |
| right adjoints preserve weighted limits | `right_adjoint_preserves_weighted_limit_cov` |
| profunctor opposite | `Op_prof A B P` |
| weighted colimit by duality | `WeightedColimit_con B J J' F W L` |
| left adjoints preserve weighted colimits | `left_adjoint_preserves_weighted_colimit_con` |
| directed join category | `Join_cat A B` |
| join inclusions | `join_fst_func A B`, `join_snd_func A B` |
| join cross cell | `join_cross_transf A B` |
| join recursor | `join_elim_func A B E first second cross` |
| strict computational isomorphism | `DefIso C x y` |
| profunctor comparison compatibility | `ProfComparison A B P Q` |
| comparison push/pull | `prof_comparison_push`, `prof_comparison_pull` |

# Appendix B. Selected Checked Normal Forms

The article quotes checked normal forms in compact mathematical notation and
keeps the fully expanded Lambdapi terms available as regression references.
The following statements are covered by `emdash3_2_checks.lp`.

Core PathOut and rho checks:

```text
Rep_Z(x)[y] = Hom_Z(x,y)
PathOut_Z(x) = Sigma_cat Z (Rep_Z(x))
PathOut_Z(p) : PathOut_Z(y) ⊢ PathOut_Z(x)
PathOut_transport(p)[(z,q : y → z)] = (z,q ∘ p)
PathOut_transport(p)[(y,id_y)] = (y,p)
Rep_Z(x)[p](id_x) = p
rho_{x,y,p} = sigma_transport_arrow(Rep_Z(x),p,id_x)
pathout_refl_arrow_sec(x)[(y,p)] = rho_{x,y,p}
PathOut_transport(p)(rho_{y,z,q}) ; rho_{x,y,p}
  = rho_{x,z,q ∘ p}
```

Path-induction projection checks:

```text
PathInd_func(Z,x)[E] = path_ind_func_fapp0(Z,x,E)
PathInd_func(Z,x)[E](u) = path_ind_sec(Z,x,E,u)
path_ind_sec(Z,x,E,u)[(y,p)] = E[rho_{x,y,p}](u)
PathInd_transfd(Z)[x] = PathInd_func(Z,x)
PathInd_transfd(Z)[x][E](u) = path_ind_sec(Z,x,E,u)
PathInd_funcd(Z)[(x,E)] = path_ind_func_fapp0(Z,x,E)
PathInd_funcd(Z)[(x,E)](u) = path_ind_sec(Z,x,E,u)
```

Composition benchmark checks:

```text
CompTarget_Z(x)[y] = Rep_Z(y) ⊢ Rep_Z(x)
CompMotive_Z(x)[(y,p)] = Rep_Z(y) ⊢ Rep_Z(x)
Pi(PathOut_Z(x), CompMotive_Z(x))
  = z :^n Z ; Rep_Z(x)[z] ⊢ CompTarget_Z(x)[z]

path_ind_sec(Sigma_proj1_pullback(D),u) = fib_cov_transf(D,x,u)
path_ind_sec(CompMotive_Z(x), id_Rep_Z(x)) = path_comp_sec(x)
CompTarget_Z(x)[p](id_Rep_Z(x)) = path_comp_func(p)
path_comp_sec(x)[p] = path_comp_func(p)
path_comp_func(p)[z][q] = q ∘ p
```

The two expanded routes that matter most are the primary telescope route:

```text
PathInd_transfd(Z)[x][CompMotive_Z(x)](id_Rep_Z(x))[p][z][q]
  = hom_postcomp_fapp0 Z Z (id_func Z) x y z q p
```

and the derived Sigma-total route:

```text
PathInd_funcd(Z)[(x,CompMotive_Z(x))](id_Rep_Z(x))[p][z][q]
  = hom_postcomp_fapp0 Z Z (id_func Z) x y z q p
```

The typed ordinary-composition component is also checked through proof-time
comparison surfaces. In the transported PathOut arrow, the base component is
the ordinary composite while the endpoint remains the runtime hom-action
normal form:

```text
PathOut_transport(p)(rho_{y,z,q}) ; rho_{x,y,p}
  = (comp_fapp0 Z x y z q p,
     id_{hom_postcomp_fapp0 Z Z (id_func Z) x y z q p})
```

Profunctor and tensor checks:

```text
Prof_cat(A,B) = Catd_cat(A^op × B)
ProfMap(P,Q) = Obj(Hom_{Prof_cat(A,B)}(P,Q))
Hom_prof_along(F,G)[a,b] = Hom_X(F[a],G[b])
Prof_reindex(R,F,G)[a',b'] = R[F[a'],G[b']]

Prof_tensor_func(P,Q) = Prof_tensor(P,Q)
Prof_tensor_func(r,s) = Prof_tensor_map(r,s)
Prof_coyoneda_cov_map(P)
  = tapp0_fapp0(Prof_coyoneda_cov_transf(A,B),P)
Prof_coyoneda_con_map(P)
  = tapp0_fapp0(Prof_coyoneda_con_transf(A,B),P)
```

Co-Yoneda and internal-hom beta checks:

```text
Prof_cell_apply(
  Prof_coyoneda_cov_map(P),
  Prof_tensor_hom_hom(M,p,Prof_func_hom(M)))
  = p

Prof_cell_apply(
  Prof_coyoneda_con_map(P),
  Prof_tensor_hom_hom(F,Prof_func_hom(F),p))
  = p

Prof_lambda_cov_map(Prof_eval_cov_map(t)) = t
Prof_eval_cov_map(Prof_lambda_cov_map(t)) = t
Prof_lambda_con_map(Prof_eval_con_map(t)) = t
Prof_eval_con_map(Prof_lambda_con_map(t)) = t
```

Weighted-limit and adjunction checks:

```text
WeightedCone_prof(F,W)
  = Prof_imply_cov(Hom_prof(F),W)

IsWeightedLimit_cov_iso(F,W,L)
  = IsoEvidence(Prof_cat(B,J'), WeightedCone_prof(F,W), Hom_prof(L))

WeightedLimit_cov(F,W,L)
  = ProfComparison(WeightedCone_prof(F,W), Hom_prof(L))

weighted_limit_cov_pull(isl,M, weighted_limit_cov_push(isl,M,r)) = r
weighted_limit_cov_push(isl,M, weighted_limit_cov_pull(isl,M,s)) = s

right_adjoint_preserves_weighted_limit_cov(isl,adj)
  = right_adjoint_preserves_weighted_limit_cov_comp(isl,adj)

prof_comparison_evidence(
  right_adjoint_preserves_weighted_limit_cov_comp(isl,adj))
  = right_adjoint_preserves_weighted_limit_cov_iso(
      prof_comparison_evidence(isl),adj)
```

Duality and join checks:

```text
WeightedColimit_con(F,W,L)
  = WeightedLimit_cov(Op_func(F), Op_prof(W), Op_func(L))

Op_weighted_colimit_con(Op_weighted_limit_cov(isl)) = isl

left_adjoint_preserves_weighted_colimit_con(isc,adj)
  : WeightedColimit_con(left(adj) ∘ F, W, left(adj) ∘ L)

Terminal_prof(A,B)[a,b] = Terminal_cat
join_elim_func(first,second,cross) ∘ join_fst_func = first
join_elim_func(first,second,cross) ∘ join_snd_func = second
join_elim_cross_transf(first,second,cross) = cross
join_cross_hom(a,b) = Prof_cell_eval(join_cross_transf,a,b)
```

Comparison checks:

```text
ProfComparison(P,Q) = DefIso(Prof_cat(A,B),P,Q)
prof_comparison_pull(i, prof_comparison_push(i,r)) = r
prof_comparison_push(i, prof_comparison_pull(i,s)) = s
prof_comparison_push(refl_P,r) = r
prof_comparison_push(comp(j,i),r)
  = prof_comparison_push(j, prof_comparison_push(i,r))
```

# Appendix C. Diagram Source Notes

All figures in this article are Arrowgram JSON blocks. They are intentionally
simple: the diagrams explain object and arrow flow, while the actual
normalization claims are made by Lambdapi assertions in `emdash3_2_checks.lp`.
