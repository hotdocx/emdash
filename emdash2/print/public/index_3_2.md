---
title: emdash v3.2 — Synthetic arrow induction and computational composition
authors: https://github.com/hotdocx/emdash
---

# Abstract

We present the v3.2 architecture of **emdash**, a Lambdapi specification for a
programming language and proof assistant for strict/lax $\\omega$-categories.
The central result of this iteration is a synthetic arrow-induction principle
expressed internally as a displayed transformation:

```text
PathInd_transfd(Z)
  : x :^n Z ; PathOutReflEval_Z[x] => PathOutPi_Z[x].
```

For a category $Z$ and object $x : Z$, the outgoing-arrow category
$\\mathrm{PathOut}_Z(x)$ is the Sigma category of arrows out of $x$:

$$
\\mathrm{PathOut}_Z(x) = \\Sigma_{y : Z}\\,\\mathrm{Hom}_Z(x,y).
$$

The theorem says that a motive over outgoing arrows is determined by its value
at the reflexive outgoing arrow $(x,\\mathrm{id}_x)$, with computation along
the canonical arrow

$$
\\rho_{x,y,p} : (x,\\mathrm{id}_x) \\to (y,p).
$$

The most visible checked consequence is directed transitivity: for
$p : x \\to y$ and $q : y \\to z$, path induction on the composition motive
normalizes to ordinary categorical composition,

$$
\\mathrm{path\\_comp\\_func}(p)[z][q] \\rightsquigarrow q \\circ p.
$$

The article draft below is a workbench for the v3.2 paper. It leads with this
computation, then builds outward to the shaped syntax and kernel infrastructure
that make the theorem expressible and executable.

# 1. Introduction

Higher category theory is difficult to mechanize because coherence data grows
quickly and because many equations that mathematicians treat as structural are
awkward when they must be carried as external proof terms. The emdash project
explores a different design point: categorical structure is internal to a small
type-theoretic kernel, and many structural equations are oriented as
normalization rules.

In v3.2, the main narrative is no longer just that functors and transfors have
stable computational heads. The new narrative is that this infrastructure can
state and check a genuine synthetic induction principle for arrows. The theorem
is not encoded as an external eliminator for a datatype of paths. It is built
from category-theoretic constructors already present in the kernel: Sigma
categories, representables, section categories, displayed functors, and
displayed transformations.

The leading example is simple to state. Fix $x : Z$. An outgoing arrow from
$x$ is a pair $(y,p)$ with $p : x \\to y$. There is a canonical arrow

$$
\\rho_{x,y,p} : (x,\\mathrm{id}_x) \\to (y,p)
$$

inside the outgoing-arrow category. A motive $E$ over outgoing arrows can
therefore transport an element $u : E[(x,\\mathrm{id}_x)]$ to every target
$(y,p)$ by applying $E$ to $\\rho_{x,y,p}$. The checked v3.2 theorem packages
this construction as a section.

## 1.1 Contributions Of The v3.2 Paper

This paper draft will focus on four contributions.

1. **Synthetic arrow induction.** The primitive theorem surface is
   `PathInd_transfd(Z)`, a displayed transformation over the source object
   `x :^n Z`.
2. **Computational transitivity.** The composition benchmark reduces a fully
   expanded path-induction expression to `comp_fapp0 Z x y z q p`.
3. **Canonical shaped syntax.** The current notation uses `⊢`, `⊢_`, `->`,
   `->_`, `=>`, `=>_`, and `Π` to distinguish ordinary, shaped, indexed, and
   mixed-variance constructions.
4. **Stable-head normalization.** The implementation separates semantic
   owners from presentation helpers so Lambdapi can typecheck the development
   with predictable rewrite behavior.

# 2. The Main Computation

The main checked computation is:

```text
path_comp_func(p)[z][q] = q o p.
```

This should be read in the following context:

```text
x y z : Obj Z
p     : x ->^Z y
q     : y ->^Z z
```

The expression on the left is not a hand-written composition operator. It is
the normal form obtained by applying the path-induction theorem to a motive
whose value at `(y,p)` is the category of representable precomposition maps
from `Rep_Z(y)` to `Rep_Z(x)`.

## 2.1 Outgoing Arrows

For a fixed source object $x : Z$, define:

```text
PathOut_Z(x) = Σ y :^n Z, Hom_Z(x,y)
reflout_x    = (x,id_x).
```

The implementation names are:

```text
PathOut_cat Z x
pathout_obj Z x y p
pathout_refl_obj Z x
```

The first diagram shows the category of outgoing arrows from $x$ as a total
category over $Z$. The bottom row contains objects of $\\mathrm{PathOut}_Z(x)$;
the dashed arrows remember their target object in $Z$.

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

## 2.2 The Canonical Rho Arrow

The canonical arrow is:

```text
rho_{x,y,p} : reflout_x ->^PathOut_Z(x) (y,p)
```

In the implementation this is not a primitive path. It is built from Sigma
transport for the representable family:

```text
pathout_refl_arrow Z x y p
  = sigma_transport_arrow(Rep_Z(x), p, id_x).
```

The endpoint computation is:

```text
Rep_Z(x)[p](id_x) = p.
```

Thus the fibre component of the Sigma transport is the identity at the computed
endpoint $p$.

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

## 2.3 Fixed-Source Path Induction

For a motive:

```text
E : Catd(PathOut_Z(x))
u : E[reflout_x]
```

the fixed-source theorem gives:

```text
path_ind_sec(Z,x,E,u) : Π q :^n PathOut_Z(x), E[q].
```

The intended computation is:

```text
path_ind_sec(Z,x,E,u)[(y,p)] = E[rho_{x,y,p}](u).
```

Kernel packaging:

```text
PathInd_func(Z,x)
  : E :^n Catd(PathOut_Z(x)) ; E[(x,id_x)] ⊢ Π q, E[q]
PathInd_func(Z,x)[E](u) = path_ind_sec(Z,x,E,u).
```

## 2.4 Varying-Source Telescope Theorem

The primary v3.2 theorem is the telescope/displayed-transformation form:

```text
PathInd_transfd(Z)
  : x :^n Z ; PathOutReflEval_Z[x] => PathOutPi_Z[x]
```

where:

```text
PathOutReflEval_Z[x][E] = E[(x,id_x)]
PathOutPi_Z[x][E]       = Π q :^n PathOut_Z(x), E[q].
```

The Sigma-total form is derived, not primitive:

```text
PathInd_funcd(Z) = Sigma_transfd_funcd(PathInd_transfd(Z)).
```

## 2.5 Composition As The Benchmark

The composition motive is:

```text
CompTarget_Z(x)[y] = Rep_Z(y) ⊢ Rep_Z(x)
CompMotive_Z(x)[(y,p)] = Rep_Z(y) ⊢ Rep_Z(x).
```

Path induction at the identity displayed functor gives:

```text
path_comp_sec(x)
  = path_ind_sec(CompMotive_Z(x), id_Rep_Z(x)).
```

The checked beta chain is:

```text
path_comp_sec(x)[p] = path_comp_func(p)
path_comp_func(p)[z][q] = q o p.
```

Both the primary telescope route and the derived Sigma-total route are checked
in `emdash3_2_checks.lp` and normalize to:

```text
comp_fapp0 Z x y z q p.
```

# 3. The Surface Language

This section will introduce the current v3.2 notation authority.

```text
a ->^C b
aa[z^-] ->_[z]^R bb[z]
A ⊢ B
z :^n Z ; E[z] ⊢ D[z]
Π (z :^n Z), D[z]
A[z^-] ⊢_[z] B[z]
F => G
FF[z^-] =>_[z] GG[z]
```

The nested telescope stress test will be treated as an expressibility example:

```text
k :^n K ; C[k] ⊢ (z :^n Z ; E[k^-;z] ⊢ D[k;z])
```

# 4. Kernel Foundations

This section will be dependency-driven rather than a broad tour:

1. `Grpd`, `Cat`, `Obj`, `Hom_cat`;
2. `Functor_cat`, `Transf_cat`, stable application heads;
3. `Catd_cat`, `Functord_cat`, `Transfd_cat`;
4. `Pi_cat`, `Sigma_cat`, `sigma_arrow`, `sigma_transport_arrow`;
5. `Functor_catd`, `Hom_catd`, `Transf_catd`;
6. representables `Rep_catd`, `PathOut_cat`, and path induction.

# 5. Computational Normalization Discipline

This section will explain stable heads, rewrite rules versus unification rules,
semantic owners before helper aliases, and why diagnostics are split into
`emdash3_2_checks.lp`.

# 6. Supporting Constructions

This section will cover supporting examples after the main theorem:

- product-valued functors and projections;
- semantic curry/uncurry object and capped hom-action checks;
- Sigma/Pi helper beta laws;
- ordinary adjunction cut-elimination:

```text
counit[f] o left(unit[g]) -> f o left(g)
right(counit[g]) o unit[f] -> right(g) o f.
```

# 7. Implementation And Validation

The implementation is split into:

- `emdash3_2.lp`: definitions and rewrite rules;
- `emdash3_2_checks.lp`: executable assertions and regression checks;
- `reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`:
  current status and SOP;
- `reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`:
  notation authority.

Validation commands:

```bash
timeout 60s lambdapi check -w emdash3_2.lp
timeout 60s lambdapi check -w emdash3_2_checks.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
npm run check:render
```

# 8. Limitations And Future Work

The v3.2 article should be explicit about deferred work:

- structural functor logic is planned but not implemented;
- general dependent adjunctions `Σ_F ⊣ F^* ⊣ Π_F` remain future work;
- arbitrary Sigma-map transport is not strict without strict/cartesian
  specialization;
- whole-transfor displayed laxity is deferred;
- full product/curry adjunction coherence is future work;
- `section_total(s) : K ⊢ Σ_K E` is not yet a named presentation facade.

# 9. Conclusion

The conclusion will return to the main claim: v3.2 shows that arrow induction
and directed transitivity can be internalized as checked computational
structure in a Lambdapi kernel, while the new shaped syntax makes these
constructions presentable as a programming-language/proof-assistant surface.

# Appendix A. Identifier Glossary

This appendix will map mathematical notation to implementation identifiers.

# Appendix B. Selected Checked Normal Forms

This appendix will quote the main normal forms from `emdash3_2_checks.lp`,
including the fully expanded telescope and Sigma-total composition benchmarks.
