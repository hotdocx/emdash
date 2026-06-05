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

# 3. The Telescope Theorem

The fixed-source eliminator is useful, but the real v3.2 theorem is the
source-indexed package. The source object $x$ itself varies in $Z$, and the
family of motives varies with it:

```text
PathOutMotives_Z[x] = Catd(PathOut_Z(x)).
```

The two displayed functors in the theorem are:

```text
PathOutReflEval_Z[x][E] = E[(x,id_x)]
PathOutPi_Z[x][E]       = Π q :^n PathOut_Z(x), E[q].
```

Thus the theorem interface is:

```text
PathInd_transfd(Z)
  : x :^n Z ; PathOutReflEval_Z[x] => PathOutPi_Z[x].
```

This formulation is intentionally not a separate family of external naturality
squares. The naturality information is part of being a displayed
transformation. The regressions inspect the induced transports. Along
$p : x \\to y$, a motive $E$ over $\\mathrm{PathOut}_Z(x)$ is transported to

```text
p_*E = Pullback_catd(E, PathOut_transport_func(p)).
```

The source transport is the concrete functor:

```text
PathIndSrc_transport(p,E) = E[rho_{x,y,p}]
  : E[(x,id_x)] ⊢ E[(y,p)].
```

The target transport is section pullback along the contravariant PathOut
transport:

```text
PathIndTgt_transport(p,E)
  : Π q :^n PathOut_Z(x), E[q]
    ⊢ Π q :^n PathOut_Z(y), E[PathOut_transport(p)[q]].
```

The next diagram isolates the source side: path induction moves a base value
$u$ by applying the motive to $\\rho_{x,y,p}$.

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

The Sigma-total presentation is deliberately secondary. It is derived by the
generic Sigma-total operation on displayed transformations:

```text
PathInd_funcd(Z) = Sigma_transfd_funcd(PathInd_transfd(Z)).
```

Its component at `(x,E)` reduces back to the fixed-source component:

```text
PathInd_funcd(Z)[(x,E)] = path_ind_func_fapp0(Z,x,E).
```

This distinction matters for the article. The theorem is most naturally
telescope-shaped; the Sigma-total form is a useful presentation for checking
ordinary functor-level applications and expanded normal forms.

<div class="arrowgram">
{
  "version": 1,
  "nodes": [
    { "name": "mot", "left": 100, "top": 230, "label": "$x :^n Z ;\\ \\mathrm{Catd}(\\mathrm{PathOut}_Z(x))$" },
    { "name": "src", "left": 140, "top": 80, "label": "$\\mathrm{PathOutReflEval}_Z$" },
    { "name": "tgt", "left": 560, "top": 80, "label": "$\\mathrm{PathOutPi}_Z$" },
    { "name": "sigsrc", "left": 140, "top": 390, "label": "$\\mathrm{PathIndSrc}_Z$" },
    { "name": "sigtgt", "left": 560, "top": 390, "label": "$\\mathrm{PathIndTgt}_Z$" }
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

# 4. The Surface Language

The notation is part of the result. The v3.2 file is still Lambdapi, but its
comments and planned parser surface use a disciplined syntax so that a reader
can distinguish ordinary homs, indexed homs, ordinary functor categories,
shaped functor categories, and mixed-variance displayed functor categories.

| Surface form | Kernel meaning | Role |
| --- | --- | --- |
| `a ->^C b` | `Hom_cat C a b` | ordinary hom with explicit ambient category |
| `a -> b` | `Hom_cat C a b` | ordinary hom when `C` is clear |
| `aa[z^-] ->_[z]^R bb[z]` | `Hom_catd R aa bb` | indexed/displayed hom |
| `A ⊢ B` | `Functor_cat A B` | ordinary functor/program category |
| `z :^n Z ; E[z] ⊢ D[z]` | `Functord_cat E D` | shaped functor/program category |
| `Π (z :^n Z), D[z]` | `Pi_cat D` | terminal-shape section category |
| `A[z^-] ⊢_[z] B[z]` | `Functor_catd A B` | mixed-variance displayed functor family |
| `F => G` | `Transf_cat F G` | ordinary transformation category |
| `FF[z^-] =>_[z] GG[z]` | `Transf_catd FF GG` | indexed/displayed transformation category |

There are two details that are easy to miss. First, ordinary hom ambient
parameters are superscripts:

```text
a ->^C b
```

The notation `->_` is reserved for indexed/displayed homs:

```text
aa[z^-] ->_[z]^R bb[z].
```

Second, the shaped category

```text
z :^n Z ; E[z] ⊢ D[z]
```

does not bind an object variable of `E[z]`. The shape `E[z]` is part of the
generalized quantification. If the target family depends on an actual object
of `E[z]`, the construction is different and should be represented using a
Sigma-style telescope.

The nested telescope stress test is:

```text
k :^n K ; C[k] ⊢ (z :^n Z ; E[k^-;z] ⊢ D[k;z])
```

This is not a product-base notation. It is telescope-style: `k` is the first
input and `z` is the next input. The order `k;z` is therefore meaningful. The
inner category is an ordinary shaped functor category, not a `⊢_` expression;
the indexed-hom notation `->_` is the right way to spell fibrewise homs when
the displayed family itself is the object of interest.

# 5. Kernel Foundations

The kernel section of the paper should be dependency-driven. The theorem uses
only the following infrastructure, in this order.

1. `Grpd`, `Cat`, `Obj`, and `Hom_cat` give the strict categorical base.
2. `Functor_cat` and `Transf_cat` provide ordinary program and transformation
   categories.
3. `Catd_cat`, `Functord_cat`, and `Transfd_cat` provide directed families,
   shaped programs, and displayed transformations.
4. `Pi_cat` and `Sigma_cat` provide section and total categories.
5. `Functor_catd`, `Hom_catd`, and `Transf_catd` provide mixed-variance
   displayed functor, hom, and transformation families.
6. `Rep_catd`, `PathOut_cat`, `pathout_refl_arrow`, and `PathInd_transfd`
   assemble the arrow-induction theorem.

The representable family is the first key construction:

```text
Rep_Z(x)[y] = Hom_Z(x,y).
```

Its action on a base arrow is precomposition:

```text
Rep_transport(p) : Rep_Z(y) ⊢ Rep_Z(x)
Rep_transport(p)[z][q] = q o p.
```

`PathOut_Z(x)` is then just the Sigma category of this representable family:

```text
PathOut_Z(x) = Σ y :^n Z, Rep_Z(x)[y].
```

All later path-induction terms are built from this small list. That is why the
paper can lead with the theorem and postpone the broader library tour.

# 6. Computational Normalization Discipline

The implementation style is as important as the definitions. The v3.2 file
uses named semantic owners for constructions whose projections must compute
predictably, and it avoids introducing helper aliases as independent rewrite
owners.

For example, `CompTarget_catd` is a semantic `hom_con` expression:

```text
CompTarget_Z(x)[y] = Rep_Z(y) ⊢ Rep_Z(x).
```

The readable helper `CompTarget_fapp1_func` exposes a capped action with
canonical endpoints, but it routes through `CompTarget_catd`. The helper is
not a second semantic definition of the same operation.

The stable-head discipline is visible in the application names:

```text
fapp0        ordinary functor object action
fapp1_fapp0  ordinary functor arrow action
tapp0_fapp0  transformation component
tdapp0_fapp0 displayed-transformation component
piapp0       section evaluation
```

Rules are installed at the lowest stable head that carries the relevant
discriminator. This is why many assertions use canonical forms such as
`Hom_cat`, `Functor_cat`, and `Functord_cat` rather than readability wrappers:
the canonical heads are better unification targets.

The diagnostics live in `emdash3_2_checks.lp` rather than in the main file.
That split keeps `emdash3_2.lp` readable while still making normalization
claims executable. The checks are not ornamental; they are the regression
catalog for the paper.

# 7. Supporting Constructions

After the path-induction theorem, the paper should include smaller examples
that show the same kernel discipline in other constructors.

Product-valued functors and product projections are already computational. In
particular, maps into a product category reduce through the two projection
functors, and diagonal or swap maps can be presented as ordinary product maps
when the needed product context is available.

The curry/uncurry layer is treated as supporting infrastructure. Object-level
semantic curry and uncurry are present, and capped hom-action checks document
the current computational behavior. The remaining higher action needed for
some whole-functor semantic uncurry statements is deferred to the planned
structural functor-logic work.

Ordinary adjunctions provide another good example because their triangle
computations have the shape of cut-elimination:

```text
counit[f] o left(unit[g]) -> f o left(g)
right(counit[g]) o unit[f] -> right(g) o f.
```

This should remain a later section or sidebar. It reinforces the same message,
but it is not the central theorem of v3.2.

# 8. Implementation And Validation

The implementation is split into two Lambdapi files:

- `emdash3_2.lp`: definitions, interfaces, and rewrite rules;
- `emdash3_2_checks.lp`: executable assertions and regression checks.

The active reports used by the paper are:

- `reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`;
- `reports/EMDASH_FOUNDATIONS.md`;
- `reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`;
- `reports/REPORT_EMDASH_V3_2_RESEARCH_ARTICLE_ARCHITECTURE_2026-06-05.md`.

The core validation commands are:

```bash
timeout 60s lambdapi check -w emdash3_2.lp
timeout 60s lambdapi check -w emdash3_2_checks.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
npm run check:render
```

The print pipeline treats this file as a draft variant:

```text
print/public/index_3_2.md
```

It is previewed with:

```text
/?paper=index_3_2.md
```

Once this long version is coherent, it can replace `print/public/index.md`;
the short version `index_0.md` should then be regenerated from the v3.2 long
article rather than from the old v2 text.

# 9. Limitations And Future Work

The v3.2 article should be explicit about what is implemented now and what is
planned.

Structural functor logic is still planned. The likely operations are exchange,
weakening/constant, and contraction/diagonal at the level of nested functor
categories, with displayed and transformation variants treated carefully.

General dependent adjunctions remain future work:

```text
Σ_F ⊣ F^* ⊣ Π_F.
```

The current ordinary adjunction interface is useful and computational, but it
is not yet the general fibred adjunction story.

Arbitrary Sigma-map transport is not claimed to be strict without the right
cartesian or strict specialization. The v3.2 path-induction story uses the
canonical transport arrows it needs; it does not claim a fully general
strictification theorem for every Sigma arrow.

Whole-transfor displayed laxity and full product/curry adjunction coherence
are also deferred. Finally, a presentation facade such as

```text
section_total(s) : K ⊢ Σ_K E
```

is not yet named, even though the semantic construction it would expose is
conceptually clear.

# 10. Conclusion

The v3.2 development shows that arrow induction can be presented as
computational categorical structure. The theorem is shaped as a displayed
transformation over the source object, its fixed-source and Sigma-total
presentations compute to the same section, and the composition benchmark
normalizes to ordinary categorical composition.

The broader contribution is a surface and kernel architecture for
omega-oriented categorical programming: shaped quantification, indexed homs,
displayed transformations, Sigma/Pi categories, and stable-head normalization
work together as a small executable specification.

# Appendix A. Identifier Glossary

| Mathematical notation | Kernel identifier |
| --- | --- |
| `Rep_Z(x)` | `Rep_catd Z x` |
| `Rep_transport(p)` | `Rep_transport_func Z x y p` |
| `PathOut_Z(x)` | `PathOut_cat Z x` |
| `(y,p)` in `PathOut_Z(x)` | `pathout_obj Z x y p` |
| `(x,id_x)` | `pathout_refl_obj Z x` |
| `rho_{x,y,p}` | `pathout_refl_arrow Z x y p` |
| `E[rho_{x,y,p}]` | `pathout_refl_eval_base_func Z x y p E` |
| `PathOutMotives_Z` | `PathOutMotives_catd Z` |
| `PathOutReflEval_Z` | `PathOutReflEval_funcd Z` |
| `PathOutPi_Z` | `PathOutPi_funcd Z` |
| fixed-source path induction | `PathInd_func Z x` |
| telescope path induction | `PathInd_transfd Z` |
| Sigma-total path induction | `PathInd_funcd Z` |
| composition target | `CompTarget_catd Z x` |
| composition motive | `CompMotive_catd Z x` |
| composition section | `path_comp_sec Z x` |
| composition functor for `p` | `path_comp_func Z x y p` |

# Appendix B. Selected Checked Normal Forms

The article should quote checked normal forms in compact mathematical notation
and keep the fully expanded Lambdapi terms available as regression references.
The following statements are covered by `emdash3_2_checks.lp`.

Core PathOut and rho checks:

```text
PathOut_Z(x) = Sigma_cat Z (Rep_Z(x))
PathOut_transport(p)[(z,q)] = (z,q o p)
PathOut_transport(p)[(y,id_y)] = (y,p)
Rep_Z(x)[p](id_x) = p
rho_{x,y,p} = sigma_transport_arrow(Rep_Z(x),p,id_x)
PathOut_transport(p)(rho_{y,z,q}) ; rho_{x,y,p}
  = rho_{x,z,q o p}
```

Path-induction projection checks:

```text
PathInd_func(Z,x)[E] = path_ind_func_fapp0(Z,x,E)
PathInd_func(Z,x)[E](u) = path_ind_sec(Z,x,E,u)
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

path_ind_sec(CompMotive_Z(x), id_Rep_Z(x)) = path_comp_sec(x)
path_comp_sec(x)[p] = path_comp_func(p)
path_comp_func(p)[z][q] = q o p
```

The two expanded routes that matter most are:

```text
expanded(PathInd_transfd, CompMotive_Z(x), p, q) = q o p
expanded(PathInd_funcd, CompMotive_Z(x), p, q) = q o p
```

# Appendix C. Diagram Source Notes

All figures in this draft are Arrowgram JSON blocks. They are intentionally
simple: the diagrams explain object and arrow flow, while the actual
normalization claims are made by Lambdapi assertions in `emdash3_2_checks.lp`.
