Subject: GPT 5.2 vs ω-categories — Re: [FOM] Autoformalization getting easy?

Dear Josef Urban, dear FOM,

many thanks for your note and for posting “130k Lines of Formal Topology in Two Weeks: Simple and Cheap Autoformalization for Everyone?” (arXiv:2601.03298). The “LLM ↔ fast checker” feedback loop you describe resonates strongly with what we have been exploring in the emdash project, albeit in a rather different direction (higher categories and rewrite-based normalization).

I’m writing to highlight one specific design pattern from our current public write-up (`print/public/index.md`) that seems relevant to Kevin Buzzard’s “Definitions / technical debt” concerns, and to your “autoformalization getting easy?” intuition:

1) A *definition* that makes later coherence “compute”: dependent arrow/comma (`homd_cov`)
2) An observation that surprised us in practice: in a rewrite-oriented type-theoretic kernel, *strict ω-categories can actually be easier to express than 1-categories*, because higher coherence lives as higher cells (data) rather than as propositional equality (proofs).

## 1) The dependent comma/arrow of a dependent category (`homd_cov`)

In `emdash2.lp` (a Lambdapi specification), we work with **displayed / dependent categories** over a base `Z` (morally a fibration `E : Z → Cat`). In the special (computational) case where such a dependent category is given by a Grothendieck construction `∫E0` for a Cat-valued functor `E0 : Z → Cat`, we have strict transport on fibre objects along base arrows (currently strict, intended to become lax later).

Fix:

- a base category `Z`,
- a dependent category `E` over `Z`,
- a chosen base object `W_Z : Ob(Z)` and chosen fibre object `W ∈ E[W_Z]`,
- a “probe” displayed category `D` over `Z` together with a displayed functor `FF : D → E` (over `id_Z`).

Then the central “triangle classifier” is a Cat-valued functor called `homd_cov`. In the Grothendieck–Grothendieck case, it has a pointwise *computation rule* which, informally, says:

- given `f : W_Z → z` in `Z` and `d ∈ D[z]` (so `FF_z(d) ∈ E[z]`),
- the value of `homd_cov` at `(z, d, f)` reduces definitionally to the hom-category in the fibre:
  \[
    \mathrm{Hom}_{E_0(z)}(f_!(W), FF_z(d)).
  \]

This is exactly the **dependent arrow / dependent comma** construction: it is the category of “displayed arrows over a chosen base arrow”, i.e. triangles whose base edge is fixed to be `f`.

Why this matters for autoformalization is that it gives a *canonical, compositional home* for “2-cells over a base edge”, from which one can iterate:

- a 2-cell becomes an object in a dependent hom category (“a triangle over a base edge”),
- a 3-cell becomes an object in an iterated dependent hom (“a tetrahedron over a base triangle”),
- etc., yielding a simplicial organization of higher cells that is friendly to computation by rewriting.

In other words: instead of encoding naturality/exchange/coherence as separate propositions, we try to design *stable head symbols + rewrite rules* so that diagram chasing becomes normalization.

## 2) Why ω-categories can be easier than 1-categories (for type theory + rewriting + AI)

This may sound backwards, but in a rewrite-driven kernel the “1-categorical” stopping point is often the annoying one:

- In a 1-category formalization, “2-dimensional structure” typically gets forced into propositional equality of morphisms (or setoid equality), which is exactly where proof assistants (and LLM-driven code generation) can accumulate debt: you end up with large proof terms, fragile rewrite/unification behavior, and lots of transport bookkeeping.
- In an ω-categorical presentation where `Hom(x,y)` is itself a category (and recursively so), higher coherence is represented as *directed higher cells* instead of *equations that must be proved*. For a computational account, this is a feature: you can orient coherence as rewrite rules on stable heads.

So, while *weak* ω-categories are of course conceptually deep, a *strict/lax ω-category kernel with explicit higher-cell interfaces* can be structurally uniform in a way that is particularly amenable to “AI coding assistant” workflows: the agent repeatedly instantiates the same patterns (stable-head application, functoriality folding, dependent-hom iteration) rather than inventing bespoke proof scripts for each coherence lemma.

This is one sense in which “autoformalization getting easy?” might first become true for domains where:

- the definitions can be engineered so that major equalities compute (normalization),
- and higher structure is made explicit as data (cells) rather than implicit as equality proofs.

If useful, the best “single page” overview of these ideas is currently our public narrative (`print/public/index.md`), especially §6 “Dependent Arrow/Comma Categories: `homd_cov`”.

Best regards,
— m— / emdash project

---

Appendix: Arrowgram JSON specs (copy/paste into the Arrowgram editor)

Notes:
- Labels use KaTeX/LaTeX; JSON strings require `\\` for backslashes.
- You can rename node IDs freely as long as arrows reference them consistently.

1) A displayed arrow over a base arrow (triangle over a base edge)

```json
{
  "version": 1,
  "nodes": [
    { "name": "e",  "left": 120, "top": 80,  "label": "$e\\in E(b)$" },
    { "name": "x",  "left": 520, "top": 80,  "label": "$x\\in E(b')$" },
    { "name": "b",  "left": 120, "top": 240, "label": "$b$" },
    { "name": "bp", "left": 520, "top": 240, "label": "$b'$" }
  ],
  "arrows": [
    { "from": "b",  "to": "bp", "label": "$f$", "label_alignment": "left" },
    { "from": "e",  "to": "x",  "label": "$\\sigma : f_!e \\to x$", "curve": 40, "label_alignment": "left" },
    { "from": "e",  "to": "b",  "label": "$p$", "label_alignment": "right", "style": { "body": { "name": "dashed" } } },
    { "from": "x",  "to": "bp", "label": "$p$", "label_alignment": "left", "style": { "body": { "name": "dashed" } } }
  ]
}
```

2) A 2-cell between parallel composites (arrow-to-arrow 2-cell)

```json
{
  "version": 1,
  "nodes": [
    { "name": "X", "label": "$X$", "left": 120, "top": 120 },
    { "name": "Y", "label": "$Y$", "left": 420, "top": 120 },
    { "name": "Z", "label": "$Z$", "left": 270, "top": 320 }
  ],
  "arrows": [
    { "name": "f",  "label": "$f$",       "from": "X", "to": "Y", "label_alignment": "right" },
    { "name": "g",  "label": "$g$",       "from": "Y", "to": "Z", "label_alignment": "right" },
    { "name": "h",  "label": "$h$",       "from": "X", "to": "Z", "curve": -200,  "label_alignment": "left" },
    { "name": "gf", "label": "$g\\circ f$", "from": "X", "to": "Z", "curve": 200, "label_alignment": "right" },
    { "from": "gf", "to": "h", "label": "$\\alpha$", "label_alignment": "left", "style": { "level": 2, "mode": "arrow" } }
  ]
}
```

3) “Stacking along a 1-cell” as a tetrahedral over-a-base-edge picture (schematic)

```json
{
  "version": 1,
  "nodes": [
    { "name": "v0", "label": "$\\bullet$",      "left": 0,   "top": 150 },
    { "name": "v1", "label": "$b_0\\ \\bullet$", "left": 190, "top": 0   },
    { "name": "v2", "label": "$\\bullet\\ b_1$", "left": 190, "top": 150 },
    { "name": "v3", "label": "$\\bullet\\ b_2$", "left": 300, "top": 265 }
  ],
  "arrows": [
    { "name": "e0", "label": "$e_0$",    "from": "v0", "to": "v1", "label_alignment": "right", "style": { "level": 1 } },
    { "name": "e1", "label": "$e_1$",    "from": "v0", "to": "v2", "label_alignment": "left",  "style": { "level": 1 } },
    { "name": "e3", "label": "$b_{01}$", "from": "v1", "to": "v2", "label_alignment": "left",  "style": { "level": 1 } },
    { "name": "e2", "label": "$b_{12}$", "from": "v2", "to": "v3", "label_alignment": "left",  "style": { "level": 1, "body": { "name": "dashed" } } },
    { "name": "e4", "label": "$b_{02}$", "from": "v1", "to": "v3", "label_alignment": "right", "style": { "level": 1, "body": { "name": "dashed" } } },
    { "name": "e5", "label": "$e_2$",    "from": "v0", "to": "v3", "label_alignment": "left",  "style": { "level": 1, "body": { "name": "dashed" } } },
    { "name": "e01", "label": "$e_{01}$", "from": "e0", "to": "e1", "label_alignment": "right", "style": { "level": 2 } },
    { "name": "e12", "label": "$e_{12}$", "from": "e1", "to": "e5", "label_alignment": "right", "style": { "level": 2 } },
    { "name": "b012op", "label": "$b_{012}^{op}$", "from": "e4", "to": "e2", "label_alignment": "left", "style": { "level": 2 } }
  ]
}
```
