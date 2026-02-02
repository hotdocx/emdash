Subject: GPT 5.2 vs ω-categories — Re: [FOM] Autoformalization getting easy?

Dear Josef Urban, dear FOM,

Indeed, as soon as you can setup some « MathOps » (i.e. math DevOps engineering) for a long-running “LLM ↔ proof-checker” feedback loop (fast checker + minimal trusted core library) then your “≈130k lines in two weeks” as reported in arXiv:2601.03298 is totally feasible. 

Emdash v2 — Functorial programming for strict/lax ω-categories in Lambdapi [ `https://github.com/hotdocx/emdash` ] is such a "core library", and once that loop is tight, GPT 5.2 with Codex CLI can sustain large formal developments. Key learning: "mathops/devops engineering" matters: Gemini 3 Pro + Gemini CLI was bad (even if maybe Gemini 3 Pro defeats GPT 5.2 in "pure thinking").

## 0) “Internal” kernel aspects: why this scales to a real language / proof assistant

The core v2 idea is to treat large swaths of “diagram chasing” as **normalization** rather than as external propositions. Concretely, `emdash2.lp` is written in a *rewrite-head discipline*: we expose stable head symbols for categorical computation (e.g. `comp_fapp0`, `fapp1_fapp0`, `tapp0_fapp0`, `tapp1_fapp0`), and then orient coherence as rewrite rules and unification hints on those heads. This has two practical consequences for a future user-facing proof assistant:

- **Traditional surface syntax becomes an elaboration problem**. You can write textbook terms with implicit arguments, binder sugar, and “pasting-like” expressions; elaboration compiles them down to a small set of stable heads, and definitional equality is decided by normalization.
- **Definitions/technical-debt concerns are shifted to the kernel interfaces**. Instead of auto-generated proofs that are 10× longer than necessary, normalization compresses composites into canonical stable heads, and many coherence steps become one-step reductions. This is exactly the direction we took in the v1 prototype kernel (TypeScript) described in `emdash_cpp2026.md`; v2 extends that pipeline with the ω-category-facing stable heads and rewriting discipline specified in `emdash2.lp` and documented in `print/public/index.md`.


## 1) Dependent comma/arrow for a dependent category (`homd_cov` in emdash2.lp)

We use displayed/dependent categories over a base category B (morally a fibration E : B → Cat, i.e. a displayed category over B).

For:
- b₀ ∈ B and e₀ ∈ E(b₀).

Then the dependent comma/arrow (“dependent hom”, triangle classifier) is the functor
- Homd_E(e₀, –) : E ×_B (Hom_B(b₀, –))ᵒᵖ → Cat.

On a base arrow b₀₁ : b₀ → b₁ and a fibre object e₁ ∈ E(b₁), it returns the fibre hom-category
- Hom_{E(b₁)}( (b₀₁)! e₀ , e₁ ).

This is the entry point for iterating simplicially (triangles → tetrahedra → …) with rewriting as normalization.

And the functoriality of `Homd_E(e₀, –)`, especially in the second argument  `(Hom_B(b₀, –))ᵒᵖ`, espresses precisely the "stacking" of 2-cells along 1-cells (generalized horizontal composition of 2-cells).

- A key learning is that an **internal** computational-logic for lax ω-categories is easier to express, by Lambdapi and AI agents, than for only strict 1-categories; because the hom-part of a category `Hom(x,–)` is recursively a (fibred) category and the hom-part of a functor `F₁ : Hom(x,–) → Hom(F₀ x, F₀ –)` is recursively a (non-cartesian) fibred functor. (`fapp1_funcd` in emdash2.lp)

## 2) Naturality as “accumulation” (rewrite rules) and the exchange law as normalization

In emdash, transfors (transformations) are not primarily exposed as records “with a naturality equation”, but via *projection heads* for components:

- diagonal components on objects: `tapp0_fapp0 … ϵ X` (think: $\\epsilon_X$),
- off-diagonal / arrow-indexed components: `tapp1_fapp0 … ϵ α` (think: $\\epsilon_{(\\alpha)}$ over a 2-cell/base-arrow $\\alpha$).

The key point is that **naturality can be oriented as an “accumulation” rewrite** on these off-diagonal components, e.g. schematically:
$$
(\\epsilon_{(g)}) \\circ F(f) \\;\\rightsquigarrow\\; \\epsilon_{(g\\circ f)}.
$$
This makes “pasting diagrams” *computationally unambiguous*: you do not need to choose a parenthesization up front; normalization accumulates the base-arrow index as you compose.

An important sanity check is a concrete **exchange law** instance for postcomposition. In the notations of the paper (`print/public/index.md`), with two vertically composable 2-cells $\\alpha:X\\Rightarrow Y$ and $\\beta:Y\\Rightarrow Z$ in a hom-category and a horizontal 2-cell coming from postcomposition, we normalize the same pasted diagram in two ways and get the same normal form:
$$
\\mathrm{postcomp}(g)(\\beta) \\circ \\epsilon_{(\\alpha)} \\;=\\; \\epsilon_{(\\beta\\circ\\alpha)}.
$$

## 3) MathOps and arrowgram diagrams specification

One MathOps requirement was to enable the AI coding agent to (natively) understand and generate commutative diagrams; therefore I built **arrowgram**: a strict JSON specification for commutative diagrams, meant to be understood and generated by AI coding agents. `arrowgram` https://github.com/hotdocx/arrowgram/ is open-source and comes with an AI diagram editor/generator exporting JSON/SVG/PNG/TikZ, and a paper document editor that renders markdown with embedded arrowgram diagrams (and with KaTeX + Mermaid + Vega-Lite via Paged.js). And the host app `LastRevision` https://hotdocx.github.io adds an extra academic-publisher (i.e. "sharing") layer on top of this new `arrowgram` paper format.


Best regards,
— m— / emdash project

---

Appendix: Arrowgram JSON specs

1) “Stacking along a 1-cell” as a tetrahedral over-a-base-edge picture (schematic)

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

2) Exchange law (pasting diagram): two vertical 2-cells plus one horizontal 2-cell

```json
{
  "version": 1,
  "nodes": [
    { "name": "M", "label": "$M$", "left": 80, "top": 220 },
    { "name": "N", "label": "$N$", "left": 320, "top": 220 },
    { "name": "L", "label": "$L$", "left": 560, "top": 220 }
  ],
  "arrows": [
    { "name": "x", "label": "$x$", "from": "M", "to": "N", "curve": 250, "label_alignment": "left" },
    { "name": "y", "label": "$y$", "from": "M", "to": "N", "curve": 0, "label_alignment": "over" },
    { "name": "z", "label": "$z$", "from": "M", "to": "N", "curve": -250, "label_alignment": "right" },
    { "name": "f", "label": "$f$", "from": "N", "to": "L", "curve": 250, "label_alignment": "left" },
    { "name": "g", "label": "$g$", "from": "N", "to": "L", "curve": 0, "label_alignment": "right" },
    { "name": "fx", "label": "$f\\circ x$", "from": "M", "to": "L", "curve": 400, "label_alignment": "left", "style": { "body": { "name": "dashed" } } },
    { "name": "gy", "label": "", "from": "M", "to": "L", "curve": 0, "label_alignment": "over", "style": { "body": { "name": "none" } } },
    { "name": "gz", "label": "$g\\circ z$", "from": "M", "to": "L", "curve": -400, "label_alignment": "right", "style": { "body": { "name": "dashed" } } },
    { "label": "$\\alpha$", "from": "x", "to": "y", "label_alignment": "left", "style": { "level": 2 } },
    { "label": "$\\beta$", "from": "y", "to": "z", "label_alignment": "right", "style": { "level": 2 } },
    { "label": "$\\epsilon ≔ e ∘ —$", "from": "f", "to": "g", "label_alignment": "left", "style": { "level": 2, "body": { "name": "solid" } }, "shorten": { "source": 0 } },
    { "label": "$\\epsilon_{(\\alpha)}$", "from": "fx", "to": "gy", "label_alignment": "left", "style": { "level": 2 } },
    { "label": "$g(\\beta)$", "from": "gy", "to": "gz", "label_alignment": "right", "style": { "level": 2 } }
  ]
}
```
