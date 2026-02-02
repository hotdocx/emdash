Subject: GPT 5.2 vs ω-categories — Re: [FOM] Autoformalization getting easy?

I read arXiv:2601.03298. A striking (and actionable) data point is the reported “≈130k lines in two weeks” at low subscription cost, driven by coding agents inside a tight loop against a fast checker. One key practical insight that matches our experience: the long-running “LLM ↔ proof-checker” feedback loop (fast checker + minimal trusted core library) is the main multiplier; once that loop is tight, the assistant can sustain large formal developments.

A related perspective from our ongoing emdash experiment (`emdash2.lp` in Lambdapi; public narrative `print/public/index.md`):

## 1) Dependent comma/arrow for a dependent category (`homd_cov`)

We use displayed/dependent categories over a base category B (morally a fibration E : B → Cat, i.e. a displayed category over B).

Fix (notation as in our Figure 6 / abstract):
- b₀ ∈ B and e₀ ∈ E(b₀).

Then the dependent comma/arrow (“dependent hom”, triangle classifier) is the functor
- Homd_E(e₀, –) : E ×_B (Hom_B(b₀, –))ᵒᵖ → Cat.

On a base arrow b₀₁ : b₀ → b₁ and a fibre object e₁ ∈ E(b₁), it returns the fibre hom-category
- Hom_{E(b₁)}( (b₀₁)! e₀ , e₁ ).

In the current kernel snapshot, when E is a Grothendieck total ∫E₀ (and similarly for the probe), this is a definitional computation rule: evaluating `homd_cov` at the triple (b₁, e₁, b₀₁) normalizes to that fibre hom. This is the entry point for iterating simplicially (triangles → tetrahedra → …) with rewriting as normalization.

## 2) Why strict/lax ω-cats can be easier than 1-cats (for TT + rewriting + AI)

In a 1-category formalization, 2D structure tends to get forced into propositional equality of 1-cells (or setoids), which is where agent-generated code often becomes long and brittle (transport/equality glue). In a strict/lax ω-categorical presentation with `Hom(x,y)` itself a category (recursively), coherence can be explicit higher-cell data, and many “diagram chases” can be oriented as normalization on stable rewrite heads. That uniformity is unexpectedly agent-friendly.

## 3) Arrowgram + LastRevision: machine-checkable diagrams/papers

Separately, we built **Arrowgram**: a strict JSON `DiagramSpec` for commutative diagrams (validated by `@arrowgram/core`), a web editor (`packages/web`) exporting SVG/PNG/TikZ, and a paper viewer (`packages/paged`) that renders Markdown with KaTeX + Arrowgram + Mermaid + Vega-Lite via Paged.js. **LastRevision** (`packages/lastrevision`) is the private SaaS host adding remote persistence/auth/attachments + an AI proxy while keeping the same diagram core. The appendix JSON blocks are valid Arrowgram specs (paste into the editor, or embed in Markdown).

Best regards,
— m— / emdash project

---

Appendix: Arrowgram JSON specs

Note: JSON strings require `\\` for LaTeX backslashes.

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
