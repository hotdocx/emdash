# Book Style And Evidence Contract

This file governs prose written for *Functorial Type Theory: Univalent
Foundations for Mathematics*. Kernel-development policy remains in the root
`AGENTS.md` and current SOP.

## Voice

- Lead with a mathematical question, construction, or theorem.
- Use mathematical notation in the main line and place Lambdapi identifiers in
  compact formal-status notes.
- Explain why a construction is needed before cataloguing its components.
- Treat directionality as mathematical content, especially when comparison
  with homotopy type theory might otherwise import invertibility silently.
- Do not call the current calculus a complete weak omega-category semantics or
  a complete computational univalence metatheory.

## Formal status

Every theorem-like claim has exactly one status:

- **Checked:** an active declaration and reviewer/check evidence support the
  stated interface.
- **Formal consequence:** the claim follows from named checked premises but is
  not packaged under the stated name.
- **Mathematical development:** free-form theory with explicit prerequisites
  and a plausible future emdash owner.
- **Research boundary:** conjectural or blocked on named infrastructure.

Use a block of the following form near the claim:

```markdown
> **Formal status — checked.** Evidence `WE-HOM-NAT-CARRIER`.
```

For checked claims, add a marker consumed by the book checker:

```html
<!-- evidence:WE-HOM-NAT-CARRIER -->
```

The evidence register is traceability metadata, not a substitute for a proof
or readable exposition.

## WalkingEnd boundary

- Keep the opaque `WalkingEnd_cat` separate from the concrete
  `BNat_cat` model.
- State the implemented result as a carrier equivalence unless a stronger
  package has actually been added.
- Construct and explain the directed normalization cell before using
  hom-discreteness to extract equality.
- Do not add inverse powers, predecessor action, or group cancellation to the
  directed argument.
- Mark monoid preservation, a reverse BNat functor, full hom-category
  equivalence, and full functor-category initiality as absent until checked.

## HoTT adaptation and attribution

Before adapting a passage from the HoTT Book:

1. add an entry to
   `book/references/third-party-sources.json` identifying the source
   file, section or label, and adaptation type;
2. retain the pinned source revision;
3. make the adaptation and directionality changes clear;
4. preserve the attribution and ShareAlike notice in
   `book/CREDITS.md`;
5. do not paste upstream text into a source file while the provenance entry is
   absent.

Near-verbatim quotation should be rare. Prefer a fresh derivation adapted to
the functorial setting.

## Notation

The canonical surface-syntax report owns notation. In particular:

```text
a ->^C b                 ordinary hom
F : A ⊢ B                ordinary functor
E : K ⊢ Cat              directed Cat-valued family
Π (k :^n K), E[k]        section category
```

Book-only abbreviations must be declared in the notation appendix and must not
be described as implemented parser syntax.

## Source mechanics

- Each source file begins with one stable explicit HTML anchor.
- Source files do not contain YAML frontmatter; the assembler owns it.
- Link to stable anchors, never generated line numbers.
- Do not edit `print/public/emdash-book.md`.
- Avoid timestamps, absolute host paths, and generated build data in prose.
