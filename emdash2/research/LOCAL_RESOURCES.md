# Local Research Resources

Inventory observed: 2026-09-23; HoTT reference layout repaired 2026-09-24,
on the `/home/user1` development host.
Purpose: find existing material before searching or downloading again.

These paths are optional research aids, not portable build dependencies or
mathematical authority. Check availability and revision before use. This
inventory inspected filenames and Git metadata; it does not claim new paper
reading or successful builds. Follow the [literature workflow](literature.md)
and [formal SOP](../AGENTS.md).

## Existing reading and citation owners

- [Homological and categorical-spectra references](../../docs/TYPESCRIPT_EMDASH_HOMOLOGICAL_REDESIGN_REFERENCES.md)
  owns HRI identifiers, bibliographic versions and recorded reading coverage.
- [Posur/homalg review](../../docs/TYPESCRIPT_EMDASH_POSUR_HOMALG_REDESIGN_REVIEW.md)
  and [homology internalization review](../../docs/TYPESCRIPT_EMDASH_HOMOLOGY_INTERNALIZATION_REDESIGN_REVIEW.md)
  record the actual mathematical comparisons.
- [Dependent-spectra review](../../docs/EMDASH_DEPENDENT_SPECTRA_RESEARCH_REVIEW.md)
  distinguishes reference arguments from proposed higher constructions.
- The book owns its [bibliography](../book/references/bibliography.md) and
  [third-party adaptation ledger](../book/references/third-party-sources.json).
  Keep citation/license/provenance updates there when changing book sources.

## PDF and text collections

Counts cover top-level files only. Matching `.txt` files are search aids;
extraction can lose formulas, indices and diagrams. Inspect the PDF or original
source before relying on an exact mathematical statement. Preserve versions
already named in filenames; do not silently replace them with a newer download.

| Directory | Available material | Reading route |
| --- | --- | --- |
| `/home/user1/algebraic-geometry/` | 20 PDFs and 21 text files: Lurie HA, HTT and Stable Infinity Categories; van Doorn; Heine; Hadzihasanovic; Cisinski; Posur/homalg; Zeuner; Tabareau; Pédrot | HRI inventory and the reviews above; the extra `review-of-max-zeuner.txt` is a note, not a PDF extraction |
| `/home/user1/dosen-book/` | Two PDF/text pairs: Došen's cut-elimination book and Petrić–Zekić coherence for closed categories with biproducts | HRI-01 and the internalization review |
| `/home/user1/misc-ai-proof-assistant/` | Two PDF/text pairs: Kimina Prover and Recursive Reasoning with Tiny Networks | Auxiliary agent research; not default mathematical context |

Useful filename stems in `algebraic-geometry/`:

- `lurie-Higher-Algebra-HA`, `lurie-Higher-Topos-Theory-HTT`,
  `lurie-Stable-Infinity-Categories-0608228v5`;
- `vandoorn-On-the-Formalization-of-Higher-Inductive-Types-and-Synthetic-Homotopy-Theory-1808.10690v1`;
- `Heine-Stable-homotopy-theory-of-higher-categories-2605.05195v1`,
  `Hadzihasanovic-Combinatorics-of-higher-categorical-diagrams-2404.07273v2`,
  `cisinski-Book-project-Synthetic-Category-Theory-2026-sep-7`;
- `posur-*` and `barakat-*` locate the constructive category/homalg cluster;
  both the arXiv and journal versions of the Freyd paper are retained;
- `max-zeuner-*`, `nicolas-tabareau-*` and `pedrot-*` locate the
  constructive geometry, sheafification and comparison material.

To list exact names without searching every extracted book:

```bash
rg --files /home/user1/algebraic-geometry /home/user1/dosen-book \
  /home/user1/misc-ai-proof-assistant -g '*.pdf' -g '*.txt'
```

The Lurie HA/HTT filenames alone do not identify a precise edition. Verify
their internal date and acquisition evidence when citing them; no new edition
identification or content hash is claimed by this inventory.

## Source checkouts

All five listed checkouts were clean when inspected. The two spectral copies
have the same revision; neither needs another download for source reading.

| Local path | Observed revision | Use and qualification |
| --- | --- | --- |
| `/home/user1/cmu-phil-spectral` | `3b078f5f1de251637decf04bd3fc8aa01930a6b3` | `cmu-phil/spectral`, historical Lean 2 reference; start with `README.md`, `algebra/exact_couple.hlean`, `cohomology/serre.hlean`; no build claimed |
| `/home/user1/algebraic-geometry/cmu-phil-spectral` | Same revision | Duplicate reference checkout already recorded by HRI-03; leave removal to a separate cleanup decision |
| `/home/user1/lean4-source-code` | `f29e9e488ea8242c875806e4b0564820c2d553b2` | `leanprover/lean4`; implementation reference, not an emdash runtime dependency |
| `/home/user1/lambdapi-source-code` | `40b12b4e2615c60340608ab9656ed9eb1dc0c070` | `Deducteam/lambdapi`; this checkout does **not** contain the pinned verification commit below |
| `/home/user1/hott-book` | `578b85cc8d586b1677ec4335148adeb443057d24` | `HoTT/book`; standalone TeX reference, same pin as the book adaptation ledger |

The [verification toolchain](../../toolchains/verification.json) pins Lambdapi
`db4f7809961b8c107247613067fb567491fb0b84`. Do not diagnose that checker's
implementation from the different local HEAD without checking the difference.
If exact implementation reading is needed, obtain a separate matching source
checkout; this inventory neither fetches nor switches the existing checkout.
Repository copies of selected Lambdapi docs/examples are already listed in
the [local-reference SOP](../AGENTS.md#local-lambdapi-references).

The HoTT book is research input, not a build dependency: book source,
bibliography and adaptation attribution are already maintained in this repo.
On 2026-09-24 a clean standalone checkout was copied locally with independent
Git objects and the upstream origin, at the exact pin above. The undeclared
`.hott-book-review-20260720` Git link was removed on the consolidation branch;
its original local checkout was preserved intact at
`/home/user1/hott-book-review-20260720` during main integration. Use
`/home/user1/hott-book` as the canonical local reading copy. No book attribution,
adaptation record or source bytes changed.

On another host, optional acquisition at the recorded book revision is:

```bash
git clone https://github.com/HoTT/book.git /path/to/references/hott-book
git -C /path/to/references/hott-book checkout --detach 578b85cc8d586b1677ec4335148adeb443057d24
```

Choose a fresh destination; this reference checkout does not need a build.

A bounded directory-name search through three visible directory levels under
`/home/user1` did not locate standalone Agda/Coq/HoTT formalization checkouts
beyond these references. CloserFans has a `templates_artifacts/jscoq` template;
that is not evidence of a checked-out Coq/HoTT research library. Absence from
this inventory does not establish that no other local copy exists.

## Project identity

The active repository is `/home/user1/emdash1`. Sibling `/home/user1/closerfans`
owns hosted workspaces/platform integration; `/home/user1/arrowgram` owns
diagram/document tooling. Read each repository's own guidance when working
there. Their existence does not authorize platform operations or publication.

`/home/user1/emdash`, `/home/user1/emdash-doc` and
`/home/user1/emdash_template` are distinct older locations, not aliases for
this checkout or its `emdash-template/` distributable fixture. A previous
platform book assessment used the wrong `emdash` directory; its correction is
recorded in CloserFans' September 1 Emdash1 book-workspace correction plan.
Do not use those copies as the current mathematical or book authority.
