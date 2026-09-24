# EMDASH Literature Workflow

Date: 2026-06-16
Navigation reviewed: 2026-09-23

Purpose: keep literature discovery useful without letting external papers
replace the current v3.2 design authority.

## Source Priority

Use papers and books to clarify mathematics, terminology, examples, and
reviewer-facing milestones. Follow the authority order in
[the formal SOP](../AGENTS.md#authority-and-document-roles) for project-local
architecture; external references do not override active owners, profile
qualifications or retained counterexamples.

Start with the [local resource index](LOCAL_RESOURCES.md) before downloading
another copy. It routes to the existing homological/spectral reading inventory
and book provenance records. Availability, substantive reading, successful
external builds and transferred emdash results are distinct claims.

The existing [arXiv helper](../scripts/arxiv_search.py) searches metadata and
caches API responses under `.cache/arxiv/`. It does not download a PDF library
or manage citations. The commands below run from `emdash2/`. For a retained
local PDF, record its source/version and reading coverage in the relevant
existing review; use extracted text for search and the PDF/source for exact
formulas. Keep the book's bibliography and adaptation ledger with the book.

## arXiv / ar5iv SOP

- Use the arXiv API for repeatable searches and bibliographic metadata.
- Use ar5iv HTML pages for quick skimming, browser search, and copying section
  headings.
- Use the arXiv PDF or source when exact formulas, definitions, or citation
  details matter.
- Record the arXiv id and version when a result influences design.
- Do not treat an ar5iv rendering failure as evidence about the paper.

## Starter Queries

Run these through `scripts/arxiv_search.py` and save useful notes under
`research/notes/`.

```bash
python3 scripts/arxiv_search.py \
  --query 'cat:math.CT AND (abs:"omega category" OR abs:"higher category")' \
  --max-results 25 \
  --sort lastUpdatedDate

python3 scripts/arxiv_search.py \
  --query 'cat:math.CT AND (abs:polygraph OR abs:computad OR abs:"higher dimensional rewriting")' \
  --max-results 25 \
  --sort relevance

python3 scripts/arxiv_search.py \
  --query '(cat:math.LO OR cat:cs.LO) AND abs:"dependent type theory" AND abs:"category theory"' \
  --max-results 25 \
  --sort lastUpdatedDate

python3 scripts/arxiv_search.py \
  --query '(cat:math.CT OR cat:cs.LO) AND (abs:"displayed category" OR abs:"Grothendieck construction")' \
  --max-results 25 \
  --sort relevance

python3 scripts/arxiv_search.py \
  --query '(cat:math.LO OR cat:cs.LO) AND (abs:"proof assistant" OR abs:formalization) AND abs:category' \
  --max-results 25 \
  --sort lastUpdatedDate
```

## Review Notes Template

Use one file per theme or paper cluster:

```text
research/notes/YYYY-MM-DD_topic.md
```

Suggested structure:

```markdown
# Topic

## Papers

- arXiv:NNNN.NNNNNvN - Title
  - arXiv: https://arxiv.org/abs/NNNN.NNNNN
  - ar5iv: https://ar5iv.labs.arxiv.org/html/NNNN.NNNNN

## Useful Definitions

## Possible EMDASH Milestones

## Non-Goals / Do Not Port Directly
```

## Candidate Milestone Themes

- path category and equality-to-arrow bridges;
- strict and weak omega-categorical composition;
- computads, polygraphs, and higher-dimensional rewriting;
- displayed categories and Grothendieck/Sigma total categories;
- dependent type theory with directed or categorical contexts;
- categorical proof theory and cut-elimination in categories;
- formalized category theory libraries and their CI/review practices.
