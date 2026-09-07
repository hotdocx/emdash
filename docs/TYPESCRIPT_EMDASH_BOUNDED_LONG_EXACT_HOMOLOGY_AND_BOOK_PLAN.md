# TypeScript/emdash Bounded Long Exact Homology And Book Plan

Date: 2026-09-03

Plan-ID: `TS-EMDASH-BOUNDED-LONG-EXACT-HOMOLOGY-AND-BOOK`

Status: active on a dedicated branch/worktree

Baseline: `054b43bd777d260f5da8b1242294ce0335780d0d`

Branch: `goal/bounded-long-exact-homology-book-v3.2`

Worktree: `/home/user1/emdash1-long-exact-v1`

Decision-Response-Evidence:

- `/home/user1/emdash1/emdash2/tmp/ai-responses/sessions/2026-08-23_01a02f686142/responses/0109_2026-09-03T09-11-42Z_01a06681-10dc-7941-b48b-b879a4729fe0.md`

## Purpose

This plan governs the next computational-and-internal vertical slice shared by
the generic categorical kernel, bounded polynomial Freyd homology, the
CAP-like categorical-program compiler, the witnessed formal Freyd boundary,
the proof–CAS workflow, and the emdash book:

**complete six-term snake exactness, specialize it to bounded short-exact
sequences of complexes, assemble the resulting bounded long exact homology
sequence, and explain the resulting architecture in the book.**

The completed baseline already supplies:

- additive and computational Abelian categories;
- genuine fiber products and pushouts with contractible factor spaces;
- pullback stability of epimorphisms and pushout stability of monomorphisms;
- image/coimage comparisons and constructive bimorphism evidence;
- witness-rich exactness and short-exact triples;
- one-degree and bounded polynomial Freyd homology;
- bounded chain maps and induced homology maps;
- the generic nonsplit snake connecting arrow, both derived normal tests, and
  a whole final factor-space result;
- native, categorical, formal witnessed, proof–CAS, and independent
  constant-field implementations of that connecting construction.

The missing dependency chain is:

```text
local exactness + completed connecting arrow
  → full six-term snake maps and exactness
  → canonical selected short-exact rows
  → usability comparison with arbitrary witnessed short-exact rows
  → degreewise short-exact bounded complexes
  → one exact homology window
  → complete finite long exact homology sequence
  → native/categorical/formal/proof–CAS agreement
  → evidence-bearing book exposition and architecture review.
```

The long exact sequence is not treated as a formatting loop over already
identical endpoints. The goal must expose and solve the comparison between the
canonical snake endpoints and the existing selected homology objects. It must
not create a second homology theory merely to avoid that comparison.

## Preparatory Integration And Git Boundary

Before this worktree was created, clean historical `main` in
`/home/user1/emdash1` was fast-forwarded from the completed Freyd-homology
baseline `4036ef47be6c3f82dcac05c257c98b2201c101d7` to the completed snake head
`054b43bd777d260f5da8b1242294ce0335780d0d`. The reviewed ancestry was exactly
`0 28`; both worktrees were clean. No path-cubical, global-strictness, or other
orthogonal branch was integrated.

Historical book branches have no commits absent from the integrated baseline
and are not resumed. Book work for this goal occurs in this new worktree after
the corresponding implementation claims are checked.

The user explicitly authorized this plan, branch/worktree, persistent goal,
implementation continuation, the preparatory fast-forward, and local validated
checkpoint commits following the repository Git SOP. This does not authorize
push, publication, release, PR creation, any further merge to `main`, rebase,
amend, reset, history rewriting, branch deletion, or worktree removal.

The baseline commit remains comparison and backtracking evidence. It is not
permission to discard descendant work.

## Why The Full Long Exact Sequence Is Not The First Declaration

The completed generic construction starts from a composable triple

```text
A --delta--> B --beta--> C --lambda--> D
```

and a retained point witnessing

```text
lambda o beta o delta = 0.
```

It selects induced arrows

```text
gamma : Coker(delta) -> D
alpha : A -> Ker(lambda)
```

and constructs

```text
partial : Ker(gamma) -> Coker(alpha).
```

This is the middle connecting arrow. It is not yet the complete exact sequence

```text
Ker(alpha) -> Ker(beta) -> Ker(gamma)
           -> Coker(alpha) -> Coker(beta) -> Coker(gamma).
```

Nor is it immediately a homology map. Given a degreewise short-exact sequence
of complexes

```text
0 -> A -> B -> C -> 0,
```

the degree-`n` CAP substitution is

```text
delta  := i_n,
beta   := d^B_n,
lambda := p_(n-1).
```

Then `gamma` is the map induced from `d^C_n` after identifying
`Coker(i_n)` with `C_n`, and `alpha` is the map induced from `d^A_n` after
identifying `Ker(p_(n-1))` with `A_(n-1)`. These identifications are canonical
isomorphisms supplied by short exactness; they are not generally one literal
runtime object normal form.

The homology connecting map additionally requires:

- descent from cycles along the selected boundary cokernel at degree `n`; and
- factorization into cycles before quotienting at degree `n - 1`.

Those two facts, plus the endpoint comparisons above, are the architectural
content of the long-exact construction. They must be explicit and reusable.

## Primary Computational Form Of A Snake Diagram

Do not introduce a six-object record whose main payload is a collection of
hand-written commuting squares. The existing `AbelianSnakeTriple` remains the
primary computational owner.

It already determines two canonical exact rows:

```text
A -> B -> Coker(delta)
Ker(lambda) -> C -> D.
```

The side arrows `alpha` and `gamma` are selected by kernel/cokernel
universality. Thus the apparent snake diagram is generated by:

- one triple-zero internal Hom-fibre point;
- selected kernels and cokernels;
- genuine fiber products and pushouts;
- their contractible factor spaces; and
- normal monomorphism/epimorphism factor spaces.

The remaining four snake arrows and every exactness witness should be derived
from the same owners. A reviewer may display the usual diagram, but that
display is not a second semantic input grammar.

## Complete Six-Term Snake Exactness

Construct the remaining canonical maps:

```text
k_alpha_beta : Ker(alpha) -> Ker(beta)
k_beta_gamma : Ker(beta) -> Ker(gamma)
c_alpha_beta : Coker(alpha) -> Coker(beta)
c_beta_gamma : Coker(beta) -> Coker(gamma).
```

Each map must be selected by an existing kernel or cokernel factor space from
the reconstruction paths already owned by the triple. Retain the selected
whole construction and readable arrow/path projections.

Derive all four adjacent-zero points and prove exactness at the four interior
objects:

```text
Ker(beta), Ker(gamma), Coker(alpha), Coker(beta).
```

Use the existing `ComputationalExactAt` notion unless the owner audit proves
that a more generic indexed exactness carrier is required. Exactness remains
epicity of the actual boundary-to-selected-kernel factor, not object equality
between a selected image and kernel.

If repeated sequence packaging is needed, introduce one generic finite exact
spine retaining:

- the indexed objects and arrows;
- each adjacent-zero Hom-fibre point;
- each interior `ComputationalExactAt` witness; and
- endpoint metadata for bounded iteration.

Do not add a snake-specific list AST when an existing finite-family owner can
carry this data.

## Selected Short-Exact Rows And Usability

The primary runtime form should be a selected short-exact row whose kernel and
cokernel objects come from the active computational owners. This gives the
strictest and cheapest endpoint form for the long-exact computation.

Separately, an arbitrary `ComputationalShortExactTriple` must receive a
usability theorem constructing canonical evidence that:

```text
incoming is the kernel of outgoing, up to selected IsoEvidence;
outgoing is the cokernel of incoming, up to selected IsoEvidence.
```

The comparison should use normality, exactness, and the existing image/coimage
bimorphism results. It must not use an opaque object equality or transport
through a postulated path. Univalence explains why equivalent selected
objects represent the same mathematics, but the computational API should
retain explicit comparison arrows and inverse laws.

Only add proof-time unification when a concrete typed consumer needs to compare
two rigid owner heads and an `eq_refl` probe validates the equation. Do not add
broad runtime folds merely to erase these canonical isomorphisms.

## Degreewise Short-Exact Bounded Complexes

Add a whole structure over the existing bounded Freyd complexes and bounded
chain maps. It should retain:

- sub-, middle-, and quotient complexes over one bounded degree range;
- inclusion and projection chain maps;
- their existing component-square agreements;
- one witness-rich short-exact row at every degree; and
- deterministic degree lookup with explicit endpoint zeros.

The commutativity squares are the existing chain-map agreements or their
internal Hom-fibre counterparts. They are not manually duplicated fields.

The primary constructor should accept the three complexes and two checked chain
maps, then compute and validate the degreewise short-exact witnesses. A selected
constructor may instead build the quotient or subcomplex degreewise from
canonical cokernels/kernels. Keep these as distinct computational and usability
surfaces rather than silently identifying them.

## One Long-Exact Homology Window

Before recursive assembly, construct and prove one complete degree window:

```text
H_n(A) -> H_n(B) -> H_n(C)
       -> H_(n-1)(A) -> H_(n-1)(B).
```

The first, second, and fourth arrows reuse the existing induced-homology-map
owner. The middle arrow must be obtained from the generic snake construction
with the degree substitution recorded above, followed by the canonical
short-exact-row endpoint comparisons and the required homology descent/factor
operations.

Retain:

- all five homology objects;
- all four arrows;
- the raw snake result;
- endpoint comparison isomorphisms;
- descent through source boundaries;
- factorization into target cycles;
- adjacent-zero agreements; and
- exactness at the three interior displayed objects.

This window is the decisive architecture consumer. Reject a design that:

- defines a second homology object to match the snake endpoint;
- transports through arbitrary object equality;
- chooses a splitting of an epimorphism;
- accepts the connecting arrow or its zero tests as data;
- hides a chain square in an ad hoc diagram record; or
- duplicates the matrix algorithm above categorical lowering.

## Complete Bounded Long Exact Sequence

### Operational reference priority (2026-09-07 clarification)

Decision response: `0119_2026-09-07T19-46-57Z_01a07d52-6b95-7fd1-a9a7-ded8d98ebc85.md`
in the session archive under `/home/user1/emdash1/emdash2/tmp/ai-responses/`;
the user explicitly accepted it and requested continuation. This section,
not that ignored archive, is the living execution authority for the update.

The user clarified that the immediate useful result is a working end-to-end
proof–CAS reference baseline. The current rule-free mathematical development
is valuable reference evidence, not a commitment to its final logical
packaging. A later literature-informed redesign may replace that packaging
with a whole category-of-complexes/homology-functor calculus. It must preserve
the intended operations and observable mathematics, not today's dependent
Sigma layout or proof-term expansion.

Give the homology connecting operation its own public identity. Its input is
the short-exact sequence and degree; its output is the arrow
`delta_n : H_n(C) → H_(n-1)(A)` and the selected reconstruction data. The
current snake-based method remains one transparent implementation strategy.
It first produces `Ker(gamma) → Coker(alpha)`, then compares endpoints,
factors into target homology, and descends through source boundaries. Those
intermediates are not user-supplied inputs of homology connecting, and must
not determine the essential categorical operation contract. Retain the
algorithm trace for replay and inspection without duplicating the algorithm
above backend-neutral lowering. An independent operation does not by itself
require a new kernel primitive or runtime rewrite.

After the row-7C2 checkpoint, prioritize the named homology-connecting
operation, native bounded assembly, categorical lowering, and an actual
proof-assistant delegation/replay/adoption consumer on nonsplit nonzero
examples. The existing native five-term window is the operational gate for
that path. The full generic window theorem in row 7D and generic bounded
exactness remain required, unfinished work; they are not prerequisites for
demonstrating the first end-to-end operational baseline. This reorders the
work without shrinking the full persistent goal or calling its mathematical
boundary complete. Book claims must distinguish the checked generic snake
theorem, native computations, witnessed formal consumers, and any still-open
generic homology theorem.

### Bounded assembly

After the one-degree window is green, iterate it over the finite degree range.
The whole result should present the conventional order

```text
... -> H_n(A) -> H_n(B) -> H_n(C)
    -> H_(n-1)(A) -> H_(n-1)(B) -> H_(n-1)(C) -> ...
```

with selected zero objects outside the bounded range. Retain a deterministic
index mapping between long-exact positions and `(degree, A/B/C)` roles.

Prove every adjacent composite zero and exactness at every nontrivial interior
term by reusing the checked window. The iteration must not recompute an
independent degreewise snake result when the whole sequence already stores it.

The full result is finite and bounded. Unbounded complexes, derived categories,
triangulated categories, and spectral sequences remain successor work.

## Native Polynomial Freyd Specialization

Extend the existing native bounded-complex and snake implementations rather
than creating a parallel algorithm. Required consumers include:

- a genuinely nonsplit degreewise short-exact polynomial-module sequence;
- at least two adjacent nonzero degrees;
- endpoint degrees with selected zeros;
- invalid chain-map and invalid short-exact inputs;
- deterministic repeated execution;
- exact whole-result serialization; and
- agreement with the existing field implementation after passage to canonical
  quotient coordinates.

The native whole result must retain each degreewise short-exact witness, each
snake window, all induced homology maps, all connecting maps, and every selected
agreement used by formal replay.

## CAP-Like Categorical Program And Compilation

Expose whole operation roles for:

```text
short-exact-bounded-complex;
snake-exact-sequence;
long-exact-window;
bounded-long-exact-homology.
```

The exact names follow the category-operation owner audit. Derived methods must
record prerequisites through existing kernel/cokernel, homology, induced-map,
snake, and exactness operations. One retained whole long-exact operation is
preferred over a snake-specific categorical AST.

One direct execution and one compiled graph execution must serialize to the
same complete selected result. Matrix syntax and polynomial reduction remain
below the backend-neutral lowering boundary.

## Witnessed Formal Freyd Boundary

The formal polynomial layer remains capability- and agreement-indexed. It does
not acquire an arbitrary quotient-path decoder or a closed ring-wide
`ComputationalAbelianCategory` merely because the native CAS can decide the
selected example.

The formal result should construct as much as possible from the existing
witnessed kernel, cokernel, normality, homology, induced-map, and snake owners.
Effective raw agreements that cannot be recovered from truncated paths remain
explicit proof–CAS inputs. Required output includes:

- degreewise short-exact raw witnesses;
- the selected raw snake windows;
- connecting raw morphisms;
- boundary-zero and cycle-factor agreements;
- adjacent-zero agreements for the long-exact spine; and
- exactness witnesses at every displayed interior term that the present formal
  capabilities can construct.

Any remaining formal exactness limitation must be recorded at the exact
effectiveness boundary rather than hidden behind an opaque theorem constant.

## Proof–CAS Consumer

Replay the complete native/categorical whole result and reify the selected
equations. At minimum cover:

- every degreewise chain square and short-exact zero;
- all five maps and all four adjacent-zero equations of each snake sequence;
- each connecting-map descent and target-cycle factorization;
- every adjacent-zero equation in the long-exact spine;
- the induced-map and connecting-map reconstruction equations; and
- the exactness witness data actually consumed by the formal boundary.

Adoption remains an explicit usability action after canonical whole-result
comparison. The bridge does not certify the CAS implementation and adds no
trusted Core owner.

## External Differential

The finite-dimensional field implementation and reviewed CAP operation order
remain non-authoritative differentials. Compare induced quotient-coordinate
maps rather than raw representatives in unrelated bases.

An external CAP/homalg or Singular process is optional and injected. No native,
categorical, formal, or proof–CAS result may depend on its availability.

## Book Architecture And Content

The current book ends with Chapter 30 and has no dedicated additive or
homological-algebra chapter. Add Chapter 31, provisionally titled:

**Additive, Abelian, and Homological Computation.**

Its planned progression is:

1. preadditive categories, additive categories, zero objects, and biproducts;
2. kernels and cokernels as contractible internal factor spaces;
3. images, coimages, normality, and witness-rich exactness;
4. one-degree and bounded homology;
5. genuine fiber products, pushouts, and Abelian stability;
6. the snake construction without manual diagrams;
7. the six-term snake exact sequence;
8. short-exact bounded complexes and the long exact homology sequence; and
9. native CAS, categorical lowering, formal witnessed equations, proof–CAS
   adoption, and field/CAP differential evidence.

The chapter should distinguish carefully:

- runtime computation, proof-time comparison, and theorem-level paths;
- generic categorical structure and concrete polynomial algorithms;
- selected canonical rows and arbitrary semantic short-exact rows;
- raw presentation matrices and induced quotient maps;
- the formal effectiveness boundary and native decidability; and
- checked results from research boundaries.

Also update:

- the preface/contents only as needed for the new chapter;
- Appendix A notation;
- Appendix B evidence routing;
- Appendix D glossary/index;
- Appendix E computation and normalization, emphasizing that the current
  Abelian/homological layer is rule-free unless this goal proves otherwise;
- Appendix F current status and successor boundaries;
- `book/evidence.json` and third-party CAP/homalg provenance; and
- the living architecture metadata in `book.json` and `expansion.json`.

Book prose follows checked code. Outline and terminology may be prepared early,
but theorem-like claims become checked only after their owning implementation
and reviewer are green. Do not hand-edit assembled Markdown or PDF artifacts.

## Architecture Review And Consolidation

Use this milestone to audit, not merely exercise, the current design:

- Does local `ComputationalExactAt` scale cleanly to indexed exact sequences?
- Are selected short-exact rows and arbitrary semantic rows separated clearly?
- Do image/coimage and balancedness owners expose the comparisons needed by
  homology without endpoint transports?
- Do whole kernel/cokernel/fiber/pushout results retain enough data for later
  iterations without recomputation?
- Can categorical prerequisite plans express the long-exact construction
  without a special AST?
- Does canonical serialization distinguish raw representatives from quotient
  morphisms consistently?
- Does the formal boundary request only genuinely effective raw agreements?
- Are repeated TypeScript serializers, schemas, and operation wrappers ready
  for a generic reusable helper, or would consolidation obscure ownership?

Small, directly required corrections may be implemented in this goal with
focused tests. Broader improvements enter a side-task ledger with a concrete
consumer and successor plan. Do not absorb the orthogonal strictness/cubical
migration.

## Computation And Rule Policy

- Start from transparent semantic definitions and theorem-level paths.
- Generic identity, composition, zero, addition, biproduct, kernel/cokernel,
  normality, homology, and snake owners remain unchanged unless a measured
  defect is exposed.
- Add runtime rules only for genuinely new constructor-visible normal forms
  with concrete consumers.
- Use proof-time unification only between suitable rigid heads, validated by
  typed `eq_refl`; unification rules are not reliably transitive.
- Follow inferred-slot SOP and avoid reducible compound endpoint expressions
  in nondiscriminating rule-LHS positions.
- Warnings are diagnostic evidence, not a veto. Timeout, subject-reduction
  failure, false-positive conversion, unjoinable semantics, or retained-action
  loss are rejection signals.
- Prefer rule-free use of existing universal operations.
- Do not use opacity to hide expensive endpoint conversion. Select one
  canonical owner presentation or split a module at a genuine semantic
  boundary when required by the uniform 90-second target limit.

## Implementation Ledger

### Inner-zero validation result

The second and third adjacent-zero points are implemented and the focused
reviewer is green. Current-source quiet and warning-enabled probes of the two
independent universal-property branches pass below 90 seconds; the warning
inventory remains exactly `1,217` critical-pair plus `169`
replaceable-variable reports. Strict audits find zero rule clauses because the
entire tranche is theorem-level and rule-free. The pre-existing kernel,
cokernel, and outer-zero reviewers remain green after the source-preserving
one-map split.

A direct fresh-source process that loads both branches reaches the uniform
limit before the new root declaration, even though each branch and the root
term checked separately. The maintained focused gate
`emdash2/scripts/check_abelian_snake_six_term.sh` copies the exact current
Lambdapi sources into a disposable directory, source-checks each branch with
fresh object generation in separate bounded invocations, then checks all five
cross-branch source modules, the whole result/projection modules, and both
six-term reviewers against those exact objects. The same gate now continues
through the exactness-cover infrastructure, both canonical-row instances, the
first three snake exactness chases, and their reviewers. The third-position
extension stages and reviewer now pass that same focused gate. Its complete
run is green and leaves no `.lpo` in the worktree. `check.sh`,
`check_examples.sh`, and the resumable health runner route these measured
targets through that gate. This is the same source-checked compilation model
used by the documented large-module fallback; an object-backed failure must
still be retried from source before semantic diagnosis.

The tracked health report is not regenerated at this intermediate checkpoint:
that would be an unrelated repository-wide aggregate. Its content snapshot is
therefore expected to remain stale until the next authorized proportional
health boundary; the focused gate and its unit-tested health dispatch are the
current evidence.

### Third-position validation result

The 2026-09-07 warning-enabled isolated gate passed through every registered
third-position source and reviewer, while retaining the earlier maps, zero
equations, whole-result projections, and first/second exactness reviewers.
Every individual Lambdapi process remained bounded to 90 seconds. The exact
warning inventory is unchanged at `1,217` critical-pair and `169`
replaceable-variable reports; all thirty affected source/reviewer strict
audits pass with zero new rule clauses. The nine focused health-dispatch unit
tests pass, as do shell syntax, the strict fresh catalog, source TOC, report
headers, active links, and staged whitespace checks. The integration log is
`emdash2/logs/snake-third-integration.ZoG8vA.log`.

Six inherited extension files had a final blank line removed after the
isolated copy was taken. Their resulting current source was checked again in
the successful fourth-foundation probe; the change was whitespace-only.
Disposable `.lpo` files from the exploratory checks have been removed.
The full health rebuild and unrelated TypeScript/book aggregates remain at
the previously documented boundary.

### Fourth-position validation result

The promoted `examples/abelian_snake_exact_fourth.lp` passes from source in
both quiet and warning-enabled modes with no dependency objects. The final
quiet log is `emdash2/logs/probes/abelian_snake_exact_fourth-20260907-064124.log`;
the warning log is `emdash2/logs/probes/abelian_snake_exact_fourth-20260907-063908.log`.
The inherited warning inventory remains exactly `1,217/169`. All eight
source/reviewer strict audits have zero rule clauses. The focused nine
health-dispatch tests, shell syntax, catalog/TOC, report/link hygiene, and
staged whitespace checks pass. No full TypeScript, book, health, or unrelated
repository aggregate was run. The seven source stages are registered on the
ordinary checker/health route, and the reviewer is discovered ordinarily.

All four individual exactness witnesses and their dependent whole result are
now implemented. The long-exact and book objective is still active.

For row 4E, the 2026-09-07 continuation starts from clean `e6165124` and a
successful fresh-source fourth reviewer. The previous turn made progress by
committing both remaining individual proofs. The package experiment uses a
fresh disposable source copy, checks each existing dependency under its own
90-second bound, and retains those exact objects only during this tranche's
incremental probes. Every promoted new source must match its checked copy;
the temporary build is removed before the checkpoint. This continues the
existing compilation discipline without retaining a worktree object cache.

### Whole exact-result validation and conversion boundary

Eight rule-free source modules and four reviewers implement row 4E. There
are 27 focused assertions: twelve arbitrary pair projections, two whole beta
projections, two negative snapshot/noncollapse guards, four canonical pair
identities, six canonical snapshot/data/exactness observations, and generic
reindexing beta. The promoted module names pass with warnings enabled against
freshly compiled exact dependencies. The generic reindexing reviewer also
passes directly from source and inherits the unchanged `1,217/169` warning
boundary. All twelve strict source/reviewer audits have zero rule clauses.

The complete dependency/check sequence ran incrementally in one disposable
copy. A target-list comparison confirms coverage of all 93 targets in the
updated focused gate, plus the ordinary fourth-position reviewer. Each
invocation was bounded to 90 seconds. Logs are
`emdash2/logs/exact-result-base.KObZEa.log`,
`emdash2/logs/exact-result-proofs.x73QjV.log`,
`emdash2/logs/exact-result-promoted.RCtjQ0.log`, and
`emdash2/logs/exact-result-regressions.kTwn1P.log`.
The nine focused health-dispatch tests, shell syntax, catalog/TOC, and
report/link hygiene pass. This is scoped incremental gate evidence, not a
claim that a repository aggregate was run.
Byte-for-byte comparison also confirms that all 94 checked target sources
match the worktree. The disposable build was moved to recoverable trash, and
no `.lpo` remains in the worktree; source probes and validation logs remain
available for recovery.

The straightforward canonical proof assignment exceeded 90 seconds, both in
the combined constructor and at the isolated first position. Its pair
identity nevertheless passes direct conversion checking. The accepted code
records that identity by `eq_refl` and invokes
`computational_exactness_reindex` before expanding the exactness predicate.
The ordinary canonical reviewer compares the resulting declared instances;
a direct comparison to the old differently presented bare proof type was
also too expensive. Generic reindexing beta and the independent pair
conversion/reflexivity checks account for the reuse of the original proofs.
No object equality assumption, unifier, runtime rule, or alternative homology
was introduced to get a passing target.

| ID | State | Dependencies | Required result |
|---|---|---|---|
| `LEH-PLAN-0` | complete; checkpoint `bf217fe9` | integrated baseline `054b43bd` | living plan, isolated branch/worktree, Git/scope boundary, persistent goal |
| `LEH-AUDIT-1` | complete; checkpoint `01fd062c` | current exactness, snake, bounded-complex, book, CAP/homalg owners | exact owner/endpoint matrix, focused baselines, rejection signals, book chapter map |
| `LEH-EXACT-SPINE-2` | pending | `ComputationalExactAt`, finite families | reusable finite exact-sequence carrier or durable evidence that windows suffice |
| `LEH-SNAKE-MAPS-3` | complete through checkpoint `17a7dd6a` | completed connecting result | remaining four snake maps, all adjacent-zero points, whole six-term result |
| `LEH-SNAKE-KERNEL-MAPS-3A` | complete; checkpoint `dd330e5e` | snake spine and selected kernels | `Ker(alpha) -> Ker(beta) -> Ker(gamma)` as selected kernel lifts with both reconstruction paths |
| `LEH-SNAKE-COKERNEL-MAPS-3B` | complete; checkpoint `737b36fe` | snake spine and selected cokernels | `Coker(alpha) -> Coker(beta) -> Coker(gamma)` as selected cokernel colifts with both reconstruction paths |
| `LEH-SNAKE-ZERO-3C` | complete; checkpoint `3ecad40d` | 3A–3B and completed connecting factor spaces | all four adjacent-zero points |
| `LEH-SNAKE-OUTER-ZERO-3C1` | complete; checkpoint `72e6fa6b` | 3A–3B and selected structural cancellation | first and fourth adjacent-zero points |
| `LEH-SNAKE-INNER-ZERO-3C2` | complete; checkpoint `3ecad40d` | 3A–3B, fiber factor, pushout cofactor, `u`, and `partial` | second and third adjacent-zero points |
| `LEH-SNAKE-RESULT-3D` | complete; checkpoint `17a7dd6a` | 3A–3C | whole six-object/five-arrow snake result with readable projections |
| `LEH-SNAKE-EXACT-4` | complete; whole-result checkpoint `2ca9ac9c` | row 3 and generic exactness | exactness at all four interior six-term positions |
| `LEH-SNAKE-EXACT-FIRST-4A` | complete; checkpoint `8dfde0a6` | canonical cokernel exactness and first two snake maps | `ComputationalExactAt` at `Ker(beta)` via epimorphic local covers |
| `LEH-SNAKE-EXACT-SECOND-4B` | complete; checkpoint `08d97080` | fiber product, first normal-epi factor, connecting map | `ComputationalExactAt` at `Ker(gamma)` |
| `LEH-SNAKE-EXACT-THIRD-4C` | complete; checkpoint `e19ac569` | pushout, final normal-mono factor, connecting map | `ComputationalExactAt` at `Coker(alpha)` |
| `LEH-SNAKE-EXACT-FOURTH-4D` | complete; checkpoint `aa7a3a06` | canonical kernel exactness and final two snake maps | `ComputationalExactAt` at `Coker(beta)` |
| `LEH-SNAKE-EXACT-RESULT-4E` | complete; checkpoint `2ca9ac9c` | 4A–4D and whole six-term snapshot | one whole exact result whose exactness witnesses depend on its actual stored arrows and zero points |
| `LEH-SHORT-EXACT-NORMAL-5` | complete; normalization checkpoint `521af261` | short exactness, image/coimage, normality | selected short-exact-row normal form and canonical arbitrary-row comparison isomorphisms |
| `LEH-SHORT-EXACT-KERNEL-5A` | complete; checkpoint `18f2ba33` | selected boundary and short-exact evidence | canonical `A -> Ker(p)` comparison isomorphism and reconstruction |
| `LEH-SHORT-EXACT-COKERNEL-5B` | complete; checkpoint `18f2ba33` | exactness, normal epi colifting, selected cokernel | canonical `Coker(i) -> D` comparison isomorphism, inverse, and reconstruction |
| `LEH-SHORT-EXACT-SELECTED-5C` | complete; checkpoint `521af261` | 5A–5B and canonical image/kernel row | selected `Im(i) -> B -> Coker(i)` row and whole arbitrary-row usability comparison |
| `LEH-BOUNDED-SHORT-EXACT-6` | complete through 6A–6B; finite-support interface | row 5 and bounded chain maps | degreewise short-exact bounded-complex sequence with retained chain squares |
| `LEH-BOUNDED-SHORT-EXACT-NATIVE-6A` | complete; checkpoint `8a32323b` | existing bounded Freyd complexes, chain maps, and short-exact triple operation | checked whole finite sequence, retained input chain maps and row witnesses, zero extension, deterministic serialization |
| `LEH-BOUNDED-SHORT-EXACT-FORMAL-6B` | complete through 6B1–6B2 | formal bounded Freyd spine and witnessed morphisms | corresponding bounded chain-map/short-exact interface without claiming closed quotient effectiveness |
| `LEH-BOUNDED-FREYD-CHAIN-MAPS-6B1` | complete; checkpoint `3b87d386` | formal bounded Freyd complexes and one-degree chain-map agreements | whole dependent map iterator, constructor/projection computation, direct one-degree homology consumer |
| `LEH-BOUNDED-FREYD-EXACT-ROWS-6B2` | complete; checkpoint `10f57b4b` | 6B1 and witnessed one-degree Freyd homology/mono/epi | explicit exact-row witnesses indexed by the actual two stored chain maps, retained homology identity |
| `LEH-WINDOW-7` | in progress; native window and generic inclusion/maps/row comparisons complete; full generic factor/descent/exactness remain | rows 4–6 and bounded homology | one five-term homology window, endpoint comparisons, connecting descent/factor, three exactness witnesses |
| `LEH-WINDOW-NATIVE-7A` | complete; checkpoint `cae22d6b` | degreewise native sequence and existing snake/homology/normality operations | full native five-term window, four comparison isomorphisms, target factor/source descent, all zeros and exactness, endpoint windows, full serialization |
| `LEH-WINDOW-HOMOLOGY-INCLUSION-7B` | complete; checkpoint `8161a141` | generic homology, canonical cokernel exactness or monic pushout stability | constructed canonical homology-to-differential-cokernel arrow, reconstruction, and generic monicity theorem |
| `LEH-WINDOW-GENERIC-MAPS-7C` | complete through 7C1–7C2 | generic kernel/cokernel Hom-fibres and actual selected homologies | generic induced homology maps and selected endpoint-comparison consequences matching the native/witnessed Freyd owners |
| `LEH-GENERIC-MAP-OPERATIONS-7C1` | complete; checkpoint `3df110ee` | existing Hom fibres and actual whole kernels/cokernels/homologies | maps, reconstruction, identity/composition/extensionality paths, inverse comparisons, and explicit choice isomorphisms |
| `LEH-SNAKE-ROW-COMPARISONS-7C2` | complete; final promoted gates green | 7C1, row-5 short-exact comparisons, generic snake | actual short-exact-row map to snake triple; alpha/gamma comparisons; source-cycle and target-cokernel isomorphisms at the actual selected owners |
| `LEH-WINDOW-GENERIC-EXACT-7D` | pending | rows 7B–7C and completed generic snake exactness | full generic homology connecting factor/descent and three interior exactness witnesses; no native decision substituted for the theorem |
| `LEH-HOMOLOGY-CONNECTING-API-7E` | next operational tranche | native window 7A and the 2026-09-07 priority clarification | independently named homology-connecting operation preserving actual selected homology and retaining its algorithm trace without making snake intermediates public inputs |
| `LEH-LONG-EXACT-8` | pending; operational assembly prioritized | native 7A/7E; generic exactness additionally requires 7D | complete bounded long exact sequence with endpoint zeros and all interior exactness |
| `LEH-NATIVE-9` | pending | operational polynomial Freyd provider | nonsplit multi-degree whole result, failures, deterministic serialization |
| `LEH-CATEGORY-10` | pending | categorical compiler and row 9 | operation roles, prerequisite trace, lowering, direct/graph agreement |
| `LEH-FORMAL-11` | pending | witnessed formal Freyd capabilities | maximal capability-indexed formal result with explicit effective agreements |
| `LEH-BRIDGE-12` | pending | rows 9–11 | proof–CAS replay/adoption of whole result and exact selected equations |
| `LEH-DIFFERENTIAL-13` | pending | field/CAP references | quotient-coordinate differential with no runtime dependency |
| `LEH-BOOK-14` | pending | checked rows 2–13 | Chapter 31, appendices, evidence/provenance, focused book checks and render |
| `LEH-CONSOLIDATE-15` | pending | architecture findings | necessary corrections complete; broader side tasks recorded without orthogonal expansion |
| `LEH-CLOSE-16` | pending | all scoped rows | authorities, validation evidence, checkpoints, health exception audit, successor boundary |

Rows may be split or reordered when an owner-position audit refines the
dependency graph. A row may be rejected or deferred only with durable evidence
and a concrete replacement, prerequisite, or human decision.

## Initial Decision Ledger

The interruption before the third exactness checkpoint preserved seven new
rule-free extension-criterion/canonical-kernel modules and the successful
`zeta o iota = 0` and gamma-extension probes. The 2026-09-07 continuation
revalidated current files, ancestry, and the exact unfinished target; the
preceding turn therefore made mathematical implementation progress. The
resumed chase uses two monomorphic extensions. For a cocone `psi` killed by
`partial`, push out monic `q2` along `psi` to obtain `s q2 = m psi`. Extend the
resulting `zeta` through `gamma`, obtaining `n zeta = y gamma` with `n` monic.
Then `w = n s q1 - y lambda` kills `beta` and descends to `Coker(beta)`.
Cancelling epic `pi` gives the required extension of `psi` across
`Coker(alpha) -> Coker(beta)`; the generic extension criterion proves
epicity of the existing selected boundary. This proof and its reviewer now
pass in the promoted source and integrated validation.

The fourth-position probes also pass through the final theorem. A test
`psi:Coker(beta) -> T` killed by `c34` makes `psi c_beta` vanish on `mu`.
Canonical kernel-row extension through `lambda` supplies `m psi c_beta = y
lambda` with `m` monic. The gamma reconstruction and epic `epsilon` show
`y gamma = 0`; descending `y` through `Coker(gamma)` and cancelling epic
`c_beta` supplies the exact extension. These seven stages are now promoted
under `emdash2/emdash3_2_abelian_snake_exact_fourth_*`, with a separate
reviewer. They form the follow-up tranche after the third-position checkpoint.
After removing all compilation objects, the fourth reviewer also passed as
one fresh-source target: `emdash2/logs/probes/abelian_snake_exact_fourth_reviewer-20260907-063322.log`.

| ID | State | Decision |
|---|---|---|
| `D-LEH-001` | accepted | The next primary milestone is the full six-term snake exactness followed by bounded long exact homology, not a book-only maintenance pass. |
| `D-LEH-002` | accepted | `AbelianSnakeTriple` remains the computational snake-diagram owner; no manual commutative-diagram record is introduced. |
| `D-LEH-003` | accepted | The long-exact degree substitution is `delta = i_n`, `beta = d^B_n`, and `lambda = p_(n-1)`. |
| `D-LEH-004` | accepted | Canonical snake endpoints must be compared with the existing selected homology objects; no second homology theory is introduced. |
| `D-LEH-005` | accepted | Selected short-exact rows are the primary computational form; arbitrary witnessed rows receive explicit comparison isomorphisms as a usability layer. |
| `D-LEH-006` | accepted; operational sequencing clarified by D-LEH-042 | One exact five-term homology window is the architecture gate before bounded iteration. The checked native window qualifies operational iteration; the full generic window theorem remains required before generic long-exactness claims. |
| `D-LEH-007` | accepted | The full result is bounded and finite; unbounded complexes, derived categories, triangulated categories, spectral sequences, and Čech hypercohomology remain later goals. |
| `D-LEH-008` | accepted | Native/categorical/formal/proof–CAS layers reuse the completed snake and homology owners rather than duplicating matrix algorithms. |
| `D-LEH-009` | accepted | Chapter 31 is an evidence-bearing deliverable of this goal; checked code remains authority and generated book/PDF artifacts remain tool-owned. |
| `D-LEH-010` | accepted | The divergent path-cubical/global-strictness branch remains outside this goal. |
| `D-LEH-011` | accepted after owner audit | The homogeneous `FiniteFamily` carrier is not by itself a dependent categorical sequence. Construct the concrete six-term window first; if bounded iteration needs a generic spine, follow the recursive dependent-Sigma precedent of formal bounded complexes. |
| `D-LEH-012` | corrected after endpoint audit | A six-object snake sequence has five arrows and four adjacent arrow composites. Proof–CAS and validation requirements use those exact counts. |
| `D-LEH-013` | accepted after kernel-side owner probe | The first two snake arrows are direct selected kernel lifts of `delta o k_alpha` and `epsilon o k_beta`. Their zero tests derive from the existing alpha/gamma reconstruction and kernel annihilation paths; no comparison rule or endpoint transport is required. |
| `D-LEH-014` | accepted after cokernel-side owner probe | The final two snake arrows are the direct cokernel-colift mirror, selected from `c_beta o mu` and `c_gamma o lambda`. Their tests derive from the alpha/gamma reconstruction and cokernel annihilation paths, with no duality bridge or new computation rule. |
| `D-LEH-015` | accepted after outer-zero owner probes | Calculate each outer composite after the literal selected kernel embedding or cokernel projection, then use generic selected-structural-arrow zero cancellation. Keeping the exact owner head avoids expensive alias conversion; splitting calculation from cancellation keeps every target bounded without opacity or new rules. |
| `D-LEH-016` | accepted after inner-zero owner probes | Retain the canonical fiber factor and pushout cofactor with both reconstructions, then derive the inner zero points by the existing `u`/`partial` paths and monic/epic cancellation. Split the two-map sides into unchanged one-map foundations and move readable fiber/pushout object aliases to the snake spine that owns them. Because the two independently source-green branches exceed 90 seconds only when loaded together, validate their join through fresh exact objects in an isolated disposable tree; do not weaken, hide, or duplicate the mathematics. |
| `D-LEH-017` | rejected after measured probe | Do not replace the selected factor/cofactor calculation by one oversized generic annihilation combinator. The generic statement was mathematically valid, but its concrete pushout instantiation alone required about 36 seconds and did not improve the source dependency boundary. The smaller named reconstruction steps are faster, more inspectable, and have direct whole-result consumers. |
| `D-LEH-018` | accepted after whole-result probes | The whole six-term snapshot retains the existing whole connecting-factor result, the other four selected arrows, and the four adjacent-zero points. Do not re-expand all four kernel/cokernel factor-space types inside a second carrier: the maximal side-package probe exceeded 90 seconds even with exact dependencies primed. Universal reconstruction points remain named at their original owners, while nine readable projections of the lighter snapshot reduce definitionally to the five canonical arrows and four canonical zero proofs. |
| `D-LEH-019` | accepted after exactness-owner review | Add an epimorphic local-cover interface equivalent to `ComputationalExactAt`: every annihilated cone factors through the incoming arrow after an epic cover. Exactness gives covers by pulling the cone factor back along the epic boundary; covers imply exactness by applying one to the selected kernel. This is internal universal-property data, not element syntax or a second exactness notion. |
| `D-LEH-020` | accepted after canonical-row probes | Canonical cokernel exactness is proved with one explicit `PreAbelianCategory` and its two normality capabilities, following the image-bimorphism owner discipline. The epic map `Coim(f) -> Im(f)` after the coimage projection is retained as a point of the selected image factor fibre; `computational_exact_at_from_epic_factor_point` transports epicity to the actual boundary. Bundled concrete wrappers that repeatedly projected `ComputationalAbelianCategory` were rejected after measured conversion timeouts. |
| `D-LEH-021` | accepted after the first snake exactness probe | At `Ker(beta)`, apply canonical cokernel-row covers to `k_beta o psi`; monicity of `mu` forces the covered preimage through `Ker(alpha)`, and monicity of `k_beta` proves the covered reconstruction through the first snake arrow. The resulting cover family proves epicity of the actual boundary with no image/kernel object equality. |
| `D-LEH-022` | accepted after the second snake exactness probe | At `Ker(gamma)`, pull a connecting-kernel test back along epic `p1`; use the existing `beta o p2` lift, connecting/pushout reconstructions, and monic `q2` to obtain a cone for the canonical `alpha` cokernel row. After its second epic cover, factor the corrected `p2 - delta` difference through `Ker(beta)` and cancel monic `iota`. Compose the two covers and apply the generic cover criterion. Fine-grained one-symbol cover projections are retained because larger projection files exceeded the 90-second bound. |
| `D-LEH-023` | accepted after extension-criterion probes | A monomorphic local-extension family implies the existing boundary-epicity exactness. Push the actual boundary cokernel out along the cycle embedding, extend the first injection, and cancel the two monomorphisms to make that cokernel zero. A general converse has not been added. |
| `D-LEH-024` | accepted after canonical kernel-row probes | Descend a kernel-annihilated test to the coimage and push out the monic canonical map `Coim(f) -> B`. This constructs the kernel row's extension family with explicit pre-Abelian/normality capabilities, no new property postulate, and no new computation rule. |
| `D-LEH-025` | accepted after third-position probes | Two monomorphic extensions give the corrected coextension `n s q1 - y lambda`; its selected beta-cokernel colift reconstructs after `pi`. Separate that calculation from a readable transparent instance of generic `pi` epicity. This reduces the final application from a timeout to about two seconds without opacity or an extra rule. |
| `D-LEH-026` | accepted after whole-result type audit | The exactness data of a whole six-term result must depend on its actual projected arrows and zero points. Define each chain pair from those projections and use the existing homology constructor on that pair. Do not attach exactness of the fixed canonical maps to an unconstrained arbitrary `AbelianSnakeSixTermResult`. Canonical projection reduction should connect the selected instance to the four completed proofs. |
| `D-LEH-027` | accepted after fourth-position probes | Extend the `mu`-annihilated test `psi c_beta` through `lambda`; epic `epsilon` makes the coextension kill `gamma`, and epic `c_beta` proves the reconstruction after its selected gamma-cokernel colift. The full reviewer fits one fresh-source invocation, so this tranche uses ordinary source/example/health registration rather than the special multi-branch gate. |
| `D-LEH-028` | accepted after canonical exact-result probes | Keep the actual snapshot-indexed exactness family. Its canonical pairs compute to the old pairs; record those identities by reflexivity and reindex exactness at that small data owner before opening the large predicate. This retains the selected homology and ordinary reflexivity beta while avoiding the measured direct-assignment/type-comparison timeout. No semantic arrow or object bridge is postulated. |
| `D-LEH-029` | accepted after endpoint-comparison probes | The actual boundary gives the kernel comparison; monic-factor cancellation and constructive balancedness construct its inverse. The cokernel comparison uses its ordinary colift, while exactness makes the cokernel projection a normal-epi test for the outgoing arrow. Its selected colift and common-epic cancellation give the inverse comparison without a section into the middle object. |
| `D-LEH-030` | accepted after normalization probes | Construct a kernel row from its existing whole kernel and identity exactness covers. Use a single literal kernel-object presentation throughout the selected image row and its isomorphism. Build the source comparison fibre generically at PA/f before specializing to a bundled short exact row; this preserves the actual-row dependency and avoids the measured composite-compatibility conversion timeout. |
| `D-LEH-031` | accepted after native degreewise consumers | Retain the two existing bounded chain maps and compute each short-exact row through the existing operation. Compare their endpoints by selected presentations and raw differentials, not object identity alone or quotient congruence. Store one zero row for explicit extended lookup. Full serialization retains raw agreements and bounded-free provenance; it excludes only derived Gröbner caches, following the existing presentation convention. |
| `D-LEH-032` | accepted after formal chain-map consumers | Iterate raw presentation morphisms and their existing agreements over the actual two formal complex tails. The single-square name is transparent; two stored laws package directly as the existing one-degree homology chain map. Keep formal short-exact row evidence capability-indexed and downstream of this iterator. |
| `D-LEH-033` | accepted after formal exact-row consumers | Store the existing whole witnessed homology in each raw row and index its exactness by that actual value. Iterate rows on the actual projected components of the two retained chain maps; a dependent whole sequence owns both maps and the resulting evidence. Wrong-homology and wrong-map consumers must fail. Native row computation and formal effective evidence remain distinct interfaces. |
| `D-LEH-034` | accepted after native window tests; generic proof required | Compare the actual snake endpoints with source cycles and the target differential cokernel, factor along the canonical homology inclusion, then descend by the actual source homology cokernel. Do not require a global raw target-cycle lift or choose an epimorphism section. All four isomorphisms retain both inverse agreements; all factors retain their effective tests and reconstructions. |
| `D-LEH-035` | accepted after endpoint-window tests | Extend complex terms by the retained zero presentation, but compute outside-support homology with its true neighboring differentials. In particular, `0 → C_top` is not the unrelated `0 → 0` pair. Retain an identity-equals-zero agreement for the resulting outside homology object. |
| `D-LEH-036` | accepted after generic cokernel/homology consumers | Derive the monic cokernel-composite comparison through a selected pushout factor and generic monic-factor cancellation. Specialize to the actual homology cycles/boundary; no pushout isomorphism, object transport, or monicity axiom is needed. |
| `D-LEH-037` | accepted after bounded owner-position probes | Use one literal preadditive presentation in the Abelian cokernel wrapper, and prove homology monicity with PA/normality explicit before exposing a thin bundled observation. The shorter-alias and direct bundled alternatives each timed out in quiet and warning-enabled checks; the aligned/PA-explicit versions and actual cancellation consumers pass with no new rule or unifier. |
| `D-LEH-038` | accepted after generic map consumers | Use transparent internal Hom pre/postcomposition fibres as the compatibility owner. A chain-pair map retains its middle arrow and two factor points; ordinary components and equations are projections or a transparent usability constructor, not a new square datatype. |
| `D-LEH-039` | accepted after map-law and choice consumers | Construct maps on actual kernels/cokernels, derive identity/composition/extensionality by their existing uniqueness, and package inverse maps as ordinary IsoEvidence. Homology reuses these two stages and derives boundary compatibility. Different universal choices receive actual isomorphisms, not object equality or transport. |
| `D-LEH-040` | accepted after row-comparison probes | Derive the snake triple from the existing chain-pair map; use actual short-exact comparison arrows and kernel/cokernel uniqueness to identify alpha/gamma, then generic map isomorphisms at the supplied endpoint choices. Retain PA/normality explicitly internally and use existing Sigma elimination for a one-Abelian-package interface; add no eta rule or object equality. |
| `D-LEH-041` | accepted after timed consumer isolation | Keep every original assertion and validate the exact source dependencies in separate bounded invocations. Separate the source and target whole-row beta consumers, each still below 90 seconds. Do not claim that staged qualification solves the remaining interactive checking-cost concern. |
| `D-LEH-042` | accepted user priority clarification, 2026-09-07 | Give homology connecting and bounded long exact sequence their own public operation identities. Keep the snake-based route as an implementation/reference strategy. Prioritize the end-to-end operational proof–CAS baseline without silently dropping the generic window theorem or shrinking the full persistent goal. |

### Short-exact endpoint checkpoint evidence

Rows 5A and 5B now have six promoted rule-free modules and the independent
`examples/short_exact_comparisons.lp` reviewer. All seven assertions pass from
source in quiet and warning-enabled modes. They check the selected kernel
comparison, both cokernel comparison arrows, and the actual reconstruction
equations; the negative type guard prevents calling the inverse comparison
a section into the middle object. The inherited warning inventory is exactly
`1,217/169`; the extra unsolved-equation message belongs to that successful
`assertnot`. Logs are
`emdash2/logs/probes/short_exact_comparisons-20260907-102411.log` and
`emdash2/logs/probes/short_exact_comparisons-20260907-102904.log`.
Seven strict source/reviewer audits, the nine focused health tests, shell
syntax, catalog/TOC, and report/link checks pass. These files use ordinary
checker and health registration; no unrelated aggregate was run.

### Whole normalization checkpoint evidence

Row 5C now has ten promoted source modules and five reviewers. Their 21 new
assertions pass, as does the existing seven-assertion endpoint reviewer.
The selected row is `Im(f) -> B -> Coker(f)` over a pre-Abelian capability;
the arbitrary-row comparison uses Abelian normality and the original
short-exact evidence. The output retains an actual whole row and two
isomorphism-comparison `HFiber` points over its actual arrows. The negative
reviewers reject mismatched pair evidence and a comparison from another row.

The direct full-source canonical reviewer exceeded 90 seconds while loading
the combined dependency closure. The new scoped gate
`emdash2/scripts/check_short_exact_normalization.sh` freshly checks each
dependency and consumer in its own bounded invocation. Its warning-enabled
public run passed in
`emdash2/logs/normalization-public-gate.Hw2l8i.log`, with the unchanged
`1,217/169` warning inventory plus expected `assertnot` diagnostics.
The gate excludes the unrelated snake-proof chain. Kernel checks, reviewer
discovery, and the health runner each execute this group once; a focused test
checks its independence from the snake group. Ten dispatcher tests pass.

The accepted computational presentation uses literal kernel-object endpoints
and the existing whole image kernel. Its exactness proof uses identity covers
without replacing the selected homology. Generic source-comparison formation
at PA/f succeeds before specialization to the full short-exact input. The
maintained canonical path tests observe the stored fibre points, and the
generic comparison beta tests observe their original reconstruction paths;
the direct specialized bare-path comparison was too expensive. No object
equality assumption, new rule, unifier, or weaker normalization was used.

The experimental build `/tmp/emdash-short-exact.xSl9rC` is disposable and is
removed at this checkpoint; source probes and logs remain in the worktree.
The public gate removes only its generated file kinds and empty directories,
retaining unexpected content instead of performing a forced recursive cleanup.

## Baseline And Validation Policy

### Degreewise sequence implementation boundary

The continuation starts from clean `999f24d7`; the previous turn completed
and committed short-exact normalization. Workspace validation and eleven
focused bounded-complex/native-snake tests pass. The first implementation
keeps the existing input chain-map objects, including their square agreements,
and checks their endpoints against the declared complexes using selected
presentation and raw-differential equality. Equal reconstructed inputs are
accepted; differentials that merely share object endpoints are not.

The native constructor computes every short-exact row with the existing
short-exact operation, retains those whole witnesses, and stores one selected
zero row for explicit extension outside the finite support. Bounded lookup
remains range checked; the separately named extended lookup returns that
stored zero row. The principal nonsplit test has `R --x--> R` as both sub-
and middle complexes, quotient `R/(x) --0--> R/(x)`, inclusion `x` and the
quotient projection in both degrees. This prepares a nonzero connecting-map
consumer for the following homology-window row.

The new module is directly importable during this tranche; public-barrel and
categorical-operation integration are batched with the later whole long-exact
consumer rather than triggering an unrelated TypeScript aggregate now.
The formal Freyd bounded tail already exists, but its bounded chain-map and
short-exact iterator must be audited explicitly in row 6B. Native data is not
silently promoted to the stronger formal Abelian capability.

Row 6A is implemented in
`src/v3_2/algebra_polynomial_freyd_bounded_short_exact.ts` and its companion
serialization module. Twelve new focused tests cover nonsplit rows, retained
map/square owners, a nonzero adjacent-degree snake connecting map, both zero
extensions, one-degree support, identical reconstructed inputs, different raw
differentials even when their quotient maps agree, failed squares/rows,
invalid complexes/ranges/rings, deterministic whole serialization, and
bounded-free provenance. Together with the seven existing bounded-complex
and four snake tests, all 23 pass. Root `typecheck` and affected-file ESLint
also pass on the final source. The lost pre-recovery process handle was first
checked and found no longer running; only these focused suites were rerun.
No Lambdapi, book, public-barrel, shared LF, or repository aggregate change is
part of this native checkpoint.

The formal iterator experiment follows
`emdash3_2_commutative_algebra_bounded_free_chain_maps.lp`, replacing ranks
and matrices by actual selected presentations and raw presentation morphisms.
Each step stores the same presentation-morphism agreement used by the
one-degree functorial-homology owner; the single-square name is a transparent
alias, not a new square primitive. Its first two laws must package directly
as `CommRingFreydHomologyChainMap`. Nil/cons, whole component/tail beta tests,
and a wrong-endpoint negative consumer are the acceptance tests before
proceeding to row exactness. No new computation rules are planned.

That iterator is now promoted as
`emdash2/emdash3_2_commutative_algebra_freyd_bounded_chain_maps.lp`, with
`examples/commutative_ring_freyd_bounded_chain_maps.lp`. All twelve assertions
pass directly from source in quiet and warning-enabled modes. Eleven are
positive beta/consumer checks and one rejects a wrong target. The final logs
are `emdash2/logs/probes/commutative_ring_freyd_bounded_chain_maps-20260907-121257.log`
and `emdash2/logs/probes/commutative_ring_freyd_bounded_chain_maps-20260907-121349.log`.
The exact imported warning inventory is `1,223/169`, identical to the
pre-existing bounded Freyd reviewer checked in
`emdash2/logs/probes/commutative_ring_freyd_bounded_complexes-20260907-121348.log`.
This dependency closure differs from the generic normalization closure's
`1,217/169`; there is no warning increase from the new module. ANSI color
codes are stripped in the read-only warning-summary pipeline so its strict
critical-pair parser can classify all inherited pairs. The negative type
test emits its expected unsolved-equation diagnostic separately.

Both strict source/reviewer audits find zero rule clauses. Ordinary source
and health registration now include the module; reviewer discovery is
automatic. The global health snapshot remains deliberately stale at the
previously recorded, unrelated aggregate boundary. Formal exact-row iteration
is the next subrow; no complete formal degreewise short-exact structure or
long-exact homology window is claimed by the chain-map checkpoint.
The ten focused health-dispatch tests, shell syntax, fresh strict catalog,
source TOC, active-reference/report-header checks, and exact whitespace review
also pass. No compilation objects remain in the worktree.

The next formal experiment packages one raw short-exact row as its existing
adjacent-zero agreement, whole witnessed homology, incoming monomorphism,
outgoing epimorphism, and exactness of that actual stored homology boundary.
These are effective witness inputs, not a closed formal decision procedure.
The bounded predicate then follows three actual complex tails and the two
actual chain-map tails, retaining this evidence on their projected components.
Its whole form stores rows zero and one plus the remaining tail (only row
zero at length zero). Constructor/projection beta and wrong-map/wrong-homology
guards must pass before promotion. No independent chain squares or second
homology definition are admitted.

Both row and iterator probes are now promoted in
`emdash2/emdash3_2_commutative_algebra_freyd_short_exact_rows.lp` and
`emdash2/emdash3_2_commutative_algebra_freyd_bounded_short_exact.lp`.
Their two matching reviewers have seventeen assertions: fifteen positive
constructor/projection consumers and the wrong-homology and wrong-map
negatives. Quiet fresh-source checks pass in
`emdash2/logs/probes/commutative_ring_freyd_short_exact_rows-20260907-122408.log`
and `emdash2/logs/probes/commutative_ring_freyd_bounded_short_exact-20260907-122410.log`.
Warning-enabled checks pass in the corresponding `122443` and `122445`
logs, with the unchanged `1,223/169` Freyd dependency inventory and only the
expected negative-test diagnostics. All four strict audits find zero rule
clauses. The formal interface covers the given finite support; native lookup
already retains the outside zero row. Formal endpoint-window witnesses must
still come through the same explicit effective boundary when row 7/11 uses
that extension; no unconditional formal zero-row algorithm is being claimed.

The next architecture gate is still the full row-7 window on the existing
selected homology objects. Row 6 does not construct its descended connecting
map or establish long-exactness. No TypeScript/formal adapter, category graph,
or book claim is silently inferred from this data-interface completion.
Source/health registration, all ten focused health-dispatch tests, shell
syntax, strict fresh catalog, source TOC, active-reference/report-header
checks, and exact whitespace review pass for this tranche. An ignored-file
inclusive scan confirms that no Lambdapi compilation objects remain. The
unchanged native layer carries forward its 23-test/typecheck/lint evidence;
no unrelated aggregate or publication is performed.

The continuation checkpoint chain is `8a32323b` (native sequence),
`3b87d386` (formal bounded maps), and `10f57b4b` (formal degreewise exact
rows). The next dependency-ready semantic row is `LEH-WINDOW-7`; the
persistent objective remains active. Its first owner review should retain
the actual five homology results, reuse the existing induced-map operation
for the three ordinary arrows, and reuse the actual snake result for the
connecting arrow. In particular, the snake's `Ker(gamma)` and `Coker(alpha)`
must not be silently treated as the source/target homology objects. Compare
the row endpoints, factor into the target homology, and descend through the
source boundary at the existing kernel/cokernel/normality owners. Only then
package the three interior exactness witnesses and proceed to iteration.

### Homology-window owner experiment

The continuation starts from clean `cfd2b04f`; the preceding turn completed
and checkpointed the finite-support native/formal degreewise interface.
Workspace validation and sixteen nearest native sequence/functorial-homology
tests pass. The first native window will retain the five existing homology
results, the original sequence, and one actual snake result. Its three
ordinary arrows must consume those homology results through the existing
one-degree induced-map operation.

The connecting-map experiment first constructs and checks both inverses of
the short-exact endpoint comparisons `Coker(i_n) ⇄ C_n` and
`A_(n-1) ⇄ Ker(p_(n-1))`, reusing the snake's actual selected kernel/cokernel.
These induce `Z_n(C) ⇄ Ker(gamma)` and
`Coker(alpha) ⇄ Coker(d^A_n)`. The latter intermediate object is not a second
homology definition. Existing cokernel universality constructs the canonical
map from the actual `H_(n-1)(A)` into `Coker(d^A_n)`; its monicity permits
the existing normal-mono lift of the compared snake arrow. Finally the
source homology cokernel descends that map. Every comparison, zero test,
factor, reconstruction, and inverse agreement must remain in the result.

This refines “factorization into target cycles before quotienting”: it must
not require a global lift from source cycles into raw target cycles, which
need not exist in the nonsplit situation. The generic snake already works
after an epic cover. The proposed homology inclusion gives a quotient-level
target-cycle factor without choosing a section. Native computation must
validate this on the nonsplit polynomial example; the corresponding generic
monicity/factorization theorem and exactness transfer remain required before
row 7 is complete. Endpoint-zero windows are included, not silently omitted.

That native route is now implemented in
`src/v3_2/algebra_polynomial_freyd_homology_window.ts` with its companion
whole-result serializer. The window consumes an existing checked sequence
and a degree from zero through one above support. The ordinary arrows reuse
the existing induced-homology owner on the actual five stored homology
values. The connecting construction retains its one snake result, both
short-exact row factors, four checked isomorphisms, the alpha/gamma comparison
agreements, target differential cokernel, canonical homology inclusion and
monicity witness, normal-mono factor, and actual source-cokernel descent.
All three adjacent pairs retain zero agreements and native exactness results
indexed by those actual pairs. No global cycle representative or section is
chosen.

Eight focused tests pass, alongside sixteen sequence/functorial-homology
regressions (24 total). The richer nonsplit fixture has ranks `1,2,1`,
differentials `[x,0]` and `[0,1]`, degreewise inclusion `x`, and quotient
complex over `R/(x)`. Its source boundary is genuinely nonzero, its connecting
map is nonzero, and target factor/source descent succeed. Both endpoint-zero
windows and length-zero support pass. Tests also check all inverse laws,
actual homology-object reuse, invalid indices/chain-map flags, complete
deterministic serialization, and sensitivity to an altered descent witness.
Root typecheck, affected-file lint, and exact whitespace review pass. No
Lambdapi semantic changes, public-barrel changes, or unrelated aggregates
belong to this native checkpoint.

The generic owner audit finds no existing category-generic induced-homology
map operation: the baseline's existing induced-map owners are native and
witnessed formal Freyd. Row 7C must construct the generic kernel/cokernel
counterpart within this goal, using existing internal factor fibres rather
than a second manual-diagram grammar. Likewise native monicity and exactness
decisions do not discharge rows 7B/7D. This earlier sequencing required the
generic window before any bounded iteration. D-LEH-042 now explicitly permits
the operational proof–CAS baseline to proceed from the checked native window;
generic window/long-exactness claims still require their actual formal proofs.

The first row-7B generic probe can be stated more generally than homology.
For monic `k:Z → B`, `b:A → Z`, and `f = k b`, choose the existing whole
cokernels `q:Z → H` of `b` and `pi:B → D` of `f`. Their universal property
gives `j:H → D` with `j q = pi k`. Push out monic `k` along `q`; the
injection `v:H → PO` is monic by existing Abelian stability. The other
injection kills `f`, so the `f`-cokernel gives `s:D → PO`. Cancelling epic
`q` proves `s j = v`; existing monic-factor cancellation then makes `j`
monic. Specialize to the actual homology cycles/boundary. This avoids both
a second homology object and the need to package an unnecessary pushout
isomorphism. It is the next owner-position construction, not yet a theorem
claimed by the native checkpoint.

Native implementation checkpoint: `cae22d6b`. The worktree was clean after
that commit. No generic theorem is claimed complete by it; row 7B is the
next dependency-ready proof tranche. The full persistent goal, including
long-exact iteration, formal/categorical/proof-CAS consumers, and Chapter 31,
remains active and unchanged in scope.

The row-7B continuation starts from clean `ec3a7805` and a successful
fresh-source `examples/abelian_fiber_pushout_stability.lp` baseline. First
construct the cokernel-composite comparison for arbitrary actual whole
cokernels and an explicit factorization path. Prove its monicity via a
supplied actual pushout with monic opposite injection; the Abelian wrapper
must instantiate that evidence using the existing selected pushout and
stability theorem. Finally specialize to the actual homology cycles and
boundary. This separates the generic universal-property calculation from
bundled capability projections, without new axioms or computation rules.

The generic construction is now promoted in seven rule-free modules:
`emdash2/emdash3_2_cokernel_composite_comparison.lp`,
`emdash2/emdash3_2_cokernel_composite_pushout.lp`,
`emdash2/emdash3_2_cokernel_composite_monic.lp`,
`emdash2/emdash3_2_abelian_cokernel_composite_monic.lp`, and the three
`homology_cokernel_inclusion`/`abelian_homology_cokernel_inclusion` modules.
The comparison and its reconstruction are selected from the existing whole
cokernels. The pushout factor reconstructs the second injection after
cancelling the original cokernel projection, and monic-factor cancellation
supplies the desired monicity. The homology instance uses its original whole
cycles and boundary cokernel. The public theorem again accepts one Abelian
capability, not extra monicity evidence for the homology map.

The direct short-alias Abelian comparison probe exceeded 90 seconds both
quietly (`125913`) and with warnings (`130301`). Spelling the common literal
preadditive presentation consistently passes. Direct bundled homology
instantiation also exceeded 90 seconds (`130457`/`130752`); the PA-explicit
proof and its thin bundled wrapper pass. These are constructor/endpoint
presentation fixes, not weakened statements, opaque sealing, new equality
rules, or evidence that the mathematics is unavailable. All failed and
successful variants remain in `emdash2/tmp/probes/` with their logs.

The two promoted reviewers have thirteen assertions, including both
reconstruction equations, the generic and Abelian monicity statements,
the literal actual-homology comparison, a usable monic cancellation, and
negative wrong-cokernel/wrong-homology endpoints. Quiet source checks pass in
`emdash2/logs/probes/cokernel_composite_comparison-20260907-131545.log` and
`emdash2/logs/probes/homology_cokernel_inclusion-20260907-131546.log`;
warning-enabled source checks pass in the corresponding `131709` and
`131708` logs. The inherited inventory remains `1,217/169`, plus the expected
negative-test diagnostics. All nine strict audits find zero rule clauses.
Source and health registration use the ordinary route; no new isolated gate
or unrelated aggregate is needed. The next semantic row is 7C, generic
induced homology maps. The full window exactness proof remains row 7D.
The ordinary `scripts/check.sh` route passes on the final homology-inclusion
module and its complete source dependency closure. All ten focused health
dispatcher tests, strict fresh catalog, source TOC, shell syntax, active
references, report headers, and exact whitespace checks pass. The unchanged
native window retains its 24-test/typecheck/lint evidence. The global health
snapshot remains at the earlier documented unrelated aggregate boundary.

Generic homology-inclusion checkpoint: `8161a141`. The worktree was clean
after the commit. Row 7C is next; the full window proof, bounded sequence,
cross-layer consumers, and book deliverables remain active requirements of
the unchanged persistent objective.

The row-7C continuation starts from clean `9ed7025f` and a successful
fresh-source homology-inclusion reviewer. Factor the construction through
generic maps on existing whole kernels and cokernels, with reconstruction,
identity, composition, and inverse-comparison consumers. A map's compatibility
is an existing `HFiber` point of ordinary pre/postcomposition on internal
Homs; no new square primitive or six-object manual-diagram grammar is added.
The chain-pair interface can retain a middle map and its two such factor
points, with conventional components/paths as a transparent usability view.
Lift the middle map to actual cycles, derive boundary compatibility by target
kernel monicity, then use the generic cokernel map on the actual boundary
cokernels. Do not postulate any of the induced maps or reconstruction laws.
This slice constructs typed map operations and their laws; it does not by
itself claim a packaged whole homology functor from a newly declared category
of complexes. The existing homology objects and underlying generic category
operations remain unchanged.

Fifteen rule-free modules now implement row 7C1. The two `hom_factor_*`
modules are transparent instances/operations of `HFiber`. The three
`kernel_map*` and three `cokernel_map*` modules construct maps, their
reconstructions, identity/composition/extensionality laws, and inverse
comparisons. The two `chain_pair_map*` modules retain a middle component and
its upper/lower factor points, with derived component/path observations and
identity/composition. The five `homology_*map*` modules lift to the actual
cycle kernels, derive boundary compatibility by target kernel monicity, and
map the actual boundary cokernels. All intermediate tests are derived from
the original chain-map data; no induced map or agreement is postulated.

The map laws are theorem paths, not additional runtime functoriality rewrites.
Homology-map equality depends only on equality of the middle component, so
inverse middle components induce inverse homology maps. Kernel, cokernel,
and homology choice comparisons construct `IsoEvidence` between actual
different choices. They do not identify those objects judgmentally. The
existing formal Freyd effectiveness boundary is unchanged: generic whole
universal structures must not be inferred from native decisions.

All five promoted reviewers pass in quiet and warning-enabled source checks:
`examples/hom_factor_spaces.lp`, `kernel_maps.lp`, `cokernel_maps.lp`,
`chain_pair_maps.lp`, and `homology_maps.lp`. Their 49 assertions comprise
43 positive checks and six negative guards. They exercise factor/component
beta, kernel/cokernel/homology reconstruction and laws, actual isomorphism
projections, and comparisons of distinct universal choices. A positive
false-negative guard accepts different proofs of the same chain-zero
equation; wrong fibre targets, wrong selected objects, and a mismatched
intermediate chain pair are rejected.

The quiet logs end in `142128`, `142130`, `142131`, `142132`, `142134` on
2026-09-07; warning logs end in `142616`, `142618`, `142619`, `142620`,
`142621` respectively under `emdash2/logs/probes/`. The Hom-factor-only
closure inherits `1,117/157`; the other four inherit `1,217/169`, unchanged
from their corresponding existing kernel/additive closures. All twenty
strict audits pass. No new rule, unifier, opaque operation, or equality axiom
is added. The ordinary check/health lists include the new modules and the
reviewers are automatically discovered. No new special aggregate is needed.

Row 7C2 remains a real consumer gate. Use an actual `ComputationalChainPairMap`
between two existing short-exact row pairs to derive the snake triple, then
compare alpha/gamma with its end components using the row-5 isomorphisms.
Instantiate the new kernel/cokernel map-isomorphism operations at those
actual selected snake endpoints. This is not a fresh six-object manual
diagram input. The generic full-window factor/descent/exactness proof stays
in row 7D; row 7 and the full persistent goal remain active.
The ordinary checker also passes on the kernel, cokernel, and homology
isomorphism roots and their full source closures. A declaration audit confirms
that all 63 new symbols have definition bodies and no rule/unifier/opaque
clauses were added. All ten focused health-dispatch tests, strict catalog,
source TOC, shell syntax, active-reference/report-header checks, and exact
whitespace review pass. No compilation objects remain. The global health
snapshot and unchanged TypeScript tests remain at their recorded proportional
boundaries; no unrelated aggregate was run.

Generic map checkpoint: `3df110ee`; the worktree was clean after it. The
next row-map-to-snake construction can already start from two arbitrary
chain pairs and `F:ComputationalChainPairMap(p0,p1)`: select
`delta = dNext(p0)`, `beta = middle(F)`, and `lambda = d(p1)`. The upper
factor gives `beta delta = dNext(p1) next(F)`; the target pair's existing
zero law proves `lambda beta delta = 0`. Thus the snake triple is derived
without another coherence input. Short exactness is used subsequently for
the endpoint comparison isomorphisms, not for forming this triple. This
remains the first row-7C2 implementation, not a completed claim.

The row-7C2 continuation starts from clean `3ef10eb2` and rechecks the
short-exact comparison reviewer. Form the triple generically over the
existing preadditive chain-pair map. For alpha/gamma and the endpoint
isomorphisms, keep PA/normality explicit internally when instantiating the
existing Abelian/short-exact owners, following the measured row-7B discipline.
All comparison paths must be derived from factor reconstructions and monic/
epic cancellation; no manual diagram fields or object equality are inputs.

The continued owner probes now derive the triple, alpha/gamma comparisons,
and both endpoint isomorphisms. The source is the actual supplied kernel of
the row map's last component; the target is the actual supplied cokernel of
its first component. Forward/inverse maps and their inverse laws are checked
against the existing generic kernel/cokernel maps, not fresh object choices.
At that stage the probes were not yet promoted. Direct bundled-Abelian wrappers exceeded
90 seconds. A transparent eliminator through the two existing Sigma
eliminators checks and supplies wrappers at the original Ab-owned endpoints.
Its beta is constructor computation; a neutral Ab does not acquire a new
judgmental eta rule.

The status-review turn established a second terminal reviewer timeout; this
is diagnostic progress, not completion of row 7C2. Warning-enabled verbose
rechecks then confirmed multiple successful assertions before each timeout.
The isolated target-isomorphism reviewer and arbitrary-Ab consumer pass.
Other cumulative source runs still exceed the bound: dependency imports alone
have measured 45–84 seconds in these runs. The next experiment therefore
checks fresh exact dependency objects in separate bounded invocations, as at
the existing snake/normalization joins, and retains every original assertion.
No failing consumer is being replaced by a weaker type or opaque proof.

The first fresh-dependency run passed all nine owner modules and the triple,
elimination, comparison-path, source-isomorphism, target-isomorphism, and
bundled-comparison reviewers. It retains exactly the inherited
`1,217/169` warning inventory. Only the six-assertion whole-row reviewer
still exceeded its single 90-second invocation. Its source and target
constructor computations were then tested in separate reviewer targets,
with all six original assertions retained. This is a bounded consumer split,
not removal of a required computation or a claim that the entire tranche is
already green.

The split whole-row probes now pass as well. The last target constructor
comparison took 71.36 seconds with freshly checked exact dependencies in
`emdash2/logs/probes/snake-row-whole-isolated-20260907.log`; this is green
reference evidence, not satisfactory final interactive performance. All 28
original assertions are retained across eight promoted reviewers. The nine
owner modules contain 25 transparent definitions and no primitive, rewrite,
unifier, or opaque proof. `scripts/check_snake_row_comparisons.sh` registers
the same bounded staging for ordinary, reviewer, and health dispatch. The
full promoted quiet/warning runs and metadata audits are now green. This
continuation is progress: it resolves the failed consumers without weakening
their statements and implements the named row-comparison layer.

Final promoted evidence is
`emdash2/logs/probes/snake-row-promoted-warnings-20260907.log` and
`emdash2/logs/probes/snake-row-promoted-quiet-20260907.log`. The latter ran
through ordinary `scripts/check.sh emdash3_2_short_exact_row_snake.lp`
dispatch, not a separate unregistered substitute. Both gates check all nine
owners and eight reviewers; all 28 assertions (24 positive, four negative)
pass. Each Lambdapi process remains bounded to 90 seconds. The warning
inventory is unchanged at `1,217/169`. Seventeen strict rule audits,
thirteen focused health-dispatch tests, central catalog freshness/strict
classification, source TOC, shell syntax, active-reference/report-header
hygiene, and exact diff checks pass. The central catalog is unchanged because
the new assertions are independent examples, not central-kernel assertions.
No compilation objects remain in the worktree. The full health snapshot
remains intentionally stale at its recorded unrelated-baseline exception;
no complete CI, TypeScript, or repository aggregate is claimed.

The next operational tranche is row 7E. Extract the native connecting
construction from the window into one independently named operation while
preserving its selected source/target homologies, factor/descent data,
nonzero/nonsplit behavior, and full serialization. The window must call that
operation, not retain a second implementation. Subsequent bounded assembly
must retain and project its actual degreewise homology/window results rather
than recomputing independent copies. Generic row 7D remains unfinished.

Use proportional, bounded checks. Do not run repository-wide TypeScript,
kernel, book, print, package, or release aggregates merely for reassurance.

### Planning and audit

- inspect exact staged/unstaged state and all worktrees;
- verify baseline ancestry and current branch identity;
- run `workspace:check`;
- locate owners and consumers with `rg`;
- run the nearest exactness, snake, bounded-homology, category, proof–CAS, and
  book structural checks; and
- record the inherited warning/LHS/catalog/health boundary.

### TypeScript implementation

- root typecheck and affected-file lint;
- focused positive, negative, nonsplit, endpoint, foreign-ring, bounded-range,
  determinism, and serialization tests;
- direct operation, category method, planner, compiler, graph, and reference
  execution;
- exact whole-result serialization comparison; and
- no complete `check:ts` unless a genuinely affected shared integration
  boundary and current user scope authorize it.

### Lambdapi implementation

- smallest owner-position probe and first real consumer;
- quiet and warning-enabled checks, each target bounded to 90 seconds;
- explicit imported warning-boundary classification;
- strict inferred-slot/LHS audit;
- positive reviewer and relevant negative/noncollapse boundary;
- source registration, catalog, and proportional health evidence; and
- `scripts/check_abelian_snake_six_term.sh` for the measured whole six-term
  and exactness join: each dependency source, final target, projection module,
  exactness-cover/canonical-row stage, and reviewer is checked in a separate
  90-second invocation inside one disposable exact-source copy;
- no unrelated full health rebuild while the recorded dependent-simplex
  baseline defect remains outside scope.

### Book implementation

- read and follow `emdash2/print/AGENTS.md` before edits;
- edit only authoring sources, manifests, evidence, and provenance owners;
- run typography, assembly freshness, link/evidence, and focused render checks;
- render within the bounded policy and inspect affected pages; and
- do not publish, promote, or release artifacts without separate authorization.

## Rejection Signals

Refine or reject a candidate when it:

- asks users to supply the connecting arrow or either normal test;
- stores ordinary commuting squares instead of deriving them from chain-map or
  internal Hom-fibre data;
- defines a second homology object for endpoint convenience;
- equates selected kernel/cokernel objects by an opaque path;
- chooses a section of an arbitrary epimorphism;
- represents exactness only by a Boolean;
- decodes arbitrary truncated Freyd equality into raw agreement;
- duplicates the snake or homology matrix algorithm above lowering;
- recomputes degree windows instead of projecting them from the whole result;
- adds broad hot-head runtime rewrites;
- labels a book theorem checked before its implementation/reviewer is green;
- expands into unbounded/derived/spectral or orthogonal cubical work; or
- depends on an unrelated worktree.

## Completion Boundary

The goal is complete only when:

- the complete generic six-term snake sequence and its four interior exactness
  witnesses are constructed without manual diagrams;
- selected and arbitrary witnessed short-exact rows are related by explicit
  canonical comparison evidence;
- degreewise short-exact bounded complexes are available;
- one five-term homology window solves the snake-to-homology endpoint bridge and
  is exact at all three interior terms;
- the entire bounded long exact homology sequence is assembled with endpoint
  zeros and exactness at every displayed interior term;
- a genuinely nonsplit multi-degree polynomial Freyd example computes;
- categorical direct and compiled execution agree canonically;
- the witnessed formal boundary checks without quotient decoding;
- proof–CAS replays and adopts the selected whole result and equations;
- field/CAP differential evidence remains non-authoritative;
- Chapter 31 and affected appendices/evidence are coherent and pass their
  proportional book checks;
- every new rule/unifier, if any, has complete owner-position evidence;
- focused TypeScript/Lambdapi/book validation and standing authorities are
  synchronized, with any unrelated aggregate defect recorded honestly; and
- every ledger row is implemented, rejected with durable evidence, or
  explicitly deferred behind a concrete prerequisite.

The goal does not complete merely because a list of homology objects and arrows
can be printed or because the field-split example returns matrices.

## Deliberate Non-Goals

- unbounded complexes or infinite exact-sequence infrastructure;
- chain homotopies, quasi-isomorphisms, derived-category localization, or
  triangulated-category axioms;
- bicomplexes, DG categories, spectral sequences, or spectral algebraic
  geometry;
- Čech hypercohomology or sheaf cohomology;
- arbitrary quotient-path decoding or choice;
- a closed formal polynomial Freyd Abelian-category claim;
- a parser or complete TypeScript compiler for the book surface;
- integration of path-cubical/global-strictness work;
- external CAP/homalg/Singular runtime dependency;
- push, merge beyond the preparatory fast-forward, publication, PR, release,
  branch deletion, or worktree removal.

## Sources And Design References

- completed snake plan:
  `docs/TYPESCRIPT_EMDASH_ABELIAN_SNAKE_CONNECTING_PLAN.md`;
- completed Freyd homology plan:
  `docs/TYPESCRIPT_EMDASH_FREYD_HOMOLOGY_COMPUTATION_PLAN.md`;
- focused CAS/categorical architecture:
  `docs/TYPESCRIPT_EMDASH_FOCUSED_CAS_AND_CATEGORICAL_ENGINE_PLAN.md`;
- proof–CAS architecture:
  `docs/TYPESCRIPT_EMDASH_PROOF_CAS_DELEGATION_PLAN.md`;
- active exactness, homology, bounded-complex, snake, and witnessed formal
  owners under `emdash2/` and `src/v3_2/`;
- current book authoring sources under `emdash2/book/`; and
- CAP's reviewed `SnakeLemmaImplementation.tex`, CAP fiber/pushout APIs, and
  homalg's abstract homological-algebra architecture as differential/design
  references.

Active code, focused diagnostics, repository SOP, and this living decision
ledger remain implementation authority.

## Persistent `/goal` Launch Prompt

Implement `TS-EMDASH-BOUNDED-LONG-EXACT-HOMOLOGY-AND-BOOK` in
`/home/user1/emdash1-long-exact-v1` on
`goal/bounded-long-exact-homology-book-v3.2`, delegating every evolving owner
audit, exact-spine decision, complete snake-map/exactness construction,
short-exact-row normalization/usability comparison, degreewise bounded
short-exact sequence, one-window gate, full bounded long exact sequence,
native whole result, categorical operation/lowering result, witnessed formal
boundary, proof–CAS consumer, differential, book chapter/appendix/evidence
update, architecture consolidation, validation result, checkpoint, and
completion condition to this living plan. Preserve baseline
`054b43bd777d260f5da8b1242294ce0335780d0d` as comparison evidence. Preserve
contractible factor spaces, explicit raw agreements, selected whole universal
owners, existing homology identity, generic identity/composition/additive and
kernel/cokernel ownership, backend-neutral lowering, the Freyd quotient
architecture, and the nonsplit boundary. Follow root/nested persistent-goal,
Lambdapi, and book SOP; keep every Lambdapi target bounded to 90 seconds; avoid
unrelated aggregates; make only local validated checkpoint commits after
synchronizing exact staged diffs and the plan ledger. Do not push, merge,
publish, release, create a PR, amend, rebase, reset, rewrite history, delete
branches, or remove worktrees. Do not claim arbitrary quotient effectiveness
or begin unbounded complexes, derived categories, spectral sequences, Čech
hypercohomology, or orthogonal cubical/strictness integration. The goal
completes only when every scoped row is implemented, rejected with durable
evidence, or explicitly deferred behind a concrete prerequisite and all
affected authorities are synchronized.
