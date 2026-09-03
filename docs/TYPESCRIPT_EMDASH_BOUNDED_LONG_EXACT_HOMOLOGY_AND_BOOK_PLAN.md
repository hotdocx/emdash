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

| ID | State | Dependencies | Required result |
|---|---|---|---|
| `LEH-PLAN-0` | complete; checkpoint `bf217fe9` | integrated baseline `054b43bd` | living plan, isolated branch/worktree, Git/scope boundary, persistent goal |
| `LEH-AUDIT-1` | complete; checkpoint `01fd062c` | current exactness, snake, bounded-complex, book, CAP/homalg owners | exact owner/endpoint matrix, focused baselines, rejection signals, book chapter map |
| `LEH-EXACT-SPINE-2` | pending | `ComputationalExactAt`, finite families | reusable finite exact-sequence carrier or durable evidence that windows suffice |
| `LEH-SNAKE-MAPS-3` | pending | completed connecting result | remaining four snake maps, all adjacent-zero points, whole six-term result |
| `LEH-SNAKE-EXACT-4` | pending | row 3 and generic exactness | exactness at all four interior six-term positions |
| `LEH-SHORT-EXACT-NORMAL-5` | pending | short exactness, image/coimage, normality | selected short-exact-row normal form and canonical arbitrary-row comparison isomorphisms |
| `LEH-BOUNDED-SHORT-EXACT-6` | pending | row 5 and bounded chain maps | degreewise short-exact bounded-complex sequence with retained chain squares |
| `LEH-WINDOW-7` | pending | rows 4–6 and bounded homology | one five-term homology window, endpoint comparisons, connecting descent/factor, three exactness witnesses |
| `LEH-LONG-EXACT-8` | pending | row 7 and finite exact spine | complete bounded long exact sequence with endpoint zeros and all interior exactness |
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

| ID | State | Decision |
|---|---|---|
| `D-LEH-001` | accepted | The next primary milestone is the full six-term snake exactness followed by bounded long exact homology, not a book-only maintenance pass. |
| `D-LEH-002` | accepted | `AbelianSnakeTriple` remains the computational snake-diagram owner; no manual commutative-diagram record is introduced. |
| `D-LEH-003` | accepted | The long-exact degree substitution is `delta = i_n`, `beta = d^B_n`, and `lambda = p_(n-1)`. |
| `D-LEH-004` | accepted | Canonical snake endpoints must be compared with the existing selected homology objects; no second homology theory is introduced. |
| `D-LEH-005` | accepted | Selected short-exact rows are the primary computational form; arbitrary witnessed rows receive explicit comparison isomorphisms as a usability layer. |
| `D-LEH-006` | accepted | One exact five-term homology window is the mandatory architecture gate before bounded iteration. |
| `D-LEH-007` | accepted | The full result is bounded and finite; unbounded complexes, derived categories, triangulated categories, spectral sequences, and Čech hypercohomology remain later goals. |
| `D-LEH-008` | accepted | Native/categorical/formal/proof–CAS layers reuse the completed snake and homology owners rather than duplicating matrix algorithms. |
| `D-LEH-009` | accepted | Chapter 31 is an evidence-bearing deliverable of this goal; checked code remains authority and generated book/PDF artifacts remain tool-owned. |
| `D-LEH-010` | accepted | The divergent path-cubical/global-strictness branch remains outside this goal. |
| `D-LEH-011` | accepted after owner audit | The homogeneous `FiniteFamily` carrier is not by itself a dependent categorical sequence. Construct the concrete six-term window first; if bounded iteration needs a generic spine, follow the recursive dependent-Sigma precedent of formal bounded complexes. |
| `D-LEH-012` | corrected after endpoint audit | A six-object snake sequence has five arrows and four adjacent arrow composites. Proof–CAS and validation requirements use those exact counts. |

## Baseline And Validation Policy

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
