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
| `LEH-SHORT-EXACT-NORMAL-5` | in progress via 5A–5C | short exactness, image/coimage, normality | selected short-exact-row normal form and canonical arbitrary-row comparison isomorphisms |
| `LEH-SHORT-EXACT-KERNEL-5A` | complete; validated endpoint checkpoint pending | selected boundary and short-exact evidence | canonical `A -> Ker(p)` comparison isomorphism and reconstruction |
| `LEH-SHORT-EXACT-COKERNEL-5B` | complete; validated endpoint checkpoint pending | exactness, normal epi colifting, selected cokernel | canonical `Coker(i) -> D` comparison isomorphism, inverse, and reconstruction |
| `LEH-SHORT-EXACT-SELECTED-5C` | in progress; selected-row/image-iso probes pass, compatibility assembly being refined | 5A–5B and canonical image/kernel row | selected `Im(i) -> B -> Coker(i)` row and whole arbitrary-row usability comparison |
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
| `D-LEH-006` | accepted | One exact five-term homology window is the mandatory architecture gate before bounded iteration. |
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

Row 5C remains active in the ignored `short_exact_*` probes. The selected
row, PA-explicit monic-image comparison, normalization carrier, projections,
and canonical isomorphisms check. The compatibility-point assembly still
requires an owner-position refinement. The next probe constructs a kernel
row from its existing whole kernel value, using identity exactness covers,
so the row and the image isomorphism can share that same owner. No object
equality assumption or weaker normalization result is being substituted.

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
