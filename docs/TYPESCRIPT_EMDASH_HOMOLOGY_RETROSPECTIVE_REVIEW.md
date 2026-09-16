# Homology Retrospective: Deferred Boundaries And Recommended Direction

Date: 2026-09-12

Status: review and proposed sequencing; no mathematical implementation or deferred experiment resumed

Parent: [bounded long-exact homology and book plan](TYPESCRIPT_EMDASH_BOUNDED_LONG_EXACT_HOMOLOGY_AND_BOOK_PLAN.md)

Execution continuation (2026-09-12): the user accepted the corrected review
and launched the [native universality and homology plan](TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_AND_HOMOLOGY_PLAN.md)
in a dedicated worktree. That living plan controls current scope and
validation; spectra/Heine/dependent stabilization research is explicitly
deferred, as are the endpoint checker experiments.

Follow-up: the [semantic architecture review](TYPESCRIPT_EMDASH_HOMOLOGY_SEMANTIC_ARCHITECTURE_REVIEW.md)
addresses universality, the global duality and native-Hom story, native
simplicial/cubical diagrams, automatic model/reifier setup and future
derived/directed-stable constructions. Its semantic-specification-first
sequence refines the implementation priorities below.
The latest clarification preserves foundational `hom_int`/`homd_int`, selects
whole categorical universality as the primary formal owner, and studies
one fixed endpoint with the other varying. The companion corrects the
earlier total-Hom-first and two-pole proposals rather than retaining them
as the selected architecture.

## Judgment

Keep the whole kernel/cokernel/homology architecture and the direct formal
connecting construction. Retain degree-and-role indexing as the preferred
public mathematical interface to investigate, while preserving the qualified
field-indexed iterator. Pursue total opposite together with its shifted
universe duality as a coherent foundation repair. A whole-H snake comparison
is a worthwhile next mathematical consolidation. Useful Došen-style
computation is already present; a general homology normalization theorem is
a separate research question.

Three corrections to the recovered recollection matter:

1. There are **two independently reproduced foundational defects**, involving
   internal opposite and Sigma Hom. Repairing only the literal `op` cannot
   qualify the theory.
2. The van Doorn-inspired formal replacement was **prototyped, not promoted**.
   Some direct boundary laws passed, but complete H/delta sharing did not.
3. The formal connecting construction is direct, but the **native CAS method
   still uses snake**. Mathematical definition, runtime algorithm and their
   interpretation are different parts of the current implementation.

These findings support consolidation, not another wholesale homology rewrite.
The soundness repair has priority before renewed formal certification claims.
The endpoint issue concerns a real missing theorem interface, but it does not
prevent the existing native computations.

## Evidence And Current State

This review inspected the clean main checkout at `3e6e2b96`, the parent plan,
the current kernel declarations, relevant one-way modules and reviewers,
the standing reports, the final boundary audit, the repair/prototype ledgers,
and selected recovered responses including 0208, 0210 and 0218. The latest
response confirms the documentation deployment; it does not supply another
mathematical checkpoint. The archive is historical evidence, not new action
authorization.

The active LP sources/reviewers have no diff from `ff139362`. The inspected
retained-model workflow/preparation and bounded consumer have no diff from
`09f9dd1a`. Historical validation below is identified as historical; this
review did not rerun the checker or native test aggregates.

| Question | Current implementation/evidence | Review judgment |
| --- | --- | --- |
| Whole H | Coherent K/Q presentations; H is a transparent composite on native one-degree zero diagrams | Keep this architecture |
| Connecting | Direct formal component; declared whole transformation with component computation | Keep, and compare its characterization across implementations |
| Window exactness | Three formal interior results and adjacent-zero laws | Preserve; these are substantive mathematical evidence |
| Finite assembly | Field-indexed Nat iterator with retained arrows/interior evidence | Working baseline, independent of the unfinished public endpoint wrapper |
| Conventional zero-ended theorem | Local zero-object laws exist; final symbolic attachment remains deferred | Missing formal result, not a failed homology algorithm |
| Degree/role formal indexing | Successful local prototypes; unresolved shared-input/H/delta comparisons | Preferred design experiment, not a completed migration |
| Native LES | Retained degree/role objects and window computations; snake-based connecting method | Preserve original choices and algorithmic witnesses |
| Proof-CAS interpretation | Computed equations plus supplied universal/model semantics and optional normality | Useful conditional interface; no closed-model theorem inferred |
| Foundation | Both Empty derivations remain admitted by the active encoding | Passing checks cannot certify consistency |

The [final boundary audit](TYPESCRIPT_EMDASH_HOMOLOGY_FINAL_BOUNDARY_AUDIT.md)
provides the detailed evidence inventory. Some older paragraphs in large
standing reports still describe intermediate obligations as pending; use
the final audit, latest plan direction and actual source to resolve chronology.

## 1. What Timed Out, And What A Record Redesign Could Change

The final right boundary was being recovered through recursive observations
of a generated, trimmed arrow sequence. Schematically:

```text
original:  ... -> H_0(C) -> S -> T
trimmed:   ... -> H_0(C) -> S
S = retained H_-1(A)
P(X) = (id_X = 0_X)

P(last_source(original)) -> P(last_target(trimmed)).
```

The zero-object lemma and generic trimming implication checked separately.
Their application at the expanded dependent endpoints exceeded the resource
limit. The original S need not be replaced by a chosen zero object: in an
additive category, `id_S = 0` implies that every map into or out of S is zero,
so S is a zero object.

Later isolation is stronger than the description “one large proof timed out.”
The [final experiment archive](../emdash2/audits/bounded-homology-endpoint-deferral-2026-09-11/README.md)
records a small additive-law comparison at native zero-cone projections,
without homology, short-exact rows or window exactness. Proof-bearing
classifiers themselves could exhaust the guard; comparison of two proof
inhabitants was unnecessary. Direct nested-pair target expressions did not
solve it either.

Two private same-head-congruence checker variants made that reduced case
complete in about a second, but turned an existing prerequisite from under
a second into a 90-second timeout. Neither variant was installed or used to
qualify the library. This supports a conversion-strategy explanation without
establishing a safe checker fix. A timeout is neither a mathematical
counterexample nor evidence of a missing Abelian hypothesis.

Primitive-projection records remain a sensible **owner-level** experiment.
A projection should be able to expose an operational field without repeatedly
reconstructing the nested dependent motives surrounding unrelated laws.
However, an ordinary record encoded by another Sigma alias does not achieve
that automatically. The failed specialized evidence/row records already show
that merely repackaging the same terms is insufficient.

The next bounded representation study should test, in this order:

1. The archived minimal native-endpoint law, with the original failure as a
   control and the proposed projection behavior explicitly specified.
2. A symbolic overlapping-row comparison, retaining the same chain-zero data.
3. H(inclusion) and delta at the actual public endpoint types.
4. The final symbolic endpoint-zero result and one retained native consumer.

Reject a design that helps only constructor beta or a neutral toy record.
Do not erase all proof data: raw relation witnesses and universal-factor
inputs can be computationally essential. Keep exactness/endpoint predicates
separate from operational observations where possible. Neither proof
irrelevance nor broad injectivity declarations follow from this diagnosis.

The existing guard remains the boundary for a future experiment: serial
checks, at most 90 seconds, and the repository memory/file limits. No such
experiment was restarted for this review.

## 2. Total Opposite And The Shifted Universe

The current nucleus has

```text
Hom(Op_cat(C), x, y) = Hom(C, y, x)
op : Functor(Cat_cat, Cat_cat).
```

The first formula reverses dimension 1 only. The second forces covariant
action on transformations because `Hom_cat(Cat_cat,A,B)` is the directed
functor category. These choices conflict. From a transformation between
point functors into C, the current whole op produces an arrow in the reverse
direction in C. Applying this construction to `Empty -> Unit` in the
category of groupoids/types yields `Unit -> Empty` and then an Empty
inhabitant. This is an encoding defect, not merely an unjoined warning.
See the [diagnostic and actual reproducer](TYPESCRIPT_EMDASH_INTERNAL_OP_VARIANCE_DIAGNOSTIC.md).

The user's proposed recursive Hom equation describes **total duality**:
all positive dimensions, including dimension 1, reverse. Write O for that
operation and R for reversal of dimensions 2 and above:

```text
Hom(O C, x, y) = O(Hom(C, y, x))
Hom(R C, x, y) = O(Hom(C, x, y))
op : R(Cat) -> Cat.
```

Thus “Op2” must mean “from dimension 2 upward,” not “dimension 2 only” or
“strictly above dimension 2.” `CoAbove2_cat` is the name already recorded in
the repair plan, with the explicit inclusive meaning.

The shift is necessary because a transformation's component is one
dimension lower than the corresponding cell of the category universe.
Functor direction stays forward; transformations, modifications and higher
transfors reverse. The induced whole Hom action has the useful type

```text
O(Functor(A,B)) -> Functor(O A, O B).
```

Ordinary dimension-1 transposition is then derived as `R(O C)`. Its Hom is
`Hom(C,y,x)` because the two Hom-level total duals cancel. This is a useful
two-operation basis, not a request to install an arbitrary dimension-mask
API. Ordinary 1-category opposite and higher duality must still have distinct
semantic readings. Lack's [2-category duality discussion, §1.6](https://arxiv.org/pdf/math/0702535#page=7)
explains the elementary op/co distinction.

The higher-dimensional literature supports this choice particularly well:
total duality is monoidal for the Gray tensor and preserves the oplax
internal-Hom profile; its action on the enriched universe has the shifted
source. Odd/even dualities have different lax/oplax behavior. These are
results for specified strict/Gray models, not a soundness proof for emdash's
entire signature. See Ara–Guetta, [§§2.22–2.27](https://arxiv.org/pdf/2503.08832v3#page=24).

Propagation is essential. A family `E:K->Cat` acquires an opposite over R(K):

```text
E^O : R(K) -> Cat
E^O = op composed with R(E).
```

An unrestricted same-base `Op_catd(E):K->Cat` can reconstruct the original
bad whole op even after deleting its literal declaration. A base restriction
or explicit justified comparison is needed wherever same-base notation is
retained. In particular, do not postulate `R(K)=K` for arbitrary K.

There is also an independent Sigma defect. For a constant family over the
terminal category, the product rule yields the expected Hom category, while
the generic Sigma-Hom rule supplies its opposite with the fibre direction
flipped. The [Sigma diagnostic](TYPESCRIPT_EMDASH_SIGMA_HOM_VARIANCE_DIAGNOSTIC.md)
derives Empty without whole op or opposite-family calls. Totalizing a
contravariant Hom family must compensate both base and fibre variance;
changing the op signature alone does not do this.

The [preferred repair candidate](TYPESCRIPT_EMDASH_INTERNAL_OP_VARIANCE_REPAIR_PLAN.md#total-op-prefix-preserved-result-at-deferral)
already implements the total-Op/R basis in an isolated source copy. Its
prefix has positive higher-cell controls and rejects the direct-op,
family-only and Sigma counterexamples at real type mismatches. The full
candidate still fails at `Homd_target_section_catd`, where R(Z) is being
compared with Z. This is a precise outstanding owner boundary, not evidence
that total duality is mathematically wrong. Resume there if repair is selected;
do not restart the discarded naming experiments.

The practical repair gate must include the complete affected dependent-Hom
target and consumers, both Empty negatives, and positive whole-action/Sigma
controls. Prefix rejection alone cannot qualify the full kernel. The
strict/lax/Gray profile also needs explicit interpretation; arbitrary
noninvertible interchange cannot silently be treated as strict equality.

## 3. What “Došen-Style Homology Computation” Can Mean

There are three useful targets, with different strength.

### Existing structural computation

Whole kernels and cokernels already have the appropriate adjunctions:

```text
J(X) = (X -> 0),     J adjoint-to K
I(X) = (0 -> X),     Q adjoint-to I.
```

The actual [kernel](../emdash2/examples/kernel_adjunction_presentations.lp)
and [cokernel](../emdash2/examples/cokernel_adjunction_presentations.lp)
reviewers contain nonidentity Došen rectangles. Whole mate functors and their
inverse cuts also exist. For a coherent family `h:J A=>D`, the active
[H definition](../emdash2/emdash3_2_homology_families.lp) is

```text
Z = K composed with D
beta = K(h) composed with eta_A
H = Q composed with Arr(beta).
```

Generic fapp/tapp already supplies composition, identity and naturality at
the selected profile. It would be inaccurate to say that the homology
development has no Došen-style computation until a global theorem appears.

The best near-term extensions are measured simplifications at these existing
owners: mate cancellation, universal reconstruction and composition of whole
H maps. For example, applying H to composable chain maps should reuse the
generic functor cut, not introduce another homology-specific composition
system. Formal K/Q heads must survive long enough for their cuts to match;
eagerly unfolding them into chosen record projections previously destroyed
those discriminators.

These are ambient computations. A separate user-facing syntax, parser or
free-category frontend is not a prerequisite. A restricted syntax could be
a metatheoretic device for studying a reduction theorem without becoming a
second product architecture.

### A relative normalization study

My proposed next research target is to simplify the structural part of one
real connecting-map calculation down to a finite collection of explicit
factor/equality obligations. Useful candidate equations include kernel-lift
and cokernel-colift reconstruction and uniqueness, always at the original
selected object and with their premises retained.

This would specify the supported operations, computational normal forms,
residual algebraic obligations and a preservation argument. Termination and
joining of the chosen reductions need separate evidence. It need not decide
all morphism equality in the supplied coefficient category. Unconditional
decision of arbitrary homological equality would already include equality
of maps between complexes concentrated in one degree.

The reviewed end of Došen's *Cut Elimination in Categories*, §§6.8–6.10,
explicitly discusses additional difficulties when adjunctions interact.
One cannot infer a normalization theorem for their combination from the
individual triangle laws. The local text is
[/home/user1/dosen-book/kosta-dosen-book-cut-elimination-in-categories.txt](/home/user1/dosen-book/kosta-dosen-book-cut-elimination-in-categories.txt).
Petrić–Zekić's [coherence theorem](https://arxiv.org/abs/2001.09736v4),
§§5 and 7, concerns structural closed/biproduct arrows and has a proper-object
restriction in the symmetric-monoidal-closed case. It does not supply
kernel/cokernel or arbitrary homology normalization.

Homology is not an exact functor on ordinary complexes merely because its
construction uses adjunctions. For a concrete check, over a field k take
the short exact sequence of complexes

```text
A:   0 -> k       (degrees 1 -> 0)
B:   k --id-> k
C:   k -> 0.
```

The evident degreewise inclusion/projection gives `0->A->B->C->0`.
Here H(B)=0 and the connecting map `H_1(C)->H_0(A)` is the identity with
the positive lift/differentiate convention. The connecting construction
contains substantive information even for termwise split rows.

### Universal computation beyond testing a CAS instance

Posur's [free-Abelian-category paper](https://arxiv.org/pdf/2103.08379),
Theorems 1.11 and 2.2 and §2.2, provides a genuine computational theorem
strategy: calculate a universal diagram in an Adelman category and interpret
it through exact functors. Effectiveness requires decidable two-sided
homotopy equations in the additive base. The paper constructs a universal
snake and gives Dowker's connecting formula; it does not offer an
unconditional decision procedure for arbitrary homological assertions.

For emdash I recommend a later, finite integral universal-snake benchmark,
not a replacement of the current module backend. An actual universal
interpretation can turn a symbolic computation into a theorem for every
interpretation of the premise. Testing a rational or polynomial instance
cannot do that alone.

The existing [Posur/homalg review](TYPESCRIPT_EMDASH_POSUR_HOMALG_REDESIGN_REVIEW.md#free-abelian-categories-as-a-universal-computation-mode)
records prerequisites that this proposal must retain: two-sided homotopy
witnesses, integral coefficients for the unrestricted universal claim, and
an exact interpretation. An Adelman object has both a relation and a
corelation; their composite need not vanish. Its general interpretation
uses `Im(Ker(g)->Coker(f))`. The present chain-pair H covers the
zero-composite case, and the present one-sided Freyd implementation cannot
simply be renamed Adelman.

## 4. Retain The Indexing Principle, Qualify The Implementation

Van Doorn changes the homotopy LES indexing from flattened natural numbers
to degree and one of three roles, using a successor structure so its endpoint
types are defined directly. This is the relevant lesson of
[§4.1.1, printed pp.68–69](https://arxiv.org/pdf/1808.10690v1#page=71).
It does not identify homotopy groups with module homology or remove the
proof's exactness/sign obligations.

For emdash's forward display, use

```text
E(n,A) = H_n(A)     E(n,B) = H_n(B)     E(n,C) = H_n(C)
(n,A) -> (n,B) -> (n,C) -> (n-1,A).
```

Finite constructor indices or downward offsets can express the last step
without arithmetic transports in dependent endpoint types. Van Doorn's
displayed maps run from successor to current position, so copy the design
principle, not his orientation verbatim. His statement about Nat elimination
does not prove impossibility for Lambdapi's extensible rewriting framework.

This separates two questions that earlier investigation sometimes combined:

- **Index computation:** which degree and role is next?
- **Observation cost:** how cheaply can the same row, zero witness, whole H
  object or complete arrow be recovered at that index?

Degree/role constructors address the first. Shared operational fields and
projection behavior address the second. Neither logically entails the other.
The native result already stores the mathematical degrees and roles; the
formal prototype passed some boundary and local-exactness tests, but failed
later H/delta sharing. Therefore maintain the principle and working iterator,
not an assertion that the new formal interface is complete or uniquely best.

The proposed public endpoint law should mention `E(boundary)` directly.
Flattening, trimming and serialized arrow order should be downstream views.
Their comparisons should first concern small index data, then its
interpretation. This is a design recommendation supported by the recovered
failures, not a measured performance guarantee for an unimplemented record
system.

## 5. Direct LES, Snake Specialization, And Whole-H Snake

### What actually changed

The active formal [direct component](../emdash2/emdash3_2_homology_record_connecting.lp)
uses the actual short-exact rows and retained homology records. Its
[whole transformation](../emdash2/emdash3_2_homology_window_connecting_transformation.lp)
is declaration-backed and computes that component. H itself is defined from
K/Q; the whole delta owner is declared with its computing observation.
Those are different foundational mechanisms, both requiring an appropriate
semantic interpretation.

The native
[connecting implementation](../src/v3_2/algebra_polynomial_freyd_homology_connecting.ts)
still advertises and calls the snake method, followed by selected endpoint
comparisons and descent. Consequently the redesign changed the primary formal
construction, not every execution algorithm.

Keeping the direct formal route was a good choice for this architecture.
It expresses the desired H endpoints directly and centralizes naturality.
It avoids making the public LES depend on a chain of alternate selected
snake kernels/cokernels. This is an engineering judgment, not a claim that
the traditional snake-based proof is mathematically inferior. For comparison,
the [Stacks proof](https://stacks.math.columbia.edu/tag/0111) obtains the
homology LES from snake on quotient/cycle rows.

A useful common specification is the covered formula. Write Z_C,Z_A for
cycles and q_C,q_A for their homology quotients. Pull back the row epimorphism
along `Z_C->C_n` to obtain an epic cover `e:E->Z_C`. The differential of the
lift into B_n factors through A_(n-1), giving a cycle map `a:E->Z_A`.
The connecting map satisfies

```text
delta composed with q_C composed with e = q_A composed with a.
```

Since `q_C composed with e` is epic, this determines delta at those
endpoints. This gives a focused way to compare algorithms. Exactness and
naturality alone do not generally choose its sign; delta and its negative
can both satisfy them.

### Snake as a short-complex specialization

For a commuting diagram with **both rows short exact**, regard its three
vertical arrows `a:A_1->A_0`, `b:B_1->B_0`, `c:C_1->C_0` as two-term
complexes. Their degreewise short exact sequence has

```text
H_1(A)=Ker(a), H_0(A)=Coker(a), and similarly for B,C.
```

The homology LES specializes to

```text
0 -> Ker(a) -> Ker(b) -> Ker(c)
  -> Coker(a) -> Coker(b) -> Coker(c) -> 0.
```

This is a mathematical derivation, not a claim that the current symbolic
endpoint wrapper already checks. It motivates deriving a public short-row
snake interface from the whole-H/window construction without requiring an
arbitrary-length generator.

The general snake hypothesis is weaker: the top row need only be right
exact and the bottom left exact. Leading/trailing zeros require additional
conditions. See the [precise snake statement](https://stacks.math.columbia.edu/tag/07JV).
The current `AbelianSnakeTriple` also packages a zero triple composite rather
than demanding two short exact rows. Do not replace that API by the two-term
short-exact specialization until its full scope has adapters or another
derivation. Preserve the general six-term theorem and its native witnesses.

### A more direct internalization through Dowker's formula

For `A -u-> B -v-> C -w-> D` with `w v u=0`, both rows below are chain
pairs and `(id,v,id)` is a chain map:

```text
X = (A -u-> B -wv-> D)
Y = (A -vu-> C -w-> D)
X --(id,v,id)--> Y.
```

Dowker's formula, as stated in
[Posur, Remark 2.10](https://arxiv.org/pdf/2103.08379#page=14), expresses the
snake connecting map by H of this map, with endpoint comparisons.
This suggests a small whole-H snake interface now that actual whole H exists.

The proposed implementation work is to construct X,Y and their map in the
existing native zero-diagram category, apply the existing H action, and
compare the result with the selected snake arrow via universal endpoint
isomorphisms and the covered characterization. Fix the sign and reuse the
original selections. This can internalize the connecting operation without
waiting for an unbounded complex category or the final bounded endpoint
packaging. It still needs its own complete-arrow/naturality and native
consumer qualification.

The current snake API is already internal to emdash in the sense of typed
universal operations and proof terms. It is not yet simply this specialization
of the newer whole-H operation. Calling it “external” without this distinction
would understate what is implemented.

## 6. Other Deferred Matters And Proposed Order

The most consequential additional boundary is **closed model construction**.
The [retained-model workflow](https://github.com/hotdocx/emdash/blob/df9b4778584121c3ad6ef7575093bd6d84be89e8/src/v3_2/algebra_formal_freyd_long_exact_model.ts)
distinguishes computed matrix equations, all-test selected-provider semantics
and whole-model presentation semantics. Whole K/Q presentations and normality
are supplied; a finite raw equation inventory does not prove those universal
contracts. With no normality, connecting coverage is explicitly not requested.
The direct/native connecting comparison should target a stated theorem or a
stated model contract, not silently convert current semantic adoption into a
derived proof.

Also retain these separate boundaries:

- Ordinary-target internalization uses `IsNCat 1 C`; preadditive object/Hom
  data alone does not establish the required entire higher-Hom profile.
- Runtime conversion, proof-time usability, equality paths and isomorphisms
  are different interfaces. Agreement need not mean identical matrix data or
  serialized records.
- The parallel strictness migration does not repair the confirmed variance
  defects. Its control also admitted the counterexample.
- Chain homotopies, derived/stable categories, spectra and spectral sequences
  remain future layers. The reference inventory also retains a directed-
  spectrum proposal; this review does not qualify it. Those routes would need
  a comparison with the present Abelian H and a sign convention, not just new
  terminology.
- The source-only health inventory is not a runtime check of every registered
  target. Documentation deployment did not remove mathematical deferrals.

Recommended bounded work, with no implementation launched by this review:

| Priority | Tranche | Concrete completion criterion |
| --- | --- | --- |
| 1 | Joint total-op/Sigma/dependent-Hom repair | Full affected source and positive consumers qualify; all three existing Empty routes fail for the corrected variance reason |
| 2 | Whole-H snake and direct/native connecting comparison | One actual whole chain map, original endpoint comparisons, fixed sign, characterization agreement and retained nonsplit consumer |
| 3 | Public degree/role endpoint interface and record study | The minimal failure, real H/delta sharing and final symbolic endpoint theorem all check within the existing limits |
| 4 | Concrete coherent-model/provider construction | State and discharge one currently supplied semantic contract without changing retained native selections |
| 5 | Relative structural reduction and integral universal-snake research | A specified finite fragment with checked residual obligations; universal interpretation only where actually constructed |

Priorities 2–4 can be reordered for a concrete consumer. Priority 1 governs
formal soundness claims; it need not erase the usefulness of independent
reference algorithms. The endpoint study and universal-normalization study
should remain separate so that neither becomes an unbounded prerequisite
for the other.

## Review Validation

Changes from this review are limited to this document and a recovery link in
the parent plan. Local Markdown targets and diff whitespace were checked;
the active-reference and report-header/lifecycle checks were run. No LP,
TypeScript, generated book/PDF, installed checker or Git history was changed.
Previously recorded mathematical validation is carried forward only for the
unchanged boundaries identified above.
