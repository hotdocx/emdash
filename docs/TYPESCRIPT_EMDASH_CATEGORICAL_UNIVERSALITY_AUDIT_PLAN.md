# Categorical Universality Audit

Date: 2026-09-09

Plan-ID: `TS-EMDASH-CATEGORICAL-UNIVERSALITY-AUDIT`

Status: proposed staged audit; reference-window-first sequencing

Parent: [bounded long exact homology and book goal](TYPESCRIPT_EMDASH_BOUNDED_LONG_EXACT_HOMOLOGY_AND_BOOK_PLAN.md)

## Decision And Sequencing

The whole adjunction interface, not an independently rebuilt groupoidal
fibre predicate, is the primary categorical universality already available
for K and Q. `Adjunction_hom_prof_comparison` retains whole variation in the
probe and differential, and `adjunction_hom_component_iso` gives a
`DefIso Cat_cat` of the actual Hom categories. Its whole mate functors and
their point/whole cancellation already compute.

For the current arrow-diagram and zero-arrow embeddings, the readable forms are:

```text
Hom_Arr(C)(J₀X,d) ≅ Hom_C(X,Kd)
Hom_C(Qd,X)       ≅ Hom_Arr(C)(d,I₀X).
```

H is built from K, Q and the actual boundary transformation. There is no
separate declared adjunction for H, and neither connecting maps nor long-exact
exactness follow just by naming H.

The user's later sequencing proposal is the recommended execution policy:
finish a working reference homology window and its retained proof–CAS consumer
before attempting a broad migration. This window must include the connecting
map at actual H endpoints, adjacent-zero results and its three interior
exactness statements. The full parent goal still includes bounded assembly
and the book update; this audit does not replace or shrink those obligations.
Use the completed window as a comparison corpus for later redesign, not as
permission to declare the full goal complete.

Whole K/Q/H remain the public mathematical interface during this reference
work. Checked fibre-based records can serve as implementation and older-proof
adapters. Small direct categorical improvements are appropriate when they
serve the current consumer; a repository-wide replacement of IsContr fields
is not a prerequisite for closing the reference loop.

## What The Current Record Layer Means

`ComputationalKernel` and its dual package an object, structural arrow,
annihilation law and contractible factor fibres. A centre of such a fibre
is computational data: its arrow supplies the selected lift/colift. These
records are not merely human assurance, but neither are they a replacement
for a whole directed Hom-category comparison.

The recent whole-owned record proof uses W/V-selected contractibility and
installs the actual whole K/Q fields and mate centres. That is a valid
compatibility construction. It should not be described as extra universality
that the already supplied adjunction lacks.

Being classified by Grpd, or packaged as a record, is not itself the problem:
adjunction evidence also has a classifier. The question is whether the
universal condition controls complete directed Hom actions or only arrow
objects and equality paths. Groupoidal paths must not silently stand for
arbitrary noninvertible higher cells.

## Initial Owner Inventory

This is an initial classification, not a completed transitive audit. The
literal IsContr scan currently reaches 24 root v3.2 source files, including
the integrated diagnostics. Aliases such as IsEquivMap, representedness
interfaces and derived fields need separate dependency tracing.

| Owner family | Existing role | Candidate categorical formulation and disposition |
|---|---|---|
| Kernels/cokernels and the new universal records | Selected arrow/path factor operations | Prefer the already implemented J₀ ⊣ K and Q ⊣ I₀ Hom-category comparisons in new categorical consumers; retain records as qualified adapters. |
| Normal mono/epi lifts and Abelian structure | All-test contractible lift/colift fibres | Probe selected inverses of the canonical image/coimage comparisons, using K/Q mates for operations. This is a candidate for the ordinary realization, not an automatic directed-omega equivalence. |
| Terminal/initial objects | Whole canonical-arrow transformation plus contractible incoming/outgoing Hom carriers | Review adjunctions with the terminal category and whole represented-Hom comparisons; inspect existing higher action before calling the fibre field redundant or insufficient. |
| Algebraic fibre products and pushouts | Kernels/cokernels of additive difference maps, with contractible factors | Compare/instantiate the existing slice/base-change or weighted universal interfaces in the appropriate profile; do not identify different strict/lax cone notions without a bridge. |
| Weighted limits and representability | Already whole ProfComparison/representedness data | Positive architectural precedent; do not replace it with objectwise fibre contracts. |
| Polynomial and localization universal APIs | Ordinary ring-map factorization spaces with selected evaluators | Investigate free/reflector adjunctions or initial objects in the appropriate algebra/comma categories. These alternatives are not asserted to be implemented already. |
| IsEquivMap, truncation, HITs and equality/coherence spaces | Genuine groupoidal or homotopical conditions | Keep when this is the intended mathematical domain; no blanket migration. |
| Recentring and derived contractibility helpers | Projection/choice or proof infrastructure | Classify by consumer. Their occurrence is not an independent universal capability or evidence of a defect. |

The terminal-object audit must inspect its existing whole transfor and
off-diagonal cuts, not only `terminal_hom_contr`. Conversely, set-valued
arrow carriers alone must not be confused with discreteness of every
directed Hom category; the existing ordinary Freyd OneCat realization has
its own qualification.

## Normality And Abelianity Candidate

For ordinary additive categories with kernels and cokernels, a natural
alternative organizing condition is that the canonical comparison
Coim(f) → Im(f) is an isomorphism for every f; see
[Stacks, Definition 12.5.1](https://stacks.math.columbia.edu/tag/0109).
Related normality views compare a monomorphism with Ker(Coker(m)) and an
epimorphism with Coker(Ker(e)).

For emdash computation, an inverse must be an actual selected operation,
not merely an opaque assertion that an inverse exists. Qualify how the
comparison and inverse live in whole functor/transfor families and agree
with the retained native algorithms. Do not assume that the ordinary
characterization transfers unchanged to every directed omega profile.

## Audit Questions And Migration Gate

For each actual universal owner:

- identify the represented test category/profunctor and its variance;
- identify the whole universal operations, or the concrete missing owner;
- determine whether IsContr is primary data, derived evidence, a selected
  implementation interface, or genuinely homotopical content;
- retain all higher action at directed parameters; a list of point formulas
  does not establish that action;
- locate the raw-model/test-representation adapter and state its profile;
- verify runtime computations and proof-time usability separately, following
  inferred-slot, owner-position, warning and noncollapse SOP;
- preserve native selections and algorithms, without a blanket old/new
  wrapper-comparison project; and
- compare the candidate on the same completed reference-window consumer.

Do not mechanically replace equality by Hom or IsContr by TerminalObject.
That changes the permitted comparison cells and may change strict universality
into a lax factorization problem. Reuse native internal-Hom/comma owners
rather than introducing manually stored commuting-square syntax.

Where an ordinary consumer needs a fibre contract, it can be derived from
the categorical comparison once the test-representation bridge is checked.
The bridge from raw annihilator data to an actual arrow-diagram morphism
must not be assumed merely because the reverse projection already exists.

## Preservation And References

The current and rejected source experiments are preserved as non-executable
[recovery patches and a checksum manifest](../emdash2/audits/homology-universality-2026-09-09/README.md).
All six patches pass isolated-index applicability checks; 65 embedded
source/driver versions were recovered with their original SHA-256 hashes.
Accepted code and its reviewer history remain authoritative.

The later direct-connecting tranche adds 27 recovered prototype/driver
versions, including failed mixed-presentation alternatives. Its selected
point construction now reaches literal whole-H endpoints, but the complete
reference window and its connecting naturality/consumer remain unfinished.
This progress does not by itself start or complete the broader migration.

The whole-H window zero tranche now derives its cycle/quotient factors
directly from whole naturality and proves all three adjacent-zero laws.
Nineteen further prototype/control/driver files have verified recovery,
bringing the archive to 111 embedded versions. Interior exactness and the
retained connecting consumer still precede the broad migration gate.

The first interior is now proved exact at H(B), using the retained quotient,
boundary correction, original row kernel and left-cycle operations.
Twenty-three further recovered source/control/driver versions preserve that
construction and its LF interface experiments, for 134 embedded versions
in total. The remaining two interiors and native connecting consumer still
precede the broad migration gate.

The second interior, at H(C), is also now proved by an epic presentation
of delta and a corrected middle cycle. Ten further source/driver versions
have verified recovery hashes, for 144 embedded versions. The final
H(A') interior and retained connecting consumer remain before the broad
migration gate.

The third interior, at H(A'), is now proved using the original connecting
cover and retained source cycles. Its covered target lift is identified
by the original row/cycle monomorphisms, without object-equality casts.
Nine further prototype/driver versions have verified recovery, bringing
the archive to 153 versions. All three interior witnesses are complete;
exact-window packaging, connecting naturality and the retained connecting
consumer still precede the broad universality-migration gate. This result
strengthens the reference baseline, not a claim that the broad migration
has been implemented or that the whole parent goal is complete.

The three witnesses are now packaged in `HomologyWholeExactWindow`, indexed
by the original whole-H inputs with no duplicate objects or arrows. Generic
and canonical projections compute; a rigid unrelated-witness negative
passes. The expanded wrong-interior negative remains a recorded timeout.
Nine more recovered source/control versions bring the archive to 162.
Connecting naturality and native interpretation remain ahead of the broad
universality migration; packaging the proofs is not that migration.

Riehl–Verity's
[2-category theory of quasi-categories](https://arxiv.org/abs/1306.5144)
uses comma objects and lifting universal properties; their
[homotopy coherent adjunctions](https://arxiv.org/abs/1310.8279)
distinguish categorical adjunction structure from contractible spaces of
coherent extensions. These guide the architecture, not a proof of emdash's
full directed omega semantics. The existing Posur/Barakat research review
and local references remain available for constructive algorithm design.
General op/Sigma repair and orthogonal strictness-branch integration remain
deferred under the parent goal's existing policy.
