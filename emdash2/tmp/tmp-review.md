# Temporary independent review checkpoint

Status: rebased peer-review draft; not an Emdash implementation authority.
Scope: the staged baseline plus the completed current working-tree candidate,
including its unstaged source/check/report/example changes.
Constraint: no Lambdapi/make/probe/check commands were run for this review.

## Provisional bottom line

- Strong, mathematically literate, unusually candid research prototype/specification.
- Not yet a defensible small foundational kernel, completed HoTT foundation, or
  end-user-ready standard-library base.
- Appropriate external verdict: promising research artifact; major revision
  before foundational/computational-univalence or library-readiness claims.
- Most named H0/H1/Omega0 surface slices exist, and the current candidate now
  completes the scoped OneCat ordinary-isomorphism comparison relative to the
  ambient decoder assumptions. The hardest assurance work remains: a primary
  certificate representation/extensionality/property story, scalable
  observational fibrancy/elimination, HIT/reflectors, universe
  stratification/model, and normalization/confluence/canonicity.

## Review boundary and evidence

- The first pass below records the staged snapshot so that the review remains
  reproducible. This rebase additionally reads the now-paused working tree.
  Where the two differ, the later “Rebased current-candidate findings” section
  and the final verdict supersede the staged-progress statements.
- Existing generated evidence for the current candidate (not rerun here)
  reports a 20,013-line source with 809 symbols, 581 rewrite rules, and 58
  unification rules; 18,460 check lines with 1,514 positive assertions; 1,705
  classified checks across 63 areas; and successful exits for 41 measured
  files. This includes the 271-line/17-assertion Nat-action example and the
  480-line/33-assertion completed OneCat example.
- There is a small current status synchronization defect: source, checks,
  Foundations, SOP, README, catalog, and health evidence contain
  `nat_succ_ind_eqr`, while the plan header and ledger still call that facade
  an active/selected probe and quote the immediately preceding 19,988-line,
  808-symbol, 1,694-check snapshot.

- Re-scan after context compaction is explicitly anchored to Git-index blobs
  (`git show :emdash2/...`), not the concurrently changing working copies.
- Snapshot blob IDs used for the final trust/status pass: source
  `53a880419b6618506233fc19ab7243ceae89bedb`, checks
  `46e5098fc8e9612514a0cce042c5c82752d321c5`, plan
  `7886bd989fe5b9d469bb89020d38c0ddbd323bf9`, SOP
  `f6f3c54b9d71f71f46ea657deb6cdad6a1a55f3d`, Foundations
  `520cc4fd951488aba4d4c70e381047b240e8769c`, catalog
  `ab391935d8960ce6038584d4a3a0969d6eca9e99`, health
  `ddba400e0a911fc8cfe368a4496162cb436e2074`, and staged OneCat example
  `bfcee83dc703f682d8e8a8c325e5ed22d27d5a2d`.
- The staged OneCat boundary includes `one_cat_omega_inverse_path` but not the
  currently unstaged right-law decoding/transport and
  `one_cat_omega_iso_evidence`; those are encouraging in-progress details, not
  promoted evidence for this review.
- The staged plan is 6,344 lines, source 19,373, checks 17,861, Foundations
  2,040, SOP 1,610, and canonical-syntax guide 516. The staged change itself is
  large: +1,384 source lines, roughly +1,364/-87 checks, and five new reviewer
  examples.
- Existing generated health evidence (not rerun) reports source 19,373 lines,
  790 symbols, 581 rewrite rules, 56 unification rules; checks 17,861 lines and
  1,472 positive assertions; 40 measured files exit successfully (the source,
  checks, and 38 `.lp` examples).
- The staged generated check catalog reports 1,650 classified assertions over
  59 areas and zero unclassified checks. The staged SOP still reports an older
  1,637 total, and the staged Foundations text still describes the selected
  OneCat inverse comparison as missing although it is present in staged source.
  The staged plan's handoff header/OneCat ledger is stale in the same way: it
  asks for the directed selected-inverse comparison that staged source, checks,
  catalog, and example already contain.
  These are authority-synchronization defects, not failures of the underlying
  declarations, but they make status claims harder to audit externally.
- SOP warning inventory: 1,128 warnings = 971 unjoinable critical pairs + 157
  replaceable-variable reports. This is diagnostic evidence, not confluence.
- Lambdapi local manual says `unif_rule` is experimental and has no sanity
  check. Successful typed `eq_refl` only shows a rule fires, not that it is
  semantically justified.
- Nearly all reviewer examples contain assertions only; only
  `path_induction_transitivity.lp` defines one symbol. They are useful regression
  witnesses, not yet realistic downstream-library case studies.
- The staged `examples/README.md` names only six older examples even though the
  staged tree contains 38 `.lp` examples. This reinforces that the examples are
  currently an internal milestone suite rather than a curated user entry point.

## Staged plan reading

- The plan succeeds as an architecture/decision ledger: it distinguishes H0,
  H1, H2, and Omega0; direct vs view-based universe identity; runtime rewrite
  vs proof-time comparison; truncation vs directed dimension; and active,
  probed, prerequisite, and deferred states.
- Its own formal threshold for a “foundational HoTT MVP” permits decoder
  univalence capabilities, opaque contraction, no HITs, no universe model, and
  no global normalization/canonicity. Therefore the plan can call its H1/Omega0
  compatibility surface active while an external foundations review still
  judges the result non-foundational. Both statements can be internally
  consistent; the milestone name is the problem.
- The document is also too accretive for an external status report. Current
  handoff text, historical snapshots, phase start/completion logs, and stale
  matrix rows coexist across 6,344 lines. In the reviewed index snapshot, the
  handoff/OneCat ledger still asks for the selected-inverse comparison even
  though the staged implementation, checks, catalog, and example contain it.
  Labels such as “initial snapshot” reduce but do not remove the navigation
  burden.
- The plan explicitly accepts every `C : Cat` as omega-univalent and defers
  stratification/model/consistency. At the staged boundary it also kept global
  ordinary-iso capability inhabitants. The current candidate has correctly
  retired those inhabitants and replaced their intended use with the scoped
  OneCat construction. It retains the general `CatIsoUnivalence` interface and
  the legacy `iso_evidence_path` decoder; the latter is coherence debt, but is
  no longer packaged as a global ordinary-iso univalence capability.
- The architecture honestly identifies its highest-risk missing mechanism:
  extensible structured equality needs a scalable registration/fibrancy owner;
  the current closed per-former bridges do not establish an open protocol.

## What is genuinely good/natural

- Separation of homotopy truncation from directed categorical dimension.
- Generic functoriality/naturality owners instead of constructor-local copies.
- Fixed-arrow `OmegaEquivAlong_D0(f)` plus Sigma packaging supports named arrows
  and iterated hom structure.
- `Path_cat` uses generic composition and a genuine opposite/symmetry boundary.
- Standard-looking recursive truncation predicates and meaningful Pi/Sigma
  closure architecture.
- Hybrid generic/shaped equality retains generic J while adding decoded views.
- Strong positive/negative regression discipline and honest rejected-candidate,
  blocker, and deferral records.
- OneCat validation asks the right question: recover ordinary isomorphism only
  after hom discreteness, rather than globally collapsing omega equivalence.

## Core trust/semantic concerns

- `Grpd`, equality, reflexivity, and J are primitive; this is acceptable for a
  signature, but the trusted base grows substantially beyond them.
- The file has 31 `constant symbol` declarations. That count must not be called
  “31 axioms”: several are native decoded classifiers or opaque categorical
  constructors with projection rules. It does, however, show that the theory
  is a sizeable primitive rewrite specification rather than a tiny derived
  kernel. Logical trust is better audited declaration-by-declaration.
- Important ordinary theorems remain opaque capabilities:
  `is_equiv_map_by_inverse`, product/Sigma/Pi equivalence preservation.
- Groupoid univalence relies on global opaque
  `grpd_univalence_by_decoder`; categorical univalence relies on global
  `cat_univalence(C)` and `cat_univalence_by_decoder(C)` for every active Cat.
- `Cat_cat : Cat` decodes its own objects to `Cat`; no hierarchy,
  stratification, consistency model, or normalization argument is supplied.
- Likewise `Grpd_grpd : Grpd` decodes to `Grpd`, and the universe is closed
  under full dependent `Pi_grpd`. This has the classic unstratified
  Type-in-Type/Girard-Hurkens risk; Lambdapi acceptance cannot be read as
  consistency. Avoid claiming a definite contradiction without a formal
  derivation, but treat this as a foundational blocker rather than optional
  polish.
- Direct category-universe equality reduces to `OmegaEquiv`, but terminates
  because the recursively intended certificate owner remains opaque.
- `OmegaEquivAlong_D0` has observers but no inductive/coinductive definition,
  eliminator, eta/extensionality theorem, reverse view decoder, or proved
  property-valuedness. This is the central architecture bottleneck.
- The finite evidence views are one-way observations, not representations.
- The new evidence-view examples explicitly test that opaque certificate
  equality is *not* convertible to either the one-layer or dimension-indexed
  view and that observations of arbitrary certificates do not unify. This is
  honest boundary testing, but confirms that no representation theorem or
  certificate extensionality has been obtained.
- Generic `eq_refl` can inhabit a classifier that reduces to structured Sigma
  data without itself becoming the canonical Sigma constructor; projections
  may therefore depend on special bridges or remain stuck.
- The Sum action slice needs four special proof-time unification bridges. This
  is an early warning that per-former registration may scale by rule
  proliferation rather than by one principled eliminator/fibrancy mechanism.
- 56 trusted unification rules and 971 nonjoinable critical-pair warnings are
  too large a trust surface for foundational claims without a semantic audit
  and confluence/normalization evidence.
- The complete unification scan is not random: many families express rigid-head
  inversion, associativity, ordinary/displayed facade comparison, variance,
  Hom-action factorization, or endpoint recovery. But repeated direct bridges
  are installed because unification is not reliably transitive, and these
  equations participate in typing without Lambdapi sanity checking. This is a
  coherent engineering workaround and simultaneously a large trusted layer.

## Current milestone reading (rebased)

- H0 elementary decoded formation/elimination: substantially implemented.
- Observational identities for Unit/Bool/Nat/Sum and Pi/Sigma/one record:
  useful bounded slices, not a closed/open extensible theory of formers.
- H1: useful funext, structural path, TypeEquiv, truncation, and decoder surface;
  several equivalence/univalence proofs are assumed as capabilities.
- Omega0: impressive executable interface and recursion-by-observation skeleton,
  but its certificate is opaque and global categorical univalence is assumed.
- OneCat ordinary-iso recovery: completed in the current candidate relative to
  global categorical decoder univalence and the opaque generic
  `is_equiv_map_by_inverse` theorem. The code constructs the inverse comparison,
  transports the right law to the selected left inverse, reconstructs
  `IsoEvidence`, proves both nested-Sigma round trips using hom discreteness,
  packages a OneCat-scoped decoder capability, and derives a named
  `TypeEquiv`.
- `IsNCat -> object truncation`: only conditional on an explicit
  `OmegaEquivAlongEvidenceProp_D0` inhabitant, which is not constructed.
- Direct Grpd universe equality: rejected due self-normalization timeout; finite
  `GrpdPathView := TypeEquiv` fallback only.
- H2/HIT/truncation reflectors: deferred.
- Metatheory (model, consistency, normalization, canonicity): deferred.

## Usability/reuse assessment

- Current canonical notation is comment/future-parser notation, not active
  syntax.
- One monolithic 19k-line kernel, no stable modular public API, no general
  user-level schema for registering a new datatype/record/category and deriving
  identity/action/fibrancy.
- Reviewer files validate predeclared interfaces but barely demonstrate users
  defining reusable new mathematics.
- Therefore: reusable internally by expert maintainers; premature as an
  external standard-library substrate.

## Example-level findings

- The examples are commendably precise about runtime versus propositional
  equality and include negative controls. `pi_funext.lp`, for example, shows a
  computational happly/funext beta but only propositional eta, whose reflexive
  base uses the selected proof-time Pi coherence rule.
- `grpd_univalence_decoder.lp`, `omega_equiv_d1.lp`, and
  `categorical_universe_identity.lp` demonstrate rich downstream behavior, but
  all inherit their decisive inverse laws from decoder capabilities. They are
  coherent API tests relative to those assumptions, not derivations of
  univalence from primitive equality/J.
- `categorical_universe_identity.lp` carefully distinguishes generic
  `eq_refl` from canonical `cat_path_refl`; this preserves J computation but
  exposes the two-reflexivity/projection issue rather than solving it globally.
- `truncation_universe_univalence.lp` explicitly says its result is restricted,
  propositional, and not direct observational universe identity. This is a
  mathematically meaningful theorem interface, but again depends on ambient
  decoder univalence.
- `ncat_object_truncation_conditional.lp` includes strong negative controls:
  neither `IsNCat` alone nor an arbitrary certificate witness yields the desired
  result. This correctly exposes the missing evidence-property inhabitant.
- `sum_observational_action.lp` obtains useful componentwise computation and
  negative provenance controls. Its reliance on two basis heads plus four
  direct unification bridges for only two constructors is concrete evidence of
  the scalability concern.
- `nat_observational_action.lp` is a useful second data point: successor action
  is the exposed predecessor proof, agrees propositionally with generic
  `eq_ap`, and the new former-specific `nat_succ_ind_eqr` delegates to generic
  J without adding another rule. It still needs one stable basis and two
  proof-time comparisons to reconcile component and outer reflexivity.
- `path_category.lp` is among the most natural demonstrations: it routes
  composition and reversal through generic categorical owners and proves
  agreement with J-derived operations propositionally.
- `path_induction_transitivity.lp` is the sole example that actually declares a
  downstream theorem symbol. Even it is a short facade proof via an existing
  unification bridge, so it does not yet test sustained third-party library
  development.

## HoTT/OTT comparison checkpoint

- Book HoTT has a much broader coherent mathematical foundation/library
  (ordinary identity types, univalence as axiom, HITs/truncations), but its
  univalence is not computational in the cubical sense.
- Cubical type theory supplies a constructive semantics for univalence and
  function extensionality, with separate canonicity results and HIT examples.
  Emdash has selected computational betas but no corresponding global semantics
  or canonicity theorem.
- Narya is also experimental, but already provides normalization-by-evaluation,
  a parser, user-defined records/inductive/coinductive types, separate
  compilation, holes, and type-directed observational identities. This is a
  useful usability and kernel-coherence benchmark.
- Emdash is more directly expressive for strict/lax directed omega-categorical
  data, transfors, displayed/directed families, and adjunction-style
  computation than classical HoTT's core. That is orthogonal to, not evidence
  of, greater foundational maturity.

## Feasibility

- Completed/high-confidence relative milestone: bounded OneCat
  right-law/reconstruction and ordinary-iso univalence.
- High-to-medium: derive the presently opaque quasi-inverse-to-equivalence
  theorem and product/Sigma/Pi equivalence-closure witnesses inside the theory.
- High-to-medium: prove a direct OneCat object 1-truncation result from the new
  path/isomorphism equivalence and discrete homs, without waiting for a global
  omega-certificate property theorem.
- Medium: continue per-former observational equality and restricted action only
  if it is made an instance of a common registration/fibrancy interface rather
  than an indefinitely growing family of hand-written proof-time bridges.
- Medium for each finite level: replace the finite observation map by a primary
  dimension-indexed certificate representation and prove its property-valuedness
  and extensionality by induction.
- Medium/low research: relate those finite certificates to a guarded omega-limit
  certificate with an explicit corecursor, productivity discipline, and
  bisimulation/path-extensionality account. Lambdapi has no native coinductive
  checker, so part of this discipline may remain external unless tooling grows.
- Low under the current unstratified representation: direct recursive Grpd or
  certificate universe identities plus convincing global normalization.
- Low now, potentially medium after the equality/elimination and universe work:
  computational truncation reflectors, Circle, and representative HITs.
- Unknown until redesign/model: consistency and canonicity of the global
  self-universe plus every-category univalence policy.
- Goal drift must be stated explicitly: the plan's own “Foundational HoTT MVP”
  and even its long-term completion checklist permit axiomatic global Cat
  univalence and omit a model/canonicity gate. Passing those internal criteria
  therefore would still not achieve the original phrase “computational
  foundation” in the external proof-theoretic sense.

## Rebased current-candidate findings and requested clarifications

### The actual goal and the honest milestone name

The best reading of the intended project is not “reimplement Book HoTT in
Lambdapi.” It is a minimal Emdash/Kosta–Došen cut-elimination kernel for
functorial and directed omega-categorical programming, augmented with enough
HoTT, cubical, and observational-equality ideas to make identity structured and
useful. Runtime rewrite rules should express chosen computation; narrowly typed
unification rules should express proof-time comparison; generic categorical
owners should keep higher-dimensional constructions iterable.

That is coherent and worth pursuing. However, three thresholds must remain
distinct:

1. **Compatibility/API MVP:** the desired names, types, selected betas, and
   examples are present relative to stated capabilities. This is substantially
   achieved for H0/H1/Omega0.
2. **Computational implementation skeleton:** a useful body of reductions and
   typed proofs exists, but some central theorems and decoders are primitive
   authorities. The current candidate is an advanced skeleton of this kind.
3. **Foundational computational type theory:** the trusted constants and
   proof-time equations have a model or proof-theoretic account; universes are
   size-safe; normalization/canonicity/confluence claims are justified; and
   univalence/HIT computation comes from the design rather than a decoder
   postulate. This is not achieved.

Therefore “Foundational HoTT compatibility MVP” is defensible only if
*compatibility* is prominent. “Foundational HoTT MVP” or “computational
foundation completed” overstates the result.

### Does the observational equality actually reduce/compute?

Yes, but only in a deliberately hybrid and nonuniform sense. “The equality
computes” currently conflates four different claims:

| Layer | Current status |
| --- | --- |
| Equality **classifier** | Often genuinely rewrites: Unit, visible Bool/Nat/Sum constructors, Sigma, Pi, PathRecord, Product, and direct Cat-universe equality expose structured classifiers. |
| Proof **observers/actions** | Selected projections, happly/funext beta, PathRecord reflexivity, Sum/Nat action, and canonical categorical packages compute. |
| Proof **normal form/canonicity** | Generally absent. Generic `eq_refl` often stays distinct from the constructor proof suggested by the reduced classifier. |
| Arbitrary dependent elimination | Generic J computes only on its guarded literal `eq_refl`; a few shaped/former-specific facades exist, but there is no general fibrancy protocol. |

Concrete examples:

- `succ m = succ n` rewrites to `m = n`, but
  `eq_refl Nat (succ n)` does not rewrite to `eq_refl Nat n`.
- Equal Sum tags expose component equality and mixed tags expose Empty, but an
  outer Sum reflexivity proof is not erased into a component reflexivity proof.
- Pi equality exposes a related-input view. `PiHapply(PiFunext(h))[x]` has a
  computational beta; the reverse eta law is propositional and its reflexive
  case uses a proof-time coherence rule.
- Sigma equality exposes a nested path view and generic reflexivity has selected
  projection rules, but the whole proof does not normalize to one canonical
  Sigma-path constructor. One eta comparison is proof-time.
- PathRecord is the strongest shaped case: its generic reflexivity rewrites to
  a stable shaped head, projections compute, and the selected shaped J beta
  fires.
- `nat_succ_ind_eqr` is a good improvement: because successor equality already
  exposes predecessor equality, it delegates an arbitrary dependent motive to
  generic `ind_eqr` and computes on *component* `eq_refl n` without adding a
  rule or unification axiom. It intentionally does not make outer
  `eq_refl(succ n)` or the action basis a generic-J redex.

This is real computation, not cosmetic notation. It is nevertheless not the
uniform normalization/canonicity story supplied by a mature computational type
theory. A future report should always say which of classifier reduction,
observer beta, definitional proof equality, or propositional theorem is meant.

### Why Sum needs basis heads and unification rules

Mathematically, a Sum injection should act on paths componentwise. The problem
is operational provenance. After the Sum equality classifier rewrites, the
component proof and the outer proof produced by generic J inhabit convertible
classifiers but remain different proof terms. The guarded J beta deliberately
refuses to mistake a component reflexivity proof for literal outer Sum
reflexivity, because that broader rule was subject-reduction-dangerous.

For each of `inl` and `inr`, the implementation introduces a rigid basis head
and compares it at proof time with:

1. normalized action on component reflexivity; and
2. the exact outer generic-J action normal form.

That yields two basis heads and four `unif_rule`s. The theorem then composes
paths through the basis explicitly because Lambdapi unification rules are not
reliably transitive. The semantic law is natural; the mechanism is a local
proof-time adapter. The scalability warning is that a two-constructor former
already needs four trusted comparison clauses, while Nat successor adds one
head and two more. This is acceptable as an MVP probe, but not a good
open-ended datatype protocol unless the clauses can be generated from a small,
audited former/fibrancy interface.

### What “opaque theorem/capability” means here

“Opaque” in this review means a declared symbol has no Lambdapi definition
body (`≔ ...`) proving its result. It is part of the trusted signature. It may
still have narrow projection rewrite rules, so selected downstream data can
compute even though the proof of existence/coherence is assumed.

`TypeEquiv` itself is standard: a forward map plus contractible homotopy
fibres. Its selected inverse and left/right paths are derived from those
fibres. The following remain bodyless theorem capabilities:

- `is_equiv_map_by_inverse`;
- `product_type_equiv_is_equiv`;
- `sigma_type_equiv_same_base_is_equiv`;
- `pi_type_equiv_same_domain_is_equiv`.

For `is_equiv_map_by_inverse`, a rewrite exposes the chosen centre of a fibre
from the supplied inverse and right law, but the contraction proof is still
primitive. These statements are mathematically conventional and likely
provable; this is proof debt, not evidence of a false theorem. Deriving the
generic quasi-inverse theorem first, then Product/Sigma/Pi closure using
explicit inverses, would materially shrink the trusted logical surface.

### Groupoid universe: finite view versus direct identity

`GrpdPathView(A,B) := TypeEquiv(A,B)` is a finite *normalization interface*; it
does not mean the space of equivalences is finite or truncated. The decoder
`grpd_equiv_path` has selected reflexive/Product computation, while both
general round trips are projections of the bodyless
`grpd_univalence_by_decoder` inhabitant. Thus general groupoid univalence is
currently assumed through a specified inverse, not derived by complete case
analysis over formers.

The rejected direct public equation `A =_Grpd B ↦ TypeEquiv A B` recursively
reopens itself at the self-universe: `TypeEquiv` contains homotopy fibres, whose
definitions contain equality between universe elements. This is why the finite
named view normalizes but the direct self rule timed out.

An inductive or coinductive certificate alone is not the missing prerequisite.
The universe problem principally needs one of:

- a hierarchy `U_i : U_(i+1)` with no same-level self code;
- a semantically justified impredicative/stratified encoding; or
- a guarded/lazy universe computation discipline with a model.

Structural case analysis can compute univalence for canonical equivalences of
closed codes. It cannot, by itself, normalize every arbitrary/open equivalence
into a syntactic constructor equivalence. Full computational univalence usually
needs a Glue/coe/extent-like semantic mechanism or an observational universe
relation, not merely more cases.

### What `_D0` means and what the omega certificate currently is

`_D0` is an implementation-stage owner name, not a mathematical dimension:

- D0 is fixed-arrow certificate data and its low-level observations;
- D0b is the variable-evidence/next-hom action layer;
- D1 is the public package/decoder/generator layer.

The public `OmegaEquivAlong` is a transparent alias to
`OmegaEquivAlong_D0`, and `OmegaEquiv(C,x,y)` is the natural dependent sum
`Σ(f : Hom(x,y)), OmegaEquivAlong(f)`. The fixed-arrow/Sigma split is a good,
reusable mathematical choice. The staging suffix should eventually disappear
behind a stable public module/API once its normal forms settle.

The certificate itself is presently an abstract codata-like interface:

- `OmegaEquivAlong_D0(f) : Grpd` is a primitive classifier;
- destructors select left/right inverses and two recursively packaged cells;
- reflexive/Product/opposite/iso-derived generators have selected projection
  rules;
- one-layer and dimension-indexed records observe existing evidence.

It is **not** yet an implemented inductive/coinductive object: there is no
constructor schema or corecursor for arbitrary evidence, eliminator, eta or
bisimulation/extensionality law, reverse decoder from observations, formal
productivity/guardedness discipline, or proof that evidence is property-valued.
The finite `CatDim` observation tree is a useful prototype for the shape of a
finite representation, but today it is only a map *out of* the opaque object.

### Why direct Cat-universe equality terminates, and what would solve it

The public rule makes Cat-universe equality expose
`OmegaEquiv(Cat_cat,A,B)`, which unfolds one finite layer to a Sigma of a
functor and `OmegaEquivAlong_D0` evidence. Normalization stops because the
certificate classifier is opaque. That gives useful outer computation:
forward functor, evidence projection, canonical reflexivity/Product packages,
and next-hom observations. It does not computationally explain the recursively
coherent evidence.

There is a mathematically credible solution: use size-stratified universes of
categories and define equivalence as a property with recursively coherent
higher data; model the omega-limit by guarded/coinductive observations. The
hard part is turning that semantics into a Lambdapi rewrite system whose
conversion is productive, terminating enough for checking, and coherent.

A real finite/guarded certificate would resolve several present blockers, but
not all of them:

- **would help:** reverse views, evidence extensionality, construction by
  recursion/corecursion, property-valuedness, unconditional finite-NCat object
  truncation, and a principled stopping rule for Cat-universe observations;
- **would not alone solve:** self-universe consistency/size, generic
  observational fibrancy/J, computational groupoid univalence for arbitrary
  open equivalences, HIT eliminators, or global rewrite confluence.

The representation must make “is an equivalence” a property. A raw package of
chosen left/right inverses is analogous to HoTT quasi-inverse data and need not
itself be a proposition. Contractible inverse spaces, half-adjoint/coherent
equivalence data, or a recursively property-like formulation are better
targets than simply declaring the current four-field observation record to be
the datatype.

### Why both `cat_univalence` and `cat_univalence_by_decoder` exist

`CatUnivalence(C)` is the abstract contractible-fibre statement that
`idtoequiv_cat` is an equivalence. `CatUnivalenceByDecoder(C)` is the more
operational presentation: it names `omega_equiv_path` as an inverse and stores
both round trips. `cat_univalence_from_decoder` derives the former from the
latter using `is_equiv_map_by_inverse`.

The current source nevertheless declares independent bodyless inhabitants of
both types for every `C : Cat`. Operational consumers route through the decoder
version, so the standalone `cat_univalence(C)` is redundant authority. The
cleaner design is to define it as `cat_univalence_from_decoder(C)` (or retire
the inhabitant while retaining the interface). More fundamentally, if every
active `Cat` is definitionally/policy-wise univalent, that evidence should
eventually be reflected in the type of categories—e.g. `PreCat` versus a
packaged univalent `Cat`—rather than only in a global axiom.

The same distinction explains groupoid univalence: selected constructor cases
compute, but the general decoder round trips remain fields of a bodyless global
capability. The intended “case analyse on every type former” design is only
partly realized.

### Is the missing certificate machinery central or merely nice-to-have?

It is central. Each missing operation answers a different foundational need:

- constructors/corecursor: how an end user creates evidence;
- eliminator: how generic theorems consume it;
- eta/bisimulation/extensionality: whether observations determine evidence;
- reverse view decoder: whether the finite/deep view is complete rather than
  merely observable;
- productivity: why recursive observation does not make conversion diverge;
- property-valuedness: why the certificate fibre does not add unwanted higher
  choices and why Sigma truncation closes.

The current observation records are good reconnaissance, but promoting a
reverse rule before selecting such a representation would be unsound
engineering: it could manufacture eta loops or conceal non-propositional
choices.

For finite dimensions, an inductive family
`EquivAlong_n(n,C,h,x,y,f)` with zero/successor clauses is a realistic target;
prove property-valuedness and extensionality by induction. Treat the omega case
separately as a guarded limit/codata interface with lazy destructors and a
bisimulation principle. This avoids forcing one unguarded self-recursive rewrite
to serve both purposes.

Narya is useful inspiration for lazy codata/comatching and type-directed
observational identity, not a drop-in prerequisite or validation. Its own
documentation describes codata/comatching and normalization-by-evaluation but
also records incomplete positivity/productivity enforcement and no implemented
HITs. Emdash therefore needs its own guardedness contract or external checker.

### NCat object truncation: meaning and feasibility

The conditional theorem is mathematically meaningful and follows the standard
shape. With the convention in this file, a zero-category has a set of objects;
an `(n+1)`-category has n-categorical homs; consequently the object type should
be `(n+1)`-truncated. The successor proof uses:

1. object paths equivalent to `OmegaEquiv` by categorical univalence;
2. `OmegaEquiv = Σ f, Certificate(f)`;
3. inductive truncation of the arrow base; and
4. propositionality of each certificate fibre.

The implementation computes exactly at zero and successor given a global
inhabitant of `OmegaEquivAlongEvidenceProp_D0`; that inhabitant is not
constructed. So the theorem is useful and correctly conditional, but does not
yet establish unconditional object truncation.

The dimension-indexed primary certificate design is the broad solution for all
finite n. There is also a nearer, high-value special case now available:
the completed OneCat equivalence identifies object paths with ordinary
`IsoEvidence`. In a OneCat, hom-arrow types are sets and their equality/law
types are propositions; the nested Sigma of an isomorphism should therefore be
a set. Transporting setness back across the path/isomorphism equivalence should
give object 1-truncation without the global omega-certificate property axiom.
This would be an excellent next theorem and an independent test of the new
OneCat lane.

### Ordinary Cat isomorphism retirement and the two reflexivities

The earlier criticism that global `cat_iso_univalence(C)` was only quarantined
by prose has been resolved in the current candidate: the arbitrary-`Cat`
capability inhabitants/classifier were retired. The general interface
`CatIsoUnivalence` remains, as it should, and OneCat constructs an inhabitant.
The old `iso_evidence_path` primitive decoder remains public for legacy/Product
computation; it should still be retired or reduced to a derived compatibility
alias once its last consumer is migrated.

For direct Cat-universe identity, generic
`eq_refl (Obj Cat_cat) A` and canonical `cat_path_refl A` are intentionally
distinct:

- generic `eq_refl` is the literal head on which guarded J and generic `eq_ap`
  compute;
- `cat_path_refl` is the projectable Sigma package whose functor/evidence
  observations compute.

Collapsing the first globally into the second broke generic consumers and
created overlap/provenance problems. Keeping both preserves the two useful
betas. It does not reduce propositional expressiveness because the decoder
round trips relate the views, but it makes definitional computation depend on
which reflexivity presentation a term uses. This is a defensible interim
boundary and a visible sign that a uniform structured-reflexivity/fibrancy
protocol is still missing.

### Is the foundation ready for truncation reflectors, Circle, and HITs?

No—not for promoted *computational* HITs. The current `IsTruncGrpd(n,A)` says an
existing type is truncated; it is not a reflector. A truncation reflector needs
a new carrier `||A||_n`, point and higher squash constructors, a restricted
dependent eliminator into n-truncated motives, constructor betas/coherence,
functoriality, and universe behavior. Circle needs at least `base`, `loop`, a
dependent eliminator, and point/loop computation.

Current PathOver, Pi/Sigma paths, truncation predicates/closure, and structured
reflexivity are useful prerequisites. Missing are a generic higher-constructor
schema, a sound motive/fibrancy discipline, a universe/model boundary, and an
account of higher computation. Lambdapi native inductives do not automatically
supply higher path constructors; manually adding symbols and rewrites now would
mostly create another axiomatic interface.

A small non-promoted syntax probe is feasible. A representative promoted HIT
should wait until one can state exactly which computation is runtime, which is
propositional, and why the rules are subject-reducing and semantically modeled.
Cubical type theory is the more relevant semantic source for computational
univalence/HITs; Narya currently does not supply an implemented HIT model.

### Recommended redesign sequence

1. **Freeze and classify the trusted base.** For every bodyless theorem,
   decoder capability, rewrite, and `unif_rule`, record whether it is primitive
   semantics, derivable proof debt, operational axiom, or temporary adapter.
2. **Remove redundant authority.** Derive `cat_univalence` from the decoder;
   prove `is_equiv_map_by_inverse`; derive Product/Sigma/Pi equivalence closure;
   finish migrating the legacy ordinary-iso decoder.
3. **Exploit the completed OneCat result.** Prove OneCat object 1-truncation
   directly through ordinary `IsoEvidence`. This checks mathematical reuse
   without waiting on the hardest omega problem.
4. **Make finite certificates primary.** Define a CatDim-indexed,
   property-like certificate with constructors/eliminator, observation,
   reverse decoding, eta/extensionality, and an inductive property theorem.
5. **Separate the omega limit.** Add a guarded codata/corecursor and
   bisimulation story rather than an eager recursive equality rule. State which
   productivity checks are in Lambdapi and which are external.
6. **Stratify universes or supply a model.** Do not reopen direct Grpd
   self-identity merely because the certificate becomes guarded.
7. **Generalize former registration.** Use Bool/Nat/Sum/PathRecord as a test:
   the common protocol should derive classifier action and selected dependent
   elimination without linear growth in hand-authored unification bridges.
8. **Only then add one representative HIT/reflector.** Require an eliminator,
   computational beta evidence, negative controls, and a clear trust/model
   classification before expanding H2.

### Updated global peer-review assessment

The current design does **not** feel like arbitrary symbols were added merely
to make examples pass. Its strongest choices—iterated homs, global
functor/transfor owners, fixed-arrow certificates with Sigma packaging,
truncation/dimension separation, and the OneCat ordinary-iso recovery—are
mathematically motivated and mutually reinforcing. The examples have unusually
good negative provenance controls.

It does, however, feel accretive at the foundational boundary. A 20k-line
monolith, 581 rewrite rules, 58 experimental proof-time unification rules, 971
reported nonjoinable critical pairs, self universes, and bodyless general
univalence/theorem capabilities are too much unmodeled authority to call a
small natural kernel. End users still cannot define a new former and obtain its
observational equality/action/J through a stable library interface; they need
kernel-level rewrite/unification expertise.

Relative to Book HoTT, Emdash is currently much richer in directed
omega-categorical syntax and much poorer in established foundational semantics,
HITs, and library breadth. Relative to cubical type theory, it has useful local
definitional betas but no comparable constructive account of general univalence,
composition/filling, or canonicity. Relative to Narya, its directed categorical
ambition is distinctive, while its user-defined observational/coinductive
infrastructure and normalization story are much less mature.

## Final-answer shape

Lead with verdict and precise status. Separate:
1. what is implemented;
2. what computes versus is assumed;
3. correctness levels (parser/typechecker, internal typing, mathematics,
   metatheory);
4. coherence/reuse;
5. HoTT comparison;
6. feasibility and priority order;
7. external peer-review decision.

## Final external-review decision

- Status against the plan's deliberately permissive internal milestone:
  advanced/substantially implemented H0/H1/Omega0 compatibility prototype.
- Status against the original “computational foundation” intent: materially
  incomplete. The missing work is not merely polish; it includes the semantic
  account of the universes/unification equations, explicit certificate
  representation/extensionality, H2 formers, and global normalization or a
  model.
- Status as mathematics: most visible definitions and theorem statements are
  recognizable and dimension-correct; the now-complete OneCat reconstruction
  and scoped ordinary-iso univalence are especially natural. Claims derived
  through opaque theorem or decoder inhabitants remain valid only relative to
  those assumptions.
- Status as computation: many local projections, eliminators, action laws, and
  canonical constructor cases really reduce. Univalence round trips,
  associativity, and several closure results rely on proof-time/opaque
  authority; there is no whole-theory computational guarantee.
- Status as a user platform: not yet. A third-party user cannot add ordinary
  formers and obtain observational equality/action/J through a stable library
  interface; doing so still entails kernel rewrite/unification engineering.
- Peer-review recommendation: accept as an interesting experimental artifact
  or research prototype with strong documentation; major revision/reject if
  submitted as a sound foundational kernel, completed computational
  univalence implementation, or standard-library-ready proof assistant.
- Rebased change in verdict: current work raises the implementation-completeness
  score and removes one unnecessary global authority, but does not change the
  foundational verdict because the decisive certificate, universe, decoder,
  unification-trust, and metatheory issues remain.
