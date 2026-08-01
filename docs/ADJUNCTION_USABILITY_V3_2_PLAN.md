# Emdash v3.2 Adjunction Usability Plan

Date: 2026-07-31 (America/Toronto)

Status: implemented and validated; uncommitted handoff-ready result

Plan-ID: `ADJUNCTION-USABILITY-V3.2`

Baseline: `cea2605ca4fe6a3023b46c26c5997956cc4e9f03`
(`docs: record recursive Hom Pages deployment`)

Branch: `goal/adjunction-usability-v3.2`

Worktree: `/home/user1/emdash1-adjunction-usability`

Persistent-goal objective: implement a direct-TypeScript outer-LF trusted
rectangular adjunction declaration, then investigate the smallest coherent
full-functor counit/transpose bridge toward Došen-style triangular
presentations. A faithful object-only `G^o` classifier remains consumer-gated.

Checkpoint authorization: branch/worktree creation and implementation are
authorized. Local checkpoint commits are not yet authorized. Push, merge,
publication, history rewriting, branch/worktree removal, and cleanup are not
authorized.

Recovery evidence: the review that selected this plan is archived as
`infinity-codex:019fbb03-cc64-7cf2-be18-24c35b0dfab0:019fbb0c-13af-7e83-81af-e6c58ad75cd5`
and, in the launch worktree, under
`emdash2/tmp/ai-responses/sessions/2026-08-01_019fbb03cc64/responses/0001_2026-08-01T02-23-04Z_019fbb0c-13af-7e83-81af-e6c58ad75cd5.md`.
That response is decision evidence, not an authority: active code, the nested
SOP, and this living ledger decide the current state.

## 1. Purpose And Outcome

The project now has a mostly settled mathematical and syntactical ordinary
adjunction core, but declaring and consuming a concrete adjunction remains
awkward. Independently named functors, unit, and counit do not automatically
acquire a canonical `Adjunction(F,G)` witness or agreement with the kernel's
stable adjunction observations. Consumers also meet adjunctions in several
mathematically equivalent presentations, including Došen's rectangular and
triangular formulations.

This plan addresses those usability gaps without weakening the trusted Core
or prematurely multiplying kernel classifiers. It separates two layers:

1. a small direct-TypeScript outer-LF macro that assumes a rectangular
   adjunction from already declared full functors and transformations and
   expands to ordinary explicit LF commands; and
2. a separate, evidence-gated kernel-presentation investigation for a
   full-functor counit/transpose formulation, followed only if justified by a
   consumer by a faithful object-only `G^o` triangular classifier.

The first production outcome is a typed API comparable to:

```ts
program.assumeAdjunction({
    name: "myAdj",
    sourceCategory: R,
    targetCategory: L,
    leftAdjoint: F,
    rightAdjoint: G,
    unit: eta,
    counit: epsilon
});
```

This is a TypeScript host declaration. It is not expression string syntax and
does not authorize an outer-LF text parser.

## 2. Authority And Non-Authority

Read and apply the following order on every continuation:

1. `emdash2/emdash3_2.lp` for active definitions and computation;
2. the one-way active extensions named in `emdash2/AGENTS.md`;
3. `emdash2/emdash3_2_checks.lp` for executable statements;
4. `emdash2/reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`;
5. `emdash2/reports/EMDASH_FOUNDATIONS.md`;
6. `emdash2/reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`;
7. `docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md` and its selected active
   elaborator plans;
8. this plan for this side goal's scope, decisions, evidence, and next row;
9. the Došen source for mathematical comparison, not kernel authority.

The local reference copy of Kosta Došen's *Cut Elimination in Categories* is
`/home/user1/dosen-book/kosta-dosen-book-cut-elimination-in-categories.pdf`.
The extracted text is useful for search, but page images and the PDF decide
ambiguous notation.

The retired root category-specific prototype is not mathematical authority.
Its generic implementation techniques may be reused only when they fit the
active v3.2 owner and trust boundaries.

## 3. Current Kernel Boundary

The active kernel declares an indexed relation

```text
J : Adjunction(F,G)
F : R ⊢ L
G : L ⊢ R
```

with stable observations

```text
unit_adj_transf(J)   : id_R => G ∘ F
counit_adj_transf(J) : F ∘ G => id_L.
```

`left_adj_func` and `right_adj_func` are transparent views of the functor
indices. The unit and counit are opaque stable heads because their
`tapp1_fapp0` applications select the two triangle cut-elimination rules.
The kernel deliberately gives an independently named `eta` or `epsilon` no
runtime or proof-time equation with those observations without
declaration-backed agreement.

That last sentence identifies the exact usability seam owned by this plan.
The rectangular macro supplies declaration-backed agreement for one concrete
adjunction instance. It does not change the generic kernel relation or erase
the existing negative boundary for unrelated names.

## 4. Došen Mapping And Terminology

Use Došen's categories `B` and `A` as the kernel's `R` and `L`, respectively.
The exact rectangular mapping is:

| Došen | Active kernel | Reading |
| --- | --- | --- |
| `F : B -> A` | `F : Functor R L` | left adjoint |
| `G : A -> B` | `G : Functor L R` | right adjoint |
| `phi : FG -> I_A` | `counit_adj_transf` | counit, often epsilon |
| `gamma : I_B -> GF` | `unit_adj_transf` | unit, often eta |
| `phi^a(f) : FGA1 -> A2` | `tapp1_fapp0 counit f` | antecedental/off-diagonal counit action |
| `gamma^c(g) : B1 -> GFB2` | `tapp1_fapp0 unit g` | consequential/off-diagonal unit action |

The current two triangle rules are therefore the rectangular `||` `(ac)`
formulation. This is the formulation for which Došen's Cut Disintegration
exactly characterizes adjunction. The alternative `(cc)`, `(aa)`, and `(ca)`
formulations can support a cut-disintegration procedure, but the procedure
then characterizes a more general junction unless the additional rectangular
laws are separately retained.

The alternative `phi^c` and `gamma^a` spellings compose with individual
counit/unit components:

```text
phi^c_A2(f)   = phi_A2 ∘ f
gamma^a_B1(g) = g ∘ gamma_B1.
```

The active `hom_postcomp_fapp0` and identity-specialized
`hom_precomp_along_fapp0` families are plausible carriers, but no exact owner
claim is made until an owner-position probe checks the endpoints, higher
action, and interaction with current stable heads.

### 4.1 Triangular `forward` correction

In Došen's Table 1 and section 4.1.6, triangular `forward` takes `F^a`, `phi`,
and `Gamma` as primitive. `phi` is the counit side, not the unit. The standard
data on p.112 are:

- a full functor `F`;
- only an object function `G^o`;
- an objectual counit `phi_A : F(GA) -> A`; and
- a family
  `Gamma : Hom_A(FB,A) -> Hom_B(B,GA)`.

The arrow action of `G`, the unit `gamma`, and the inverse transpose `Phi`
are derived. In section 4.8.1, the cut-oriented formulation uses the stronger
off-diagonal operation `phi^a`, corresponding to `tapp1_fapp0`, because a
whole transformation cannot yet be typed when only `G^o` exists.

Section 4.8.2 does not use the final `(Gamma phi^a)` law. Cut Disintegration
therefore characterizes a triangular junction strictly more general than a
triangular adjunction. Future kernel naming must preserve the distinction
between `TriangularJunction` and `TriangularAdjunction` if both become
first-class.

## 5. Selected TypeScript Architecture

### 5.1 Host macro, not trusted Core

The macro belongs in a direct-TypeScript outer-command layer:

```text
typed host command / macro
  -> deterministic expansion
  -> ordinary CoreLfTransferDeclaration and CoreLfTransferProofRule values
  -> createCoreLfModuleSpec validation
  -> existing declaration/proof/mixed compilers
  -> optional deterministic Lambdapi conformance emission
```

It must not add an `AdjunctionDeclaration` node to backend-neutral explicit
Core or to `CoreLfModuleSpec`. The trusted checker continues to see only
ordinary declarations and proof rules. No callback or macro object survives
in the explicit IR.

An outer discriminated command union may contain primitive declaration,
inductive, runtime-rule, and proof-rule entries plus an
`adjunction-declaration` macro entry. This is a grammar of TypeScript values,
not a string grammar. Expansion owns source ordinals so a single macro can
atomically occupy one declaration phase followed by two proof-rule entries.

### 5.2 Input contract

The initial API uses named fields rather than positional `epsilon eta` data:

```ts
interface CoreLfAssumeAdjunctionInput {
    readonly name: string;
    readonly sourceCategory: ResolvedGlobal;
    readonly targetCategory: ResolvedGlobal;
    readonly leftAdjoint: ResolvedGlobal;
    readonly rightAdjoint: ResolvedGlobal;
    readonly unit: ResolvedGlobal;
    readonly counit: ResolvedGlobal;
}
```

Every value must be a branded resolved global issued for an already declared
same-module symbol or an explicitly imported symbol. The first slice rejects:

- local/De Bruijn-bound occurrences;
- unresolved or forward names;
- open contextual metavariables;
- foreign builder identities;
- duplicate output names;
- reversed functor directions;
- a unit/counit swap;
- non-transformation operations; and
- endpoint types outside the canonical explicit forms supported by the
  selected owner bindings.

The exact required types are:

```text
F       : Functor R L
G       : Functor L R
eta     : Transf(id_R, G ∘ F)
epsilon : Transf(F ∘ G, id_L).
```

Initial validation may deliberately require structurally canonical explicit
types. Any later conversion-aware relaxation must pass through the existing
checker/runtime comparison and gain its own positive and negative evidence;
the macro must not invent a separate semantic conversion relation.

### 5.3 Trusted declaration semantics

The selected public verb is `assumeAdjunction`. The operation introduces an
LF assumption; it does not synthesize or check triangle proofs supplied by
the user. Merely declaring

```text
myAdj : Adjunction(F,G)
```

already assumes that the indexed functors form an adjunction under the
kernel's classified laws. Tying `eta` and `epsilon` to the canonical
observations asserts that they are this witness's operations.

If a later facade uses `declareAdjunction`, documentation and provenance must
still say `trusted-declaration`. A future proof-requiring constructor would be
a separate API and kernel representation.

### 5.4 Atomic explicit expansion

For an input `myAdj`, expansion produces exactly:

```lambdapi
constant symbol myAdj : tau (@Adjunction R L F G);

unif_rule
  @unit_adj_transf R L F G myAdj
  == eta
  -> [ tt == tt ];

unif_rule
  @counit_adj_transf R L F G myAdj
  == epsilon
  -> [ tt == tt ];
```

The displayed ASCII spellings stand for the actual Lambdapi Unicode syntax.
In explicit transfer IR the witness is one absent-body opaque/constant
declaration and the agreements are two ground proof rules with no matched
variables and one trivial generated constraint each.

Expansion is all-or-nothing. It first validates the complete input, output
name, owner bindings, source order, and expected types against a temporary
immutable state. Failure returns a source-located diagnostic and leaves the
program unchanged.

The expansion result returns a typed handle containing at least:

```text
witness             canonical global myAdj
unit                unit_adj_transf(myAdj)
counit              counit_adj_transf(myAdj)
declaredUnit         original eta
declaredCounit       original epsilon
unitAgreementRuleId
counitAgreementRuleId
```

The handle's `unit` and `counit` are the preferred computational expressions.
The original operations remain agreement endpoints.

### 5.5 Proof-time versus runtime boundary

A bounded launch probe established all of the following:

1. ground `unif_rule`s between a canonical observation and an independently
   named constant are accepted;
2. typed `eq_refl` inhabits both cross-head equality types;
3. `assertnot canonicalObservation == namedOperation` still succeeds as a
   runtime non-conversion; and
4. a raw triangle expression written entirely with the independent names does
   not close merely by chaining the two agreements with the canonical triangle
   rewrite.

This is expected. `unif_rule` is proof-time only and is not reliably
transitive. The stable `unit_adj_transf` and `counit_adj_transf` applications
remain the runtime discriminators for triangle cut elimination.

The macro must not generate global runtime rules from `eta` or `epsilon` to
the canonical observations. Such rules may be impossible for constants, may
erase the stable owner before the outer triangle rule fires, may create
unjoinable reduction orders, and become ambiguous when one named
transformation participates in more than one declared adjunction.

TypeScript usability should instead elaborate `adj.unit` and `adj.counit` to
the canonical observations. Proof-time agreements support direct comparison
with the originally declared names without promising raw-name normalization.

## 6. Triangular Presentation Strategy

### 6.1 First practical presentation: full `F`, full `G`

The first practical triangular adapter assumes both functors already exist and
accepts:

- a whole counit `epsilon : F G => id`; and
- a coherent forward transpose `Gamma`.

In the omega-categorical setting, `Gamma` must not be represented as an
unstructured meta-level function on arrows. The likely carrier is a vertical
`ProfMap`

```text
Hom_L(F -, -) -> Hom_R(-, G -).
```

The active `Adjunction_hom_prof_comparison(J)` already classifies an
isomorphism between exactly these Hom profunctors. Its selected `to` map has
the direction of `Gamma`. The completed owner audit found no active rule that
ties this selected map computationally to the current unit/counit mate
formula, but it also established that such a runtime bridge is not a
prerequisite for a trusted declaration facade. A ground proof-time agreement
can use the existing selected `defiso_to` map directly, provided its ambient
category and endpoint implicits are left for Lambdapi to infer.

No `AdjunctionTriangular R L F G` classifier is added merely to restate an
ordinary adjunction with full functors. The implemented host adapter expands:

```ts
program.assumeAdjunctionFromCounitTranspose({
    name: "myAdj",
    sourceCategory: R,
    targetCategory: L,
    leftAdjoint: F,
    rightAdjoint: G,
    counit: epsilon,
    transpose: gamma
});
```

to the same canonical `Adjunction(F,G)` witness plus declaration-backed
agreements with the canonical counit and selected forward mate. The supplied
`Gamma` is the operation consumers should project and compute with; the
selected map remains the canonical `DefIso` cancellation owner. Their
whole-`ProfMap` agreement is intentionally proof-time only and does not become
congruence closure underneath `tapp0_fapp0`, `fapp0`, or higher projections.

### 6.2 Mate-bridge investigation

Before any active edit, the investigation must identify:

1. the exact point/component projection of `prof_comparison_to` for
   `Adjunction_hom_prof_comparison`;
2. the canonical formula `G(f) ∘ eta_B` and its dual
   `epsilon_A ∘ F(g)` in existing owners;
3. whether a semantic definition, an existing projection rule, a narrow
   proof-time comparison, or a genuinely new stable observation is missing;
4. the higher-action/naturality inherited from `ProfMap`;
5. both reduction orders around the selected stable owner; and
6. a first real consumer, not only an isolated equality.

The audit resolved these points as follows:

1. At `(a,b)`, the selected forward component is a whole functor
   `Hom_L(Fa,b) -> Hom_R(a,Gb)`, not merely a set-level function.
2. Its canonical existing-owner formula is `f |-> G[f] o eta_a`, represented
   by `fapp1_func G` followed by `hom_precomp_along_func` at the unit
   component. The selected inverse is `g |-> epsilon_b o F[g]`, represented
   by `fapp1_func F` followed by `hom_postcomp_func` at the counit component.
3. Both selected components remain opaque at runtime. A proof comparison to a
   rigid whole-fibre head succeeds in both orientations; putting the
   transparent composite formula directly on the rule RHS does not fire.
4. Whole-functor proof agreement is not inherited under `fapp0`; a usable
   point agreement would need its own direct registration. This confirms that
   unification is not congruence closure or reliable transitive rewriting.
5. A runtime component bridge would have to expose both directions and audit
   the critical pair against existing `defiso_from o defiso_to` cancellation.
   A forward-only rule is therefore not promoted without a consumer needing
   canonical point computation.
6. The actual declaration-shaped ground rule succeeds without a new owner:
   `defiso_to (Adjunction_hom_prof_comparison J) == Gamma`. Explicit Core
   retains the ambient category and endpoint arguments with their correct
   plicities; the narrow Lambdapi lowering deliberately emits the equivalent
   non-`@` surface application so those three slots are inferred. Printing
   their exact endpoint syntax in the Lambdapi rule makes matching fail.

The imported probes ran with subject reduction enabled and zero warnings.
Because the decision is to make no active Lambdapi edit, no owner-position
copy, new LHS, warning-family delta, catalog update, or standard-library
extension is justified. If a future consumer requires runtime canonical mate
projection, the full owner-position promotion protocol remains mandatory; an
append-only imported probe is not promotion evidence by itself.

### 6.3 Faithful object-only `G^o` successor

The faithful Došen version is deferred behind a concrete consumer or a
recorded prerequisite resolution. Its likely shape is indexed by `F` and

```text
Go : tau(Obj L) -> tau(Obj R),
```

not by an already available full `G`. It would require distinct observations,
for example:

```text
triangular_right_adj_func
triangular_counit_action       // phi^a, not a whole Transf input
triangular_transpose           // Gamma
```

with a possible object projection

```text
fapp0 triangular_right_adj_func A -> Go A.
```

It must not turn the existing transparent `right_adj_func(J) = G` view into a
primitive globally. The new presentation owns its own derived functor.

The intended derived equations include:

```text
G(f)    = Gamma(phi^a(f))
gamma_B = Gamma(id_(F B)).
```

The section 4.8 laws to distinguish are:

```text
phi^a(f2 ∘ f1) = f2 ∘ phi^a(f1)
phi^a(f2) ∘ F(Gamma(f1)) = f2 ∘ f1
Gamma(f ∘ F(g)) = Gamma(f) ∘ g
Gamma(phi^a(id_A)) = id_(G A).
```

The last law distinguishes triangular adjunction from the more general
junction relevant to Cut Disintegration. A full bridge to canonical
`Adjunction` is required before presenting the classifier as another ordinary
adjunction formulation.

Typing a coherent `ProfMap` target before full `G` exists may require a new
object-indexed Hom-family carrier. The plan does not guess that abstraction in
advance.

## 7. Module Placement

The rectangular macro requires no new Lambdapi kernel module. The generated
witness and ground agreements belong to the consumer's module.

If the triangular presentation acquires stable promoted machinery, prefer a
one-way additive extension named approximately:

```text
emdash3_2_adjunction_presentations.lp
```

This name makes clear that the canonical `Adjunction` remains in
`emdash3_2.lp`. The extension would import the kernel and would be integrated
with the active check script, diagnostics, report index, catalog, health, and
CI only after its dependency boundary is stable. Creating the extension is
not the deferred physical split of the main kernel file.

Disposable owner-position work remains under ignored
`emdash2/tmp/probes/`. Do not promote a module merely because an isolated term
checks.

## 8. Plan Ledger

| Row | Status | Dependency | Deliverable and exit evidence |
| --- | --- | --- | --- |
| ADJ-PLAN-0 | complete | user review, baseline `cea2605` | Dedicated living plan, authority order, Došen mapping, trust/runtime boundary, Git topology, validation matrix, and persistent goal recorded. |
| ADJ-TS-1A | complete | ADJ-PLAN-0 | Added the immutable outer `adjunction-declaration` command, branded resolved-global scope, deterministic three-ordinal atomic expansion, and direct `assumeAdjunction` facade outside trusted Core and parsing. |
| ADJ-TS-1B | complete | ADJ-TS-1A | Exact canonical validation now emits one opaque constant witness, two ground proof rules, and a frozen canonical handle; focused tests cover local/imported data, swaps, reversed directions, wrong endpoints, non-transformations, forward/foreign/open inputs, collisions, malformed provenance, and caller immutability. |
| ADJ-TS-1C | complete | ADJ-TS-1B | A bounded generated Lambdapi consumer proves both agreement orientations, two independent instances, no cross-instance or unrelated-name leakage, runtime non-collapse, canonical triangle reduction, and the raw-name triangle non-claim. |
| ADJ-TS-1D | complete with inherited baseline exception | ADJ-TS-1C | Public barrel/test-runner integration, focused tests, typecheck, lint, generated live conformance, and bounded kernel check pass. One complete `check:ts` ran; its sole 68-vs-79 stale syntax-inventory failure reproduces unchanged at baseline `cea2605` and touches no adjunction file. Decision D-ADJ-012 records why that unrelated defect is carried rather than edited here. |
| ADJ-KERNEL-2A | complete | ADJ-TS-1D | Read-only owner trace and bounded imported probes identify both whole-fibre mate formulas, prove rigid proof-time comparison and runtime non-conversion, expose the transparent-RHS and non-congruence boundaries, and validate the declaration-shaped selected-`ProfMap` rule with SR on and zero warnings. |
| ADJ-KERNEL-2B | complete: no promotion | ADJ-KERNEL-2A | No kernel or extension edit is justified for trusted declaration usability. The existing selected `defiso_to` map is an adequate canonical proof endpoint; runtime component exposure is deferred behind a consumer and would require both directions plus an owner-position confluence audit. |
| ADJ-TS-2C | complete with inherited baseline exception | ADJ-KERNEL-2B resolved | `assumeAdjunctionFromCounitTranspose` is implemented with optional profunctor owner bindings, exact coherent-`ProfMap` validation, ordinary witness/counit/transpose proof-rule expansion, deterministic inferred-implicit emission, structural tests, and a green live Lambdapi consumer. The final aggregate passed workspace/type/lint and every affected test; its sole failure is the unchanged baseline 68-vs-79 audit recorded by D-ADJ-018. |
| ADJ-RESEARCH-3 | deferred | concrete object-only consumer and carrier decision | Faithful `G^o`, `phi^a`, `Gamma` junction/adjunction classifier, derived functor/unit, bridge to `Adjunction`, and complete kernel interaction audit. |
| ADJ-FINAL-4 | complete | all scoped nondeferred rows | Exact unstaged/untracked diff, clean staged state, baseline ancestry, all worktrees, routing links, and generated-temp cleanup reviewed. Focused/live/type/lint/kernel gates pass; the complete aggregate has only D-ADJ-018's inherited failure. Plan and report routing are synchronized for an uncommitted user handoff. |

Only one row may be implementation-active at a time. Failed hypotheses update
this table and the decision ledger; they are not silently bypassed.

## 9. Decision Ledger

| Decision | Status | Rationale and consequence |
| --- | --- | --- |
| D-ADJ-001 | accepted | The first deliverable is rectangular declaration usability. Triangular semantics do not block it. |
| D-ADJ-002 | accepted | Outer adjunction declaration is a TypeScript host macro expanded before explicit Core; no string grammar and no trusted `CoreLfModuleSpec` macro node. |
| D-ADJ-003 | accepted | Use named fields and the verb `assumeAdjunction` to expose trusted-declaration semantics and prevent positional unit/counit confusion. |
| D-ADJ-004 | accepted | Inputs are already resolved global declarations/imports; bound variables, forward names, open metas, and arbitrary untyped expressions fail closed. |
| D-ADJ-005 | accepted | Expansion emits one canonical witness declaration plus two ground proof-time agreements with trivial generated constraints. It emits no runtime alias rule. |
| D-ADJ-006 | accepted | Canonical `adj.unit`/`adj.counit` observations own computation. Original names are agreement endpoints and raw-name triangle normalization is a non-claim. |
| D-ADJ-007 | accepted | The first practical triangular carrier assumes full `F` and `G`; coherent `Gamma` is likely a `ProfMap`, not a raw function. |
| D-ADJ-008 | accepted | Audit the existing Hom-profunctor comparison and its mate coherence before adding any full-functor triangular classifier. |
| D-ADJ-009 | accepted | Preserve Došen's distinction between triangular junction and triangular adjunction. The object-only `G^o` version is consumer-gated. |
| D-ADJ-010 | accepted | A promoted optional presentation belongs in a one-way `adjunction_presentations` extension; the existing canonical Adjunction stays in the kernel. |
| D-ADJ-011 | active Git boundary | Work occurs only in the dedicated branch/worktree. No local commit, push, merge, rewrite, publication, or cleanup without additional authorization. |
| D-ADJ-012 | accepted validation exception | The complete branch `check:ts` passed workspace validation, typecheck, and lint, then reported 1,225 passes, 52 intentional skips, and one failure: the untouched syntax-graduation audit expects 68 methods while the current parity inventory contains 79. The same focused failure reproduces in the clean `cea2605` baseline worktree, and this branch has no diff in either owning categorical file. Do not broaden this goal to repair that independent stale inventory; carry the exact failure until its owner synchronizes it. |
| D-ADJ-013 | accepted | The full-functor counit/transpose facade reuses the existing `Adjunction` and `Adjunction_hom_prof_comparison`; it adds no parallel classifier, kernel rule, or standard-library module. |
| D-ADJ-014 | accepted | Explicit Core records all four `defiso_to` arguments. The deterministic Lambdapi lowering elides its three implicit ambient/endpoints and spells only the explicit comparison argument; that inference is a required backend matching detail covered by exact structural and live-conformance tests. |
| D-ADJ-015 | accepted boundary | Whole-`ProfMap` proof agreement is neither runtime conversion nor congruence closure. Consumers compute with the supplied `Gamma`; the canonical selected map remains available for `DefIso` cancellation and whole-map comparison. |
| D-ADJ-016 | deferred promotion | Direct transparent-formula RHS comparisons do not fire, while rigid forward and inverse fibre heads do. Do not add point/higher projection registrations or runtime mate rules until a consumer requires canonical projection computation and justifies the full two-direction owner-position audit. |
| D-ADJ-017 | accepted trust semantics | `assumeAdjunctionFromCounitTranspose` validates the shapes of a full counit and coherent `ProfMap`, then assumes the ordinary adjunction witness. It is not a checker for Došen's triangular laws and must not be described as constructing an adjunction from proofs. |
| D-ADJ-018 | accepted final aggregate exception | The post-ADJ-TS-2C `check:ts` passed workspace validation, typecheck, and lint, then completed 1,283 tests in about 32.6 minutes: 1,230 passed, 52 intentionally skipped, and only the untouched categorical-text graduation audit failed with the same `79 !== 68` baseline defect. No adjunction test failed, and the failure path/values are identical to D-ADJ-012's clean-baseline reproduction. |
| D-ADJ-019 | completed handoff | The dedicated worktree remains at baseline HEAD with only the reviewed unstaged/untracked task diff and an empty index. No commit, push, merge, kernel source, generated PDF render, or other worktree was changed. |

## 10. Focused Acceptance Corpus

The rectangular slice is incomplete until the durable tests cover:

### Positive

1. exact deterministic expansion to one witness and two proof rules;
2. correct canonical types for `F`, `G`, `eta`, and `epsilon`;
3. same-module earlier declarations and dependency-module imports;
4. immutable returned module and handle;
5. direct proof-time agreement in both comparison orientations;
6. two independent adjunction instances without leakage;
7. deterministic backend names, IDs, source orders, and provenance; and
8. Lambdapi acceptance of the generated consumer.

### Negative and non-collapse

1. duplicate witness name;
2. unbound, bound, forward, or foreign global handle;
3. reversed `F` or `G` direction;
4. swapped unit/counit;
5. wrong transformation endpoints;
6. non-transformation input;
7. missing/foreign owner binding;
8. caller-owned input not frozen or mutated by validation;
9. `unit_adj_transf(J)` and `eta` remain non-convertible at runtime;
10. same for the counit;
11. an unrelated transformation does not gain agreement;
12. one instance's operation does not unify with another instance's
    observation; and
13. raw independently named triangle reduction remains an explicit non-claim.

No test may pass by relying on the obsolete category-specific TypeScript
prototype.

### Full-functor counit/transpose facade

The optional second facade additionally requires:

1. exact validation of
   `Gamma : ProfMap(Hom_L(F-,-), Hom_R(-,G-))`;
2. rejection of malformed transpose types and absent profunctor owner
   bindings;
3. deterministic expansion to the same ordinary witness, one counit rule,
   and one selected-mate rule;
4. emitted `defiso_to` endpoint inference accepted by live Lambdapi;
5. proof-time agreement in both orientations;
6. runtime non-conversion and unrelated-transpose non-leakage;
7. preservation of canonical `DefIso` cancellation; and
8. an explicit negative showing that the provided transpose is not installed
   as a runtime cancellation alias.

## 11. Validation Matrix

### Documentation/plan edits

```bash
git diff --check
git diff -- docs/ADJUNCTION_USABILITY_V3_2_PLAN.md \
  docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md \
  emdash2/reports/INDEX.md
```

### ADJ-TS inner loop

```bash
node --require ts-node/register --test \
  tests/v3_2_lf_adjunction_macro_tests.ts
./scripts/pnpmw run typecheck
./scripts/pnpmw run lint
```

Run the nearest generic declaration/proof/mixed suites when their shared
interfaces are touched. Because the new public barrel and shared outer-LF
behavior are in scope, run one complete:

```bash
./scripts/pnpmw run check:ts
```

after the bounded adjunction-macro tranche is otherwise green. The final
post-ADJ-TS-2C run is recorded by D-ADJ-018; its only failure is the expected
unrelated baseline exception from D-ADJ-012.

The target depends on current kernel names and proof-time behavior, so also
run:

```bash
EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
```

The Lambdapi conformance test must remain bounded to 60 seconds and may use a
temporary generated consumer. It must preserve raw diagnostics and delete its
owned temporary directory through the existing probe workflow.

### Kernel investigation/promotion

For ADJ-KERNEL-2A/2B follow `emdash2/AGENTS.md` completely:

```bash
EMDASH_PROBE_TIMEOUT=60s emdash2/scripts/probe.sh tmp/probes/NAME.lp
EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
make -C emdash2 check-warnings
make -C emdash2 audit-rules
make -C emdash2 catalog
make -C emdash2 health
make -C emdash2 examples       # when reviewer behavior changes
make -C emdash2 ci             # before substantial handoff
```

Compare warning families rather than treating counts alone as a veto. Never
disable subject reduction.

Run `check:all` only at an actual affected cross-layer integration/release
boundary, not for documentation or an isolated TypeScript inner loop.

## 12. Launch Baseline

At `cea2605` in the dedicated worktree:

```text
./scripts/bootstrap-worktree.sh
  passed; workspace contract pnpm@11.16.0, Node 24.11.1

./scripts/pnpmw run typecheck
  passed

./scripts/pnpmw run lint
  passed

node --require ts-node/register --test
  tests/v3_2_lf_transfer_tests.ts
  tests/v3_2_lf_transfer_compiler_tests.ts
  tests/v3_2_lf_transfer_proof_tests.ts
  tests/v3_2_lf_transfer_mixed_tests.ts
  passed

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  passed the active kernel, four extensions, and diagnostics
```

The original root, the existing `goal/typescript-elaborator-v3.2` worktree,
and both detached orientation worktrees were clean at launch. `main` and
`origin/main` both named the baseline. No dependency tree is shared across
worktrees.

### 12.1 Rectangular implementation record

The first implementation tranche adds:

- `src/v3_2/lf_adjunction_macro.ts`, containing the backend-neutral outer
  command, resolved-global scope, direct `assumeAdjunction` facade, canonical
  structural type validation, atomic ordinary-LF expansion, frozen handle,
  and a deliberately narrow deterministic Lambdapi fragment emitter;
- the public root-only export in `src/v3_2/index.ts`;
- `tests/v3_2_lf_adjunction_macro_tests.ts`, wired into
  `tests/main_tests.ts`; and
- no parser node, trusted-Core node, runtime rewrite, browser export, or
  Lambdapi source change.

The final focused and live evidence on 2026-07-31 is:

```text
node --require ts-node/register --test \
  tests/v3_2_lf_adjunction_macro_tests.ts
  10 passed; 1 opt-in live probe skipped; 0 failed

timeout 60s env EMDASH_RUN_LAMBDAPI_ADJUNCTION_PROBES=1 \
  node --require ts-node/register --test \
  tests/v3_2_lf_adjunction_macro_tests.ts
  11 passed; 0 skipped; 0 failed
  generated Lambdapi consumer: accepted in about 5.5 seconds

./scripts/pnpmw run typecheck
  passed

./scripts/pnpmw run lint
  passed

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  passed the active kernel, four extensions, and diagnostics

git diff --check
  passed
```

The complete `./scripts/pnpmw run check:ts` was allowed to finish. Workspace
validation, typecheck, and lint passed. Its test phase completed all 1,278
tests in about 38.5 minutes with 1,225 passes, 52 intentional skips, and the
single inherited failure recorded by D-ADJ-012. The exact focused failure was
then rerun in clean `/home/user1/emdash1` at `cea2605` and reproduced as
`79 !== 68`. The branch diff changes only the v3.2 public barrel among source
files that test imports; it does not change `categorical_program.ts`, the
parity inventory, or the failing graduation audit.

The generated consumer establishes the intentionally asymmetric contract:

1. canonical observation versus declared operation works in both proof-time
   comparison orientations;
2. neither agreement becomes runtime conversion;
3. a second adjunction's operation and an unrelated same-typed operation do
   not satisfy the first witness's proof-time comparison;
4. canonical unit/counit observations still select the left triangle runtime
   rule; and
5. spelling that triangle with the independently declared names remains a
   checked non-conversion.

### 12.2 Full-functor mate audit and adapter record

The read-only owner trace established that `ProfMap P Q` is the existing
vertical hom in `Prof_cat`, while
`Adjunction_hom_prof_comparison(J)` is the existing rigid
`DefIso` certificate between the two representable Hom profunctors. Its
selected `defiso_to` and `defiso_from` maps therefore already carry coherent
Cat-valued naturality and higher action.

Bounded ignored probes record the exact component formulas and boundaries:

```text
tmp/probes/adjunction_mate_forward_bridge.lp
  selected forward component has type
    Functor(Hom_L(Fa,b), Hom_R(a,Gb))
  formula is f |-> G[f] o eta_a
  runtime selected/formula conversion: rejected as intended
  direct proof rule to transparent formula: does not fire
  proof rule to a rigid whole-fibre head: accepted in both orientations
  whole-functor agreement under fapp0: not inherited
  direct point agreement to a rigid point head: accepted
  final successful log:
    logs/probes/adjunction_mate_forward_bridge-20260801-002459.log

tmp/probes/adjunction_mate_inverse_bridge.lp
  selected inverse component has type
    Functor(Hom_R(a,Gb), Hom_L(Fa,b))
  formula is g |-> epsilon_b o F[g]
  rigid proof comparison accepted; runtime conversion remains absent
  successful log:
    logs/probes/adjunction_mate_inverse_bridge-20260801-003943.log

tmp/probes/adjunction_counit_transpose_declaration.lp
  ground counit agreement accepted
  ground whole-ProfMap selected-mate agreement accepted in both orientations
  runtime conversion remains absent
  exact matching requires inferred defiso_to category/endpoint implicits
  successful log:
    logs/probes/adjunction_counit_transpose_declaration-20260801-002904.log
```

All successful probe runs used the normal probe wrapper with subject reduction
enabled and reported zero warnings. No tracked Lambdapi source, LHS, extension,
catalog, or health artifact changed.

The resulting TypeScript addition extends the same outer macro scope with an
optional profunctor-owner capability and:

```ts
scope.assumeAdjunctionFromCounitTranspose({
    name,
    sourceCategory,
    targetCategory,
    leftAdjoint,
    rightAdjoint,
    counit,
    transpose,
    order,
    provenance
});
```

It validates the transpose as the exact coherent `ProfMap`, emits one ordinary
`Adjunction` assumption plus counit and selected-mate ground proof rules, and
returns both canonical and originally declared handles. The generated live
consumer covers both proof orientations, runtime non-conversion,
unrelated-name non-leakage, canonical `DefIso` cancellation, and the negative
that the supplied name is not a runtime cancellation alias.

Current focused evidence is:

```text
node --require ts-node/register --test \
  tests/v3_2_lf_adjunction_macro_tests.ts
  12 passed; 1 opt-in live probe skipped; 0 failed

timeout 60s env EMDASH_RUN_LAMBDAPI_ADJUNCTION_PROBES=1 \
  node --require ts-node/register --test \
  tests/v3_2_lf_adjunction_macro_tests.ts
  13 passed; 0 skipped; 0 failed
  generated combined consumer: accepted in about 5.6 seconds

./scripts/pnpmw run typecheck
  passed

./scripts/pnpmw run lint
  passed

./scripts/pnpmw run check:ts
  workspace validation, typecheck, and lint passed
  node:test completed 1,283 tests in about 32.6 minutes
  1,230 passed; 52 intentionally skipped; 1 failed
  sole failure: unchanged baseline audit, 79 !== 68 (D-ADJ-018)

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  passed the active kernel, four extensions, and diagnostics
```

## 13. Start/Resume Protocol

On every persistent-goal continuation:

1. read root and nested `AGENTS.md`;
2. read this plan's current ledger and decisions;
3. inspect every worktree, this branch/HEAD, and baseline ancestry;
4. inspect unstaged, staged, and untracked state separately;
5. resolve any relevant archived decision response only after active sources;
6. relocate owners and consumers with `rg`;
7. run the smallest baseline for the active row;
8. continue only the one `in progress` row;
9. record accepted, refined, rejected, or deferred evidence here; and
10. do not commit or perform any broader Git mutation without authorization.

No dependency-ready scoped implementation row remains. The uncommitted result
is ready for user review in the dedicated worktree. A future continuation may
start only from a new authorized row, such as a concrete consumer for runtime
canonical mate projection or the faithful object-only `G^o` presentation;
neither is implied by this completed goal.
