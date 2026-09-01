# TypeScript/emdash Computational Freyd Direct Sums and Additive Categories Plan

Date: 2026-09-01

Plan-ID: `TS-EMDASH-FREYD-ADDITIVE-BIPRODUCTS`

Status: complete on a dedicated branch/worktree; integration not performed

Baseline: `c3bb8691e76d47bebca1aa58d28cd1126335fc26`

Branch: `goal/freyd-additive-biproducts-v3.2`

Worktree: `/home/user1/emdash1-freyd-additive-biproducts-v1`

Decision-Response-Evidence:

- `infinity-codex:01a02f68-6142-7e53-993a-4505aa8e2cbe:01a05d21-c6d3-7853-9400-668717238bc1`

## Purpose

This plan is the immediate structural continuation from full Freyd
preadditivity. It builds computational finite direct sums and the zero
presentation, reuses the existing Došen-style product and terminal-object
calculus, and culminates in the first formal additive-category instance:

```text
comm_ring_freyd_additive
  : AdditiveCategory(
      CommRingFreydPresentation_cat(R),
      comm_ring_freyd_direct_sum_func(R),
      comm_ring_zero_presentation(R)).
```

The intended vertical slice is:

```text
finite-family concatenation/splitting
  -> vector and matrix blocks
  -> finite-free direct sums
  -> presentation direct sums and zero
  -> quotient-Hom projections and pairing
  -> selected Cartesian Freyd structure
  -> generic preadditive-plus-cartesian additive bridge
  -> formal Freyd AdditiveCategory
  -> concrete TypeScript additive-doctrine qualification.
```

This is the first direct-sum consumer needed by the longer proof-assistant/CAS
architecture. Matrix algorithms remain the computational backend; generic
category structure remains the internal semantic surface.

## Operational Baseline And Git Boundary

The branch starts directly from completed set-extensionality/preadditivity
checkpoint `c3bb869`. Historical `main` remains at `85f459a`; this goal does
not mutate or first fast-forward it. The orthogonal path-cubical and global-
strictness worktrees remain excluded.

The user explicitly authorized this dedicated branch/worktree, persistent
goal, and continuation under the established local validated-checkpoint
workflow. Local commits are permitted only after a bounded tranche is green,
this ledger is synchronized, and the exact staged diff excludes unrelated
work. This does not authorize push, merge, publication, release, PR creation,
amend, rebase, reset, history rewriting, branch deletion, or worktree removal.

Initial state is clean and the baseline is an ancestor of `HEAD`. The fresh
worktree was bootstrapped with the pinned workspace dependency graph.

Focused baseline checks are green for:

- `emdash3_2_commutative_algebra_finite_modules.lp`;
- `emdash3_2_commutative_algebra_freyd_preadditive.lp`;
- `emdash3_2_cartesian_categories.lp`; and
- the clean branch/ancestry boundary.

No repository-wide aggregate is part of the initial baseline.

### Initial owner-audit result

The active product and terminal classifiers have no exposed constructors and
there are no existing concrete `BinaryProducts` or `TerminalObject` instances
to reuse. A Freyd instance will therefore require narrow stable whole
assembly, with its point projections, pairing, zero arrows, and contractions
connected to constructed semantic operations. This does not alter the central
architecture: the coproduct half remains derived from product computation and
preadditivity.

The generic additive derivation is feasible with the current interfaces. Its
first missing reusable lemmas are abelian cancellation/idempotent-zero and
preadditive zero-composition paths. Those belong in the later generic additive
module and require no new runtime rule.

## Central Architecture: Products Become Biproducts

Do not implement a parallel primitive coproduct calculus. The active kernel
already has:

- `PreadditiveCategory(C)`, with set-valued abelian Homs and bilinear generic
  composition;
- `BinaryProducts(C,P)`, with one whole product functor, whole projection
  transfors, whole pairing, and Došen-style triangular computation;
- `TerminalObject(C,t)`, with one whole canonical-arrow transfor and Hom
  contractibility; and
- `CartesianCategory(C,P,t)`, the thin package of the previous two structures.

The selected generic theorem is therefore:

```text
PreadditiveCategory(C)
  + CartesianCategory(C,P,t)
  --------------------------------
  AdditiveCategory(C,P,t).
```

In a preadditive category, terminality implies initiality. If `t` is terminal,
its identity and zero endomorphism agree by uniqueness. For every
`f : t -> X`,

```text
f = f o id_t = f o 0 = 0,
```

where composition with zero is derived from bilinearity and additive
cancellation. Thus `t` is a zero object.

Similarly, a selected product `P(A,B)` is automatically a biproduct. Define:

```text
iota_1 := <id_A,0_(A,B)> : A -> P(A,B)
iota_2 := <0_(B,A),id_B> : B -> P(A,B)

[f,g] := f o pi_1 + g o pi_2 : P(A,B) -> X.
```

Product beta/eta, preadditive bilinearity, and the derived zero-composition
paths prove the coproduct beta/eta and the matrix identity

```text
iota_1 o pi_1 + iota_2 o pi_2 = id_(P(A,B)).
```

The new generic additive module must expose those constructions and paths.
Merely pairing two evidence records without deriving the missing initial and
coproduct observations is not sufficient for an `AdditiveCategory` claim.

## Finite-Family Concatenation And Splitting

The existing representation is

```text
FiniteFamily(A,0)     = Unit
FiniteFamily(A,n+1)   = A × FiniteFamily(A,n),
```

while `nat_add(m,n)` recurses on `m`. These choices align directly with
left-family recursion:

```text
append(nil,ys)        = ys
append(cons(x,xs),ys) = cons(x,append(xs,ys)).
```

Add the smallest reusable operations required by block matrices:

- `finite_family_append`;
- `finite_family_take_left`;
- `finite_family_drop_left`; and
- reconstruction/extensionality paths showing that splitting and appending
  agree.

Prefer transparent Nat-recursive functions and theorem-level paths. Add a
runtime rule only when it is a constructor-visible beta owned by the recursive
operation. Do not install broad arithmetic or Sigma-projection rewrites.

Required boundaries include zero-left, zero-right, successor, rank-one, and
nontrivial mixed lengths. Distinct families must not collapse.

### Implemented finite-family result

`emdash3_2_finite_family_sums.lp` now provides transparent
`finite_family_append`, `finite_family_take_left`, and
`finite_family_drop_left`. Nat-inductive theorem paths prove both
split-after-append equations, append-after-split reconstruction, and
right-empty append. Constructor computations are inherited from the existing
`nat_elim`/`FiniteFamily` owners; the module adds no rewrite or unification
rule. Its focused implementation/reviewer checks pass, the strict LHS audit is
empty, and the reviewer retains a noncollapse boundary. The warning-enabled
predecessor and candidate each report 1,274 diagnostics.

## Vector And Matrix Block Calculus

Use concatenation to construct actual flattened vectors and matrices, not a
parallel record of four unrelated blocks.

Required vector operations:

```text
u ++ v                 : R^(m+n)
inl(u) = u ++ 0        : R^m -> R^(m+n)
inr(v) = 0 ++ v        : R^n -> R^(m+n)
pr1, pr2                : split projections.
```

Required matrix operations should include the smallest general block owner
from which the special cases derive:

```text
[ A B ]
[ C D ]

block_diag(A,D)
horizontal(A,B)
vertical(A,C)
matrix_inl, matrix_inr
matrix_proj1, matrix_proj2.
```

The column-oriented convention remains authoritative: an `m × n` matrix is an
arrow `n -> m`.

Construct theorem-level paths for:

- block application to concatenated vectors;
- projection/inclusion beta equations;
- diagonal identity and composition;
- horizontal/vertical composition;
- zero off-diagonal blocks; and
- the biproduct matrix identity.

Reuse existing matrix additive, subtractive, identity, composition, and
extensional paths. Do not add global block normalization rules merely to make
these equations reflexive.

### Implemented block-matrix result

`emdash3_2_commutative_algebra_matrix_blocks.lp` now constructs actual
flattened vector concatenation/splitting, horizontal and vertical matrices,
the general four-block matrix, block diagonals, and canonical inclusions and
projections. The four-block owner is oriented as a vertical pair of horizontal
rows, matching the product/projection consumer.

`emdash3_2_commutative_algebra_matrix_block_laws.lp` constructs, without rules
or unifiers:

- append congruence and preservation of zero, addition, and scalar action;
- horizontal and vertical matrix-application formulas;
- identity-matrix action on arbitrary vectors;
- both projection/vector beta laws;
- projection after vertical pairing for arbitrary column counts;
- vertical projection eta for arbitrary matrices;
- horizontal/vertical composition laws; and
- block-diagonal composition.

The focused implementation and reviewer checks pass, strict LHS audits are
empty, and the predecessor/candidate warning counts are both 1,274. Distinct
canonical inclusions remain nonconvertible.

## Finite-Free Direct Sums

For `CommRingFiniteFree_cat(R)`, choose:

```text
m ⊕ n := nat_add(m,n).
```

The whole direct-sum action on a pair of matrices is block diagonal. Generic
category identity/composition remain their existing runtime owners. Any rigid
direct-sum action head must compare with transparent block computation through
constructed paths or narrowly typed proof-time usability rules; do not repeat
the rejected generic-composition-to-transparent-matrix rewrite.

This layer provides the matrix evidence consumed by presentation sums. It need
not independently package the final Freyd `BinaryProducts` instance if doing
so would duplicate the presentation-level consumer.

### Implemented finite-free result

`emdash3_2_commutative_algebra_finite_free_direct_sums.lp` now provides one
whole functor from the product of two finite-free matrix categories to the
same category. Its object action is `nat_add`; its first-arrow action computes
to the flattened block diagonal; and its first Hom action remains available as
a whole functor. The direct transparent action passed owner-position probing,
so no rigid intermediary or proof-time unifier was required. Constructed
diagonal identity/composition paths give the semantic functor-law joins.

The focused implementation/reviewer checks and strict LHS audit pass. After
replacing the unused ring argument in the object-rule LHS by `_`, the warning
count remains 1,274, equal to the predecessor boundary.

## Presentation Direct Sums And Zero

For presentations

```text
P = [R_P : R^rP -> R^gP]
Q = [R_Q : R^rQ -> R^gQ],
```

define:

```text
P ⊕ Q
  := [block_diag(R_P,R_Q)
        : R^(rP+rQ) -> R^(gP+gQ)].
```

The selected zero presentation is:

```text
0_R := [0 : R^0 -> R^0].
```

Raw presentation direct sums retain both matrices:

```text
(F,W) ⊕ (G,V) := (block_diag(F,G), block_diag(W,V)).
```

Its stored relation square must be constructed from block-composition and the
two input squares. Projection and pairing raw morphisms likewise retain their
generator and relation matrices; no manual square field is accepted.

Prove at the raw level:

- projection/pairing beta;
- product eta;
- identity/zero at `0_R`;
- direct-sum identity and composition; and
- compatibility with target-factorization agreement.

### Implemented raw-presentation result

`emdash3_2_commutative_algebra_presentation_direct_sums.lp` now defines the
zero presentation and block-diagonal binary presentation sum. Raw direct-sum
morphisms, both projections, and pairing retain generator and relation
matrices. Their relation laws are constructed respectively from block-diagonal
composition/congruence, block projection squares, and componentwise diagonal
action on vertical pairing. No manual square, rewrite, unifier, or opaque
equality witness is introduced.

Focused implementation/reviewer checks and strict LHS audits pass. The target
remains at 1,274 warning diagnostics. Agreement-category action and quotient
descent are separated into the next ledger row rather than hidden inside this
constructor checkpoint.

## Quotient Descent And Whole Direct-Sum Structure

Descend projection, pairing, block-diagonal action, and zero through the
existing agreement-groupoidification and `0`-truncation architecture.

Use the completed set-target groupoidification and truncation path-induction
helpers to promote class equations to arbitrary quotient points. Do not add a
general dependent eliminator or representative-selection operation.

### Implemented agreement result

`emdash3_2_commutative_algebra_presentation_direct_sum_agreements.lp` now
combines target-factorization witnesses by block diagonal for direct-sum maps
and by vertical pairing for maps into a presentation sum. The laws use
block-diagonal/vertical composition followed by the input agreement paths and
the new subtraction compatibility. The module is rule-free, passes its
focused reviewer and strict LHS audit, and leaves the warning inventory at
1,274.

### Implemented quotient-descent result

`emdash3_2_commutative_algebra_freyd_direct_sums.lp` now descends raw pairing
through the existing agreement groupoidification and set truncation. It
provides quotient projection classes, arbitrary quotient-Hom pairing, the
derived arrow operation

```text
f ⊕ g := <f o pi_1,g o pi_2>,
```

and one whole direct-sum functor on the formal Freyd category. Its object
action computes to presentation direct sum, its first-arrow action computes to
the quotient operation above, and its first Hom action remains available as a
whole functor.

The two nested groupoidification extensions retain the functorial action used
to prove representative independence. The inner action meets its constructed
paired agreement through a rigid point head and a narrow proof-time unifier.
A direct runtime rule from the outer generic `fapp1_fapp0` observation to its
large transparent function-path body repeatedly exceeded the 90-second bound.
The selected outer design therefore also uses a rigid action head and
proof-time comparison, followed by a runtime fold from that rigid head to the
fully constructed semantic path. This is an owner-placement correction, not
an opaque witness or a loss of action. The public whole direct-sum functor's
ordinary arrow action remains a direct runtime rule and checks comfortably
inside the bound.

The focused source/reviewer checks pass; the strict LHS audit reports zero
unreviewed slots; and predecessor and candidate warning-enabled checks both
report `1,300 = 1,143 + 157` diagnostics, with no warning owned by the new
module.

### Implemented selected-binary-products result

`emdash3_2_commutative_algebra_freyd_binary_products.lp` selects the existing
whole Freyd direct-sum functor as a `BinaryProducts` structure. It does not
restate the triangular theory. The generic whole projection transfors,
pairing transfor, pairing functors, `K_i^a` operations, beta/eta rules,
naturality, distribution, and comparison with whole product-functor action
remain the runtime and higher-action owners.

The concrete instance connects the two selected point projections and point
pairing to the constructed quotient operations. Direct runtime rules on the
generic `binary_products_*_fapp0` heads repeatedly exceeded the 90-second
bound because they enlarged already-hot generic triangular decision trees.
The promoted design instead uses one rigid Freyd head per observation, a
narrow proof-time unifier from the selected generic observation to that head,
and a typed `eq_refl` path declared before the rigid head folds at runtime to
the quotient projection or pairing. Thus the generic heads survive for
Došen-style normalization, while their concrete Freyd meaning is explicit,
non-opaque, and propositionally available.

The source and reviewer pass bounded quiet checking. The reviewer instantiates
generic product beta and eta, retains the whole pairing functor, checks the
three concrete comparison routes, and keeps projection distinct from zero.
The strict LHS audit is empty. The warning-enabled import-union baseline and
candidate both report `1,382 = 1,215 + 167`; the selected instance adds no
warning family.

### Implemented terminal-zero and Cartesian result

`emdash3_2_commutative_algebra_freyd_terminal_zero.lp` proves that the zero
presentation is terminal. The proof begins with an internal theorem that every
zero-row matrix is the selected zero matrix. It turns a raw map into the zero
presentation into a constructed presentation agreement with the zero map,
then uses the existing groupoidification set-extensionality and set-truncation
path induction to prove every quotient-Hom point equal to zero. This gives
`IsContr(Hom(P,0))` with centre the selected zero arrow; no representative
choice or manually stored square occurs.

The primitive `TerminalObject` witness retains its whole canonical-arrow
transfor and generic terminal cut. Its stable point arrow uses the same
proof-time rigid-head pattern as selected products and then folds to the
quotient zero class. The semantic contractibility observation reduces directly
to the constructed evidence. The terminal source/reviewer and strict LHS audit
pass. Its import-union baseline and candidate are exactly equal at
`1,394 = 1,225 + 169` warnings.

`emdash3_2_commutative_algebra_freyd_cartesian.lp` then transparently pairs the
selected binary-products and terminal-zero witnesses as one
`CartesianCategory`. Its evidence projections compute to those two witnesses;
it adds no rule, unifier, or parallel product/terminal operation.

### Implemented generic and formal additive result

`emdash3_2_additive_categories.lp` defines `AdditiveCategory(C,P,t)` as
exactly the product of the existing `PreadditiveCategory(C)` and selected
`CartesianCategory(C,P,t)` evidence. Its rule-free theorem layer derives:

- left zero and inverse laws from the selected abelian-group basis;
- both composition-with-zero laws from bilinearity and additive-idempotent
  cancellation;
- equality of identity and zero at a terminal object, hence contractibility of
  every outgoing Hom and the initial half of the zero object;
- the two injections `<id,0>` and `<0,id>`;
- copairing `f o pi_1 + g o pi_2`;
- both copair beta laws;
- the diagonal identity `iota_1 o pi_1 + iota_2 o pi_2 = id`; and
- copair eta.

All constructions use the existing product, terminal, Hom-addition, and
ordinary composition owners. No initial-object/coproduct classifier, runtime
rule, unifier, or parallel category syntax is added.

`emdash3_2_commutative_algebra_freyd_additive.lp` transparently combines the
checked Freyd preadditive and Cartesian witnesses. The generic initiality,
copair beta/eta, and biproduct identity specialize directly to the formal
Freyd quotient Homs. Focused generic and Freyd reviewers pass; both modules
are rule-free and have empty strict LHS audits. Their inherited warning
inventories are respectively `1,358 = 1,189 + 169` and
`1,392 = 1,223 + 169`, with no module-owned warning.

The selected whole functor is approximately:

```text
comm_ring_freyd_direct_sum_func(R)
  : Freyd_R × Freyd_R -> Freyd_R.
```

It must retain ordinary Hom and higher action. Its object observation computes
to presentation direct sum. The Došen-derived map action supplied by
`BinaryProducts` should remain primary at the generic product surface; a
concrete block-diagonal comparison belongs at a stable semantic owner.

The selected witness is approximately:

```text
comm_ring_freyd_binary_products(R)
  : BinaryProducts(
      Freyd_R,
      comm_ring_freyd_direct_sum_func(R)).
```

Because `BinaryProducts` and `Transf` are primitive classifiers, the first
owner audit must determine the minimal stable instance/whole-operation
assembly. Concrete point projections and pairing must connect to the checked
matrix classes. Do not introduce unrelated opaque equality bridges.

## Zero Presentation And Terminality

The preferred generic route is:

1. prove `id_(0_R) = 0_(0_R,0_R)` from the zero-rank matrix computation;
2. derive composition with zero from the generic preadditive laws;
3. derive contractibility of every `Hom(P,0_R)`; and
4. assemble the selected terminal whole arrow from zero morphisms.

Since `TerminalObject` and `Transf` are primitive classifiers, a narrow stable
whole zero-arrow assembly may be required. If so, its components must compute
to the existing preadditive zero maps and its contractions must be the derived
ones. It is not permission to postulate terminality without exposing the
computational zero-map semantics.

The resulting evidence is approximately:

```text
comm_ring_freyd_terminal_zero(R)
  : TerminalObject(Freyd_R,0_R)

comm_ring_freyd_cartesian(R)
  : CartesianCategory(Freyd_R,oplus_R,0_R).
```

Preadditivity will then derive the initial half; a separate primitive initial-
object or coproduct theory is not selected.

## Generic Additive Category Package

Introduce an internal `AdditiveCategory` package indexed by the already-
selected product functor and terminal object. It should retain:

- the existing `PreadditiveCategory`;
- the existing `CartesianCategory`;
- derived initial/zero-object contractibility;
- derived injections and copairing;
- coproduct beta and eta;
- the biproduct matrix identity; and
- readable projections for later weak-kernel consumers.

The package adds no parallel category grammar and no duplicate generic
identity/composition rule. The Freyd instance should be a transparent package
of checked components once its stable product/terminal owners are selected.

## TypeScript Operational Doctrine Promotion

The direct polynomial Freyd model already computes representative identity,
composition, zero, addition, and negation, but its category-operation registry
currently exposes only primitive morphism construction. This goal supplies the
first concrete consumer for the deferred operational bridge.

Add direct zero-presentation and direct-sum operations, then register category
operations for:

- `zero-morphism`;
- `add-morphisms`;
- `negate-morphism`;
- `zero-object`; and
- `biproduct`.

Only after the registry and qualification tests are green should the model's
operational doctrine become `additive-category`. The direct category remains
a computation engine over presentations; it is not replaced by formal proof
certificates.

### Implemented operational additive result

`src/v3_2/algebra_polynomial_freyd_category.ts` now constructs the rank-zero
presentation and flattened direct sum of polynomial presentations. The latter
embeds both relation families into one free module. Its operational
`AlgebraPolynomialFreydBiproduct` retains the sum object and all four canonical
injection/projection presentation morphisms, while direct sum on morphisms is
the corresponding block-diagonal column map. Relation-preservation evidence
continues to be computed by the existing presentation-morphism engine.

The category registry now exposes executable operations for zero morphism,
addition, negation, zero object, biproduct, and direct-sum morphism. Every
operation also has an algebra lowering and TypeScript-reference implementation,
so categorical programs can delegate to the same direct engine. Binding the
first five operations qualifies the model against the inherited
`additive-category` doctrine roles before construction returns; its profile
and categorical tower now advertise that doctrine rather than merely
preadditivity.

The focused reviewer checks all five role methods, block-diagonal whole arrow
action and composition, all four projection/injection beta cases, the diagonal
biproduct identity, rank/relation concatenation, zero-object computation,
doctrine qualification, and a compiled biproduct program executed by the
reference algebra engine. Workspace validation, root typecheck, affected lint,
and the focused suite are green. The one required `check:ts` integration run
also passed workspace, typecheck, and full lint; its consolidated tests reached
completion but retained unrelated pre-existing failures in byte/line-position
pins for the active kernel and overview article. No failure named the changed
Freyd source, operation registry, compiler lowering, or focused reviewer, so
those orthogonal transfer/audit pins are not rewritten in this goal.

## Feasibility And Rejection Signals

The architecture is considered highly feasible because:

- `FiniteFamily` and `nat_add` share the correct recursion orientation;
- matrix identity/addition/composition and their theorem paths already exist;
- whole computational binary products and terminal objects already exist;
- full Freyd preadditivity is active;
- arbitrary quotient-point descent is active; and
- TypeScript doctrine roles already name the desired operations.

The main engineering risk is interaction between concrete direct-sum heads and
generic product/functor-action computation. The experiment loop must reject or
refine a candidate when it causes subject-reduction failure, loses whole/higher
action, requires compound reducible inferred LHS slots without justification,
or forces a global generic composition rewrite.

Warnings alone are not a rejection signal. Classify overlaps, test both
reduction orders, and add only narrowly justified joins.

If the full product instance cannot be promoted in the first bounded tranche,
retain the checked block/presentation operations as a coherent checkpoint and
record the exact missing stable-owner interface. Do not replace the missing
interface by opaque universal-property equality constants.

## Deliberate Non-Goals

This goal does not include:

- a parallel primitive coproduct theory;
- arbitrary finite/n-ary direct sums beyond binary plus the empty case;
- general finite colimits;
- computable weak kernels;
- the weak-kernel-to-Abelian theorem;
- an unconditional Abelian claim for arbitrary `CommRing`;
- kernels, cokernels, exactness, homology, or derived categories;
- source-functorial `Groupoidify_func` or its adjunction;
- integration of path-cubical/global-strictness work; or
- unrelated print, book, release, or repository-wide maintenance.

Additivity is expected for arbitrary `CommRing`. The successor weak-kernel and
Abelian goals remain capability-indexed, for example by polynomial rings over
computational fields with Gröbner/syzygy support.

## Corrected Longer-Term Order

```text
full Freyd preadditivity                         complete
  -> computational zero/direct sums             this goal
  -> formal and operational additive category   this goal
  -> computable weak kernels                     next capability goal
  -> generic weak-kernel-to-Abelian theorem
  -> kernels, cokernels, homology, derived constructions.
```

The action-category/groupoidification/truncation model remains the quotient-Hom
foundation throughout. Additive and later Abelian packages organize its
consequences rather than replacing it.

## Proposed Implementation Sequence

1. Audit the exact generic additive bridge and the primitive product/terminal
   instance assembly boundary.
2. Implement and prove finite-family append/split operations.
3. Implement vector/matrix blocks and the exact block law set required by
   direct sums.
4. Construct finite-free rank sums and block-diagonal matrix action.
5. Construct presentation direct sum, zero, raw projections/pairing, and
   agreement compatibility.
6. Descend the operations through groupoidification/truncation and construct
   the whole direct-sum functor.
7. Select and connect the Freyd `BinaryProducts`, terminal-zero, and
   `CartesianCategory` instances.
8. Derive the generic additive bridge and construct the Freyd
   `AdditiveCategory` instance.
9. Register TypeScript additive operations and qualify the direct model.
10. Add focused reviewers/conformance and synchronize standing authorities,
    catalog, health snapshot, and the final ledger.

## Implementation Ledger

| Row | Status | Dependency | Deliverable and acceptance boundary |
| --- | --- | --- | --- |
| `FAB-PLAN-0` | complete; initial plan checkpoint recorded in branch history | completed preadditive checkpoint `c3bb869` | living plan, isolated branch/worktree, clean focused baseline, Git and scope limits, persistent goal |
| `FAB-AUDIT-1A` | complete; recorded in plan checkpoint `5359dbf` | plan | generic additive theorem and concrete primitive-instance owner audit with explicit rejection signals |
| `FAB-FAMILY-2A` | complete; checkpoint `76eef67` | finite-family owner | append/take/drop, constructor betas, reconstruction/extensionality and boundary reviewers |
| `FAB-BLOCK-3A` | complete; checkpoint `8fdf7ca` | matrix owners | vector concatenation and general/special block matrices with the required composition, zero, identity, and split paths |
| `FAB-FREE-4A` | complete; checkpoint `38e54d1` | finite-free category | rank addition and block-diagonal direct-sum action with categorical comparison paths |
| `FAB-PRESENTATION-5A` | complete; checkpoint `794f163` | presentations | zero/direct-sum presentations, raw direct sums, projections, pairing, and computed relation squares |
| `FAB-AGREEMENT-5B` | complete; checkpoint `5d7ce09` | raw presentation sums | direct-sum and pairing compatibility on fixed-endpoint agreement categories; fixed projections require no varying input action |
| `FAB-DESCENT-6A` | complete; checkpoint `5643fbf` | quotient machinery | quotient projection/pairing/action, arbitrary-point laws, and whole direct-sum functor with retained action |
| `FAB-CARTESIAN-7A` | complete; selected-product checkpoint `d3880d0`; terminal-zero/Cartesian checkpoint `219660a` | generic product/terminal owners | connected `BinaryProducts`, terminal-zero, and `CartesianCategory` Freyd instances |
| `FAB-ADDITIVE-8A` | complete; checkpoint `118d6c2` | preadditive + Cartesian | generic zero/biproduct derivation, `AdditiveCategory`, and formal Freyd instance |
| `FAB-TYPESCRIPT-9A` | complete; checkpoint `eadfc8e` | direct model | registered additive roles, direct zero/biproduct computations, doctrine qualification and focused conformance |
| `FAB-CLOSE-10A` | complete; closeout checkpoint pending | all rows | reviewers, standing docs, catalog/health, proportional final gates and checkpoints |

Rows may be split, reordered when dependencies permit, rejected, or deferred
only with durable evidence and a synchronized ledger. Difficulty alone is not
evidence for an opaque axiom.

## Initial Decisions

| Decision | Status | Rationale |
| --- | --- | --- |
| `D-FAB-001` | accepted | The goal combines direct sums, zero object, biproduct derivation, and additive packaging as one coherent vertical slice. |
| `D-FAB-002` | accepted | Preadditive plus Cartesian is the primary additive architecture; no parallel primitive coproduct theory is selected. |
| `D-FAB-003` | accepted | Terminality becomes zero-object structure through generic preadditive proofs; coproduct operations derive from products and addition. |
| `D-FAB-004` | accepted | Finite-family append recurses on the left index, matching the active `nat_add` owner. |
| `D-FAB-005` | accepted | Block matrices are flattened into the existing column-matrix representation rather than retained as a second matrix carrier. |
| `D-FAB-006` | accepted | Matrix and presentation square laws are constructed internally; no manually entered commuting square is part of the usability surface. |
| `D-FAB-007` | accepted | The whole direct-sum functor and product/terminal transfors must retain Hom and higher action. |
| `D-FAB-008` | accepted | Generic category identity/composition remain runtime owners; transparent block computation is connected by paths or narrow proof-time usability. |
| `D-FAB-009` | accepted | Existing groupoidification/truncation helpers promote class equations; no new general quotient eliminator is selected. |
| `D-FAB-010` | accepted | TypeScript becomes operationally additive only after concrete role registration and qualification. |
| `D-FAB-011` | accepted | Additivity is uniform in `CommRing`; weak kernels and Abelian structure remain capability-indexed successor goals. |
| `D-FAB-012` | accepted | Warning counts are diagnostic evidence, not a semantic veto; every new overlap still requires classification. |
| `D-FAB-013` | accepted | Orthogonal path-cubical/global-strictness histories and historical `main` are excluded from the baseline. |
| `D-FAB-014` | accepted | No unrelated repository-wide aggregate is part of the focused implementation loop. |
| `D-FAB-015` | accepted after owner audit | Primitive product/terminal classifiers require narrow stable concrete assembly; every exposed observation must still route to constructed Freyd semantics. |
| `D-FAB-016` | accepted after family probe | Transparent left-recursive append/split operations suffice; no new runtime/unification clause or alternative finite-family carrier is needed. |
| `D-FAB-017` | accepted after block probes | A vertical pair of horizontal rows is the selected general block orientation because it exposes product projections directly. |
| `D-FAB-018` | accepted after block laws | All required block beta/eta and diagonal-composition equations are constructed theorem paths; no block runtime/unification family is needed. |
| `D-FAB-019` | accepted after whole-functor probe | Finite-free direct-sum object/arrow computation can reduce directly to `nat_add`/block diagonal without a rigid intermediary or new warning family. |
| `D-FAB-020` | accepted after presentation probes | Zero/sum objects and raw sum/projection/pairing morphisms are flattened matrix data whose retained relation squares are all constructed from block laws. |
| `D-FAB-021` | accepted after agreement probes | Direct-sum and pairing agreement witnesses are block-diagonal/vertical combinations; subtraction compatibility closes their laws without quotient axioms. |
| `D-FAB-022` | accepted after quotient-descent probes | Nested agreement-groupoidification and set-truncation descent construct quotient pairing without representative choice. The outer generic action uses a rigid proof-time bridge because its direct transparent runtime fold exceeded the bounded check; the rigid head then reduces to the constructed semantic path, while the public direct-sum functor keeps direct object/arrow computation and retained Hom action. |
| `D-FAB-023` | accepted after selected-product probes | The concrete `BinaryProducts` witness reuses the whole quotient direct-sum functor and generic triangular theory. Selected point projections/pairing meet rigid Freyd observations through typed proof-time comparisons, then those rigid heads fold to constructed quotient semantics. Direct rules on the generic point heads exceeded the bounded check; the selected bridge preserves those heads for beta/eta and adds no warning beyond the exact import union. |
| `D-FAB-024` | accepted after terminal-zero probes | Terminality of the zero presentation is constructed from zero-row matrix uniqueness and the existing agreement/groupoidification/truncation descent, not postulated from preadditivity or encoded by a manual square. The generic terminal transfor/cut remain primary; selected point and contractibility observations expose the quotient zero semantics. Cartesian evidence is their transparent product. |
| `D-FAB-025` | accepted after generic-additive proofs | `AdditiveCategory` is exactly preadditive plus selected Cartesian evidence. Initiality, injections, copairing, both beta laws, the diagonal identity, and eta are theorem-level consequences of abelian cancellation, bilinearity, and generic product/terminal computation; no primitive coproduct or runtime additive rule is introduced. The formal Freyd instance is transparent. |
| `D-FAB-026` | accepted after operational qualification | The direct polynomial Freyd model constructs zero/direct sums and canonical biproduct maps, registers the five inherited additive doctrine roles plus whole direct-sum arrow action, supplies compiler lowerings/reference implementations, and advertises `additive-category` only after runtime qualification succeeds. |
| `D-FAB-027` | accepted at closeout | The objective is complete at formal and operational layers. Weak kernels, the weak-kernel-to-Abelian theorem, exactness, homology, broader finite colimits, and orthogonal cubical/strictness integration remain successor goals rather than hidden gaps in this additive package. |

## Validation Matrix

For each semantic tranche:

- smallest owner-position probe;
- positive typed consumer and zero/rank-one/nontrivial boundary cases;
- relevant noncollapse or wrong-endpoint reviewer;
- retained whole/higher action where a functor/transfor is introduced;
- bounded quiet checks;
- warning-enabled predecessor/candidate comparison;
- strict inferred-slot audit on every changed Lambdapi source;
- affected reviewer examples; and
- exact staged diff plus synchronized ledger before a checkpoint.

Catalog and no-check health/source snapshots are refreshed after registration.
Run larger aggregates only when separately justified by an actually affected
integration/release boundary; preserve the user's instruction to avoid
unrelated long aggregate checks.

## Completion Result

The requirement-by-requirement audit is closed:

- finite-family append/take/drop and reconstruction are checked at checkpoint
  `76eef67`;
- flattened vector/matrix blocks and required laws are checked at `8fdf7ca`;
- the whole finite-free sum functor is checked at `38e54d1`;
- zero/direct-sum presentations and computed raw maps/squares are checked at
  `794f163`, with agreement compatibility at `5d7ce09`;
- quotient pairing, projection classes, whole direct sums, and retained Hom
  action are checked at `5643fbf`;
- selected binary products, terminal zero, and Cartesian evidence are checked
  at `d3880d0` and `219660a`;
- the rule-free generic additive derivation and transparent formal Freyd
  instance are checked at `118d6c2`; and
- direct zero/biproduct computation, all five doctrine roles, whole arrow
  action, compiler lowering, reference-engine execution, and successful
  `additive-category` qualification are checked at `eadfc8e`.

Every changed Lambdapi module and reviewer passed its bounded focused check.
Strict LHS audits are empty. Warning comparisons are classified against exact
predecessor/import-union baselines; selected-product and terminal-zero
instance layers add no local warning. The strict check catalog, no-check health
source snapshot for 389 Lambdapi/reviewer files, source TOC, active references,
report lifecycle headers, shell syntax, Python compilation, and exact diff
hygiene pass.

For TypeScript, workspace validation, root typecheck, affected lint, and the
five-test direct polynomial Freyd suite are green. The one justified
`check:ts` boundary run passed workspace/typecheck/full lint and completed its
consolidated suite; its failures are inherited kernel/article byte and
line-position pins outside this branch's additive changes. They are recorded,
not rewritten. No print, release, kernel-wide CI, push, merge, publication, PR,
history rewrite, branch cleanup, or worktree removal was performed.

## Persistent Goal Launch Prompt

Continue `TS-EMDASH-FREYD-ADDITIVE-BIPRODUCTS` from the living plan in
`docs/TYPESCRIPT_EMDASH_FREYD_ADDITIVE_BIPRODUCTS_PLAN.md`. Treat active source
and the Lambdapi SOP as authority. Work only in
`/home/user1/emdash1-freyd-additive-biproducts-v1` on branch
`goal/freyd-additive-biproducts-v3.2`, preserving baseline
`c3bb8691e76d47bebca1aa58d28cd1126335fc26` as comparison evidence. Resume the
first dependency-ready ledger row and revise the plan when probes refine the
architecture. Preserve the preadditive-plus-Cartesian derivation, column-matrix
orientation, whole/higher action, quotient descent, owner-position probing,
warning classification, strict LHS audits, focused reviewers, and proportional
validation. Local validated checkpoint commits are authorized after each
bounded coherent tranche is green and the exact staged diff is reviewed. Do
not push, merge, publish, release, create a PR, amend, rebase, reset, rewrite
history, delete a branch, or remove a worktree. Do not integrate orthogonal
path-cubical/global-strictness work. The goal is complete only when every
scoped row is implemented, rejected with durable evidence, or explicitly
deferred behind a concrete prerequisite, and all affected authorities are
synchronized.
