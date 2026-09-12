# Native Universality: Owner, Variance And Dependency Ledger

Date: 2026-09-12

Status: active NUH-1 design; source inventory established, coupled target design not yet qualified

Parent: [living implementation plan](TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_AND_HOMOLOGY_PLAN.md)

## Source Identity And Recovery

The worktree starts at `cbef77e76fc292453c8814b5ecc6d62e84132f01`.
Its active nucleus Git blob is
`91f1974ece225e399604dce24710bf1437ad3ef5`. Active LP sources/reviewers have
no diff from the final mathematical checkpoint `ff139362`.

The preserved total-op patch is anchored to nucleus blob
`5387c65ab75ddcfff4b5ffca9fb6f9d082084774`. The current nucleus adds 328 lines
in four hunks after that anchor: a transformation observation, composition
and weakened-section observations, and displayed evaluation/pairing/identity
action. No old lines were deleted. These additions are part of the current
homology baseline and must survive a repair with their corrected variances.

An initial ordinary `git apply --check` rejected the preserved patch at its
first hunk. That is not source-conflict evidence: this is a zero-context
patch. `git apply --check --unidiff-zero` succeeds against the current source.
This establishes mechanical applicability only, not correct placement of
every zero-context insertion or qualification of the later added owners.
The old runner rejects the changed source hash and independently uses raw
timeout calls without the current memory/serialization guard. Do not run it
unchanged or bypass its anchor by resetting a worktree.

The complete original patch, its original baseline, and the four current
addition hunks must be audited together before producing a new staged copy.
There is no installed patched checker and no promoted repaired kernel.

## Native Foundations And Variance Inventory

The defining sources in the following table refer to the current nucleus
[emdash3_2.lp](../emdash2/emdash3_2.lp), unless another file is linked.
Symbols and consumer families were relocated with `rg`; line numbers are
observations of this source identity, not enduring authority.

| Owner | Current source observation | Design disposition and discriminating consumer |
| --- | --- | --- |
| `Op_cat`, `Op_func` | Lines 3282/7046; dimension-1 Hom transpose, object/arrow and whole Hom observations | Audit total-dual reinterpretation jointly with recursive Hom action; retain objects and test genuine dimension-2/3 directions |
| whole `op` | Line 7153; covariant Cat→Cat | Correct universe variance; direct Empty reproducer must fail at the repaired type, not at a missing declaration |
| `Op_catd_func`, `Op_catd`, `Op_funcd` | Lines 7221/12658/12720; unrestricted same-base formation/action | Base change and displayed-transformation variance are part of the repair; family-only reconstruction of bad op must fail |
| `hom_con`, `hom_int` | Lines 7900/8455; fixed-target and whole internal Hom owners | Preserve their ownership, cuts and distinct pre/postcomposition; classify each opposite slot by actual dimension/profile |
| `Pi_func` and negative-section observations | Line 13054 and mixed-section consumers | Preserve internal section calculus; test constant families and actual section components at the corrected bases |
| `homd_` | Line 13205; endpoint-observation family over opposite base Hom | Preserve relation to `homd_int`; audit variance of the base-Hom argument separately from total fibre duality |
| `Sigma_cat`, `Sigma_func` | Line 13258; totalization and constant-family product rule | Preserve existing owner; correct Hom totalization coherently rather than cancel only its visible base reversal |
| Sigma Hom | Line 13315; outer Op of a total of the dependent-Hom family | Terminal-base constant family must retain full fibre Hom direction; independent Sigma Empty derivation must fail |
| `Sigma_proj1_func` and second-coordinate observations | Line 13492 and associated generic action | Whole projection and further Hom action must remain typed; object pairs alone do not test fibre-cell orientation |
| `Functor_catd`, constructor package | Lines 14184/14255; negative source family and positive target family | Specify joint base/whole-action variance; no arbitrary higher regrading or duplicate composition owner |
| `Hom_catd`, `Transf_catd` | Lines 14505/14527; positive/negative section inputs | Correct the actual bases of negative sections and test the constant-Cat specialization at higher action |
| `Rep_catd_func`, `Edge_catd_func` | Lines 14565/14596; internal represented family followed by fibre opposite | Rep stays a view of hom_int; Edge must distinguish total opposite from variance-only transposition |
| `Presheaf_catd_func`, `HomPresheaf_catd_func` | Lines 14606/14618; composed mixed-functor-family target | Trace both argument variances and the external parameter through the complete composition |
| `Homd_target_section_catd`, `Homd_target_catd` | Lines 14645/14658; old mixed-family/Pi composition | First unresolved coupled semantic gate; keep original E over Z and native constructor, with no replacement-family premise |
| `homd_int` | Line 14688; fundamental syntactic package with displayed-functor argument | Preserve fundamental ownership, recoverability and canonical projection ladder; no replacement by total-category extraction |
| `homd_src_func`, `homd_src_sec`, `homd_tgt_func` | Lines 14806/14830/14852; whole-to-component-to-endpoint ladder | All levels must land in the same repaired target; test whole next action as well as endpoint equations |
| internal displayed hom action and extracted laxity | After the native homd ladder; Sigma consumes this action | Preserve the noncircular dependency: native homd action → extracted laxity → Sigma action |
| current displayed Eval/pairing/identity additions | Four post-anchor source hunks | Retain their legitimate computations while migrating every affected opposite/base annotation; historical prefix cannot validate them |

The source types are not a semantic consistency certificate. The two known
defects are still present, and the prospective repair must interpret the
whole collection together.

## First Coupled Target Question

The old pipeline has the schematic shape

```text
Rep → opposite Edge → HomPresheaf
                    → mixed Functor_catd with original E
                    → Pi → Homd_target.
```

The preserved total-op candidate moves HomPresheaf's outer base to the
shifted category and its inner base to a total opposite. The unchanged
mixed-family input then demands a regraded E. That is the documented
R(Z) versus Z type mismatch. It is a failure of that composition, not a
license to replace `homd_int` or assume R(Z)=Z.

The next design subrow must jointly derive the external x base, the inner y
base, the variance of HomZ(x,y), the family argument E and the resulting
whole homd source/target. In particular, verify that variance-only
transposition at a base Hom and total duality of a fibre are not conflated
in Edge/HomPresheaf. The preserved candidate's shifted-dual action on entire
functor categories also needs its actual strict/lax interpretation.

Possible changes to a supporting target classifier are not ruled out, but
they must have a coherent native internal interpretation and working whole
action. Do not add an opaque target solely because its point projection
can be made to resemble the desired Hom. A total-Hom observation is a
derived check, never the new defining source of native homd action.

**Acceptance gate:** a complete variance table for this composite, preserving
the original input family and native homd ladder, plus the matching
nonidentity base-arrow, base-2-cell, further-Hom and wrong-base controls.
This gate is still open; NUH-2 source mutation has not begun.

### First explicit dimension-2 constraint

The current mixed-functor action supplies a useful paper-level discriminator.
Let p,q:x→y and α:p⇒q be a genuine directed base 2-cell. For source family
A and target family B the object action at p is

```text
F ↦ B(p) ∘ F ∘ A(p).
```

An action from this p-image to its q-image needs components with directions

```text
A(p) ⇒ A(q),       B(p) ⇒ B(q).
```

With dimension-1 transposition of the base, A(p):Aᵧ→Aₓ and A(α) still has
the first required direction. With total base duality, α reverses and the
available comparison is A(q)⇒A(p). That does not supply the required action
for arbitrary noninvertible cells in the same ordinary functor category.

Therefore changing `Functor_catd`'s negative-family base from Transpose(K)
to total Op(K) merely to make the old E input fit is not a valid repair of
this interface. A changed transformation profile would require an explicit
new semantic account of the whole action, not just the same fibre formula.
This is a derivation from the displayed composition action, not a claim
that a new LP negative fixture has already been run.

Likewise, restricting Z to an ordinary category could hide R(Z) versus Z,
but would not repair native homd for arbitrary directed bases. Both the
unrestricted-base and noninvertible-2-cell controls belong in NUH-1B.
The next target design must resolve these constraints jointly with the
presheaf argument's variance while preserving the native homd owners.

## Whole Universality And Homology Dependency Inventory

| Owner | Current dependency | Intended next boundary |
| --- | --- | --- |
| [generic adjunction mates](../emdash2/emdash3_2_adjunction_mates.lp) | Defined whole Hom views of the existing adjunction comparison, with whole and point cancellation | Reuse as primary operation owners; preserve cut discriminators |
| [kernel presentation](../emdash2/emdash3_2_kernel_adjunction_presentations.lp) and [cokernel presentation](../emdash2/emdash3_2_cokernel_adjunction_presentations.lp) | Whole K/Q and adjunction heads parameterized by old selected W/V | Separate whole structure from its selected realization; no mandatory old factor dictionary for every formal operation |
| [kernel record](../emdash2/emdash3_2_kernel_adjunction_records.lp) and [cokernel record](../emdash2/emdash3_2_cokernel_adjunction_records.lp) | Whole endpoints; old selected universal evidence is transferred/recentered | Derive ordinary factor/uniqueness observations from the whole comparison at the stated profile |
| [native zero cone](../emdash2/emdash3_2_zero_arrow_cones.lp) | Represented comma built from native homdc/Sigma | Reuse native ownership, with repaired variance; no independent cone grammar |
| [ordinary-target universal transformation](../emdash2/emdash3_2_one_cat_zero_cones.lp) | Existing OneCat profile exposes a whole family | Keep the ordinary specialization explicit; do not impose it on generic higher categories |
| [chain input](../emdash2/emdash3_2_chain_pair_zero_cones.lp) and [raw Freyd input](../emdash2/emdash3_2_commutative_algebra_freyd_zero_cone_inputs.lp) | Original selected boundary lift is unmated to introduce the native input | Input formation should use its native differential/zero structure before any kernel selection |
| [whole H](../emdash2/emdash3_2_homology_families.lp) | β=K(h)∘η; H=Q∘Arr(β), currently parameterized by selected presentations | Keep this whole composite and migrate its structure dependencies |
| [direct connecting](../emdash2/emdash3_2_homology_record_connecting.lp) | Retained homology records and universal factors | Reuse mathematics and nonzero consumers while moving primary construction to whole universality |
| [whole connecting](../emdash2/emdash3_2_homology_window_connecting_transformation.lp) | Declared whole transfor whose component is the direct construction | Preserve actual endpoints and generic action; audit the declaration/interpretation contract |
| [finite iterator](../emdash2/emdash3_2_homology_bounded_generator.lp) | Retained row/map fields and whole H/δ with interior evidence | Reference consumer; symbolic endpoint debugging remains deferred |
| [formal model](../emdash2/emdash3_2_commutative_algebra_freyd_homology_models.lp) | Explicit W/V plus coherent K/Q presentations | Reusable model construction/registration and accurately classified realization contracts |
| [native connecting](../src/v3_2/algebra_polynomial_freyd_homology_connecting.ts) | Snake method with retained endpoint comparisons/descent | Preserve as computational method; compare against the whole formal characterization |
| [bounded model workflow](../src/v3_2/algebra_formal_freyd_long_exact_model.ts) | Supplied model and optional normality, prepared observations and explicit adoption | Automate repetitive model/reifier plumbing for the supported backend without upgrading trust claims silently |

The first universality prototype should expose whole K/Q, units/counits,
nonidentity action and mate cancellation without taking W/V as their
defining formal inputs. Its realization adapter must still retain and
justify a selected native result. This is a bounded vertical gate, not
permission to add a second checker or claim all interacting exactness laws
from adjunction triangles alone.

## Fresh Baseline Evidence

All four targets were checked serially by `scripts/probe.sh`, which uses the
current resource guard and ordinary subject-reduction checking. The copied
source and installed checker were not modified.

| Target | Result | Log under emdash2/logs/probes |
| --- | --- | --- |
| `emdash3_2.lp` | accepted; bounded positive baseline | `emdash3_2-20260912-151741.log` |
| `audits/internal_op_empty_reproducer.lp` | accepted; inherited defect reproduced | `internal_op_empty_reproducer-20260912-151820.log` |
| `audits/sigma_hom_empty_reproducer.lp` | accepted; independent inherited defect reproduced | `sigma_hom_empty_reproducer-20260912-151953.log` |
| `audits/internal_op_family_empty_reproducer.lp` | accepted; family reconstruction defect reproduced | `internal_op_family_empty_reproducer-20260912-152032.log` |

The last three successes reproduce failures of the encoding; they are not
positive mathematical-library tests. Eventual repair must reject their
invalid terms for the correct variance reason while keeping valid native
Hom/diagram action available.

Bootstrap/workspace validation passed, and Infinity Codex verified 1,103
archived responses in the original worktree. The latest verified recovery
response is the accepted 0003 of this session. No hook changed, no global
aggregate was rerun, and no mathematical source was edited for this initial
design tranche.

## Subrow State And Next Experiment

### NUH-1B2a: Derived negative-section operator

Hypothesis: in the preferred total-duality basis, the native negative-section
category can be defined as NΠ_K(E)=O(Π_R(K)(Eᴼ)). Its whole constructor is
obtained by dualizing the existing Pi/Op-family composite with the correctly
shifted domain. For constant E it should recover the ordinary functor
direction T(K)→C. This supplies an internal candidate ingredient for the
target-polarity repair; it does not complete the general Homd target.

Test it on the preserved preferred source prefix, which contains Pi and the
correctly based dual-family operators. Retain the prefix limitation and
ordinary installed checker, stage copies only, and use the current resource
guard. Qualify whole construction, constant-family introduction/elimination,
nonidentity arrow action and wrong-direction controls without adding a new
rewrite or unifier. Full source migration and rejection of the Homd Empty
diagnostic remain separate requirements.

The first prefix prototype checks the category expression and constant-family
whole readback, including a nonidentity arrow and a further Hom action.
However, its tentative unrestricted constructor on Catd(K) is not selected:
for a lax displayed F:E→D, the available comparison is
D(p)∘Fₓ⇒Fᵧ∘E(p). Mapping a negative section needs the opposite direction.
Typechecking the old shifted-duality prototype does not justify that inverse.

Refine the map interface to accept an actual whole map G:Eᴼ→Dᴼ over R(K).
Its section action comes from Π(G), followed by total duality. The whole
map operator has source O(Functord(Eᴼ,Dᴼ)) and target
Functor(NΠ(E),NΠ(D)); this uses existing whole actions and requires no
manufactured inverse to F's laxity. Check point action against the existing
section_postcomp_sec(G,s) and reject an ordinary F:E→D as the wrong input.
The initial unrestricted source is retained as an unselected experiment,
not promoted as a general negative-section functor.

The refined [prototype](../emdash2/audits/native_negative_pi_prototype.lp)
checks in the preferred prefix. NΠ is a defined category expression. Its
whole map functor accepts O(Functord(Eᴼ,Dᴼ)); the point action agrees by a
typed reflexivity path with the existing Π section_postcomp_sec(G,s).
An ordinary lax F:E→D is rejected as that input. Constant-family
introduction/readback returns the original functor, its nonidentity arrow
action checks and a further whole Hom action remains available. No rule,
unifier, new primitive section operation or inverse-laxity witness is added.

The [guarded driver](../emdash2/scripts/check_native_negative_pi.sh) stages
both the exact current and historical patched prefixes and checks their
byte identity before the prototype. It retains the untested complete
candidate separately and explicitly records `fullKernelChecked: false`.
The gate at `/tmp/emdash-native-negative-pi.kVNMc2` passes baseline and
prototype with ordinary subject reduction; complete warning inventories
agree at 935 critical pairs / 137 pattern reports. The prototype's strict
LHS audit reports no rule clauses. Source- and patch-anchor checks prevent
silent replay on drifted owners. The initial unrestricted variant remains
in `tmp/probes/nuh_negative_pi_unrestricted_v1.lp` and the earlier temporary
stage, not as the selected interface.

This qualifies a native direction-correct ingredient on the retained
preferred prefix, not the complete Homd target or a repair of the active
nucleus. The next design must supply the appropriate negative-family maps
from the actual target construction; it cannot pass arbitrary old lax maps
through a covariant NΠ wrapper. The original target, all Empty controls and
the 328 current post-prefix source additions remain to be migrated.

### NUH-1B1: Terminal-family section polarity probe

Hypothesis under test: the old positive section over the opposite y-base
has the wrong direction even before the full higher-base mismatch is
considered. For a covariant F:Z→C, terminal D, constant E=C, and fixed x,u,
the endpoint observation is p↦HomC(u,F(y)). Section action along p:x→y
would send its y-value (restricted along p) to its x-value. Evaluating at
idₓ would therefore appear to give HomC(u,F(y))→HomC(u,F(x)), which is not
available for arbitrary F and p.

Test this in a non-library file using only existing definitions and actions.
No primitive witness, rewrite or unifier is to be added. If the term checks,
retain it as a diagnostic of the current coupled package, not as a valid
feature; independence from the already known defects requires separate
controls. If it fails, inspect the exact action/endpoint that rejects it
before selecting a replacement target. The intended native homd constructor
remains foundational throughout.

Result: the [tracked diagnostic](TYPESCRIPT_EMDASH_HOMD_TARGET_POLARITY_DIAGNOSTIC.md)
accepts the complete reverse functor and a closed Empty witness. Its
walking-arrow specialization also accepts. The separate forward-action
companion checks typed reconstruction/identity paths, retains the next Hom
action and rejects the reverse function type. Warning-enabled runs have
identical complete 1,144/157 inventories and all three audit files contain
zero new rule clauses. Exact source/log/status details are in the diagnostic.

This changes the next action: correcting only the R(Z) versus Z type
mismatch is insufficient. The target's section polarity must also be
corrected. The result belongs to the existing coupled package; independence
from the earlier op/Sigma faults is not established. Retain the three
earlier negative controls and add this route to full-repair qualification.

### NUH-1B2: Direction-correct native target

The required y-action in the strict working transport case is

```text
Mᵧ(q,v) → M_z(p∘q, D(p)(v)),
Mᵧ(q,v)=HomEᵧ(E(q)(u),Fᵧ(v)).
```

The old positive section over the opposite y-base supplies the converse.
First qualify a native negative/mixed-section target in the terminal and
constant case, with preserved whole projection/action. Then combine it with
varying D/E and noninvertible base-2-cell controls. A lax-comma interpretation
is a candidate semantic comparison for the target, not a new definition of
homd_int. Its complete higher variance remains to be established.

A limited primary-source review of comma polarity and dependent two-sided
fibrations is recorded in the diagnostic. It does not start a general
external calculus or a spectral research task. The new target's type,
projections and computation must be specified together before promotion.

| Subrow | State |
| --- | --- |
| NUH-1A source/dependency inventory and baseline | established; launch checkpoint records the exact anchors and controls |
| NUH-1B1 terminal-family polarity control | complete diagnostic tranche; reverse Hom and Empty reproduced, lawful forward companion checked |
| NUH-1B2 complete native Homd target variance/polarity design | active; resolve the corrected section direction and all bases/profiles together |
| NUH-1B2a negative-section ingredient | refined object/whole-map and constant-family prototype checked on preferred prefix; unrestricted lax covariance rejected |
| NUH-1C whole-universality/realization separation design | initial dependency inventory established; exact native interface remains to qualify |
| NUH-2A repaired full-owner candidate | not started; requires NUH-1B |

Continue with NUH-1B2, reading the current native projection ladder and the
preserved full candidate side by side. Keep the new Empty route as a
rejection control. Record a typed mathematical proposal and its projection
controls before generating a new full-source copy. All
spectral/stabilization brainstorming is out of scope and is not a dependency.
