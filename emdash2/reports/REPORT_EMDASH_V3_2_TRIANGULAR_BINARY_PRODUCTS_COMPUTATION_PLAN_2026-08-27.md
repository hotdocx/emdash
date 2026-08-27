# Emdash v3.2 Enhanced Triangular Binary Products Computation Plan

Date: 2026-08-27 (America/Toronto)

Plan-ID: `TRIANGULAR-BINARY-PRODUCTS-COMPUTATION-V3.2`

Status: **completed first computational tranche as of 2026-08-27**. The
enhanced triangular owner, runtime calculus, proof-time `P` coherence,
explicit map-agreement proof, ordinary hom-level uniqueness consumer, focused
diagnostics, reviewer example, warning classification, catalog, authorities,
and scoped hygiene are synchronized and green. The automatic adapter to the
existing weighted-limit package remains a separate follow-up boundary; the
terminal-object row remains deferred.

Depends-On: active v3.2 `Cat`, `Functor`, `Transf`, `tapp0_*`/`tapp1_*`,
`Product_cat`, `Product_projL_func`, `Product_projR_func`, `Product_map_func`,
represented hom/precomposition owners, fixed-base fibrewise products,
`emdash3_2_finite_limits.lp`, the rewrite/unification SOP, Foundations, and
canonical syntax

Supersedes: no earlier dedicated binary-products plan. It incorporates and
operationalizes the reviewed design in Infinity response `0019`; later entries
in this living plan supersede that response where owner probes required stable
post-projection heads and narrow duplicated runtime instances.

Infinity-Codex-Origin: session `01a02f68-6142-7e53-993a-4505aa8e2cbe`,
response `0019`

Infinity-Codex-Decision-Responses: response `0019`; the archived path below is
recovery evidence, while active source and this evolved plan are authoritative.

Side-Task-Ledger: `TBP-PLAN-0`, `TBP-OWNER-1`, `TBP-PROJ-2`, `TBP-PAIR-3`,
`TBP-RULES-4`, `TBP-NF-5`, `TBP-SEM-6`, `TBP-CAT-7`, `TBP-TERM-8`, and
`TBP-RECLOSE-9`

Baseline: clean local checkpoint `2ef786c` on
`goal/monad-comonad-computation-v3.2`

Worktree: `/home/user1/emdash1-monads-v3.2`

Branch: `goal/monad-comonad-computation-v3.2`

Git authority: the user authorized creating/evolving this dedicated living
plan, starting a new persistent goal, and proceeding with the scoped
implementation and validation. This does **not** authorize a new branch,
worktree, push, merge, publication, release, history rewrite, branch deletion,
or worktree removal. On 2026-08-27 the user separately authorized a local Git
commit/checkpoint of the completed synchronized tranche. Preserve unrelated
work and historical checkpoint `2ef786c`.

Recovery archive: response `0019` is archived at
`emdash2/tmp/ai-responses/sessions/2026-08-23_01a02f686142/responses/0019_2026-08-27T10-02-04Z_01a0429e-a4f3-7ce2-8726-87c43483b158.md`;
the active source and this evolved plan are authoritative.

## Objective

Implement a computational and internally functorial chosen-binary-product
interface for an arbitrary category `C`, guided by Došen's triangular
presentation in §§6.2-6.4 while following the successful enhanced adjunction
and Monad architecture already used by emdash.

The selected layer should:

1. index binary-product evidence by a selected whole functor
   `P : Product_cat(C,C) ⊢ C`;
2. expose the two projections as stable whole transfors from `P` to the
   existing left/right projection functors;
3. expose pairing as a whole internally natural operation retaining higher
   action, preferably one transfor between represented Cat-valued families;
4. recover Došen's `K₁ᵃ` and `K₂ᵃ` as off-diagonal transfor actions rather
   than bare primitive arrow operations;
5. orient the product beta, distribution, eta, and selected §6.4 derived
   reductions exactly toward the cut-eliminating triangular language;
6. keep the extra full-functor action of `P` semantically/propositionally
   coherent with the triangular derived product map without installing a
   competing hot runtime expansion;
7. preserve the existing per-pair weighted-limit
   `BinaryProductPresentation` as semantic authority and later bridge the
   global triangular structure to it rather than replacing it; and
8. defer the terminal-object extension until the binary-product owner is
   stable, unless a separate bounded semantic/propositional terminal probe is
   independently accepted.

This goal implements the useful generic computational consequences. It does
not construct Došen's free syntax, reproduce his metatheoretical decidability
algorithm as a new syntax normalizer, claim that every category has binary
products, or introduce an explicit Cartesian-category package prematurely.

## Authority And Recovery Order

Use the following order on every continuation:

1. active source and `emdash2/AGENTS.md`;
2. this living plan and its decision/side-task ledgers;
3. `emdash3_2_checks.lp` and focused reviewer examples;
4. current status/SOP, Foundations, canonical syntax, and `reports/INDEX.md`;
5. Došen's PDF for mathematical orientation and notation;
6. the linked Infinity response as decision evidence; and
7. raw archives and disposable probes only as historical/experimental
   evidence.

The local Došen sources are:

```text
/home/user1/dosen-book/kosta-dosen-book-cut-elimination-in-categories.pdf
/home/user1/dosen-book/kosta-dosen-book-cut-elimination-in-categories.txt
```

## Reviewed Conclusion

The selected design is an **enhanced triangular chosen-binary-product layer**,
not a literal point-level copy of the operations in §6.2.

The primary public boundary should contain:

- a selected whole product functor `P : C × C ⊢ C`;
- two stable projection transfors;
- a whole internally natural pairing operation; and
- Došen's triangular reductions on stable pairing/projection heads.

A point-level presentation built only from `hom_precomp_*` remains useful as
derived notation and semantic comparison, but it must not own the product
runtime theory.

The terminal object is a separate tranche. Its semantic internal formulation
is straightforward, but Došen's unrestricted equation `(K)` cannot safely be
implemented as a variable-headed Lambdapi rewrite or a bare-variable
`unif_rule`.

## Adjunction Precedent: Confirmed

The active adjunction interface is stronger and more internal than Došen's
literal primitive-operation presentation.

It is indexed by already available whole functors:

```text
J : Adjunction(F,G)
F : R ⊢ L
G : L ⊢ R.
```

Its primitive observations are actual whole transformations:

```text
unit_adj_transf(J)   : id_R ⇒ G ∘ F
counit_adj_transf(J) : F ∘ G ⇒ id_L.
```

Došen's operations are recovered as exact off-diagonal projections:

```text
γᶜ(g) = tapp1_fapp0(unit_adj_transf(J),g)
φᵃ(f) = tapp1_fapp0(counit_adj_transf(J),f).
```

Their types are:

```text
g : B₁ → B₂       γᶜ(g) : B₁ → GF(B₂)
f : A₁ → A₂       φᵃ(f) : FG(A₁) → A₂.
```

The two active triangle rules match those `tapp1_fapp0` forms directly, while
generic transfor naturality supplies the remaining naturality cuts. Emdash
therefore did not make bare `φᵃ` and `γᶜ` operations the highest-level
primitives. It made `φ` and `γ` whole transfors and obtained Došen's operations
through their full off-diagonal action. This retains the next hom action and is
the direct precedent for binary products.

Došen's `A*` and `B*` are the categories of the free syntax. Emdash implements
the generic categorical computation, not those free syntactic categories.

## Došen's Selected Triangular Product Presentation

Došen rejects the earlier rectangular presentation with primitive arrow-level
`×` because it does not support Total Cut Elimination. In §6.2 the primitives
are:

```text
K₁ᵃ_A(f) : B × A → C     for f : B → C
K₂ᵃ_A(f) : A × B → C     for f : B → C

⟨f,g⟩ : X → A × B       for f : X → A and g : X → B.
```

Arrow-level product is derived:

```text
f₁ × f₂
  := ⟨K₁ᵃ_{A₂}(f₁), K₂ᵃ_{A₁}(f₂)⟩.
```

The core equalities, in computational orientation, are:

```text
h ∘ K₁ᵃ_A(f)        → K₁ᵃ_A(h ∘ f)
K₁ᵃ_B(h) ∘ ⟨f,g⟩   → h ∘ f

h ∘ K₂ᵃ_A(f)        → K₂ᵃ_A(h ∘ f)
K₂ᵃ_A(h) ∘ ⟨f,g⟩   → h ∘ g

⟨f,g⟩ ∘ h           → ⟨f ∘ h, g ∘ h⟩

⟨π₁,π₂⟩             → id_{A×B}.
```

Here:

```text
π₁ = K₁ᵃ_B(id_A)
π₂ = K₂ᵃ_A(id_B).
```

For the Church-Rosser/commuting normalization of §6.4, Došen also selects the
derived orientations:

```text
⟨K₁ᵃ_A(f), K₁ᵃ_A(g)⟩ → K₁ᵃ_A(⟨f,g⟩)

⟨K₂ᵃ_A(f), K₂ᵃ_A(g)⟩ → K₂ᵃ_A(⟨f,g⟩).
```

Those last two are not needed for Total Cut Elimination itself, but they are
part of the useful normalizing surface suggested by §6.4 and should be probed
after the core beta/eta owner is stable.

## Existing Emdash Product Layers

The current kernel already has a highly internal product of categories:

```text
Product_cat(A,B)
Product_projL_func
Product_projR_func
Product_map_func
Product_cat_func.
```

This supplies category products, product functors, projection functors, and
componentwise object/arrow/transfor/higher action. It is product in `Cat`, not
a chosen product of objects inside an arbitrary category `C`.

The later `emdash3_2_finite_limits.lp` supplies a selected product of one pair
`x,y : C` through the whole weighted-limit comparison:

```text
BinaryProductPresentation(C,x,y).
```

It derives the selected object, whole cone, and two projections internally.
It deliberately has no global coherent product functor, pairing operation,
projection-after-pairing beta, distribution computation, or runtime rules.
It is an appropriate semantic per-pair layer, not the missing triangular
computational structure.

## Selected Enhanced Interface

Use the indexed-owner pattern already selected for `Adjunction` and `Monad`:

```text
B : BinaryProducts(C,P)

P : Product_cat(C,C) ⊢ C.
```

The provisional classifier is:

```lambdapi
injective symbol BinaryProducts
  [C : Cat]
  (P : τ (Functor (Product_cat C C) C))
  : Grpd;
```

The final public name remains probe-controlled. `P` is an index, not a
recoverable field. A concrete user may supply a primitive or otherwise
selected whole functor. This keeps `×` from being defined indirectly through
point-level hom-precomposition operations.

The object product is read as:

```text
A ×_P B := P[(A,B)].
```

Do not assume that `P[(A,B)]` reconstructs `A` and `B`. A chosen product
functor in a general category need not be injective on objects. Stable owners
and rule LHSs must retain the explicit factors rather than repeating reducible
`P[(A,B)]` endpoint expressions in nondiscriminating slots.

### Projection transfors

Add stable whole observations:

```text
κ₁ : P ⇒ Product_projL_func(C,C)
κ₂ : P ⇒ Product_projR_func(C,C).
```

Then Došen's operations are off-diagonal transfor actions:

| Došen operation | Canonical emdash reading |
| --- | --- |
| `K₁ᵃ_A(f)` | `tapp1(κ₁,(f,id_A))` |
| `K₂ᵃ_A(f)` | `tapp1(κ₂,(id_A,f))` |
| `π₁_{A,B}` | `tapp0(κ₁,(A,B))` |
| `π₂_{A,B}` | `tapp0(κ₂,(A,B))` |

For example:

```text
f : B → C

tapp1(κ₁,(f,id_A))
  : P(B,A) → C.
```

This is exactly `K₁ᵃ_A(f)`. Consequently `(K₁ᵃ 1)` and `(K₂ᵃ 1)` should
first be obtained from existing strict transfor naturality. Do not add
product-specific duplicates unless a measured projection order loses the
canonical head.

### Pairing must be whole

A mere operation

```text
pair(f,g) : X → P(A,B)
```

would cap the structure too early. The preferred internal owner is a transfor
between Cat-valued represented families:

```text
Pair_{A,B} :
  Hom_C(-,A) × Hom_C(-,B)
    ⇒
  Hom_C(-,P(A,B)).
```

At each `X`, its component is the whole functor:

```text
Pair_{A,B}[X] :
  Hom_C(X,A) × Hom_C(X,B)
    ⊢
  Hom_C(X,P(A,B)).
```

Its object projection is `⟨f,g⟩`; its hom action retains higher cells between
pairs of arrows. This representation also makes Došen's distribution law

```text
⟨f,g⟩ ∘ h → ⟨f ∘ h,g ∘ h⟩
```

ordinary naturality of the pairing transfor. Generic naturality should own the
computation rather than a duplicated point-level rule.

The first probe should attempt this represented-family/`Transf` or native
`Functord` carrier using the existing pointwise Cat-valued family product. If
that carrier exposes an actual typing or runtime-matching blocker, the bounded
fallback is still a stable whole functor for every `X,A,B`, plus a stable point
projection. A bare point operation is not an accepted primary endpoint.

### Product-specific runtime rules

Once `K₁ᵃ`, `K₂ᵃ`, and pairing have canonical whole/point owners, the
genuinely product-specific rules are principally:

```text
K₁ᵃ_B(h) ∘ ⟨f,g⟩ → h ∘ f
K₂ᵃ_A(h) ∘ ⟨f,g⟩ → h ∘ g

⟨π₁,π₂⟩ → id_{P(A,B)}.
```

The naturality/distribution rules should first be inherited from generic
transfor computation. The two §6.4 derived normalizations may then be added at
the same stable heads if owner-position probes confirm their types and
orientations. Warning reports are classified diagnostic evidence, not an
automatic veto.

## Coherence Of The Extra Full Functor

Because `P` is extra structure beyond Došen's minimal triangular primitives,
it must not remain unrelated to them.

Its arrow action should agree with the triangular derived product arrow:

```text
P[(f,g)]
  =
⟨K₁ᵃ(f),K₂ᵃ(g)⟩
```

with the exact source-factor subscripts restored by typing. Initially prefer a
derived propositional path or narrowly validated proof-time comparison, not a
competing runtime expansion of generic `fapp1_fapp0(P)`. The stable triangular
product-map head should be available for computation while generic
functoriality of `P` remains intact.

The beta/eta laws should also derive the same agreement propositionally where
possible, rather than postulating an opaque comparison. As in the accepted
Monad multiplication-component diamond, a proof from a common ancestor may be
preferable to a second runtime normal form.

## Relation To Existing Selected Finite Limits

The current `BinaryProductPresentation(C,A,B)` remains the semantic
universal-property view. A later bridge should show that `P(A,B)`, `κ₁`, `κ₂`,
and pairing induce that existing weighted-limit presentation. Do not replace
or duplicate the weighted-limit owner.

Conversely, one isolated `BinaryProductPresentation(C,A,B)` does not by itself
assemble a coherent global functor `P : C × C ⊢ C`. The bridge from a whole
family of selected presentations to a full functor requires coherent object,
arrow, transfor, and higher action and is not inferred automatically.

The first implementation may therefore promote the triangular structure and
its internal laws before the semantic bridge, provided the lack of that bridge
is explicit in the ledger and no equivalence claim is made prematurely.

## Why `hom_precomp_*` Is Not The Primary Interface

Given a projection `π₁ : P(A,B) → A`, one can define:

```text
K₁ᵃ_B(h) = h ∘ π₁
```

through the existing stable precomposition functor. That is a useful semantic
or readability alias.

It is not the best runtime owner because it:

- unfolds the product-specific discriminator into generic composition;
- makes product beta depend on reassociation or commuting through
  precomposition;
- hides the direct analogy with `φᵃ = tapp1(counit,-)`; and
- risks retaining only point action rather than the full transfor/hom action.

Retain `hom_precomp_*` as a comparison target, not as the sole product
interface.

## Terminal Objects: Separate Follow-Up

Došen adds a chosen object `T` and arrows

```text
K_A : A → T
```

with the unrestricted equality:

```text
f : A → T  implies  f = K_A.
```

Neither of these is acceptable Lambdapi design:

```text
f → K_A
```

with a variable-headed rewrite LHS, or a bare-variable `unif_rule` identifying
every `f : A → T` with `K_A`.

The appropriate generic internal interface is instead:

```text
TerminalObject(C,t)
! : id_C ⇒ Const_t
```

together with a derived contraction path:

```text
terminal_unique(f) : f = !_A
```

for every `f : A → t`. Transfor naturality supplies the computational
canonical-arrow law:

```text
!_B ∘ h → !_A.
```

Arbitrary-arrow uniqueness remains propositional, ideally derived from
contractibility of every `Hom_C(A,t)` or from the empty weighted-limit
comparison. Do not add an opaque equality constant if retained contractibility
evidence can supply the path.

This gives a good semantic/internal terminal-object interface, but it does not
make every opaque arrow to `t` normalize at runtime as Došen's free syntax
does. That stronger claim would require a dedicated syntax/elaborator or a
strict terminal-hom representation.

The selected boundary is therefore:

1. implement enhanced triangular binary products first;
2. retain the existing per-pair finite-limit presentation as semantic
   authority;
3. keep terminal objects in `TBP-TERM-8`; and
4. when reopened, use a whole canonical-arrow transfor plus propositional
   uniqueness, not a catch-all rewrite or bare-variable unification rule.

## Implemented Result (2026-08-27)

The promoted one-way module is now:

```text
emdash3_2_triangular_binary_products.lp
```

The settled classifier name is `BinaryProducts(C,P)`. The module imports only
the active kernel; it does not import or mutate the rule-free finite-limit
module.

The whole structural boundary is exactly the reviewed enhanced design:

- `binary_products_proj1_transf` and `binary_products_proj2_transf` are whole
  transfors from `P` to the existing projection functors;
- `binary_products_pair_transf` is one whole transfor from the pointwise
  product of `Hom(-,A)` and `Hom(-,B)` to `Hom(-,P(A,B))`;
- its component is the stable whole `binary_products_pair_func`, so pairing
  retains ordinary hom action as well as the transfor's base action; and
- the stable point observations `binary_products_K1a_fapp0`,
  `binary_products_K2a_fapp0`, and `binary_products_pair_fapp0` are projection
  rungs of those whole owners, not independent semantic operations.

The owner probes established that stable point rungs are necessary. Once
product-object aliases and generic component projections normalize, a raw
`tapp0`/`tapp1` expression no longer retains all factors needed by a
subject-reducing beta LHS. The implemented projection ladder solves that at
the canonical post-alias shape. Every rule LHS matches `Struct_sigma`; no rule
discriminates on the reducible `Product_pair` definition, and the strict LHS
audit reports zero reconstructible compound slots.

Generic transfor structure still owns the underlying mathematics and retained
higher action, but it cannot by itself own every raw ordinary-composition
normal form after stable projection. The runtime module therefore includes
the narrow post-projection instances of:

```text
h o K1a(f) -> K1a(h o f)
h o K2a(f) -> K2a(h o f)
<f,g> o h  -> <f o h,g o h>
```

as well as both general `K` betas, both direct `pi_i o <f,g>` betas after
`K_i(id)` has normalized, eta, and the two selected section-6.4 reductions.
These are intentional instances of the generic laws at the stable runtime
surface, not competing mathematical axioms.

The extra whole functor `P` remains semantic. Its generic arrow action does
not rewrite to the triangular map. Instead:

1. two narrowly typed `unif_rule`s compare `pi_i o P[(f,g)]` with the
   corresponding stable `K_i` only at proof time;
2. typed `eq_refl` declarations validate those unifiers;
3. `binary_products_map_fapp0` is the transparent triangular map; and
4. `binary_products_map_path` explicitly traverses the common ancestor
   `<pi1,pi2> o P[(f,g)]`, using eta on the semantic leg and distribution plus
   the two projection paths on the triangular leg.

There is no direct map-level unifier, runtime `P` expansion, opaque equality
constant, or equality bridge. A runtime negative confirms that generic `P`
action and the triangular map remain distinct normal forms.

The first concrete semantic consumer is also active:
`binary_products_pair_unique_path` derives

```text
h = <pi1 o h,pi2 o h>
```

from the same eta/distribution common ancestor. Together with the computing
direct projection betas, this is the ordinary hom-level universal property.
Packaging this result automatically into the existing whole weighted-limit
`BinaryProductPresentation` requires a separate comparison/assembly tranche;
the current implementation neither duplicates that owner nor claims that one
per-pair presentation assembles a coherent global `P`.

The registered module currently has 32 declarations, 18 runtime rules, and 2
proof-time unification rules. The warning-enabled promoted-module inventory is
`1179/171` against the base kernel's `1116/159`: 63 additional critical-pair
reports and 12 replaceable-variable reports. The critical-pair families are
the expected opposite/terminal/specialized-composition and nested
beta/identity/section-6.4 projection orders around the ambient `comp_fapp0`
and stable pairing heads. The replaceable-variable reports occur at
factor-retaining projection, beta, and proof-time comparison patterns; the
strict audit independently reports no reconstructible compound slot. These
warnings are classified diagnostics, not vetoes. Focused module, central
diagnostic, and reviewer-example checks are green.

## Settled Module And Public Boundary

The selected one-way additive module is:

```text
emdash3_2_triangular_binary_products.lp
```

It imports the base kernel. A later automatic weighted-limit adapter may
import `emdash3_2_finite_limits.lp`; the computational owner itself does not.
The monolithic kernel and existing rule-free finite-limit module remain
unchanged.

The selected public computational names are:

```text
BinaryProducts
binary_products_proj1_transf
binary_products_proj2_transf
binary_products_proj1_fapp0
binary_products_proj2_fapp0
binary_products_pair_transf
binary_products_pair_func
binary_products_pair_fapp0
binary_products_K1a_fapp0
binary_products_K2a_fapp0
binary_products_map_fapp0
binary_products_map_path
binary_products_pair_unique_path.
```

The shorter classifier is unambiguous beside `BinaryProductPresentation`.
No restricted `K1a_func`/`K2a_func` duplicate is exported: their higher owner
is the full generic `tapp1_func` action of each projection transfor. The point
heads above are retained only where runtime discrimination survives.

## Implementation Sequence

1. Inventory exact current owners and create a focused signature/type probe for
   the indexed product functor and two projection transfors.
2. Probe the represented-family whole pairing transfor, its point whole
   functor, retained higher action, and source naturality/distribution route.
3. Select the minimum stable point heads required for product beta and eta;
   keep all reconstructible LHS slots inferred.
4. Promote the core projection betas and eta at ordinary `comp_fapp0` and
   pairing owners; test generic naturality first, then add only the measured
   post-projection instances needed after stable heads erase its raw pattern.
5. Probe and, if sound, promote the two §6.4 derived normalization rules.
6. Define the triangular product-map surface and derive/probe its agreement
   with generic `P` action.
7. Add a first concrete consumer or semantic bridge to the existing selected
   per-pair product layer.
8. Synchronize central diagnostics, reviewer example, catalog, authorities,
   warning classification, and strict LHS audit.
9. Run only scoped validation unless the user separately expands the
   aggregate boundary.
10. Leave `TBP-TERM-8` deferred unless its separate owner and acceptance
    contract are explicitly promoted.

## Side-Task Ledger

| Row | Status | Depends on | Deliverable and exit evidence |
| --- | --- | --- | --- |
| `TBP-PLAN-0` | complete | user review; response `0019`; baseline `2ef786c` | Dedicated living plan, source/PDF review, adjunction confirmation, exact Došen rule table, existing-product inventory, selected enhanced architecture, terminal boundary, Git authority, and persistent launch objective. |
| `TBP-OWNER-1` | complete | `TBP-PLAN-0` | Quiet owner-position probe and promoted `BinaryProducts(C,P)` index, whole projection transfors, canonical factor endpoints, and empty strict LHS audit. |
| `TBP-PROJ-2` | complete | accepted `TBP-OWNER-1` | Whole projection components, full generic off-diagonal higher action, stable `K1a`/`K2a` point rungs, canonical `Struct_sigma` projection rules, and measured post-projection naturality instances. |
| `TBP-PAIR-3` | complete | accepted `TBP-OWNER-1` | Represented-family whole pairing transfor, stable whole component functor, stable point pairing, retained base/hom action, and measured ordinary-composition distribution instance. |
| `TBP-RULES-4` | complete | accepted `TBP-PROJ-2`, `TBP-PAIR-3` | Both general `K` betas, both direct post-`K(id)` projection betas, eta, naturality/distribution, positive checks, and runtime noncollapse evidence. |
| `TBP-NF-5` | complete | accepted `TBP-RULES-4` | Both §6.4 `K1a`/`K2a` reductions are active in Došen's orientation; no reverse rule is installed. |
| `TBP-SEM-6` | complete | accepted `TBP-RULES-4` | Transparent triangular/semantic map terms, two narrow proof-time projection comparisons, explicit non-opaque common-ancestor map path, and runtime noncollapse. |
| `TBP-CAT-7` | complete first consumer; weighted adapter separate | accepted `TBP-SEM-6`; existing finite-limit layer | Computing projection betas plus `binary_products_pair_unique_path` give the ordinary hom-level universal property. The automatic adapter into `BinaryProductPresentation(C,A,B)` is a separate later assembly task; the existing owner remains untouched. |
| `TBP-TERM-8` | deferred/separate | stable binary-product core; explicit user promotion | Chosen terminal object, whole canonical-arrow transfor, propositional uniqueness from contractibility/empty limit, and scoped cut computation. No arbitrary-arrow runtime normalization claim. |
| `TBP-RECLOSE-9` | complete | all accepted nondeferred rows | Focused module/check/example checks, `1179/171` warning classification, empty strict LHS audit, 2,291-check/111-area strict catalog, plan/header/authority synchronization, source-TOC/active-reference lint, script syntax, and exact diff hygiene are green. Repository-wide health/CI aggregates were intentionally not run under the user's scoped-validation policy. |

At most one implementation row may be in progress. Failed probes update this
ledger and the decision table; they are not silently bypassed.

## Decision Ledger

| Decision | Status | Conclusion |
| --- | --- | --- |
| `D-TBP-001` | accepted | Use Došen's §6.2 triangular projection/pairing formulation as the runtime normalization language. |
| `D-TBP-002` | accepted | Enhance the minimal presentation with a whole selected product functor `P : C × C ⊢ C`; treat `P` as an index rather than a recoverable field. |
| `D-TBP-003` | accepted | Projection operations are stable whole transfors `P ⇒ π₁` and `P ⇒ π₂`; `K₁ᵃ`/`K₂ᵃ` are their off-diagonal actions. |
| `D-TBP-004` | accepted | Pairing must retain higher action. Prefer one represented-family transfor whose component is the whole pairing functor; a whole-functor-per-source fallback requires a measured blocker. |
| `D-TBP-005` | accepted with measured projection refinement | Generic transfor structure owns the mathematics and retained higher action. Stable projection erases the raw ordinary-composition pattern, so the runtime surface includes only the narrow post-projection `K1a`/`K2a` naturality, identity, pairing-distribution, and direct beta instances required by executable terms. |
| `D-TBP-006` | accepted | Ordinary ambient composition owns the projection beta cuts; pairing eta reduces toward identity. |
| `D-TBP-007` | accepted and implemented | Both §6.4 derived normalization rules are type-safe, terminating in the selected orientation, and covered by focused checks. |
| `D-TBP-008` | accepted | Generic `P` arrow action is semantic structure. Relate it propositionally or at proof time to the triangular derived product map rather than expanding it at runtime. |
| `D-TBP-009` | accepted | Existing `Product_cat`/`Product_cat_func` infrastructure is reused for the domain, projections, product-valued families, and concrete Cat instance; it is not itself the arbitrary-category product object operation. |
| `D-TBP-010` | accepted | Existing `BinaryProductPresentation` remains the per-pair weighted-limit semantic authority and is not replaced by the triangular runtime layer. |
| `D-TBP-011` | accepted | `hom_precomp_*` may expose readable/semantic `Kᵃ` aliases, but it is not the primary product discriminator. |
| `D-TBP-012` | accepted | Došen's free syntax and decision algorithm are metatheoretical orientation evidence, not an implementation requirement. |
| `D-TBP-013` | accepted terminal boundary | Do not install `(K)` as a variable-headed rewrite or bare-variable unification rule. Terminal uniqueness is propositional and should derive from retained contractibility/empty-limit evidence. |
| `D-TBP-014` | accepted sequencing | Binary products are the active tranche; terminal objects remain a separate deferred row. |
| `D-TBP-015` | accepted Git boundary | Work in the clean `2ef786c` worktree without new branch/worktree/commit or remote/integration mutations unless separately authorized. |
| `D-TBP-016` | accepted | Stable `K1a`/`K2a` points and the pairing component-functor/point ladder are justified discriminators projected from whole transfors; no restricted duplicate `K1a_func`/`K2a_func` is added. |
| `D-TBP-017` | accepted | Rule LHSs use canonical `Struct_sigma` after `Product_pair` normalization. Defined aliases never discriminate a promoted rule. |
| `D-TBP-018` | accepted | Projection after generic `P` action is proof-time coherence through two narrowly typed `unif_rule`s, validated by typed `eq_refl`; generic `P` action is not rewritten at runtime. |
| `D-TBP-019` | accepted | Product-map agreement and ordinary pairing uniqueness are explicit common-ancestor equality proofs, not opaque constants or direct map-level unifiers. |
| `D-TBP-020` | accepted warning classification | The promoted `1179/171` inventory adds `63/12` diagnostic reports over the `1116/159` base. Focused terms and negatives cover the intended routes; warnings are not a veto. |

## Required Positive Evidence

The promoted layer must check at least:

1. classifier and whole product-functor typing;
2. `κ₁`, `κ₂` whole transformation types;
3. projection components and full off-diagonal `K₁ᵃ`/`K₂ᵃ` functors;
4. a retained next hom action for pairing;
5. generic `K₁ᵃ` and `K₂ᵃ` naturality in Došen's orientation;
6. both projection-after-pairing betas;
7. distribution through generic pairing naturality or the accepted fallback;
8. pairing of the two projections reducing to identity;
9. the two accepted §6.4 derived normalization reductions;
10. a product-map term and its semantic/propositional agreement with `P`
    action;
11. the ordinary hom-level universal-property consumer, with any automatic
    weighted-limit adapter explicitly staged separately; and
12. retained higher action after all selected whole projections.

## Required Negative And Noncollapse Evidence

The promoted layer must also retain negatives showing that:

1. unrelated same-typed functors do not acquire `BinaryProducts` evidence;
2. unrelated transformations do not become `κ₁` or `κ₂`;
3. unrelated arrows are not treated as pairings;
4. `K₁ᵃ(id)` and `K₂ᵃ(id)` remain distinguishable when their types coincide;
5. no reverse accumulation/eta orientation is active;
6. generic `P` action is not erased to the triangular derived map at runtime
   unless a later explicitly accepted owner requires it;
7. one selected per-pair presentation does not imply global products; and
8. terminal uniqueness does not leak into this tranche.

## SOP And Probe Discipline

- Bind category, functor, structure, and endpoint indices once at a rigid
  owner; use `_` in reconstructible implicit positions.
- Do not repeat `P[(A,B)]`, `Product_pair(A,B)`, identities, or hom endpoints
  in LHS slots merely to guide inference.
- Prefer whole transfors/functors and stable point projections over capped
  arrow operations.
- Test every proposed naturality law against the generic `tapp1` rules before
  adding a product-specific copy.
- Test both reduction orders around projection beta, pairing eta, generic
  functoriality, product-category projections, `Op_cat`, and specialized
  categories.
- Treat warnings as diagnostic evidence. Reject a rule for subject reduction,
  cycles, false negatives, unacceptable conversion loss, or a better owner -
  not merely for increasing a warning count.
- Use a runtime rewrite only when selecting an intended runtime normal form.
  Use a narrowly typed `unif_rule` only for proof-time comparison between
  stable heads, validated with typed `eq_refl` and runtime-negative controls.
- Prefer a derived propositional path from common-ancestor reductions over an
  opaque equality constant.
- Keep disposable candidates under `tmp/probes/`; do not import them into
  tracked code.

## Scoped Validation

Inner-loop validation:

```bash
./scripts/check.sh emdash3_2_triangular_binary_products.lp
./scripts/check.sh emdash3_2_checks.lp
./scripts/check.sh examples/triangular_binary_products.lp
python3 scripts/audit_rule_lhs.py --strict \
  emdash3_2_triangular_binary_products.lp
```

Warning comparison:

```bash
EMDASH_LAMBDAPI_WARNINGS=1 \
  ./scripts/probe.sh emdash3_2_triangular_binary_products.lp
python3 scripts/warning_summary.py --strict-parse LOG
```

Metadata/hygiene after tracked promotion:

```bash
make catalog
python3 scripts/generate_check_catalog.py --check --strict
./scripts/lint_active_refs.sh
python3 scripts/lint_report_headers.py
python3 scripts/check_source_toc.py
git diff --check
```

Do not run repository-wide long aggregates merely for reassurance. Follow the
user's scoped-validation boundary and record any explicitly requested broader
gate separately.

## Scoped Closure Evidence

The completed first tranche records:

- focused exit 0 for `emdash3_2_triangular_binary_products.lp`;
- focused exit 0 for `emdash3_2_checks.lp` with 23 classified checks in the
  new area;
- focused exit 0 for `examples/triangular_binary_products.lp`;
- warning-enabled exit 0 and inventory `1179/171` against base `1116/159`;
- strict LHS audit `0` reconstructible compound slots across `0` unreviewed
  clauses;
- strict generated catalog: 2,291 checks across 111 mapped areas, zero legacy
  source-line tags, and zero unclassified checks;
- passing report-header, active-reference, source-TOC, shell-syntax,
  Python-compile, and `git diff --check` hygiene; and
- registration in the focused check and health-metrics source lists.

No repository-wide `make check`, `make examples`, `make health`, `make ci`, or
root aggregate was run. That omission is deliberate under the user's scoped-
validation instruction, not evidence of a failed gate. After closure, the
user explicitly authorized one local checkpoint commit of this tranche; no
push, merge, publication, history rewrite, branch/worktree cleanup, or other
integration mutation is authorized.

## Acceptance And Stop Conditions

Accept the first tranche only when:

- the product functor, projection transfors, and pairing owner all retain their
  intended whole/higher action;
- Došen's core reductions compute at ambient composition/pairing heads in the
  correct orientation;
- generic naturality owns every law it can own without a duplicate;
- pairing eta and the accepted §6.4 reductions terminate and preserve typing;
- the extra full `P` is coherently related to the triangular map without a
  competing runtime expansion;
- current product-category and selected-finite-limit owners remain intact;
- all new warning families are classified, not merely counted;
- the strict module LHS audit is empty or every retained exception is measured
  and annotated;
- focused checks, reviewer example, catalog, authorities, and scoped hygiene
  are synchronized; and
- no claim about global products, terminal objects, free syntax, or decision
  procedures exceeds the executable boundary.

Stop and revise rather than promote if:

- the pairing carrier loses source naturality or next hom action;
- a proposed point head duplicates a generic transfor projection without a
  consumer;
- product beta requires a broad associativity or outer-eliminator/inner-cut
  commuting rule;
- the full `P` action and triangular map create two unjoined runtime normal
  forms;
- rule typing requires repeated reducible product endpoints in implicit LHS
  slots;
- an attempted semantic bridge requires opacity or a bare-variable unification
  pattern; or
- terminal `(K)` can only be expressed by matching an arbitrary variable.

## Persistent Goal Objective

```text
Execute the living and evolving plan in
emdash2/reports/REPORT_EMDASH_V3_2_TRIANGULAR_BINARY_PRODUCTS_COMPUTATION_PLAN_2026-08-27.md.
Treat that plan as the authority for current rows, exact owner choices,
acceptance evidence, validation scope, and stop conditions. Implement the
enhanced triangular chosen-binary-product layer in Lambdapi: a selected whole
product functor, whole projection transfors, internally natural whole pairing,
Došen-oriented beta/eta and accepted derived normalization rules, explicit
semantic/propositional agreement with generic product-functor action, and the
ordinary hom-level universal-property consumer. Preserve the existing
selected finite-limit layer; keep its automatic adapter and the terminal-
object row deferred unless the plan explicitly promotes their separate
contracts. Evolve the plan
and active authorities with every accepted/rejected probe. Preserve baseline
2ef786c and unrelated work. Do not create branches/worktrees, commit, push,
merge, publish, release, rewrite history, delete branches, or remove worktrees
without separate authorization; run only the user-scoped validation recorded
in the plan.
```
