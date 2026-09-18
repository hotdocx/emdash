# m— / emdash

`emdash2` is the active Lambdapi v3.2 mathematical development for
Functorial Type Theory. It treats categorical variation as computational
structure: categories behave as contexts, Cat-valued families as dependent
categories, reindexing as substitution, total categories as dependent sums,
and section categories as dependent products. Rewrite rules select runtime
normal forms; narrowly scoped unification rules compare useful proof-time
presentations.

The surrounding repository also contains a bounded TypeScript checker,
elaborator, text adapter, and browser reviewer. Those are executable
compilation and review layers. The Lambdapi kernel `emdash3_2.lp` and its
one-way extension modules remain the mathematical authority.

Book: [Functorial Type Theory](../docs/emdash-book.pdf), with
[archived book DOI](https://doi.org/10.5281/zenodo.21544186).
Code: [github.com/hotdocx/emdash](https://github.com/hotdocx/emdash).

Research qualification: the current whole-opposite and Sigma-Hom encodings
have known variance/soundness defects. Their diagnostics and deferred repair
are tracked in `AGENTS.md` and the current status report; passing local
checks is not a consistency certificate.

The [2026-09-18 reassessment](../docs/TYPESCRIPT_EMDASH_FOUNDATIONS_DEVOPS_AND_CONTINUATION_REVIEW.md)
collects the current foundational, DevOps and deferred-work boundaries,
including the completed action-profile branch awaiting integration.

## Headline results

The directed-inductive benchmark is an opaque walking-endomorphism category
`WalkingEnd` with a base object and a genuinely directed loop. A Cat-valued
code, contextual decoder, and directed normalization cell establish the
checked carrier equivalence

```text
Hom_WalkingEnd(*,*) ≃_Type Nat.
```

The concrete one-object category `BNat` is a separate model, not the
definition of `WalkingEnd`. The loop is neither collapsed to the identity nor
given an inverse.

Selected universal constructions use the same whole-owner discipline. The
monad layer retains whole extension while ordinary composition computes its
triangular cuts. `BinaryProducts(C,P)` supplies one whole product functor,
whole projections and represented-family pairing; `TerminalObject(C,t)`
supplies one whole canonical-arrow transfor and Hom contractibility. Their
thin Cartesian package adds no duplicate computation. On conventional slices,
chosen pullbacks and selected dependent products give

```text
Sigma_u |- u* |- Pi_u,
```

with actual whole adjunction transfors and mate action. A pullback cone is an
object of an internal slice Hom, not a separate record carrying two legs and a
commuting-square field.

The local-to-global development applies the same computational discipline to
geometry. It forms ordinary invertibility sieves before choosing representing
opens, represents affine instances pointwise by supplied localizations,
generates the big Zariski topology from finite unit-ideal families, and
constructs a fixed-site Cat-valued sheafification reflector by direct cover
completion. Assumption-explicit layers then expose affine schemes,
site-relative schemes, and a supplied projective line with its actual Laurent
overlap.

These are staged results, not one unrestricted completeness theorem. In
particular, constructed Cat-valued sheafification is distinct from the
supplied commutative-ring-valued structure-sheaf and locality capabilities
used by the current scheme presentations.

The additive/homological layer takes whole kernel/cokernel adjunctions
J⊣K and Q⊣I as primary. They construct whole H, the direct whole connecting
transformation δ, and canonical categorical exactness. The general native
snake retains all six terms without assuming its outer input maps monic or
epic; its comparison with the native LES includes the connecting-map sign.
Both constructions have checked displayed proof–CAS certificates on the
nonsplit polynomial-module example, reusing the selected presentations.
The [native final audit](../docs/TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_FINAL_AUDIT.md)
records the supplied model/normality/interpretation contracts and the deferred
large six-term comparison. The [consolidation review](../docs/TYPESCRIPT_EMDASH_CATEGORICAL_CORE_CONSOLIDATION_REVIEW.md)
maps the reusable adjunction, diagram, terminal-family, product and pullback
owners. Superseded model/connecting wrappers are retired, shared CAS inputs
and ordinary observations have independent owners, and whole contraction plus
ordinary terminal/initial adjunction interfaces are qualified. The whole Γ
classifier, its projection/triangle comparisons and H_family≅H_native∘Γ are
now qualified for the ordinary consumer, with the original model and inverse
data. Whole Hom-comparison data also yield η/ε and an ordinary Adjunction
introduction that preserves the native computation heads. The
[universality plan](../docs/TYPESCRIPT_EMDASH_CATEGORICAL_UNIVERSALITY_INVENTORY_AND_FOLLOWUP_REVIEW.md)
records their owners and checks; the
[higher terminality review](../docs/TYPESCRIPT_EMDASH_HIGHER_TERMINALITY_REVIEW.md)
keeps a general profile-sensitive upgrade separate.

## Where to start

- `emdash3_2.lp` is the import root and active computation authority.
- `AGENTS.md` is the mandatory Lambdapi editing and validation SOP.
- `reports/EMDASH_FOUNDATIONS.md` is the mathematician-facing guide.
- `reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`
  records exact owners, current boundaries, architecture, and selected
  baseline evidence.
- `reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`
  owns mathematical comment/example notation and records the bounded
  TypeScript text profile separately.
- `reports/INDEX.md` routes to living plans and dated decision records.
- `book/` is the reader-facing exposition; its evidence register points back
  to active declarations and checks.

Use `rg` from the import root or the current reports to locate a declaration.
The generated check catalog is useful for mechanical coverage, but it is not
the recommended mathematical reading order.

## Mathematical route

### Directed dependent structure

The core develops categories, functors, transfors, higher hom action,
Cat-valued directed families, reindexing, Sigma totals, Pi section categories,
dependent homs, mixed variance, and the projection ladders that keep higher
action iterable. Generic `fapp*` and `tapp*` owners carry identity,
composition, functoriality, and naturality; constructor-specific rules are
kept to justified projections or measured joins.

Equality-valued homs, truncation levels, dependent sums and products,
equivalence interfaces, and a restricted groupoidal core test how the directed
calculus meets ordinary type-theoretic equality. The walking-endomorphism
development is the principal directed-HIT normalization benchmark.

Computational homotopy truncation lands first in a classified category of
`n`-types and only then decodes to an ambient groupoid/type. Its restricted
dependent eliminator computes on point constructors, its map action is derived
through that eliminator, and its first concrete consumer proves
`Pi x:S1, ||base=x||_-1`. Eliminating those merely inhabited path fibres into
the set truncation gives `IsContr(||S1||_0)` while preserving the distinction
between contractibility evidence and a judgmental `Unit` normal form.

### Groupoidal realization and the Gray direction

The groupoidal Circle has judgmental point and dependent-loop computation,
with ordinary constant-family `ap` retained propositionally. Its universal
Integer cover proves the based-loop/Integer equivalence, and the concrete
WalkingEnd map identifies forward powers with the nonnegative Circle powers.
The two-ended WalkingArrow/Interval comparison tests endpoint variation.

For every category `C`, `Groupoidify(C)` has one whole unit
`C -> Path(Groupoidify(C))`, a recursor computing on represented points and
dependent first cells, and a whole target-side mapping equivalence

```text
Hom_Grpd(Groupoidify(C),G) ≃_omega Functor(C,Path(G)).
```

The current boundary does not yet construct source action,
`Groupoidify_func`, or the packaged adjunction with `Path_cat_func`.

Whole internal laxity also exposes the generic functor compositor and its next
action. Semantic strict functors are exact packages
`(F,IsStrictFunctor(F))`; these packages form the objects of the selected
`GrayHom_lax` profile while reusing the ambient transfor tower. No second
strict-functor code grammar or parallel compositor is introduced. One right
closure yields a coevaluation-derived walking square and a checked nonidentity
oriented interchanger. Its checked direction becomes the native lax-square
direction after exchanging the two coordinate roles.

Every transformation now has an iterable whole graph
`B -> LaxArrow_cat(C)`. Objects compute to its components; capped arrows
compute to the standard square with literal `F[g]` and `G[g]` sides and a
filler extracted from the existing post/left internal action. Generic
`fapp1_func` retains the next whole action. The identity instance knowingly
overlaps the historical global strict-functor cut; the intended graph beta is
kept under the prototype policy pending profile-local migration. For strict
endpoint packages, the public graph is paired with supplied
`IsStrictFunctor` evidence about its already-extracted compositor; carrier and
evidence projections compute, without a graph-specific identity rule.
Fixed-bracketing positive right-Gray cubes and one Nat-recursive
object decoder then give

```text
StrictFunctor(GrayCubePos_R(n),C)
  -> Obj(CubicalLevel(C,succ n)).
```

The index `n` denotes geometric dimension `n+1`. Dimensions one through three,
the selected `I tensor_R I` interchanger direction, four square edges, six cube
faces, and arbitrary-variable-dimension recursion are checked. The mirror
closure, tensor unit/associativity/symmetry, inverse decoder, mapping-category
equivalence, full Crans--Gray monoidality, and global migration of historical
strict endpoint cuts remain deferred.

### Two-sided dependent hom and the intrinsic semicubical nerve

The one-sided `homd_` calculus now has a transparent two-sided companion. For
`E : K1^op -> Catd(K2)`, `homdc_` transports a source along the second side
and a target back along the first side, then takes their hom in the common
cross fibre. At `E=hom_int(id_C)` its objects are the familiar directed-square
2-cells

```text
b o u ==> v o a.
```

Both side-arrow actions remain whole. A nested-Sigma total packages a
fixed-vertical-boundary square as `(a,(b,alpha))`; top, bottom, left, and right
are whole observations. The next hom has two endpoint squares and four side
faces, with the fixed left/right sides computing to identities. This is a
computational bounded test retained beside the fully varying construction.

The fully varying layer is derived from the same primitives. Define

```text
EdgeFamily_E[x1] = Sigma(x2:K2), E[x1][x2]
D_E              = Op_catd(EdgeFamily_E)
homdc_int(E)      = homd_int(id_D_E)
homdc_total_cat(E)= Op(Sigma(x1:K1^op),D_E[x1]).
```

The canonical target-edge-first projection of `homdc_int` exposes the
remaining `(b,alpha)` Sigma-Hom data. At `E=hom_int(id_C)`,
`LaxArrow_cat(C)` makes every arrow of `C` an object and every
variable-boundary lax square `(a,(b,alpha))` an arrow. `CubicalArrow_cat(C)` is
now a transparent readability alias, not a primitive category. Source and
target are whole derived functors. Generic nested-Sigma identity/composition
compute their expected endpoint boundaries; the older readable paste terms no
longer compete as runtime normal forms. A readable pseudofunctor profile
supplies fixed-forward `OmegaEquivAlong` for the one readable cell derived
from `fapp1_compositor`; `CubicalArrow_func` uses that cell forward and derives
its pre/right reverse adjustment from a selected native inverse. The readable
source ladder is a documented adapter for the temporary global strict cut and
does not claim noncollapsed lax endpoints.
Genuine Nat recursion gives

```text
CubicalLevel(C,0)   = C
CubicalLevel(C,n+1) = CubicalArrow(CubicalLevel(C,n)).
```

The matching internal index is `SemiCubePlus_cat`. Its morphisms are
set-classified `{L,R,*}` words: `L/R` fix a coordinate and star retains it.
Structural substitution owns composition, and the native action is

```text
action(L f) = action(f) o source
action(R f) = action(f) o target
action(* f) = CubicalArrow_func(action(f)).
```

One whole functor `SemiCubePlus_cat^op -> Cat_cat` packages these levels and
actions. Its object beta computes; its arrow observation is a typed path so it
does not compete with generic strict functor cuts. A recursive finite-family
frame exposes `2n` immediate faces: new source/target followed by the
star-lifted older faces. Thus a square has four independent edges and a cube
has two endpoint squares plus four independent side squares. Degeneracies,
connections, Kan operations, and the independent `homd_parameter_func`
comparison remain future work, not prerequisites of this native semicubical
nerve.

Yoneda also supplies the standard combinatorial semicube:

```text
StandardSemicube(n)[p]
  = Hom_{SemiCubePlus}(p,n)
  = Path_cat(CubeFaceCode(p,n)).
```

The whole Hom action of the native nerve decodes every such face into the
corresponding restriction functor, and
`standard_semicube_native_decode_path` compares it with the computing
`{L,R,*}` interpreter at arbitrary `p,n`. Import `emdash3_2_cubical.lp` for
the complete rule-free cubical facade.

The direct Yoneda object slice additionally sends a native cube to its coherent
face family and evaluates at the identity face; the beta is the existing whole
nerve identity path, not a full eta equivalence. The independent Gray decoder
above supplies the geometric/computadic object reading. These are complementary
adequacy statements, not an asserted equivalence of mapping categories.

### Internal semisimplicial substrate

The augmented injective simplex category is now internal and computational.
Set-classified skip/keep face codes own identity and composition;
`SemiDeltaPlus_cat` packages them as locally discrete hom categories.
Iterated joins give ordinary directed simplex shapes, while Yoneda gives the
distinct representable semisimplices. The selected two-simplex boundary and
three horns are ordinary sieves, so their inclusions and mapping-category
restrictions reuse the existing presheaf/sieve machinery.

Maps out of a directed join now have a first-stage internal observation
interface: both branch restrictions are whole functors, and the cross cell is
obtained by applying the target functor to the existing internally natural
join cross. Its `(left,right,cross)` package is intentionally object-level;
the category of coherent-square morphisms and join eta remain explicit work
rather than an external naturality record.

Every nonempty skip/keep face code now also has a variable-dimension geometric
realization. Raw recursion sends `skip` to the left join inclusion and `keep`
to the whole join map, then descends through the public set-classified code.
Identity and composition of those realizations remain a scoped join-
uniqueness boundary, so this decoder is not yet presented as one whole
semisimplicial shape functor.

The dependent-cell side is recursive through the existing calculus rather
than a second simplex record. A triangle is the `Hom(Sigma)` total of one
`homd_` family; applying a displayed functor gives the first hom action of
`Sigma(FF)`, and its next action maps `(κ,λ)` to the same base cell together
with `fdapp1_int_hom_fapp0(...,λ)`. The ordinary dimension-two specialization
is the active functor compositor, and another higher action remains iterable.
The same owner stays noncollapsed for a generic map, is constrained by the
selected semantic `IsStrictFunctor` property at the binary compositor, and
becomes invertible at both triangle and tetrahedron components when the target
fibres are path categories.

Represented composition now supplies the first non-circular groupoidal source
coherence for that recursion. The generic compositor of `Rep_catd_func` is a
whole displayed transformation with a retained next action. In
every directed `Z`, typed stable-owner comparisons expose it as
`(h o g) o f -> h o (g o f)` without invoking `comp_assoc`; in `Path_cat(A)`
the cell is invertible and its proof term remains distinct from the direct J
associator. For a constructor-visible three-edge Sigma spine, the same cell
projects to the native `(kappa,lambda)` tetrahedron, maps through the existing
dependent action with the expected base/fibre computation, and retains one
further hom action. No rewrite, unifier, or Sigma eta is added.

The resulting native finite presentation is now explicit through dimension
three. After choosing the initial lower face, every successor classifier is a
`PathOut_cat`: edges are objects of `PathOut_C(x0)`, triangles are objects of
the next PathOut category at edge `e01`, and tetrahedra are objects of the
next one at triangle `t012`. The derived `pathout_map_func` combines the
existing displayed hom action, Sigma map, and pullback-total map, so ordinary
functors act on this whole tower and retain another hom action. Constructor-
visible dimension-two and dimension-three terms expose all boundary faces and
the top filler; one typed endpoint conjugation moves the final represented
cell to literal composition before its last Sigma projection. These are
flagged classifiers, not yet one global category of all `n`-simplices or an
ordinal/dependent equivalence.

Dimension four validates the same recursion one level further. Its classifier
is `PathOut` at the flagged tetrahedron and its whole map is another
`pathout_map_func`. A visible object exposes tetrahedral faces 0124 and 0134;
the typed readable Hom(Sigma) split then exposes face 0234 and one remaining
dependent frame containing face 1234 and the top filler. A full-constructor
negative shows that frame must carry recursively normalized lower readable
views; it does not justify a dimension-specific eta or endpoint rewrite.

The corresponding intrinsic code grammar is now active. A raw code is indexed
by `(C,n,K)`, where `K` is already its decoded category. The zero constructor
has `K=C`; one successor flag `x : Obj(K)` has
`K'=PathOut_K(x)`. The public package existentially hides `K` and decoding is
its first projection. Codes selected from the visible flags recover dimensions
zero through four judgmentally. `DependentSimplexFaceRef` is only the existing
`FaceCode(succ p,succ n)`, while `DependentSimplexEndpointView` carries formal
and readable endpoints with their typed equality.

The mapped decoder is also active. For `F : C -> D`,
`dependent_simplex_code_map` recursively maps the previous code and its flag,
returning both a target code and a whole functor between decoded categories.
At successor codes that functor is the existing `pathout_map_func`; the
selected dimensions therefore reduce to `dependent_simplex1_map` through
`dependent_simplex4_map`, retain another `fapp1_func`, and do not duplicate
the native action.

`dependent_simplex_face` decodes the existing nonempty `FaceCode` against a
flag code and returns a target code plus a whole face functor. Its three
successor cases are constant action on the fixed flag, target projection for
`keep(skip ...)`, and `pathout_map_func` for `keep(keep ...)`. Together they
compute faces 01, 02, and 12 of a visible triangle and retain generic hom
action. Direct and sequential opaque whole functors are not collapsed by a
new extensionality rule.

`emdash3_2_dependent_simplex_ordinal_adequacy.lp` records the low-dimensional
ordinal comparison. Dimension zero has whole evaluation/constant functors;
dimension one observes an ordinal walking-arrow map as its native edge, and
generic join-eliminator point betas make the three restricted triangle edges
share vertices. The continuation is now constructive in dimension two.
`emdash3_2_join_generator_compatibility.lp` derives the whole walking-generator
beta from profunctor reindex, join-extension, and observation/action paths.
`emdash3_2_dependent_simplex_ordinal_filler.lp` uses one profiled source
join-cross naturality cell to construct the source filler, maps the resulting
native simplex under every ordinal triangle `H`, and projects the canonical
filler. `ordinal_dependent_simplex2_observe_canonical(H)` therefore needs no
filler argument and retains another hom action. The dimension-three
continuation `emdash3_2_dependent_simplex_ordinal_dimension3.lp` realizes the
join comparison as a shaped fixed-source `PathOut` map, extracts its whole
post-laxity top cell, and packages one native source tetrahedron. Mapping that
source by `dependent_simplex3_map(H)` gives an unconditional observation for
every ordinal tetrahedron, with faces 012, 013, 023, and 123, the dependent top
component, and one further hom action. A global mixed-variance category and an
unqualified mapping-category equivalence remain unclaimed.

The reusable successor mechanism is separate from that ordinal example.
`emdash3_2_pathout_transformation_reframing.lp` connects the formal pre/right
internal-action source to its constructor-visible Sigma source through typed
paths, and `emdash3_2_pathout_transformation_lift.lp` lifts any ordinary
transformation to one whole transformation between outgoing-path functors at
a fixed source. Its components reuse the existing pre/right laxity cell, one
constructor beta computes, and another hom action remains iterable; no core
endpoint rule or unifier is added.

`emdash3_2_ordinal_join_pathout_successor.lp` specializes this mechanism to
the identity ordinal join `A * 1` for arbitrary `A`. The dimension-four
continuation `emdash3_2_dependent_simplex_ordinal_dimension4.lp` applies two
successive lifts at the canonical edge and triangle, then evaluates at the
canonical tetrahedron. This constructs one native four-simplex, maps it under
every `H : Functor(Delta[4],C)`, exposes all five tetrahedral faces through the
existing `FaceCode` action, retains the native recursive top component, and
keeps another hom action. No opaque filler or simplex-specific conversion is
added.

`emdash3_2_dependent_simplex_ordinal_recursive.lp` internalizes the same
pattern at variable dimension. Existing raw intrinsic flag codes drive a
stage carrying the target code, two whole maps, and their transformation; the
one-flag case is the identity-join comparison and every later flag applies
`pathout_transf_lift`. A genuine Nat recursion constructs
`OrdinalDependentSimplexSource(n)`, while arbitrary-target observations and
nonempty faces reuse the existing mapped decoder and `FaceCode` action.
Selected computations through dimension four and another higher action are
checked.

For a path groupoid, one bounded algebraic 2-nerve computes the inner filler
by path composition and the outer fillers by inverses, with J-derived section
laws and iterable Path action. Categorical decalage is restriction along the
vertex-appending index shift; both the base and cone tip are whole
transformations, and fixed-tip cone fibres have a whole Path-map to their
opposite bases. Generic dimensions, degeneracies, an all-dimensional Kan
theorem, and assembly of those levelwise fibres into a whole displayed
semisimplicial object remain explicit boundaries.

### Representability and profunctors

Yoneda, represented hom action, dependent hom, Cat-valued profunctors,
selected tensor/co-Yoneda interfaces, weighted universal properties, and
opposite normalization share one comparison discipline. Synthetic arrow
induction is built from the total category of outgoing arrows; on the
composition motive its checked normal form is ordinary composition.

### Presheaves, sieves, and sites

Cat-valued presheaves are the contravariant specialization of the existing
family calculus. Ordinary sieves are pointwise-subterminal higher sieves, and
their pullback is existing family reindexing. Grothendieck topologies are
presented directly on ordinary sieves.

Witness-rich generator families produce the least accepting topology as an
intersection of all accepting Grothendieck topologies. This construction has
the expected universal property, but it is not an inductive derivation syntax
or a decision procedure for coverhood.

### Direct cover completion and sheafification

For a fixed site, matching families and sections are whole hom-categories.
Direct cover completion is a categorical-HIT-style construction with a whole
unit, recursive cover-indexed glue, and silent coherence. Locality,
functorial recursion, and uniqueness assemble a reflector

```text
a : Psh_Cat(K) ⇄ Sh_Cat(K,J) : i
a ⊣ i.
```

This is constructed fixed-site Cat-valued sheafification. It does not yet
supply a commutative-ring lift, left exactness, slice/base-change semantics, or
a general theorem that the later structure sheaves arise from this reflector.

### Constructive algebra and affine geometry

Commutative rings have set-valued carriers and structured maps. Products,
finite sums and dot products, polynomial algebras, and localization are
developed by universal property rather than by committing to one quotient or
fraction syntax. Special localizations at a unit, at zero, and at an
idempotent give concrete normalization tests.

For a section `s` of a ring-valued presheaf, invertibility after restriction
defines the ordinary sieve `D_U(s)`. In the affine case, a supplied
localization represents `D_R(f)` pointwise at every test ring. Finite
unimodular families generate the direct big-affine Zariski topology, while the
coordinate presheaf retains computing restriction along selected charts and
overlaps.

### Affine schemes, site-relative schemes, and the projective line

An `AffineSchemePresentation` combines the exact big-affine site with a
supplied reflective commutative-ring structure-sheaf presentation and supplied
whole localization locality. A global-first site-relative scheme retains one
global ringed object, a covering sieve generated by selected affine charts,
and topology-local ring behavior. Restrictions and overlaps are inherited
from the global presheaf rather than duplicated as atlas fields.

`SuppliedProjectiveLinePresentation` retains such a global scheme, its actual
selected overlap, and a whole Laurent-coordinate comparison. It is not a
construction from arbitrary charts. The active library does not yet define a
representation-independent category of schemes, graded localization,
degree-zero parts, `Proj`, general projective space, or non-affineness.

## Computation and authority boundaries

- The native TypeScript CAS and categorical programs are a distinct
  computation layer. Formal reification/adoption does not turn heavyweight
  algebra algorithms into kernel conversion or infer universal laws from
  finite equations.
- A runtime rewrite chooses an operational normal form. A proof-time
  unification rule may compare two stable presentations without orienting
  evaluation.
- One-way modules extend the kernel without becoming prerequisites of earlier
  layers. Their imports define the active authority order.
- Capability packages state supplied hypotheses explicitly. A readable
  projection from such a package is not evidence that the package itself was
  constructed.
- Positive checks are paired with negative or non-collapse checks where a
  tempting stronger computation would be unsound.
- The root TypeScript implementation compiles a reviewed surface to explicit
  Core and checks a bounded transferred profile. It is not a second source of
  mathematical truth.

The retired D0/D1 compatibility layer and obsolete v2/v3.1 scratch material
are not active interfaces.

## Quick start

Prerequisites are Lambdapi on `PATH` and Node 22.13 or newer. From a fresh
worktree, initialize the shared pnpm workspace:

```bash
../scripts/bootstrap-worktree.sh
```

Run bounded formal checks from this directory:

```bash
EMDASH_TYPECHECK_TIMEOUT=90s make check
make examples
make ci
```

Useful focused maintenance commands are:

```bash
scripts/probe.sh tmp/probes/name.lp
make check-warnings
make warning-summary
make audit-rules
make catalog
make toc
make health
```

Follow `AGENTS.md` before changing Lambdapi. In particular, probe owner
positions before adding a rule, compare warnings against the recorded
baseline, and use the bounded checker wrapper. The default is 90 seconds
per target; selected heavy native consumers have documented measured resource
profiles. Refresh generated catalog/health artifacts only through their owners.

The current groupoidal vertical slice includes a successor-localized Integer,
an opaque Circle HIT with checked `Hom(Circle,Circle) ≃ Integer`
encode--decode, the nonnegative WalkingEnd-to-Circle comparison, and coherent
product-path transport in both coordinate orders. It now also realizes the
generic `path_map_func` compositor as an invertible equality between paths,
with its familiar `eq_ap`/`eq_trans` reading and one retained higher action.
The classified truncation reflector, Circle mere connectedness, and
contractibility of its set truncation complete the next checked HoTT slice.
Category-indexed `Groupoidify(C)` now has a whole computing unit and extension,
an arbitrary-source mapping-object equivalence, an explicit nonidentity
compositor with retained higher action, and a derived
`TypeEquiv(Groupoidify(WalkingArrow),Interval)`. Source functoriality,
`Groupoidify_func`, and its adjunction with `Path_cat_func` remain later
interfaces. The source modules and reviewer examples are listed in the August
14--18 groupoidal plans.

## Functorial Type Theory book

*Functorial Type Theory: Univalent Foundations for Mathematics* is authored as
chapter-sized Markdown under `book/`. Its third mathematical spiral develops
presheaves and sieves, sites and descent, direct cover sheafification,
constructive commutative algebra, affine geometry centered on `D_R(f)`,
site-relative schemes, and the supplied projective line. Its fourth spiral
returns through paths, Circle/Integer, generic groupoidification, and a
profiled Gray interchanger. Chapter 29 begins a fifth spiral: injective faces,
join-built ordinals, and iterated outgoing paths construct canonical dependent
simplexes in variable dimension while preserving the exact
mapping-category and degeneracy boundaries.

Chapter 30 adds selected Cartesian and indexed structures. In local edition
0.9.2-dev, Chapters 12, 30 and 31 explain whole Hom-data extraction and ordinary
Adjunction introduction, primary terminal-family universality, Γ and the
whole family/global H comparison, native K/Q/H/δ, the general snake and
its LES comparison, and both nonsplit displayed certificates. The higher
terminality review records the profile-dependent refinement boundary.
The opening material and bibliography give the
book DOI and code repository; the archived publication is distinct from this
local development edition.

From the repository root:

```bash
./scripts/pnpmw run book:assemble
./scripts/pnpmw run book:check
./scripts/pnpmw run book:render
./scripts/pnpmw run book:release
```

`book/book.json` owns source order and metadata, and `book/evidence.json`
maps checked prose claims to active declarations and reviewer evidence.
`print/public/emdash-book.md` is generated and must not be edited by hand.
See `book/README.md`, `book/STYLE.md`, and `print/README.md` for the
authoring, attribution, release, and renderer contracts.

## Status

Emdash v3.2 remains a research implementation. It does not claim a finished
proof-assistant surface, global normalization or confluence, a complete weak
omega-category metatheory, systematic groupoidal specialization for every
former, arbitrary dependency/variance elaboration, representation-independent
schemes, or a
general computational univalence theorem. The living reports state each
boundary at its owning layer; dated reports preserve why earlier candidates
were accepted, qualified, or retired.
