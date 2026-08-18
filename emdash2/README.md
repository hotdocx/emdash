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
compilation and review layers. The Lambdapi sources imported by
`emdash3_2.lp` remain the mathematical authority.

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

## Where to start

- `emdash3_2.lp` is the import root and active computation authority.
- `reports/EMDASH_FOUNDATIONS.md` is the mathematician-facing guide.
- `reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`
  records exact owners, current boundaries, warning evidence, and the
  mandatory kernel workflow.
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
action. Computational strict-functor codes form the objects of the selected
`GrayHom_lax` profile while reusing the ambient transfor tower. One right
closure yields a coevaluation-derived walking square and a checked
nonidentity oriented interchanger. The mirror closure, tensor coherence, full
Crans--Gray monoidality, and global migration of historical strict endpoint
cuts remain deferred.

### Internal semisimplicial substrate

The augmented injective simplex category is now internal and computational.
Set-classified skip/keep face codes own identity and composition;
`SemiDeltaPlus_cat` packages them as locally discrete hom categories.
Iterated joins give ordinary directed simplex shapes, while Yoneda gives the
distinct representable semisimplices. The selected two-simplex boundary and
three horns are ordinary sieves, so their inclusions and mapping-category
restrictions reuse the existing presheaf/sieve machinery.

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
baseline, keep every Lambdapi invocation within 90 seconds per target, and
refresh generated catalog/health artifacts only through their owners.

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
site-relative schemes, and the supplied projective line.

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
