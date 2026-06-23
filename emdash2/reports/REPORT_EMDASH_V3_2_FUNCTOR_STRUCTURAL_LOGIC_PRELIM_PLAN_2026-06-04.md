# EMDASH v3.2 Functor Structural Logic Preliminary Plan

> Notation note: this is still a preliminary design plan. Use `REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md` as the current notation authority; early schematic code blocks in this report may use ASCII `->` as informal meta-notation before the canonical notation table.


Date: 2026-06-04

Plan-ID: EMDASH-V3-2-FUNCTOR-STRUCTURAL-LOGIC-2026-06-04
Depends-On: none
Supersedes: none
Side-Task-Ledger: none
Infinity-Codex-Origin: pre-infinity-codex
Infinity-Codex-Decision-Responses: none

Status: preliminary design note with first ordinary implementation slice
landed on 2026-06-10. The ordinary weakening/exchange/contraction layer is now
implemented in `emdash3_2.lp`; displayed/mixed-variance follow-up and
product/curry compatibility checks remain proposed.

## Implementation Note 2026-06-10

The first ordinary structural layer has been added under section 17 of
`emdash3_2.lp`, with regression assertions in `emdash3_2_checks.lp`.

Implemented:

```text
Const_func_func(A,B) : B ⊢ (A ⊢ B)
sym_func_func(A,B,C) : (A ⊢ (B ⊢ C)) ⊢ (B ⊢ (A ⊢ C))
diag_func_func(A,C)  : (A ⊢ (A ⊢ C)) ⊢ (A ⊢ C)
```

`Const_func_func(A,B)` is a defined alias through the existing
`const_section_func(A,B)` route. `sym_func_func` and `diag_func_func` are
stable primitive heads with object, capped-arrow, full hom-action projection
heads, and pointwise transfor-action beta rules.

Checked ordinary normal forms include:

```text
Const_func_func(A,B)[b] = Const_func(A,B,b)
Const_func_func(A,B)[p] = Const_transf(A,B,p)
sym(H)[b][a] = H[a][b]
sym(H)[b][p] = H[p][b]
sym(H)[q][a] = H[a][q]
sym(eta)[b][a] = eta[a][b]
diag(H)[a] = H[a][a]
diag(H)[p] = tapp1_fapp0(H[p],p)
diag(eta)[a] = eta[a][a]
```

Still deferred from this plan:

- product swap and product diagonal compatibility checks;
- product/curry presentations of exchange and contraction;
- displayed `Functor_catd_*_funcd` analogues;
- `Transf_catd`-level projections induced by displayed structural operations;
- higher `Product_cat_func` transfor action for semantic uncurry.

## Scope

This report consolidates the deferred B10 infrastructure issue that was first
noticed during the Sigma-laxity transport discussion. The preliminary
Sigma-laxity report has since been archived; this file is the active forward
reference for the structural-logic work.

The Sigma/laxity problem that exposed B10 is now settled by the displayed
internal-hom projection path:

```text
fdapp1_int_hom_func
  -> fdapp1_int_hom_fapp0
  -> fdapp1_int_cell
```

Therefore the structural-logic work below should not be implemented as a
Sigma-map workaround. It is a separate foundation layer for ordinary nested
functorial contexts, and later for displayed/mixed-variance contexts.

## Corrected Design Direction

The first plan over-emphasized product-context maps:

```text
swap  : A x B -> B x A
diag  : A -> A x A
weaken by product projections
```

Those maps are useful and computationally easy in the current product package.
For example, product swap is definable as a pair of product projections, and
product diagonal is definable as a pair of identity functors.

However, they should not be the conceptual owner of B10. The more fundamental
operations are structural operations on nested ordinary functor categories:

```text
weakening/constant:
  B -> (A -> B)

exchange/symmetry:
  (A -> (B -> C)) -> (B -> (A -> C))

contraction/diagonal:
  (A -> (A -> C)) -> (A -> C)
```

This layer should be usable without assuming product categories, curry, or
uncurry as primitive structure. Product/curry presentations should become
compatibility checks or derived comparison forms, not prerequisites.

## Correction About `Product_cat_func`

`emdash3_2.lp` already has the first arrow-action layer of internalized product
formation:

```text
rule fapp1_func Product_cat_func A A'
  -> Product_cat_fapp1_func(A,A')
```

and the adjacent projection ladder:

```text
Product_cat_fapp1_func(A,A')[G]
  -> Product_cat_fapp1_fapp0_functord(A,A',G)

Product_cat_fapp1_fapp0_functord(A,A',G)[B]
  -> Product_cat_fapp1_tapp0_func(A,A',B,G)
```

The final head computes:

```text
Product_cat_fapp1_tapp0_func(A,A',B,G)
  : A x B -> A' x B

(G * 1_B)[(x,y)] = (G[x], y)
(G * 1_B)[(p,q)] = (G[p], q)
```

The still-deferred part is the next hom-action level, where the functor `G`
itself varies by a transfor:

```text
theta : G => H
```

The expected component would be morally:

```text
(theta * 1_B)[(x,y)] = (theta[x], id_y)
```

This is the missing piece needed by the full transfor action of semantic
`uncurry_func_func`. It is not contradicted by the existing
`fapp1_func Product_cat_func` rule; that rule is one categorical dimension
lower.

## Existing Infrastructure

Already implemented ordinary ingredients:

```text
Const_func(b) : A -> B
Const_transf(p) : Const_func(x) => Const_func(y)
const_section_func(K,A) : A -> Pi_K const(A)

Functor_cat_func[A][B] = A -> B
Product_cat_func[A][B] = A x B
Product_pair_tele_func(A,B)

Eval_func(A,B) : (A -> B) x A -> B
curry_func_func(A,B,C)
uncurry_func_func(A,B,C)
tapp1_func / tapp1_fapp0
```

The key observation for weakening is that a functorial generalization of
`Const_func` is already present through `const_section_func`:

```text
const_section_func(A,B) : B -> Pi_A const(B)
Pi_A const(B)           -> Functor_cat A B
```

So, conceptually:

```text
Const_func_func(A,B) : B -> (A -> B)
Const_func_func[b] = Const_func(A,B,b)
```

can be a readable alias routed through the existing semantic owner.

## Proposed Ordinary Functor Structural Layer

### 1. Functorial Weakening / Constant

Add a readable package:

```text
Const_func_func(A,B) : B -> (A -> B)
```

Preferred implementation:

```text
Const_func_func(A,B) := const_section_func(A,B)
```

where the existing reduction:

```text
Pi_cat(Const_catd A B) -> Functor_cat A B
```

gives the intended codomain.

Required checks:

```text
Const_func_func(A,B)[b] = Const_func(A,B,b)
Const_func_func(A,B)[p] = Const_transf(A,B,p)
Const_func_func(A,B)[p][a] = p
Const_func_func(A,B)[p][q] = p
```

This should be an alias/defined symbol unless a probe shows that the existing
`const_section_func` route is too brittle for later consumers.

### 2. Exchange / Symmetry

Add a primary structural package for nested functors:

```text
sym_func_func(A,B,C)
  : (A -> (B -> C)) -> (B -> (A -> C))
```

Likely stable projection heads:

```text
sym_func(H)          : B -> (A -> C)
sym_fapp0_func(H,b) : A -> C
```

Core object computation:

```text
sym_func(H)[b][a] = H[a][b]
```

Core arrow computations should expose both ways of varying the two arguments:

```text
sym_fapp0_func(H,b)[p]
  = (H[p])[b]

sym_func(H)[q][a]
  = H[a][q]
```

More explicitly:

```text
p : a -> a'
q : b -> b'

sym(H)[b][p]
  : H[a][b] -> H[a'][b]

sym(H)[q][a]
  : H[a][b] -> H[a][b']
```

The transfor action should eventually compute pointwise:

```text
eta : H => K

sym(eta)[b][a] = eta[a][b]
```

This is the main reason to prefer a nested-`Functor_cat` primitive/stable
package over a product/curry definition: it is the direct structural operation
on functorial contexts and it should generalize to displayed contexts.

Do not initially define:

```text
sym(H) := curry(uncurry(H) o swap)
```

That equation is a later compatibility check, not the primary normal form.

### 3. Contraction / Diagonal

Add a primary structural package:

```text
diag_func_func(A,C)
  : (A -> (A -> C)) -> (A -> C)
```

Likely stable projection head:

```text
diag_func(H) : A -> C
```

Object computation:

```text
diag_func(H)[a] = H[a][a]
```

Capped arrow computation should use the existing off-diagonal transfor action:

```text
diag_func(H)[p]
  = tapp1_fapp0(H[p], p)
```

where:

```text
p    : a -> a'
H[p] : H[a] => H[a']
```

This avoids choosing one raw naturality-square route as primitive. The
off-diagonal component is already the intended owner for "move both endpoints"
in an ordinary transfor.

The transfor action should eventually compute pointwise:

```text
eta : H => K

diag(eta)[a] = eta[a][a]
```

### 4. Product Compatibility Checks

Product-level maps remain useful, but should be introduced only as comparison
or convenience infrastructure:

```text
Product_swap_func(A,B) : A x B -> B x A
Product_diag_func(A)   : A -> A x A
```

They are computationally straightforward:

```text
Product_swap_func(A,B) = (Product_projR_func(A,B), Product_projL_func(A,B))
Product_diag_func(A)   = (id_func(A), id_func(A))
```

Useful later compatibility checks:

```text
sym(H)
  == curry(uncurry(H) o Product_swap_func(B,A))

diag(H)
  == uncurry(H) o Product_diag_func(A)
```

These checks should be deferred until the direct nested structural layer is
stable. They should not block the implementation of `sym_func_func` or
`diag_func_func`.

## Displayed And Mixed-Variance Follow-Up

The ordinary `Functor_cat` layer will not be enough for the full emdash
development.

Analogous structural operations are expected around:

```text
Functor_catd
Transf_catd
```

The wording matters. The structural constructor should be owned by
`Functor_catd` or by the hom-action induced from such a constructor. The type
of a displayed operation will often be a `Functord_cat`, because maps between
Cat-valued families are displayed functors. That does not mean the operation is
conceptually "on `Functord_cat`" as a separate logical layer.

This is another reason not to make product maps the primary design. Product
operations do not directly express the binder, variance, and naturality
structure of mixed-variance displayed families.

Likely later design direction:

- first implement ordinary `Functor_cat` structural operations;
- then add pointwise/displayed analogues whose surface syntax is phrased in
  indexed binders;
- respect the `:^n` and polarity-flip conventions from the faithful surface
  syntax report;
- keep `Functor_catd` and `Transf_catd` variance explicit rather than routing
  through product encodings.

Concrete displayed signatures are deferred, but the likely policy is clarified
in the next section.

## Deferred Displayed/Fibred Context

This section records preliminary context for the displayed/fibration layer. It
is not part of the first implementation pass.

### Pointwise Fibred Products

A pointwise displayed product family is meaningful:

```text
Product_catd(E,D) : Catd K
Product_catd(E,D)[k] = Product_cat(E[k], D[k])
```

This should be the primary name for a fibrewise product family if/when needed.
It should have the expected pointwise object, hom, projection, and pairing
behavior by routing through the existing ordinary `Product_cat` machinery.

Avoid a primitive `Productd_cat` for now. The name is ambiguous among several
different constructions:

```text
Product_catd(E,D)             -- fibrewise product family
Pi_cat(Product_catd(E,D))     -- category of pairs of sections
Sigma_cat(Product_catd(E,D))  -- total category with objects (k,u,v)
```

For a fibred product of total categories over the same base, the likely
presentation is:

```text
Sigma_cat(Product_catd(E,D))
```

For pairs of sections, the likely presentation is:

```text
Pi_cat(Product_catd(E,D))
```

Later comparison checks may include:

```text
Pi_cat(Product_catd(E,D))
  ~= Product_cat(Pi_cat E, Pi_cat D)
```

but this should not be installed as a broad rewrite without a concrete
consumer and confluence/probe evidence.

### Structural Operations On `Functor_catd`

The displayed analogue of ordinary structural logic should be formulated around
`Functor_catd`, not around products and not as an unrelated operation on
`Functord_cat`.

Recall the current mixed-variance constructor:

```text
Functor_catd(A,B)[k] = A[k^-] -> B[k]

A : Catd(Op_cat K)
B : Catd K
Functor_catd(A,B) : Catd K
```

For exchange and contraction, the variance is straightforward:

```text
A,B : Catd(Op_cat K)
C   : Catd K
```

Then the displayed exchange operation should be a displayed functor whose
fibres are ordinary exchange:

```text
Functor_catd_sym_funcd(A,B,C)
  : Functord
      (Functor_catd A (Functor_catd B C))
      (Functor_catd B (Functor_catd A C))

Functor_catd_sym_funcd(A,B,C)[k](H)[b][a]
  = H[a][b]
```

Similarly, displayed contraction should identify two source-family slots:

```text
Functor_catd_diag_funcd(A,C)
  : Functord
      (Functor_catd A (Functor_catd A C))
      (Functor_catd A C)

Functor_catd_diag_funcd(A,C)[k](H)[a]
  = H[a][a]
```

The type is written as a `Functord` because it is a natural/displayed morphism
between Cat-valued families. The semantic owner remains `Functor_catd`.

### Displayed Weakening / Constant And Variance

There are two different possible readings of displayed weakening:

1. A natural displayed operation that sends a target-fibre object to the
   constant source-slot functor.
2. A pointwise mixed-variance functor family that literally has `B` as the
   source of an outer `Functor_catd` and as the target of an inner
   `Functor_catd`.

The first reading is the likely primary one:

```text
Functor_catd_const_funcd(A,B)
  : Functord B (Functor_catd A B)

A : Catd(Op_cat K)
B : Catd K

Functor_catd_const_funcd(A,B)[k](b)
  = Const_func(A[k^-], B[k], b)
```

For a base arrow `p : x -> y`, naturality uses the covariant action of `B`:

```text
B[p](b) : B[y]

Functor_catd(A,B)[p](Const(b))
  = B[p] o Const(b) o A[p]
  = Const(B[p](b))
```

So under this reading `B : Catd K` is correct. It does not need to be a family
over `Core_cat K`, because the operation should preserve directed transport in
the target family.

The second reading would look like a pointwise family:

```text
Functor_catd(B?, Functor_catd A B)
```

where the same `B` appears as an outer source and as the inner target. That
does create a variance problem: the outer source of `Functor_catd` must be a
family over `Op_cat K`, while the inner target is a family over `K`.

Using `Core_cat K` for this would make the variance conflict disappear only by
forgetting directed base arrows and keeping path/equality transport. That is
not the right default for emdash's directed displayed calculus. If a future
object-only or groupoidal comparison theorem needs such a core-restricted
version, it should be named separately and treated as a weaker comparison
surface, not as the primary displayed constant operation.

Preliminary conclusion: use the first reading for the main operation:

```text
Functor_catd_const_funcd(A,B)
  : Functord B (Functor_catd A B)
```

and keep `B : Catd K`.

### Structural Operations On `Transf_catd`

`Transf_catd` is meaningful, but it should not receive an independent logical
theory before the corresponding `Functor_catd` structural operations exist.

Current meaning:

```text
Transf_catd(A,B,FF,GG)[k] = FF[k^-] => GG[k]
```

Therefore an exchange or diagonal operation on `Transf_catd` should be the
hom-action of the corresponding structural operation on `Functor_catd`.

For exchange, semantically:

```text
eta : H => H'

sym(eta)[b][a] = eta[a][b]
```

For diagonal, semantically:

```text
eta : H => H'

diag(eta)[a] = eta[a][a]
```

The implementation policy should be:

```text
Functor_catd structural operation first.
Transf_catd operation = hom-action/projection of that operation.
Add stable Transf_catd projection heads only if the induced route is too
brittle or too expensive in a focused probe.
```

`Transfd_cat` then appears as the category of displayed transformations
between displayed functors, not as the primary owner of pointwise
mixed-variance transfor-family syntax.

## Placement Recommendation

For the first implementation attempt, avoid dependency churn.

Option A, conservative:

- add the new structural layer in a late section after the current ordinary
  transfor, product/evaluation, and generic helper infrastructure;
- this keeps `Const_transf`, `tapp1_func`, `tapp1_fapp0`,
  `const_section_func`, and product sanity checks available;
- if the rules become foundational and stable, move or split the section later.

Option B, cleaner but more sensitive:

- put `sym_func_func` and `diag_func_func` after the ordinary transfor
  off-diagonal layer, because they conceptually depend only on
  `Functor_cat`, `Transf_cat`, `tapp1_func`, and `tapp1_fapp0`;
- keep `Const_func_func` later as a defined alias through
  `const_section_func`.

Recommended first pass: Option A. The goal of the next implementation turn
should be to discover which rules typecheck and compute robustly, not to
perfect file organization.

## Probe And Validation Plan

Use a temporary copy first:

```bash
cp emdash3_2.lp tmp_functor_structural_logic_probe.lp
timeout 60s lambdapi check -w tmp_functor_structural_logic_probe.lp
```

Implement and validate in this order:

1. `Const_func_func` alias and beta assertions.
2. `sym_func_func`, `sym_func`, and `sym_fapp0_func` object/arrow assertions.
3. `sym_func_func` transfor action only after object/arrow rules are stable.
4. `diag_func_func` object and capped arrow assertions.
5. `diag_func_func` transfor action only after the capped arrow law is stable.
6. Optional product compatibility maps/checks.
7. Optional higher `Product_cat_func` transfor action if semantic uncurry
   needs it immediately.

Run after each accepted phase:

```bash
timeout 60s lambdapi check -w emdash3_2.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

## Rewrite Hygiene Notes

- Keep source and target category arguments implicit on rule LHSs unless they
  are the actual discriminator.
- Prefer stable projection heads for `sym` and `diag` stages rather than one
  large nested LHS.
- Do not add product/curry/uncurry folds for `sym` or `diag` until the direct
  nested functor computations are checked.
- Use projection/component assertions before broad equality assertions.
- If transfor action causes conversion blowups, keep it deferred and retain
  only object and capped-arrow computation.
- Do not reintroduce old Sigma/laxity probe-era heads such as
  `functord_laxity_precomp_*`, `functord_transport_fibre_*`, or
  `homd_id_canonical_triangle`.

## Current Recommendation

The likely solution is a small ordinary structural calculus for nested functor
categories:

```text
Const_func_func : B -> (A -> B)
sym_func_func   : (A -> (B -> C)) -> (B -> (A -> C))
diag_func_func  : (A -> (A -> C)) -> (A -> C)
```

`Const_func_func` should initially be a defined alias through the existing
constant-section infrastructure. `sym_func_func` and `diag_func_func` should be
treated as candidate primitive/stable heads, because later rules need to
recognize exchange and contraction directly and because product/curry encodings
are not the right foundation for displayed/mixed-variance analogues.

Product swap, product diagonal, and product weakening remain valuable
computational tests, but they are secondary.

## Postscript 2026-06-05: Shaped Turnstile And Indexed Hom Notation

This postscript consolidates the follow-up discussion after the first draft of
this report. It is intended as current notation and architecture guidance for
future v3.2 comments and surface-syntax planning. It does not change the
kernel implementation plan above by itself.

The main correction is that the displayed/fibred discussion should not suggest
that there is a separate "logic of the shape" for a `Functord` domain. A term
of shape:

```text
Functord E D
```

should be read as a generalized or shaped element of `D`, with shape `E`. The
shape is part of the quantification. It is not an explicit bound object
variable that may occur in the target expression. Formula-level operations
lift across this shaped quantification by ordinary displayed composition.

### Shaped Quantification

The preferred surface reading for:

```text
Functord_cat E D
```

is:

```text
z :^n Z ; E[z] ⊢ D[z]
```

where:

```text
E : Catd Z
D : Catd Z
```

This should be understood as an ordinary category expression. It can appear
anywhere a category is expected, for example:

```text
C ⊢ (z :^n Z ; E[z] ⊢ D[z])
```

which means:

```text
Functor_cat C (Functord_cat E D)
```

Do not insert an explicit dummy variable:

```text
z :^n Z ; e : E[z] ⊢ D[z]
```

for this constructor. The element `e` is not semantically available to the
target family `D[z]` in plain `Functord_cat E D`. If a later construction needs
the target to depend on an actual object of `E[z]`, that is a different
dependent/telescopic construction, most likely represented through a family
over `Sigma_cat E`.

The terminal-shape case should remain visibly Pi-shaped:

```text
Π (z :^n Z), D[z]
```

meaning:

```text
Pi_cat D
```

with the definitional explanation:

```text
Pi_cat D = Functord_cat (Terminal_catd Z) D
```

Avoid making:

```text
(z :^n Z) -> D[z]
```

the primary notation for `Pi_cat D`, even though that spelling is tempting by
analogy with proof-assistant dependent functions. In emdash notation, `Π`
should continue to signal the section category directly.

### Ordinary Functor Categories

The ordinary functor category should use the same turnstile idea without an
indexed prefix:

```text
A ⊢ B
```

meaning:

```text
Functor_cat A B
```

Since the kernel already has:

```text
Hom_cat Cat_cat A B ↪ Functor_cat A B
```

this can also be read as:

```text
Hom_cat Cat_cat A B
```

but the surface syntax should emphasize the functor/program category, not the
generic hom spelling.

The shaped turnstile is then the displayed version:

```text
z :^n Z ; E[z] ⊢ D[z]
```

meaning:

```text
Functord_cat E D
```

and the kernel justification is the existing canonical rewrite:

```text
Hom_cat (Catd_cat Z) E D ↪ Functord_cat E D
```

Thus:

```text
⊢
```

is the category-of-programs/functors notation, both ordinary and shaped.

### Ordinary And Indexed Homs

The hom notation should be kept distinct from turnstile notation.

Ordinary homs should use:

```text
a ->^C b
```

meaning:

```text
Hom_cat C a b
```

and most often, when the ambient category `C` is clear:

```text
a -> b
```

This keeps useful object-arrow declarations available, such as:

```text
f :^n x -> z
```

meaning:

```text
f :^n Hom_cat Z x z
```

with `Z` inferred from `x` and `z`.

The ambient category should use a superscript, not a subscript. Avoid:

```text
a ->_C b
```

because the underscore form is reserved for indexed/displayed homs.

Indexed or displayed homs should use a syntactically distinct operator:

```text
aa[z^-] ->_[z]^R bb[z]
```

meaning:

```text
Hom_catd R aa bb
```

where:

```text
R  : Catd Z
aa : Obj(Pi_cat (Op_catd R))
bb : Obj(Pi_cat R)
```

When `R` is clear, the shorter form is:

```text
aa[z^-] ->_[z] bb[z]
```

The underscore is part of the operator. A parser should distinguish `->_` from
plain `->` without doing semantic analysis. Superscript annotations such as
`^R` are "obvious explicit" ambient parameters, not implicit subscripts.

The current kernel gives:

```text
Hom_catd R aa bb [z]
  = Hom_cat (R[z]) (aa[z^-]) (bb[z])
```

so the notation is the displayed analogue of ordinary hom.

### `Functor_catd`: Two Coherent Surface Readings

There are two coherent notations for `Functor_catd`, and the distinction should
be documented rather than blurred.

The functor-category-flavored notation is:

```text
A[z^-] ⊢_[z] B[z]
```

meaning directly:

```text
Functor_catd A B
```

Here `⊢_` is its own operator, distinct from plain `⊢`. If an index is omitted
for readability, the operator should remain `⊢_`, not become `⊢`.

This spelling has the advantage that it mirrors:

```text
A ⊢ B
```

for ordinary functor categories. It also lets a parser distinguish the
displayed/mixed-variance functor-family constructor syntactically.

The generic indexed-hom spelling is:

```text
A[z^-] ->_[z]^Cat B[z]
```

meaning:

```text
Hom_catd (Const_catd Z Cat_cat) A B
```

which the kernel rewrites to:

```text
Functor_catd A B
```

via the existing rule:

```text
Hom_catd (Const_catd Z Cat_cat) X Y
  ↪ Functor_catd (Op_func X) Y
```

This spelling has the advantage that it presents `Functor_catd` as an instance
of the general indexed hom notation. It also makes clear that the ambient
displayed category is the constant family at `Cat_cat`.

Current recommendation:

- keep both readings in the design notes;
- use `A[z^-] ⊢_[z] B[z]` when emphasizing the functor-category type former;
- use `A[z^-] ->_[z]^Cat B[z]` when emphasizing the generic indexed hom
  constructor `Hom_catd`;
- do not silently collapse `⊢_` to plain `⊢`;
- do not use `->_` for ordinary homs.

The implementation may still elaborate either surface spelling to the stable
kernel head `Functor_catd A B` when that is the most useful normal form.

### `Transf_catd` And Indexed Transformation Notation

The generic indexed hom notation also explains `Transf_catd`.

For ordinary transformations:

```text
F => G
```

should remain the readable spelling for:

```text
Transf_cat F G
```

or equivalently:

```text
Hom_cat (Functor_cat A B) F G
```

For indexed transformations:

```text
FF[z^-] =>_[z] GG[z]
```

should be the readable spelling for:

```text
Transf_catd A B FF GG
```

and it can be understood generically as:

```text
FF[z^-] ->_[z]^(Functor_catd A B) GG[z]
```

meaning:

```text
Hom_catd (Functor_catd A B) FF GG
```

which the kernel rewrites to:

```text
Transf_catd A B FF GG
```

This keeps `=>_` as a readable specialization of `->_`, not as a separate
semantic principle.

### Structural Operations Lift Uniformly Over Shapes

The earlier discussion of weakening/constant should be simplified. There is no
separate phenomenon in which the usual logical operation modifies the ambient
shape `E` of a shaped quantification.

All three structural operations should be internal maps between formula
families:

```text
weak/const : B ⊢ (A ⊢ B)
exchange   : (A ⊢ (B ⊢ C)) ⊢ (B ⊢ (A ⊢ C))
diag       : (A ⊢ (A ⊢ C)) ⊢ (A ⊢ C)
```

In existing kernel notation, the ordinary versions are:

```text
Const_func_func(A,B)
  : Functor B (Functor_cat A B)

sym_func_func(A,B,C)
  : Functor
      (Functor_cat A (Functor_cat B C))
      (Functor_cat B (Functor_cat A C))

diag_func_func(A,C)
  : Functor
      (Functor_cat A (Functor_cat A C))
      (Functor_cat A C)
```

The displayed versions should be analogous maps between Cat-valued families:

```text
Functor_catd_const_funcd(A,B)
  : Functord B (Functor_catd A B)

Functor_catd_sym_funcd(A,B,C)
  : Functord
      (Functor_catd A (Functor_catd B C))
      (Functor_catd B (Functor_catd A C))

Functor_catd_diag_funcd(A,C)
  : Functord
      (Functor_catd A (Functor_catd A C))
      (Functor_catd A C)
```

Given an arbitrary shaped term, the lift is by ordinary composition. For
example:

```text
f : Functord E B
Functor_catd_const_funcd(A,B) o f
  : Functord E (Functor_catd A B)
```

and:

```text
g : Functord E (Functor_catd A (Functor_catd B C))
Functor_catd_sym_funcd(A,B,C) o g
  : Functord E (Functor_catd B (Functor_catd A C))
```

and:

```text
h : Functord E (Functor_catd A (Functor_catd A C))
Functor_catd_diag_funcd(A,C) o h
  : Functord E (Functor_catd A C)
```

So the only asymmetry is syntactic:

```text
B
```

is an uncompound source formula for weakening/constant, while exchange and
contraction start from compound source formulas:

```text
A ⊢ (B ⊢ C)
A ⊢ (A ⊢ C)
```

There is no need for a separate "shape-context logic" for this point. If later
we introduce maps between shapes, such as product-shape projections, swaps, or
diagonals, their effect on shaped terms should be ordinary precomposition along
displayed functors. That is a separate reindexing topic, not the owner of the
formula-level structural operations in this report.

### Variance Of Displayed Weakening

The variance conclusion remains:

```text
Functor_catd_const_funcd(A,B)
  : Functord B (Functor_catd A B)

A : Catd(Op_cat K)
B : Catd K
```

For a base arrow `p : x -> y`, naturality uses the covariant action of `B`:

```text
B[p](b) : B[y]

Functor_catd(A,B)[p](Const(b))
  = B[p] o Const(b) o A[p]
  = Const(B[p](b))
```

Therefore the primary operation uses `B : Catd K`, not
`B : Catd(Core_cat K)`. A core-restricted family is relevant only for a
different shape where the same family is forced to appear both covariantly and
contravariantly in a single construction. That should be treated as a weaker
comparison or groupoidal restriction, not as the default displayed constant
operation.

### Nested Telescope Stress Test

The notation should be tested on nested telescope expressions such as:

```text
k :^n K ; C[k] ⊢ (z :^n Z ; E[k^-;z] ⊢ D[k;z])
```

The order `k;z` is intentional. This is telescope-style notation, not a
product-base pair. It means:

```text
first specialize in k, then specialize the resulting Z-family in z.
```

Morally:

```text
C : Catd K
E : K^op -> Catd Z
D : K    -> Catd Z
```

and for each `k`:

```text
E[k^-] : Catd Z
D[k]   : Catd Z
```

so the inner expression is:

```text
z :^n Z ; E[k^-;z] ⊢ D[k;z]
```

meaning:

```text
Functord_cat (E[k^-]) (D[k])
```

The whole nested expression can be represented by a family over `K`:

```text
R := Hom_catd (Const_catd K (Catd_cat Z)) Ebar Dbar
```

where:

```text
Ebar[k^-] = E[k^-; -] : Catd Z
Dbar[k]   = D[k; -]   : Catd Z
```

Then:

```text
R[k]
  = Hom_cat (Catd_cat Z) Ebar[k^-] Dbar[k]
  ↪ Functord_cat (E[k^-]) (D[k])
```

and the whole expression is:

```text
Functord_cat C R
```

This is the important subtlety:

```text
z :^n Z ; E[k^-;z] ⊢ D[k;z]
```

uses plain shaped `⊢`, i.e. `Functord_cat` over `Z`. It is not itself the
indexed hom operator `->_` and not `⊢_`. However, as `k` varies, the family of
these inner categories is naturally built using `Hom_catd` over the ambient
category family:

```text
Const_catd K (Catd_cat Z)
```

So the outer variation is mixed-variance in the category of `Z`-families, while
the inner displayed quantification remains ordinary `Functord_cat`.

### Internal Constructor Packages

The nested telescope example should not be forced through
`Functor_catd_func`. The existing `Functor_catd_func(K)` internalizes the
specific mixed-variance functor-family constructor:

```text
Functor_catd(A,B)[k] = A[k^-] ⊢_[k] B[k]
```

It is not the primary owner of:

```text
k |-> Functord_cat (E[k^-]) (D[k])
```

For that, the conceptual owner is generic hom in the category `Catd_cat Z`,
expressed externally as:

```text
Hom_catd (Const_catd K (Catd_cat Z)) Ebar Dbar
```

It may still be useful to add internal convenience packages later:

```text
Functord_cat_func(Z)
  : Op(Catd_cat Z) ⊢ (Catd_cat Z ⊢ Cat)

Functord_cat_func(Z)[E][D]
  = Functord_cat E D
```

This should likely be definable from the existing ordinary internal hom
machinery, for example via `hom_int` at `Catd_cat Z`, with endpoint reductions
landing in `Functord_cat`.

Likewise, a later package:

```text
Transfd_cat_func(E,D)
  : Op(Functord_cat E D) ⊢ (Functord_cat E D ⊢ Cat)

Transfd_cat_func(E,D)[FF][GG]
  = Transfd_cat FF GG
```

could be useful for internalized transformation-category formation.

These packages are notation/projection infrastructure. They are not required
for the first implementation of ordinary `Const_func_func`, `sym_func_func`,
and `diag_func_func`, and they should not be allowed to delay that structural
logic pass.

### Substitution In Indexed Notation

The indexed operator leaves room for future substitution or pullback notation:

```text
A[z^-] ->_[z:=f]^R B[z]
```

or, in functor-category spelling:

```text
A[z^-] ⊢_[z:=f] B[z]
```

should mean that the displayed family:

```text
A[z^-] ->_[z]^R B[z]
```

or:

```text
A[z^-] ⊢_[z] B[z]
```

is pulled back along a base functor:

```text
f : K ⊢ Z
```

approximately:

```text
Pullback_catd (Hom_catd R A B) f
```

or in the `Functor_catd` case:

```text
Pullback_catd (Functor_catd A B) f
```

The exact formalization should wait until substitution notation is actively
needed, but the use of superscripts for ambient parameters and subscripts for
indices/substitutions is compatible with this future direction.

### Current Notation Table

The current likely replacement notation table is:

```text
a ->^C b
  := Hom_cat C a b

a -> b
  := Hom_cat C a b
     when C is clear

aa[z^-] ->_[z]^R bb[z]
  := Hom_catd R aa bb

aa[z^-] ->_[z] bb[z]
  := Hom_catd R aa bb
     when R is clear

A ⊢ B
  := Functor_cat A B

z :^n Z ; E[z] ⊢ D[z]
  := Functord_cat E D

Π (z :^n Z), D[z]
  := Pi_cat D

A[z^-] ⊢_[z] B[z]
  := Functor_catd A B

A[z^-] ->_[z]^Cat B[z]
  := Hom_catd (Const_catd Z Cat_cat) A B
   ↪ Functor_catd A B

F => G
  := Transf_cat F G

FF[z^-] =>_[z] GG[z]
  := Transf_catd A B FF GG

FF[z^-] ->_[z]^(Functor_catd A B) GG[z]
  := Hom_catd (Functor_catd A B) FF GG
   ↪ Transf_catd A B FF GG
```

Open choice for later parser/surface implementation:

- choose whether `A[z^-] ⊢_[z] B[z]` is the primary printed form for
  `Functor_catd A B`, with `->_[z]^Cat` kept as the generic-hom explanation;
- or choose whether `A[z^-] ->_[z]^Cat B[z]` is the primary printed form, with
  `⊢_[z]` kept as the functor-category-flavored alias.

Both are coherent. The important settled points are that `->` and `->_` are
syntactically distinct, ambient category/family parameters use superscripts,
plain `⊢` is not the same as `⊢_`, and `Π` remains the notation for
terminal-shape sections.
