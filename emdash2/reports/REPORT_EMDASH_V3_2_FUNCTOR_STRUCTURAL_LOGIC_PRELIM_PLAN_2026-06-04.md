# EMDASH v3.2 Functor Structural Logic Preliminary Plan

Date: 2026-06-04

Status: preliminary design note. No implementation has been attempted in
`emdash3_2.lp` from this report yet.

## Scope

This report consolidates the deferred B10 infrastructure issue from
`reports/REPORT_SIGMA_LAXITY_TRANSP_DISCUSSION_PRELIM_2026-06-03.md`.

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
