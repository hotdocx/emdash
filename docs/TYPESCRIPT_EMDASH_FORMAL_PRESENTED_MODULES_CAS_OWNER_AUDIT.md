# Formal Presented Modules CAS Owner Audit

Date: 2026-08-31

Plan: `TYPESCRIPT_EMDASH_FORMAL_PRESENTED_MODULES_CAS_PLAN.md`

Status: initial owner/orientation audit complete; formal vector/matrix spine
validated without new rewrite or unification rules.

## Findings

- The active formal library has finite families and commutative-ring folds but
  no matrix, module, presentation, complex, syzygy, or homology owner.
- The computational matrix convention is row-major storage with a
  `rows x columns` matrix acting from `columns` generators to `rows` outputs.
- Field-linear presentation matrices store relations as columns.
- Presented-algebra modules retain free rank, explicit relation vectors,
  quotient-algebra action relations, a transformed Gröbner basis, and whole
  membership coefficients/remainders.
- Polynomial-module syzygies are coefficient rows whose combination of the
  selected basis generators is the zero vector.
- The existing categorical engine already has matrix/module category models,
  doctrines, Freyd towers, reinterpretation, and program lowering. The new
  formal representation must be a concrete model beneath those layers.

## Selected Formal Orientation

```text
Vector(R,n) = FiniteFamily(|R|,n)
Matrix(R,rows,columns) = FiniteFamily(Vector(R,rows),columns)
```

Matrices are therefore column-oriented formally while the TypeScript CAS
retains row-major physical storage. Reification transposes explicitly and
records both dimensions.

Matrix action recursively forms the linear combination of columns. Matrix
composition maps the left action over each right column. This uses no `Fin`,
lookup, transpose owner, or second tuple representation.

## Presentation Boundary

The selected classifier is:

```text
PresentationAgreement(A,v,w)
  = Sigma coefficients, A*coefficients = v-w.
```

It is explicit relation data. It is not quotient-module equality. A later
semantic layer may interpret it through a quotient, groupoid, cokernel, or
Freyd category without changing the computational representation.

Syzygy and adjacent-zero classifiers are direct matrix equations. They do not
claim exactness, homology, or resolution universality.

## Formal Probe Result

The new rule-free one-way prototype
`emdash3_2_commutative_algebra_finite_modules.lp` passes bounded Lambdapi
checking. Its reviewer example passes:

- visible two-column matrix application;
- explicit presentation-agreement construction; and
- noncollapse of a visible singleton column against the zero matrix.

The module adds transparent definitions only and therefore adds no
critical-pair, replaceable-variable, or strict-LHS candidate of its own.

## Decision

Proceed with this formal spine, then implement exact signature mirrors and
parent-aware TypeScript reification. Select whole module membership as the
first proof–CAS consumer, followed by syzygy and bounded-resolution equations.
Keep quotient semantics and full formal categorical packaging separate.
