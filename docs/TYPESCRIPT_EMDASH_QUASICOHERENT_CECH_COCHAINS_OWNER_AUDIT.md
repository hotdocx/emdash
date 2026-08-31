# Quasi-Coherent Čech Cochains Owner And Orientation Audit

Date: 2026-08-31

Plan: `TYPESCRIPT_EMDASH_QUASICOHERENT_CECH_COCHAINS_PLAN.md`

Status: `QCC-AUDIT-1A` complete; existing degree, face, sign, and repeated-face
orientations are accepted without adaptation.

## Authorities And Baseline

The audit reviewed the completed presented-module plan and the active owners
in:

- `algebra_cech.ts`;
- `algebra_quasicoherent_cech.ts`;
- `algebra_presented_module.ts`; and
- `algebra_presented_module_map.ts`.

The unchanged quasi-coherent Čech, quasi-coherent chart, semilinear-map,
presented-module, and end-to-end artifact suites pass 29/29 after fresh
worktree bootstrap. No TypeScript or Lambdapi source changed in the audit.

## Exact Owner Map

| Required datum or computation | Existing owner | Use |
| --- | --- | --- |
| ordered degree simplices | `AlgebraAffineQuasiCoherentCechDegree.simplices` | exact cochain component order |
| incoming faces | `AlgebraAffineQuasiCoherentCechDegree.incomingFaces` | exact differential contribution order |
| removed position and sign | `AlgebraCechFace.removedPosition`, `.sign` | authoritative `(-1)^p` convention |
| lower/upper module endpoints | `AlgebraAffineQuasiCoherentCechFace.domain`, `.codomain` | source and target of one restriction contribution |
| restriction action | `.map`, an `AlgebraPresentedAlgebraModuleSemilinearMap` | computes the unsigned contribution |
| module zero/addition/negation/equality | presented-module element operations | component and target-sum arithmetic |
| repeated-face equality | `AlgebraAffineQuasiCoherentCechFaceComparison` | exact pair of equal lower-to-top composites |
| finite truncation boundary | `cover.maximumDegree`, `diagram.degrees` | forbids invented successor differential |

No new face map, sign owner, reindexing convention, or coherence input is
required.

## Binary Differential Orientation

For the ordered cover indices `[0,1]`, the retained faces are:

```text
[1] -> [0,1]  removes position 0  sign +1
[0] -> [0,1]  removes position 1  sign -1.
```

Therefore the selected and already-owned convention is:

```text
d(a_0,a_1)_[0,1]
  = res_[1]->[0,1](a_1)
    - res_[0]->[0,1](a_0).
```

The cochain implementation must look up the source component by the face's
stored `domain.simplex.indices`; it must not assume that face-array position
equals degree-component position.

## Repeated-Face Sign Audit

For the ternary top simplex `[0,1,2]`, the three stored comparisons give:

| Removed positions | First path face positions | First total | Second path face positions | Second total |
| --- | --- | --- | --- | --- |
| `(0,1)` | `(0,0)` | `+1` | `(0,1)` | `-1` |
| `(0,2)` | `(1,0)` | `-1` | `(0,2)` | `+1` |
| `(1,2)` | `(1,1)` | `+1` | `(1,2)` | `-1` |

For general `i<j`, the first path removes `j−1` in `J without i` and then
`i` in `J`; the second removes `i` in `J without j` and then `j` in `J`.
Thus:

```text
first total  = (-1)^(i+j-1)
second total = (-1)^(i+j).
```

The signs are always opposite. The existing comparison already proves that
the unsigned composite semilinear maps are canonically equal. A future
cancellation record must derive both facts from these stored routes rather
than accept either from a caller.

## Degree And Cochain Representation

The selected degree parent will retain:

- the exact diagram;
- the degree number;
- the exact ordered degree record;
- the ordered simplex-index strings; and
- the corresponding localized module parent identities.

A cochain has exactly one canonical presented-module element per retained
simplex. It is a heterogeneous additive tuple and does not receive a scalar
algebra or `AlgebraPresentedAlgebraModule` parent.

The final retained degree has no differential target. An explicit truncation
cannot use a fabricated empty successor to claim a longer complex.

## Selected Next Row

`QCC-COCHAIN-2A` will implement degree parents and cochain elements with exact
component alignment, zero/addition/negation/equality, lookup by position and
indices, schemas, serialization, and order/parent/arity failures. Its first
tests use free rank-one modules so later differential tests remain nontrivial.
