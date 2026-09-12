# Native Homd Target: Positive-Section Polarity Diagnostic

Date: 2026-09-12

Status: closed Empty derivation reproduced; target redesign required, independence from other defects not established

Parent: [native universality and homology plan](TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_AND_HOMOLOGY_PLAN.md)

Design ledger: [native owner/variance ledger](TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_OWNER_LEDGER.md)

## Finding

The active native `homd_src_sec` target permits a reverse Hom action from a
forward base arrow. The resulting transparent term derives `τ Empty_grpd`.
The [reproducer](../emdash2/audits/homd_target_empty_reproducer.lp) adds only
definitions and one assertion: no primitive witness, rewrite, unifier,
equality axiom or opaque proof. It is explicitly outside the positive
mathematical library.

This is a further diagnostic of the current coupled signature. Its
HomPresheaf/section implementation still imports the old op and Sigma
machinery, so this tranche does **not** establish a third logically
independent soundness defect. It does establish an additional concrete
derivation that the complete repair must reject.

In particular, repairing only the R(Z) versus Z annotation at
`Homd_target_section_catd` is not a sufficient semantic specification. The
target also needs the correct direction for its y-action.

The repair must preserve foundational `hom_int`/`homd_int` and their native
internalized action. This finding does not authorize replacing them with an
external relative-Hom grammar, removing their useful action, or truncating
arbitrary bases to hide the problem.

## How The Current Type Forces The Wrong Direction

Let F:Z→C be any functor. Specialize the displayed input to the terminal
family D and constant family E=C; F supplies the corresponding section/map.
For fixed x:Z and u:C, the current `homd_src_sec` gives a positive section
over the opposite y-base:

```text
s : Π y:Zᵒᵖ, HomdTargetSection(D,x)(y).
```

Its endpoint observation, after evaluating the terminal D argument, is the
presheaf

```text
p′ ↦ HomC(u,F(y)),        p′:x→y.
```

Now give p:x→y. Positive section action along the corresponding y→x in Zᵒᵖ
has direction

```text
transport(s(y)) → s(x).
```

Evaluate this arrow first at the terminal argument and then at idₓ. The
source presheaf's restriction sends idₓ to p. Consequently the resulting
whole functor has type

```text
HomC(u,F(y)) → HomC(u,F(x)).
```

This is exactly the type accepted for
`homd_target_polarity_reverse_functor` in the tracked diagnostic. It is the
opposite of the legitimate postcomposition direction induced by F(p).

Take Z=C and F=id, and set u=y. Applying the reverse functor to idᵧ gives
an arrow y→x for every arrow x→y. Finally, in `Grpd_cat`, reverse the
ordinary function Empty→Unit and apply the resulting Unit→Empty function
to tt. This gives the closed decoded-empty inhabitant.

The [walking-arrow control](../emdash2/audits/homd_target_walking_arrow_empty.lp)
also checks. It constructs F from an actual arrow by the existing
`walking_arrow_func` recursor and applies the same diagnostic to its
generator. Thus a large category universe need not serve as the base Z of
the reverse-Hom function. This remains a control within the imported
encoding, not an independent consistency analysis of all its dependencies.

## Legitimate Forward Action Is Preserved As A Separate Control

The [forward companion](../emdash2/audits/homd_target_forward_controls.lp)
does not import the Empty diagnostic. It uses the existing represented
family `hom_(F,u)` and its generic whole action to construct

```text
HomC(u,F(x)) → HomC(u,F(y)),
h ↦ F(p)∘h.
```

The whole functor declaration, its typed reconstruction/identity paths,
its next Hom-action typing and rejection of the reversed functor type all
check. These are direction and usability controls, not a consistency
certificate for the current nucleus.

Two initial raw conversion assertions failed during assertion elaboration,
with `KIND`/`Cat`/`Grpd` constraints. Making their fapp endpoints explicit did
not resolve that assertion form. The final reviewer states the same two
equations as explicitly typed reflexivity paths, which pass through the
existing proof-time interface. No runtime rule or unifier was added.
Therefore the recorded positive evidence is typed path/usability evidence,
not a claim that the two rejected raw assertions passed. The retained
temporary variants are `nuh_homd_forward_controls_inferred_v1.lp` and
`nuh_homd_forward_controls_explicit_v2.lp` under `emdash2/tmp/probes/`.

## Necessary Direction For A Repaired Target

At fixed original source x₀, write the native endpoint operation as

```text
Mᵧ(q,v) = HomEᵧ(E(q)(u), Fᵧ(v)),
q:x₀→y,   v:Dᵧ.
```

Under the strict working transport interpretation, a forward p:y→z and
the appropriately directed displayed-F comparison produce

```text
Mᵧ(q,v) → M_z(p∘q, D(p)(v)).
```

The old positive-section target over the opposite y-base instead asks for
the converse. A repaired target must retain the displayed direction without
requiring an inverse to p or its transport. The terminal/constant case above
already forces this necessary condition; it does not require a decision
about every higher laxity/compositor profile.

A possible semantic comparison model for the target uses objects (y,v,q)
and arrows to (z,w,q′) consisting of

```text
p:y→z,    β:q′⇒p∘q,    a:D(p)(v)→w.
```

For strict transport, the intended action sends h to the composite built
from E(β), E(p)(h), the displayed comparison of F and F_z(a), all in the
forward direction. The β orientation is essential. This is why the lax
versus oplax choice in a relative comma comparison matters; see
[Ara–Guetta, §3.7](https://arxiv.org/pdf/2503.08832v3#page=30).

This is a proposed model/comparison for the native target, not a selected
replacement implementation of `homd_int`. Its complete higher action,
variance under x₀, and compatibility with the actual native projection
ladder still need qualification. A negative-section or mixed-context target
may encode the needed direction; changing a Pi name alone does not establish
that qualification.

A short targeted reading of Chu Rivera–North's
[Directed type theory, with a twist, §3](https://arxiv.org/html/2602.17480v1#S3)
also distinguishes a profunctor context from its displayed unstraightening.
It is useful evidence that changing variance can change the kind of
displayed structure rather than merely its printed base. Its ordinary
category model is not an automatic interpretation of emdash's omega-level
native calculus, and no new external calculus is adopted here.

## Reproduction And Validation

Source baseline: worktree checkpoint `190cd14f`; nucleus blob
`91f1974ece225e399604dce24710bf1437ad3ef5`. The active nucleus is unchanged.
Every invocation used `scripts/probe.sh` and the existing serial resource
guard: normal subject reduction, at most 90 seconds, 2 GiB memory limit and
64 MiB per-file limit. All listed final runs completed successfully.

| Target | Mode | Log under emdash2/logs/probes |
| --- | --- | --- |
| Initial temporary diagnostic | quiet | `nuh_homd_target_polarity-20260912-153845.log` |
| Tracked Empty diagnostic | quiet | `homd_target_empty_reproducer-20260912-154335.log` |
| Walking-arrow specialization | quiet | `homd_target_walking_arrow_empty-20260912-154502.log` |
| Final forward controls | quiet | `homd_target_forward_controls-20260912-154605.log` |
| Tracked Empty diagnostic | warnings enabled | `homd_target_empty_reproducer-20260912-154633.log` |
| Final forward controls | warnings enabled | `homd_target_forward_controls-20260912-154759.log` |

The two warning-enabled inventories agree completely, including locations,
term heads and rule families: 1,144 critical-pair reports and 157 pattern
reports. Both strict parses account for all critical pairs. The three audit
files add no rule clauses and pass the strict inferred-LHS audit. They are
absent from positive source/reviewer and generated health/catalog registries.
No global aggregate, catalog/health refresh or book render is appropriate
for this non-library diagnostic-only slice.

For reproduction from emdash2, run one target at a time:

```bash
scripts/probe.sh audits/homd_target_empty_reproducer.lp
scripts/probe.sh audits/homd_target_walking_arrow_empty.lp
scripts/probe.sh audits/homd_target_forward_controls.lp
```

Before repair, acceptance of the first two reproduces the defect. After
repair, their invalid declaration must fail for the corrected target
type/polarity reason, while the forward companion must continue to check.
Missing imports, syntax failures and timeouts do not qualify that result.

## Next Bounded Design Gate

Retain the native owners and qualify a direction-correct target in the
terminal/constant case, then extend its actual section/projection typing to
varying D/E and the already identified noninvertible base-2-cell controls.
Resolve polarity and base variance jointly before replaying the total-op
patch against the full nucleus. The current repair's three earlier Empty
controls remain mandatory; this diagnostic adds another required target.
No spectral/stabilization or endpoint-checker investigation was started.
