# Primary Terminality: Categorical Comparison And Whole-Family Boundary

Date: 2026-09-17
Status: checked non-library constructions; whole-family replacement unfinished
Base: `10bff3059d999b7f0f59caa9977ad13ea034a0d3`

The [living plan](../../../docs/TYPESCRIPT_EMDASH_CATEGORICAL_UNIVERSALITY_INVENTORY_AND_FOLLOWUP_REVIEW.md)
and its [ledger](../../../docs/TYPESCRIPT_EMDASH_CATEGORICAL_UNIVERSALITY_ASSEMBLY_LEDGER.md)
own this investigation. These standalone fragments are not discovered as
library modules or positive reviewer examples.

## Concrete Consumer And Input

`one_cat_adjunction_zero_columns` and the native kernel/cokernel family-input
owners use the selected terminal/initial family comparisons. For h:F⇒const_t,
the terminal operation must compare Arr(h) with J∘F, preserving the actual
F, t, h and both endpoint identities. Its selected inverse is computational
input to later universal operations. A pointwise uniqueness path alone does
not provide this whole diagram comparison.

The primary input tested here is directly

```text
J : Adjunction(p:C→1, t:1→C).
```

The experimental `ua3_TerminalAdjunction` is only a definition of this existing
classifier. No Hom-comparison-to-adjunction constructor is used. The current
Adjunction interface supplies a computational DefIso of represented Homs;
this is its existing strong computational contract, not an assertion that all
weak higher terminality is equivalent to such strict inverse computation.
The diagram realization below retains the ordinary-category guard. The
general higher/profile interpretation is not newly qualified by these probes.

## Constructed Categorical Data

Evaluate J's whole Hom comparison at (x,*), obtaining q:D→1 and r:1→D with
D=Hom_cat(C,x,t). For f,g:D, define

```text
c(f,g) = r[Terminal_obj : q(f)→q(g)] : f→g.
```

The original comparison's inverse cuts give the endpoints f and g. The term
retains the entire Hom-action functor 1→Hom_D(f,g), not only its value.
The terminal arrow has an explicit inverse in Terminal_cat; applying the
existing iso_evidence_fmap gives c(f,g), c(g,f), and both inverse-law proofs.
No functor is transported through an equality, and callers supply no
naturality-square proof. Equality occurs in the existing IsoEvidence laws;
the forward/inverse arrows themselves are categorical action terms.

Using the existing ordinary selected-terminal adapter and square realization,
these data construct both diagram maps

```text
(x ─f→ t) ⇄ (x ─!ₓ→ t).
```

All four source/target components compute to identities. This is a component
construction at one x,f. It does not yet replace the whole family DefIso or
establish its runtime inverse cuts. A standalone runtime-identity assertion
for c(f,f) fails, whereas both IsoEvidence laws typecheck; do not relabel that
result as judgmental cancellation.

`categorical-comparison.lpfragment` contains the definitions and eight passing
assertions: both arrow projections, both inverse-law types, and the four
diagram endpoint computations. It introduces no primitive, rewrite or unifier.

## Whole-Family Experiment

The existing ordinary postcomposition lift yields, for F:B→C and V:B→1,

```text
[B,C](F, t∘V) ≅ [B,1](p∘F,V).
```

`family-mates.lpfragment` constructs this comparison and checks reconstruction
of an arbitrary whole h:F⇒const_t. The lift's ordinary Terminal_cat profile
is an explicit argument in this probe, not a new axiom or a claimed derived
profile. One experimental proof-time constant-postcomposition view is needed
to expose t∘V as const_t through the retained represented-action head. Its
absence fails exactly at that endpoint comparison. It changes no runtime
normal form and has not undergone a promotion audit.

The right-hand category `[B,1](p∘F,V)` does not currently compare to Terminal_cat
in the tested program. The retained control fails specifically at that type
comparison. This does not prove that a whole categorical contraction cannot
be derived. It identifies the next construction to investigate: coherent
terminal-valued family action/contraction, retaining its inverse, or a direct
whole comparison built from the native unit action. Merely constructing a new
Adjunction from the same Hom data would not supply this step.

Do not install a broad Functor_cat(B,1)↪1 rewrite or add a new structure
primitive solely to make this failed assertion pass. The acceptance target
remains the actual terminal-family comparison, its original inputs/endpoints,
inverse and whole action, followed by its dual. Existing native consumers
continue to use their qualified implementation.

## Reproduction And Evidence

From `emdash2`, copy each standalone positive fragment to an ignored probe:

```bash
cp audits/terminal-primary-family-boundary/categorical-comparison.lpfragment tmp/probes/ua3_terminal_diagram_comparison.lp
env OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 scripts/probe.sh tmp/probes/ua3_terminal_diagram_comparison.lp
cp audits/terminal-primary-family-boundary/family-mates.lpfragment tmp/probes/ua3_primary_terminal_family_constant_view.lp
env OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 scripts/probe.sh tmp/probes/ua3_primary_terminal_family_constant_view.lp
```

To reproduce the expected failures, append `runtime-identity-control.lpfragment`
to the categorical comparison, or `family-contraction-control.lpfragment` to
the family-mates fragment, in a distinct ignored `.lp` file. The first failure
stops at the runtime identity comparison; its later inverse-composition check
was not reached. These negative probes are not regression assertions that the
unqualified behavior must remain unavailable.

All runs used the standard serial 2GiB/90s guard with warnings and subject
reduction enabled. Recorded logs in `logs/probes/`:

- unchanged baseline: `one_cat_terminal_adjunctions-20260917-134020.log`;
- initial missing constant view: `ua3_primary_terminal_family-20260917-134248.log`;
- family comparison and whole reconstruction: `ua3_primary_terminal_family_constant_view-20260917-134357.log`;
- runtime identity control: `ua3_terminal_categorical_arrow-20260917-134527.log`;
- arrow formation: `ua3_terminal_categorical_arrow_formation-20260917-134623.log`;
- retained categorical inverse data/laws: `ua3_terminal_categorical_iso-20260917-134807.log`;
- four diagram endpoints: `ua3_terminal_diagram_comparison-20260917-134924.log`;
- terminal-valued family contraction control: `ua3_terminal_family_contraction_control-20260917-135023.log`.

The documented fragment-assembly recipes were also replayed: the retained
identity and family controls fail at the same intended comparisons in
`ua3_retained_identity_control-20260917-135332.log` and
`ua3_retained_family_control-20260917-135424.log`. The positive fragments match
the checked programs (only the family fragment's explanatory header changed).

No active library source, model contract or CAS code changes in this tranche.
The earlier adjunction-introduction candidate is separately preserved in
`../adjunction-from-hom-comparison/` and is absent from these imports.
