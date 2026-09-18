# Terminal Object And Product η Unifier Review

Date: 2026-09-18
Status: bounded non-library experiments; no production declaration/rule changed
Authority: [repository reassessment](../../../docs/TYPESCRIPT_EMDASH_FOUNDATIONS_DEVOPS_AND_CONTINUATION_REVIEW.md)

The baseline is `1ead0f3c`. `manifest.json` pins the full nucleus, installed
checker binary, local checker sources, resource profile and fourteen execution
logs. Fragments are reviewer controls, not an alternative theory or positive
library. Full owner copies remain disposable under ignored tmp/probes.

## Findings

| Experiment | Result |
| --- | --- |
| Current constant Terminal_obj, proposed variable-sided unifier | Fails first typed reflexivity check |
| Same source without unifier | Same failure |
| Isolated injective Terminal_obj, same unifier | Four checks pass: both reflexivity orientations, negative runtime conversion and unrelated-Boolean noncollapse |
| Same injective variant without unifier | Fails typed reflexivity with unsolved Terminal_obj≡x |
| Product object forward reflexivity, proposed pair unifier | Passes, but the identical no-rule control also passes |
| Eight product/Sigma observations and controls | Pass with and without the rule: object/functor/arrow/Sigma forward reflexivity, negative runtime conversion, unrelated objects, distinct Boolean pairs, projection beta |
| Reverse product reflexivity | Fails with the rule in the extended experiment and in the isolated no-rule control |
| Pair components omitted as metas | Fails with and without the rule after the first three forward observations |
| Opaque observer applied to x versus its explicit pair | Fails with and without the rule |

No timeout/OOM occurred. Early failures stop their respective file; later
assertions in those files were not counted as passed. The successful eight-case
files separately qualify the observations that the earlier inference failure
had hidden. The isolated reverse no-rule control also fails; it is recorded separately
from the earlier extended candidate.

The terminal rule is exactly:

```text
unif_rule $x ≡ Terminal_obj ↪ [ tt ≡ tt ];
```

The product investigation used both an explicit-parameter version and this
SOP-style version; both are inserted immediately after sigma_Snd beta:

```text
unif_rule $x ≡ Struct_sigma $x1 $x2
  ↪ [ sigma_Fst $x ≡ $x1; sigma_Snd $x ≡ $x2 ];
```

The public Product_pair is a transparent name for Struct_sigma. Changing a
rule to mention that alias does not provide a new rigid unification owner.
The rule also concerns general dependent Sigma, not only Product_cat; its
scope must be assessed accordingly.

## Why These Results Differ From Terminal Arrows

The opam source at `/home/user1/.opam/default/.opam-switch/sources/lambdapi`
checks out db4f7809961b8c107247613067fb567491fb0b84, matching the installed
binary's reported revision. It supplies the implementation explanation,
pinned by hashes in the manifest:

- `src/core/unif.ml`, both solve dispatches: variable/abstraction/product versus
  a symbol with `sym_prop = Const` calls error before the custom-rule fallback.
- `src/handle/command.ml`, inductive declaration handling: constructors are
  installed using `Const`. Thus Struct_sigma has that rigidity.
- `emdash3_2_terminal_objects.lp`: terminal_arrow_fapp0 is an ordinary symbol;
  its previously qualified variable-sided unifier reaches a different branch.

The [official command manual](https://lambdapi.readthedocs.io/en/latest/commands.html#inductive)
also describes inductive constructors as constant symbols. The installed
source and behavioral controls, rather than that general documentation alone,
explain the exact dispatch. This investigation does not claim every future
Lambdapi release has the same behavior.

The first product success does not test this dispatch: decoded equality
already exposes SigmaPathView and its component paths. Moving the product
inside an opaque Boolean-valued observer forces comparison of the actual
argument and distinguishes the stronger requested behavior. Reverse reflexivity
also exposes representation/injectivity sensitivity. Do not interpret a
single accepted eq_refl as arbitrary contextual η or runtime conversion.

## Warning Comparison

All controls retain 157 replaceable-variable warnings and 1140 inherited
critical pairs. The terminal candidate adds one replaceable-variable warning
at its own line; changing Terminal_obj rigidity adds no further delta. Heads,
rule families, normalized locations and parser issues agree otherwise.

The product candidate reduces reported pairs to 1112 without adding runtime
rules: 26 fewer at comp_fapp0, two fewer at fdapp1_int_hom_fapp0. Participating
families are comp_fapp0/fapp1_fapp0 (−26), fdapp1_int_hom_fapp0/self (−1), and
fdapp1_int_hom_fapp0/id (−1). The normalized owner locations are in the
manifest; no parser issue is recorded. This is a real change in the checker's
warning analysis, not proof that 28 semantic overlaps have been repaired or
that arbitrary η now works. Unification participates in more than the final
user assertion. This additional interaction is another reason not to promote
on the simple positive example alone.

## Replay

From emdash2:

```bash
python3 audits/terminal-product-unification-review/replay.py
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh tmp/probes/replay_terminal_injective_candidate.lp
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh tmp/probes/replay_product_observations_control.lp
```

The generator verifies the exact current owner hash and performs no checker
calls or production writes. Every generated target should be run individually,
serially, through the same 2GiB/90s guard with warnings and subject reduction.
The constant-terminal, injective-no-rule, observer and inference variants
are expected failures. Keep their exits/logs distinct from passing library
checks. The replay names differ from the original measured experiment names;
the manifest retains the original source/log hashes and actual observed exits.
All eight main replay sources are byte-identical to their measured originals;
this identity is recorded separately from the smaller isolated rejection files.

Recommendation: preserve the current runtime owners. A future terminal
rigidity change needs a concrete consumer and import audit. A stronger pair η
consumer needs an explicit scoped design or a separately tested checker
change; neither a duplicate pair constructor nor an unqualified global rule
is selected here.
