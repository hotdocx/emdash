# Terminal Uniqueness Unifier: Positive Feasibility Evidence

Authority: the [universality living plan](../../../docs/TYPESCRIPT_EMDASH_CATEGORICAL_UNIVERSALITY_INVENTORY_AND_FOLLOWUP_REVIEW.md).
This fragment is outside the library/check graph. It preserves the exact
working variable-sided unifier and typed consumer; it is not a global rule
promotion or a runtime eta rule. The later bounded inference audit is below;
it does not claim that all possible elaboration interactions are covered.

From `emdash2`, reproduce the positive and negative control sources:

```bash
python3 - <<'PY'
from pathlib import Path
owner = Path('emdash3_2_terminal_objects.lp').read_text()
fragment = Path('audits/terminal-uniqueness-unification/fragment.lp').read_text()
rule = 'unif_rule $f ≡ @terminal_arrow_fapp0 $C $t $T $A ↪ [tt ≡ tt];\n'
Path('tmp/probes/ua0_terminal_unifier.lp').write_text(owner + '\n' + fragment)
Path('tmp/probes/ua0_terminal_control.lp').write_text(owner + '\n' + fragment.replace(rule, ''))
PY
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh tmp/probes/ua0_terminal_unifier.lp
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh tmp/probes/ua0_terminal_control.lp
```

The first must pass: `eq_refl f` checks at f=!ₐ while runtime conversion
remains negative. The second is expected to fail precisely at the typed
reflexivity assertion, without the unifier. The source copy is needed to
preserve the owning declaration environment; never append this fragment to
the production owner as part of merely replaying the audit.

The 2026-09-17 review established these outcomes. The user explicitly
requires treating that feasibility as a design fact in further development.
It disproves a blanket infeasibility assumption; it does not by itself decide
whole higher terminality or the desired runtime normal forms.

## Bounded Inference Audit (UA-3f)

Baseline: `04c58855`, after the qualified family-normalizer retirement.
The exact same unifier is inserted in a full copy of the terminal owner,
immediately after `terminal_arrow_fapp0` and before its component rules. Seven
well-formed assertions in `inference.lpfragment` pass:

- typed reflexivity at f=!ₐ for an arbitrary supplied f;
- the same comparison for a composite and for idₜ;
- canonical arrows selected by two supplied terminal witnesses at the same t;
- inference of the omitted source argument A;
- negative runtime conversion and negative proof-time identification of
  unrelated arbitrary arrows.

Separate controls give the expected rejections:

- removing only the unifier fails at the first f=!ₐ assertion;
- `endpoint-reject.lpfragment` is rejected because the expected equality
  itself has incompatible source endpoints A and B;
- `missing-provider.lpfragment` leaves an unsolved TerminalObject(t) witness
  and is rejected. The unifier does not synthesize that omitted structure.

The endpoint control must be a separate failing file: Lambdapi checks the
expected type before the negative typing assertion. The initial combined
probe therefore exited at that malformed type after its seven earlier checks;
the separated positive file passes. This is a fixture distinction, not a
failure of terminal uniqueness or a resource issue.

Reproduce these four sources without editing the library:

```bash
python3 - <<'PY'
from pathlib import Path
base = Path('emdash3_2_terminal_objects.lp').read_text()
audit = Path('audits/terminal-uniqueness-unification')
marker = '// Component projection from the whole terminal transfor.'
rule = 'unif_rule $f ≡ @terminal_arrow_fapp0 $C $t $T $A ↪ [ tt ≡ tt ];\n'
assert base.count(marker) == 1
owner = base.replace(marker, rule + '\n' + marker)
for name in ['inference', 'endpoint-reject', 'missing-provider']:
    fragment = (audit / (name + '.lpfragment')).read_text()
    Path('tmp/probes/ua3f_replay_' + name + '.lp').write_text(owner + '\n' + fragment)
Path('tmp/probes/ua3f_replay_no-rule.lp').write_text(
    base + '\n' + (audit / 'inference.lpfragment').read_text())
PY
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh tmp/probes/ua3f_replay_inference.lp
# Each of the following commands is expected to return exit 1.
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh tmp/probes/ua3f_replay_endpoint-reject.lp
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh tmp/probes/ua3f_replay_missing-provider.lp
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh tmp/probes/ua3f_replay_no-rule.lp
```

All initial runs completed in under one second with the serial 2GiB/90s/o20
guard, warnings and subject reduction enabled. Logs:

- `ua3f_terminal_unifier_inference-20260917-163604.log`;
- `ua3f_terminal_unifier_endpoint_reject-20260917-163614.log`;
- `ua3f_terminal_unifier_missing_provider-20260917-163615.log`;
- `ua3f_terminal_unifier_no_rule-20260917-163615.log`.

The rule/control comparison retains the same seven inherited critical pairs,
term heads and rule families, with no parser issue. The exact candidate adds
five replaceable-pattern-variable warnings at its own line; these concern
f,C,t,T,A, all absent from the trivial right-hand constraint. They are recorded,
not mistaken for a new runtime critical pair or suppressed by changing the
candidate. No universal confluence claim follows from this bounded comparison.

Conclusion: the successful variable-sided comparison has useful typed and
inference behavior beyond the original single example. It remains outside the
library: the newly derived terminal-family operations and migrated native
consumers work without it. A future promotion should identify the consumer
benefit and audit that import environment. This result neither changes runtime
normal forms nor upgrades groupoidal contractibility to higher terminality.
