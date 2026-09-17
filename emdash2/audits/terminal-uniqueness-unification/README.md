# Terminal Uniqueness Unifier: Positive Feasibility Evidence

Authority: the [universality living plan](../../../docs/TYPESCRIPT_EMDASH_CATEGORICAL_UNIVERSALITY_INVENTORY_AND_FOLLOWUP_REVIEW.md).
This fragment is outside the library/check graph. It preserves the exact
working variable-sided unifier and typed consumer; it is not a global rule
promotion, a runtime eta rule or a completed inference-interaction audit.

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
