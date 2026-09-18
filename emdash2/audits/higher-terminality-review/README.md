# Conditional Higher-Terminality Observations

Date: 2026-09-18
Authority: [higher terminality review](../../../docs/TYPESCRIPT_EMDASH_HIGHER_TERMINALITY_REVIEW.md)
and [living assembly ledger](../../../docs/TYPESCRIPT_EMDASH_CATEGORICAL_UNIVERSALITY_ASSEMBLY_LEDGER.md#ua-3g--complete-terminality-review-and-conditional-native-observations).

The retained fragment uses only existing operations and supplied
J:p⊣t or J:t⊣p. It contains four derived definitions and six assertions:
the two Hom DefIso observations, terminal-side fixed-forward Ω evidence,
the original whole terminal-direction comparison, formation of the native
terminal/initial family contraction types, and both Hom-functor inverse cuts
in each direction. There is no OneCat(C) premise, new primitive or rule.

This is conditional formation/computation evidence. J already supplies the
whole computational Hom comparison. The fragment does not derive J from
TerminalObject, inhabit the two family-contraction types from that old data,
remove the ordinary family-realization guards, or certify the general higher
interpretation of the unprofiled prototype. The existing generic mate API
already exposes the operations, so no duplicate public aliases are added.

From emdash2:

```bash
cp audits/higher-terminality-review/conditional-observations.lpfragment \
  tmp/probes/ua3g_conditional_replay.lp
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh tmp/probes/ua3g_conditional_replay.lp
```

The manifest records exact source and owner hashes. Checks use the serial
2GiB/90s/o20 profile, with subject reduction and warnings enabled. The separate
mathematical review checks the full ! package and explains the strict/pseudo
versus lax distinction; it introduces no kernel inconsistency experiment.
