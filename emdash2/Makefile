.RECIPEPREFIX := >
.PHONY: check check-warnings warning-summary audit-rules examples catalog ci ci-render health watch infinity-codex-test prune-logs clean

check:
# scripts/check.sh checks the active v3.2 development and v3.2 diagnostics.
> ./scripts/check.sh

check-warnings:
# Diagnostic kernel check with Lambdapi local-confluence warnings enabled.
> EMDASH_LAMBDAPI_WARNINGS=1 ./scripts/check.sh emdash3_2.lp

warning-summary:
# Opt-in warning inventory; writes the raw output to logs/warnings/latest.log.
> ./scripts/check_warning_summary.sh

audit-rules:
> python3 scripts/audit_rule_lhs.py --strict

ci:
> python3 scripts/check_metrics.py --update-log --brief
> python3 -m py_compile scripts/*.py
> python3 -m json.tool .codex/hooks.json >/dev/null
> python3 -m unittest tests.test_infinity_codex
> bash -n scripts/*.sh
> git diff --check
> ./scripts/lint_active_refs.sh
> python3 scripts/audit_rule_lhs.py --strict
> python3 scripts/generate_check_catalog.py --check --strict

examples:
> ./scripts/check_examples.sh

catalog:
> python3 scripts/generate_check_catalog.py

ci-render:
> npm run check:render

health:
> python3 scripts/check_metrics.py --update-log --write-report

watch:
> EMDASH_TYPECHECK_TIMEOUT=$(EMDASH_TYPECHECK_TIMEOUT) python3 scripts/watch_typecheck.py --log logs/typecheck.log

infinity-codex-test:
> python3 -m json.tool .codex/hooks.json >/dev/null
> python3 -m unittest tests.test_infinity_codex

prune-logs:
# Manual cleanup only; this is never called by check, probes, or CI.
> ./scripts/prune_logs.sh

clean:
> find . -type f \( -name '*.lpo' -o -name '*.lpi' -o -name '*.lpj' \) -print -delete
> rm -rf _build .lambdapi .cache || true
