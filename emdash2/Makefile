.RECIPEPREFIX := >
.PHONY: check check-warnings warning-summary audit-rules examples catalog toc ci ci-render book-evidence book-typography book-check book-pdf book-release health watch infinity-codex-test prune-logs clean

check:
# scripts/check.sh checks the active v3.2 development and v3.2 diagnostics.
> ./scripts/check.sh

check-warnings:
# Diagnostic kernel check with Lambdapi local-confluence warnings enabled.
> EMDASH_LAMBDAPI_WARNINGS=1 ./scripts/check.sh emdash3_2.lp

warning-summary:
# Opt-in term-head/rule-family inventory; retains the raw warning stream.
> ./scripts/check_warning_summary.sh

audit-rules:
> python3 scripts/audit_rule_lhs.py --strict

ci:
> python3 scripts/check_metrics.py --no-check --check-report --brief
> python3 scripts/check_metrics.py --update-log --brief
> python3 -m py_compile scripts/*.py ../scripts/infinity_codex.py
> python3 -m json.tool ../.codex/hooks.json >/dev/null
> python3 -m unittest tests.test_infinity_codex tests.test_book_typography tests.test_book_evidence tests.test_source_toc tests.test_check_metrics tests.test_warning_summary
> node --test print/scripts/document_registry.test.mjs
> bash -n scripts/*.sh
> git diff --check
> python3 scripts/check_source_toc.py
> ./scripts/lint_active_refs.sh
> python3 scripts/lint_report_headers.py
> python3 scripts/check_book_evidence.py
> python3 scripts/check_book_typography.py
> node print/scripts/check_book_katex.mjs
> node print/scripts/assemble_book.mjs
> node print/scripts/assemble_book.mjs --check
> node print/scripts/check_book.mjs
> python3 scripts/audit_rule_lhs.py --strict
> python3 scripts/generate_check_catalog.py --check --strict

examples:
> ./scripts/check_examples.sh

catalog:
> python3 scripts/generate_check_catalog.py

toc:
> python3 scripts/check_source_toc.py

ci-render:
> ../scripts/pnpmw --dir emdash2/print run check:render

book-evidence:
> python3 scripts/check_book_evidence.py

book-typography:
> ../scripts/pnpmw --dir emdash2/print run book:typography

book-check:
> ../scripts/pnpmw --dir emdash2/print run book:check

book-pdf:
> ../scripts/pnpmw --dir emdash2/print run book:pdf
> ../scripts/pnpmw --dir emdash2/print run book:pdf:check

book-release:
> ../scripts/pnpmw --dir emdash2/print run book:release

health:
> python3 scripts/check_metrics.py --resume --update-log --write-report

watch:
> EMDASH_TYPECHECK_TIMEOUT=$(EMDASH_TYPECHECK_TIMEOUT) python3 scripts/watch_typecheck.py --log logs/typecheck.log

infinity-codex-test:
> python3 -m json.tool ../.codex/hooks.json >/dev/null
> python3 -m unittest tests.test_infinity_codex

prune-logs:
# Manual cleanup only; this is never called by check, probes, or CI.
> ./scripts/prune_logs.sh

clean:
> find . -type f \( -name '*.lpo' -o -name '*.lpi' -o -name '*.lpj' \) -print -delete
> rm -rf _build .lambdapi .cache || true
