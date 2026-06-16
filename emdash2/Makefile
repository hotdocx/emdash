.RECIPEPREFIX := >
.PHONY: check examples catalog ci ci-render health watch clean

check:
# scripts/check.sh checks the active v3.2 development and v3.2 diagnostics.
> ./scripts/check.sh

ci:
> python3 scripts/check_metrics.py --update-log --brief
> python3 -m py_compile scripts/*.py
> bash -n scripts/*.sh
> git diff --check
> ./scripts/lint_active_refs.sh
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

clean:
> find . -type f \( -name '*.lpo' -o -name '*.lpi' -o -name '*.lpj' \) -print -delete
> rm -rf _build .lambdapi .cache || true
