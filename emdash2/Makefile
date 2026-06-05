.RECIPEPREFIX := >
.PHONY: check clean

check:
# scripts/check.sh checks the v2 reference, active v3.2 development, and v3.2 diagnostics.
> ./scripts/check.sh

watch:
> EMDASH_TYPECHECK_TIMEOUT=$(EMDASH_TYPECHECK_TIMEOUT) python3 scripts/watch_typecheck.py --log logs/typecheck.log

clean:
> find . -type f \( -name '*.lpo' -o -name '*.lpi' -o -name '*.lpj' \) -print -delete
> rm -rf _build .lambdapi .cache || true
