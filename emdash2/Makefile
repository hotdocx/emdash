.RECIPEPREFIX := >
.PHONY: check clean

check:
# scripts/check.sh checks emdash2.lp and the active v3.1 file.
> ./scripts/check.sh

watch:
> EMDASH_TYPECHECK_TIMEOUT=$(EMDASH_TYPECHECK_TIMEOUT) python3 scripts/watch_typecheck.py --log logs/typecheck.log

clean:
> find . -type f \( -name '*.lpo' -o -name '*.lpi' -o -name '*.lpj' \) -print -delete
> rm -rf _build .lambdapi .cache || true
