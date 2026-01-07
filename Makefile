.RECIPEPREFIX := >
.PHONY: check clean

check:
# > lambdapi check -w emdash.lp
> ./scripts/check.sh

watch:
> python3 scripts/watch_typecheck.py --log logs/typecheck.log

clean:
> find . -type f \( -name '*.lpo' -o -name '*.lpi' -o -name '*.lpj' \) -print -delete
> rm -rf _build .lambdapi .cache || true
