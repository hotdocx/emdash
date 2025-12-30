.RECIPEPREFIX := >
.PHONY: check clean

check:
> lambdapi check -w emdash.lp
> lambdapi check -w emdash2.lp

watch:
> python3 scripts/watch_typecheck.py --log logs/typecheck.log

clean:
> find . -type f \( -name '*.lpo' -o -name '*.lpi' -o -name '*.lpj' \) -print -delete
> rm -rf _build .lambdapi .cache || true
