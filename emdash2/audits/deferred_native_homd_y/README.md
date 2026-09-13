# Deferred native Homd y-projection experiment

Status: parked by user direction on 2026-09-13. This is recovery evidence,
not an active library module or a passing implementation candidate.

The last qualified checkpoint is `29f847f7`, following `f5954098` and
`8321a9d3`, on `goal/native-universality-homology-v3.2`. All those commits
remain in history. The active nucleus was never changed by these experiments.

`candidate.patch` is the latest unqualified source delta on top of the full
candidate produced by these four retained patches, in order:

1. `../total_op_reinterpretation.patch`
2. `../native_index_family_shift.patch`
3. `../hom_presheaf_transpose.patch`
4. `../native_homd_direct_owner.patch`

That base has SHA-256
`401221ac2b5039341e65c184b3061645a978af209fc5d052036b6c22a9e61ee9`.
Apply zero-context patches only to a copied source with the appropriate
zero-context option; do not apply this experiment to the active kernel.

The latest work constructed a local inclusion and a whole restriction:

```text
Φ_y : D[y] × Transpose(Hom_Z(x,y)) → S_D(x)
Φ_y(v,a) = ((y,v),a)
R_y(M)(v)(a) = M(((y,v),a)).
```

The helper module and object/restriction checks passed in the earlier copied
prefix. The arrow observation computed `((id_y,β),θ)`, but independently
retyping that normal form exposed an opaque represented-postcomposition
unit. Two subsequent unit-rule candidates and the attempted canonical
y-projection fold are unqualified. The latest check failed subject reduction
with an unresolved category constraint. Do not count it as a repair.

The last complete local stage, including all source variants and logs, is
preserved in the repository's ignored storage:

```text
emdash2/tmp/deferred-native-duality/2026-09-13-nuh1d6/
```

`preservation_manifest.json` there hashes every archived file. The manifest
in this directory identifies the base, latest candidate and retained source
files. `native_y_index_arrow_review.lp` includes the failed retyping test;
the earlier successful compute-only observation is documented by the archived
`logs/y-index-arrow-v1.log`. The latest failure is `logs/y-fold-v4.log`.

When the user resumes this work after the universality/homology goal, first
review the strict/lax context and source drift. Retain primitive hom_int,
homd_int and pointwise Op_catd; preserve the existing rewrite/unification
roles. Strict structural comparison cells may compute to identity at their
coincident endpoints. No profile-branch integration or additional duality
work is scheduled by this preservation checkpoint.
