# TypeScript Source Requalification — 2026-09-23

Owner: [profile/performance repair](TYPESCRIPT_PROFILE_AND_PERFORMANCE_REPAIR_PLAN.md).
This records a bounded source alignment review, not whole-library transfer or a
mathematical consistency claim. No Lambdapi source or TypeScript rewrite rule is
added by the requalification. Existing Op/Sigma/Homd qualifications remain.

## Exact source worlds

| Input | Reviewed predecessor | Current source |
| --- | --- | --- |
| Core source commit | `62e9e1009b8f3ccb25c8e8cbf39a1ec68433a363` | `f9ae8d6aaebb34cdc9276497adfc8320933d60ce` |
| Core source SHA-256 | `0a117742d326bad82fe72cc73c624a0c174e3b48dd4047ebd8f6ed6ff7837860` | `f7206b8eed56897ee8483934cd5f9b31348c22865cea20a1257c409eab025e61` |
| Canonical export SHA-256 | `b16839b44dfec845fdc007884f82fea63156a273759fba4e9a8842c0c0312ccb` | `594bbfa447bb383e979d3b082d3ed063d5023d9c0a300f729c34b376cfb229d6` |

Both canonical exports were freshly obtained with the pinned Lambdapi
`3.0.0-90-gdb4f780`, `export -o lp`, under the existing serial 2 GiB/60s guard.
The predecessor came from Git into a temporary package; current source was not
edited. The five intervening post-milestone commits remain documentation-only.

## Reviewed transfer boundary

Enumeration of the root exports found 70 module/selection records targeting
`emdash3_2.lp`, including ten selection contracts. All 103 selected canonical
commands have unique, byte-identical current matches. Only their positions and
whole-source/export identities change; no selected command text digest changes.

The 150 distinct transferred declaration names comprise 147 ordinary source
symbols with byte-identical complete canonical signatures/bodies, the unchanged
`τΣ_` inductive and its `Struct_sigma` constructor, and the existing synthetic
`Obj_func__displayed_chain_mirror` alias. The alias is not asserted to be an
additional source declaration. Of the recorded source fragments, one formerly
exact fragment disappeared; the other 130 nonliteral/abbreviated fragments
already had the same status in the predecessor.

The old export loses ten exact commands. Their reviewed effects are:

| Old command(s) | Current change | Effect on this bounded transfer |
| --- | --- | --- |
| `eq_apd` (21) | Stable injective action, with retained propositional J comparison | Not a transferred declaration in this profile; no new owner is imported |
| Identity-transfor projections (759, 760, 813, 850) | Redundant endpoint patterns become wildcards; results unchanged | Existing narrower transferred cases remain instances; no wildcard widening in TypeScript |
| `Op_transf` involution (794) | Inferred endpoint patterns replace repeated endpoints | Not a transferred owner here; this does not qualify higher opposite |
| Sigma first projection (1017) | Arbitrary-object projection through `sigma_obj_base`, then `sigma_Fst` | Reviewed pair case still computes to its base; backend evidence relocates to the generic rule; directed conformance replays the pair |
| Cat-valued component hom action (1113) | Generic `tapp0_hom_fapp0` route, followed by the existing displayed specialization | Same bounded observation; full/component owners remain; no new transfer |
| Profunctor-map component/action (1350, 1351) | Inferred target presentation replaces an explicit reindexed target | No transferred `Prof_func_hom` owner; existing scale command selections remain byte-identical |

Canonical vocabulary grows from 1,531 to 1,708 commands: symbols 781→834,
rules 652→754, unification rules 72→94; all other kind counts stay fixed.
Definitions grow 488→523, assumptions 293→311, runtime clauses 688→791.
The inventory records this larger source without installing its additional
declarations/rules in the TypeScript profile.

## Selected ordinal relocation

Each transition below preserves its already recorded exact command digest.
Unlisted selected ordinals are unchanged. Acquisition still rejects source,
export, command-text, shape and import drift.

### CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_ACQUISITION

- `higher-foundation.identity-arrow: 232→234`
- `higher-foundation.displayed-composition: 400→402`
- `higher-foundation.opposite-functor: 507→511`
- `higher-foundation.displayed-opposite-functor-owner: 542→546`
- `higher-foundation.ordinary-internal-hom: 651→655`
- `higher-foundation.displayed-opposite: 960→990`
- `higher-foundation.displayed-opposite-action: 969→1001`
- `higher-foundation.mixed-functor-family-owner: 1053→1114`
- `higher-foundation.edge-family: 1076→1137`
- `higher-foundation.presheaf-family: 1077→1138`
- `higher-foundation.hom-presheaf-family: 1078→1139`
- `higher-foundation.displayed-hom-target: 1080→1141`
- `higher-foundation.displayed-internal-hom: 1081→1142`
- `higher-action.full-object-action: 1101→1162`
- `higher-action.capped-object-action: 1102→1163`
- `higher-action.object-projection: 1103→1164`
- `higher-action.full-next-hom-action: 1104→1165`
- `higher-action.next-hom-projection: 1105→1166`

### CORE_LF_SCALE_STRESS_1_CORE_ACQUISITION

- `sigma.decoded-inductive: 54→56`
- `sigma.eliminator: 63→65`
- `sigma.eliminator-beta: 64→66`
- `pi.decoded-classifier: 74→76`
- `pi.decoding-beta: 75→77`

### CORE_LF_SCALE_STRESS_1B_CORE_ACQUISITION

- `foundation.nat-inductive: 38→40`
- `foundation.nat-classifier: 39→41`
- `foundation.nat-decode: 40→42`
- `sigma.decoded-inductive: 54→56`
- `sigma.eliminator: 63→65`
- `sigma.eliminator-beta: 64→66`
- `pi.decoded-classifier: 74→76`
- `pi.decoding-beta: 75→77`

### CORE_LF_SCALE_STRESS_2_UNCURRYING_ACQUISITION

- `uncurrying.displayed-family-classifier: 391→393`
- `uncurrying.displayed-functor-category: 395→397`
- `uncurrying.section-category: 988→1020`
- `uncurrying.sigma-category: 1008→1045`
- `uncurrying.sigma-projection-pullback: 1019→1069`
- `uncurrying.sigma-section-comparison: 1026→1076`

### CORE_LF_SCALE_STRESS_2_INTERNAL_PI_ACQUISITION

- `internal-pi.opposite-category: 236→238`
- `internal-pi.opposite-object: 238→240`
- `internal-pi.displayed-functor-classifier: 396→398`
- `internal-pi.displayed-category-functor: 540→544`
- `internal-pi.pullback-family: 935→964`
- `internal-pi.pullback-fibre: 938→967`
- `internal-pi.pullback-family-functor: 941→970`
- `internal-pi.pullback-functor-object: 942→971`
- `internal-pi.constant-family: 947→977`
- `internal-pi.constant-fibre: 950→980`
- `internal-pi.constant-pullback: 952→982`
- `internal-pi.section-functor: 996→1028`
- `internal-pi.section-functor-object: 997→1029`
- `internal-pi.package: 999→1036`
- `internal-pi.package-component: 1000→1037`
- `internal-pi.pullback-package: 1001→1038`
- `internal-pi.pullback-fold: 1002→1039`
- `internal-pi.pullback-component: 1003→1040`

### CORE_LF_SCALE_STRESS_2_PI_BASE_ACTION_ACQUISITION

- `pi-base-action.terminal-category: 514→518`
- `pi-base-action.fibre-category: 934→963`
- `pi-base-action.transport-left: 1134→1195`
- `pi-base-action.transport-right: 1135→1196`
- `pi-base-action.internal-cell: 1158→1226`
- `pi-base-action.section-pullback: 1261→1358`
- `pi-base-action.internal: 1270→1400`
- `pi-base-action.pullback: 1271→1401`

### CORE_LF_SCALE_STRESS_2_SIGMA_TRANSFOR_ACQUISITION

- `sigma-transfor.transformation-category: 403→405`
- `sigma-transfor.transformation-classifier: 404→406`
- `sigma-transfor.telescope-family: 1043→1104`
- `sigma-transfor.telescope-fibre: 1044→1105`
- `sigma-transfor.uncurrying-owner: 1046→1107`
- `sigma-transfor.fibre-functor: 1108→1169`
- `sigma-transfor.displayed-component: 1110→1171`
- `sigma-transfor.object-component: 1122→1183`

### CORE_LF_SCALE_STRESS_3_PROFUNCTOR_BOUNDARY_ACQUISITION

- `profunctor-boundary.definitional-isomorphism: 580→584`
- `profunctor-boundary.category: 1273→1403`
- `profunctor-boundary.classifier: 1277→1407`
- `profunctor-boundary.comparison: 1322→1454`
- `profunctor-boundary.tensor: 1352→1486`

### CORE_LF_SCALE_STRESS_3_PROFUNCTOR_COMPARISON_ACQUISITION

- `profunctor-comparison.hom-classifier: 230→232`
- `profunctor-comparison.identity-arrow: 232→234`
- `profunctor-comparison.identity-functor: 408→410`
- `profunctor-comparison.identity-object-action: 409→411`
- `profunctor-comparison.postcomposition-action: 549→553`
- `profunctor-comparison.forward-arrow: 581→585`
- `profunctor-comparison.inverse-arrow: 582→586`
- `profunctor-comparison.vertical-map: 1279→1409`
- `profunctor-comparison.push: 1323→1455`
- `profunctor-comparison.pull: 1324→1456`

### CORE_LF_SCALE_STRESS_3_PROFUNCTOR_TENSOR_ACTION_ACQUISITION

- `profunctor-tensor.sigma-first: 59→61`
- `profunctor-tensor.sigma-second: 61→63`
- `profunctor-tensor.product-groupoid: 184→186`
- `profunctor-tensor.product-groupoid-decode: 185→187`
- `profunctor-tensor.product-category: 668→672`
- `profunctor-tensor.product-object: 670→674`
- `profunctor-tensor.product-hom-category: 687→691`
- `profunctor-tensor.map: 1354→1488`
- `profunctor-tensor.functor: 1355→1489`
- `profunctor-tensor.object-action: 1356→1490`
- `profunctor-tensor.arrow-action: 1357→1491`

## Other source bindings

PathOut proposal line numbers are historical provenance. Tests now locate each
unique active declaration and still require its body. The five complete source
declarations were also covered by the unchanged canonical-symbol comparison.
The completed PathOut trust audit and its graduation parent preserve their
original hashes and positions at `a05493b49a1ef49c18ffe921725dd1ce56f21647`.
Its tests read that local Git snapshot explicitly, then separately check the
selected declaration/rule fragments against today's pinned source. This avoids
relabeling a completed audit as newly executed against a different source world.
Contributor tests need that historical commit locally; CI already checks out
the full history. These repository-only audit tests are not package runtime code.

The historical surface specification called whole displayed laxity absent.
Current source derives `functord_laxity_transf` from whole internal action.
The binding now reports active-but-untransferred and continues to reject its
surface use. This updates source status without claiming higher qualification.
The frozen July graduation envelope still records the historical absent-source
classification. Its validator explicitly adapts only this reviewed source-status
transition and requires the owner to remain untransferred/unavailable; all other
partition and implementation checks stay exact.

The overview binding previously selected article bytes from `01dc160d`.
The current article includes later groupoidal/simplicial exposition, publication
links and the soundness qualifications. Its two exact Arrowgram bodies are
byte-identical to the previous binding; the proof-demo source, proof profile,
complete/open artifacts and named goal are unchanged. The document binding is
revision v4 and points to the actual 2026-09-11 research draft:
`sha256:1fdcc5e222d8aa707911343a44c091293a07e1727305e52237e12f28009624d4`.
The materializer still rejects arbitrary prose/diagram/proof changes and its
management-source digest is updated after this exact binding review. No article,
book, diagram or generated publication file is edited.

Validation results belong to the active repair ledger. Historical milestone
reports and immutable release decisions retain their original measurements.
