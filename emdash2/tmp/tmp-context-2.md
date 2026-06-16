tmp-context-2.md 

Final assessment: the main documentation gap is now mostly closed.

I would not add headers mechanically to every remaining rule. The remaining unheaded items are mostly covered by nearby block comments or are short projection rules where extra comments would add noise.

Best remaining candidates, if we want one more useful pass:

1. Section 4, `Ordinary internal hom and hom actions`
   Add short headers for the individual `hom_postcomp_*` and `hom_precomp_along_*` projection declarations. These are dense stable-head ladders and would benefit from the same style we added to `fdapp1_*` / `tdapp1_*`.

2. Section 5, `Ordinary binary products of categories`
   Add direct headers for `Product_projL`, `Product_projR`, `Product_pair`, `Product_projL_func`, `Product_projR_func`, and the product object/hom/action rule clusters. Current block comments explain the package, but per-symbol scanability could improve.

3. Section 3d, identity/composition/opposite/terminal/constant functors
   Optional. The section is readable already, but a few rule clusters like `id_func`, `comp_cat_fapp0`, `Terminal_cat`, and `Const_func` could get concise formula labels.

I would skip more headers in sections 0-3c, 8-15, 17a/b/e/f, and 18 for now. They already have enough mathematical context, and further comments would mostly duplicate existing `Surface/formula` blocks.

No files changed in this review pass.