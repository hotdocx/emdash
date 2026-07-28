/**
 * Live Lambdapi conformance for the exact DISPLAYED-EVAL-1A closure.
 */

import assert from 'node:assert/strict';
import {
    resolve
} from 'node:path';
import {
    describe,
    it
} from 'node:test';
import {
    checkLambdapiProbe
} from '../src/v3_2';

const source = `
require open emdash.emdash3_2;

symbol ce_subject [K A : Cat] (B : τ (Catd K)) : τ (Catd K)
≔ @Functor_catd K (@Const_catd (Op_cat K) A) B;

symbol ce_source [K A : Cat] (B : τ (Catd K)) : τ (Catd K)
≔ @comp_cat_fapp0
    K
    (Product_cat Cat_cat Cat_cat)
    Cat_cat
    (@uncurry_func Cat_cat Cat_cat Cat_cat Product_cat_func)
    (Struct_sigma (@ce_subject K A B) (@Const_catd K A));

assert [K A : Cat] (B : τ (Catd K)) (k : τ (Obj K)) ⊢
  @tapp0_fapp0 K Cat_cat (@ce_source K A B) B k (@Eval_funcd K A B)
    ≡ @Eval_func A (Fibre_cat B k);

assert [K A : Cat]
  (B : τ (Catd K))
  (k : τ (Obj K))
  (F : τ (Functor A (Fibre_cat B k)))
  (a : τ (Obj A)) ⊢
  @fapp0
      (Product_cat (Functor_cat A (Fibre_cat B k)) A)
      (Fibre_cat B k)
      (@tapp0_fapp0
        K Cat_cat (@ce_source K A B) B k (@Eval_funcd K A B))
      (Struct_sigma F a)
    ≡ @fapp0 A (Fibre_cat B k) F a;

assert [K : Cat] (E : τ (Catd K)) (k : τ (Obj K)) ⊢
  @tapp0_fapp0
      K Cat_cat E (@Const_catd K Terminal_cat) k
      (@Terminal_funcd K E)
    ≡ @Terminal_func (Fibre_cat E k);

symbol ce_const [K A : Cat]
  [E : τ (Catd K)]
  (a : τ (Obj A))
  : τ (Functord E (@Const_catd K A))
≔ @comp_fapp0
    (@Catd_cat K)
    E
    (@Const_catd K Terminal_cat)
    (@Const_catd K A)
    (@Const_func K A a)
    (@Terminal_funcd K E);

symbol ce_varying [K A : Cat]
  [E B : τ (Catd K)]
  (FF : τ (Functord E (@ce_subject K A B)))
  (xx : τ (Functord E (@Const_catd K A)))
  : τ (Functord E B)
≔ @comp_fapp0
    (@Catd_cat K)
    E
    (@ce_source K A B)
    B
    (@Eval_funcd K A B)
    (@Product_pair_funcd
      K E (@ce_subject K A B) (@Const_catd K A) FF xx);

assert [K A : Cat]
  (E B : τ (Catd K))
  (FF : τ (Functord E (@ce_subject K A B)))
  (xx : τ (Functord E (@Const_catd K A)))
  (k : τ (Obj K))
  (e : τ (Obj (Fibre_cat E k))) ⊢
  @fapp0
      (Fibre_cat E k)
      (Fibre_cat B k)
      (@tapp0_fapp0 K Cat_cat E B k (@ce_varying K A E B FF xx))
      e
    ≡ @fapp0
        A
        (Fibre_cat B k)
        (@fapp0
          (Fibre_cat E k)
          (Functor_cat A (Fibre_cat B k))
          (@tapp0_fapp0 K Cat_cat E (@ce_subject K A B) k FF)
          e)
        (@fapp0
          (Fibre_cat E k)
          A
          (@tapp0_fapp0 K Cat_cat E (@Const_catd K A) k xx)
          e);

symbol ce_fixed [K A : Cat]
  [B : τ (Catd K)]
  (a : τ (Obj A))
  : τ (Functord (@ce_subject K A B) B)
≔ @comp_fapp0
    (@Catd_cat K)
    (@ce_subject K A B)
    (@ce_source K A B)
    B
    (@Eval_funcd K A B)
    (@Product_pair_funcd
      K
      (@ce_subject K A B)
      (@ce_subject K A B)
      (@Const_catd K A)
      (@id (@Catd_cat K) (@ce_subject K A B))
      (@ce_const K A (@ce_subject K A B) a));

assert [K A : Cat]
  (B : τ (Catd K))
  (a : τ (Obj A))
  (k : τ (Obj K))
  (F : τ (Functor A (Fibre_cat B k))) ⊢
  @fapp0
      (Functor_cat A (Fibre_cat B k))
      (Fibre_cat B k)
      (@tapp0_fapp0
        K Cat_cat (@ce_subject K A B) B k (@ce_fixed K A B a))
      F
    ≡ @fapp0 A (Fibre_cat B k) F a;

assert [K A : Cat]
  (B : τ (Catd K))
  (x y : τ (Obj K)) ⊢
  @tapp1_func
      K Cat_cat (@ce_source K A B) B x y (@Eval_funcd K A B)
    : τ (Functor
        (Hom_cat K x y)
        (Functor_cat
          (Fibre_cat (@ce_source K A B) x)
          (Fibre_cat B y)));

symbol ce_higher [K A : Cat]
  [B : τ (Catd K)]
  [x y : τ (Obj K)]
  [p q : τ (Hom K x y)]
  (alpha : τ (Hom (Hom_cat K x y) p q))
  : τ (Transf
      (@tapp1_fapp0
        K Cat_cat (@ce_source K A B) B x y (@Eval_funcd K A B) p)
      (@tapp1_fapp0
        K Cat_cat (@ce_source K A B) B x y (@Eval_funcd K A B) q))
≔ @fapp1_fapp0
    (Hom_cat K x y)
    (Functor_cat (Fibre_cat (@ce_source K A B) x) (Fibre_cat B y))
    (@tapp1_func K Cat_cat (@ce_source K A B) B x y (@Eval_funcd K A B))
    p q alpha;

assertnot [K : Cat] ⊢ Op_cat K ≡ K;
`;

describe('DISPLAYED-EVAL-1A Lambdapi conformance', () => {
    it(
        'checks owner components, both consumers, action, and variance',
        {
            skip:
                process.env
                    .EMDASH_RUN_LAMBDAPI_CATEGORICAL_DISPLAYED_EVALUATION_PROBES !==
                    '1'
        },
        () => {
            const result = checkLambdapiProbe(
                {
                    source,
                    sourceMap: []
                },
                {
                    packageRoot: resolve(__dirname, '../emdash2'),
                    timeoutMs: 60_000
                }
            );
            assert.equal(
                result.accepted,
                true,
                `Expected DISPLAYED-EVAL-1A conformance:\n` +
                    result.diagnostics
            );
            assert.equal(result.timedOut, false);
        }
    );
});
