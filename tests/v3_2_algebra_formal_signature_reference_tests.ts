import assert from 'node:assert/strict';
import { it } from 'node:test';
import { checkedFormalSignatureReference } from '../src/v3_2/algebra_formal_signature_reference';
import { CoreLfDeclarationEnvironment } from '../src/v3_2/lf_declarations';
import { affineFormalCommRingType } from '../src/v3_2/algebra_formal_conformance';
import { createFormalFreydNativeConnectingProofEnvironment,
    FORMAL_FREYD_NATIVE_CONNECTING_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_native_connecting_signatures';
import { createFormalFreydNativeModelObservationProofEnvironment } from '../src/v3_2/algebra_formal_freyd_native_model_observation_signatures';
import { algebraFormalFreydNativeModelType } from '../src/v3_2/algebra_formal_freyd_native_model_signatures';
import { assertAlgebraFormalFreydNativeConnectingContext } from '../src/v3_2/algebra_formal_freyd_model_connecting_observation';
import { binderMode, kernelFree, kernelUniverse, provenance } from '../src/v3_2/kernel';

const p = provenance('derived', 'closed signature reference regression');
const mode = binderMode('explicit', 'functorial');

it('shares successful immutable references by factory identity and isolates extensions', () => {
    let calls = 0;
    const factory = (inputs: readonly unknown[]) => {
        assert.deepEqual(inputs, []);
        calls++;
        return CoreLfDeclarationEnvironment.empty();
    };
    const reference = checkedFormalSignatureReference(factory);
    assert.equal(checkedFormalSignatureReference(factory), reference);
    assert.equal(calls, 1);
    assert.ok(Object.isFrozen(reference));
    const extended = reference.extend({ name: 'cache_user_type', type: kernelUniverse(p), mode, provenance: p });
    assert.ok(extended.lookup('cache_user_type'));
    assert.equal(checkedFormalSignatureReference(factory).lookup('cache_user_type'), undefined);
    assert.notEqual(checkedFormalSignatureReference(() => CoreLfDeclarationEnvironment.empty()), reference);
});

it('does not cache a failed reference construction', () => {
    let calls = 0;
    const factory = () => {
        if (++calls === 1) throw new Error('reference construction failed');
        return CoreLfDeclarationEnvironment.empty();
    };
    assert.throws(() => checkedFormalSignatureReference(factory), /construction failed/u);
    const reference = checkedFormalSignatureReference(factory);
    assert.equal(checkedFormalSignatureReference(factory), reference);
    assert.equal(calls, 2);
});

it('rechecks supplied signatures and model parameters after the real reference is cached', () => {
    const R = kernelFree('reference_cache_R', p);
    const otherR = kernelFree('reference_cache_other_R', p);
    const M = kernelFree('reference_cache_M', p);
    const inputs = [
        { name: R.name, type: affineFormalCommRingType() },
        { name: otherR.name, type: affineFormalCommRingType() },
        { name: M.name, type: algebraFormalFreydNativeModelType(R) }
    ];
    const good = createFormalFreydNativeConnectingProofEnvironment(inputs);
    const check = (environment = good, ring = R, model = M) =>
        assertAlgebraFormalFreydNativeConnectingContext(environment, ring, model);
    check();
    check();
    assert.throws(() => check(good, otherR), /Changed supplied coherent model/u);
    assert.throws(() => check(good, R, kernelFree('missing_model', p)), /Changed supplied coherent model/u);

    let changed = createFormalFreydNativeModelObservationProofEnvironment(inputs);
    assert.throws(() => check(changed), /Changed model connecting signature/u);
    for (const name of Object.keys(FORMAL_FREYD_NATIVE_CONNECTING_SIGNATURE_BINDINGS)) {
        changed = changed.extend({ name, type: kernelUniverse(p), mode, provenance: p });
    }
    assert.throws(() => check(changed), /Changed model connecting signature/u);

    const defined = kernelFree('defined_model', p);
    const definedEnvironment = good.extend({ name: defined.name, type: algebraFormalFreydNativeModelType(R),
        body: M, transparency: 'transparent', mode, provenance: p });
    assert.throws(() => check(definedEnvironment, R, defined), /Changed supplied coherent model/u);
    check();
});
