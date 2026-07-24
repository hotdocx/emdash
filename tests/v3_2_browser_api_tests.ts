/**
 * MIGRATE-2 browser-entry-point consumer tests.
 */

import assert from 'node:assert';
import { describe, it } from 'node:test';
import {
    CoreChecker,
    CoreElaborationSession,
    KernelExpression,
    binderMode,
    kernelApplication,
    kernelBinder,
    kernelBound,
    kernelLambda,
    kernelPi,
    provenance,
    serializeKernelExpression
} from '../src/v3_2/browser';

const because = (detail: string) => provenance(
    'surface',
    detail
);

const implicitFunctorial = binderMode('implicit', 'functorial');
const explicitFunctorial = binderMode('explicit', 'functorial');

const categoryUniverse = (): KernelExpression => kernelApplication(
    'category-universe',
    [],
    because('browser category universe')
);

const bound = (index: number): KernelExpression =>
    kernelBound(index, because(`browser bound occurrence ${index}`));

const objectType = (
    category: KernelExpression
): KernelExpression => {
    const nodeProvenance = because('browser object type');
    return kernelApplication('decode', [{
        value: kernelApplication('object-classifier', [{
            value: category
        }], nodeProvenance)
    }], nodeProvenance);
};

describe('TypeScript v3.2 browser API', () => {
    it('checks a category-polymorphic identity without ambient state', () => {
        const nodeProvenance = because('browser identity');
        const expected = kernelPi(
            kernelBinder(
                'Category',
                categoryUniverse(),
                implicitFunctorial,
                nodeProvenance
            ),
            kernelPi(
                kernelBinder(
                    'value',
                    objectType(bound(0)),
                    explicitFunctorial,
                    nodeProvenance
                ),
                objectType(bound(1)),
                nodeProvenance
            ),
            nodeProvenance
        );
        const term = kernelLambda(
            kernelBinder(
                'Category',
                categoryUniverse(),
                implicitFunctorial,
                nodeProvenance
            ),
            kernelLambda(
                kernelBinder(
                    'value',
                    objectType(bound(0)),
                    explicitFunctorial,
                    nodeProvenance
                ),
                bound(0),
                nodeProvenance
            ),
            nodeProvenance
        );
        const checker = new CoreChecker(new CoreElaborationSession());
        const checked = checker.check(
            checker.rootContext,
            term,
            expected
        );

        assert.equal(
            serializeKernelExpression(checked.term),
            'λ [v0 : Cat], λ (v1 : τ (Obj v0)), v1'
        );
        assert.equal(
            serializeKernelExpression(checked.type),
            'Π [v0 : Cat], Π (v1 : τ (Obj v0)), τ (Obj v0)'
        );
    });

    it('creates isolated checker sessions through the browser entry point', () => {
        const left = new CoreElaborationSession();
        const right = new CoreElaborationSession();
        const type = categoryUniverse();

        const leftMeta = left.freshMeta(
            new CoreChecker(left).rootContext,
            type,
            because('left browser meta')
        );
        const rightMeta = right.freshMeta(
            new CoreChecker(right).rootContext,
            type,
            because('right browser meta')
        );

        assert.equal(leftMeta.identity.index, 0);
        assert.equal(rightMeta.identity.index, 0);
        assert.notEqual(leftMeta.identity.session, rightMeta.identity.session);
    });
});
