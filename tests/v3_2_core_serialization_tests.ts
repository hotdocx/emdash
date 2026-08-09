/**
 * Focused USABILITY-1D backend-neutral explicit-Core serialization tests.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_EXPLICIT_SERIALIZATION_REVISION,
    binderMode,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelFree,
    kernelLambda,
    kernelMeta,
    provenance,
    serializeCoreExpression,
    serializeCoreExpressionAtDepth,
    sourceSpan
} from '../src/v3_2';

const at = (
    file: string,
    line: number,
    detail: string
) => provenance(
    'surface',
    detail,
    sourceSpan(file, line, 1, line, 2)
);

describe('TypeScript v3.2 deterministic explicit-Core serialization', () => {
    it('publishes a versioned backend-neutral inspection format', () => {
        assert.equal(
            CORE_EXPLICIT_SERIALIZATION_REVISION,
            'EMDASH-CORE-SEXP-1'
        );
        assert.equal(
            serializeCoreExpression(
                kernelFree('A', at('one.ts', 1, 'A'))
            ),
            '(free "A")'
        );
    });

    it('is invariant under provenance and binder-hint changes', () => {
        const firstProvenance = at('first.ts', 10, 'first');
        const secondProvenance = at('second.ts', 40, 'second');
        const mode = binderMode('explicit', 'functorial');
        const first = kernelLambda(
            kernelBinder(
                'x',
                kernelFree('A', firstProvenance),
                mode,
                firstProvenance
            ),
            kernelBound(0, firstProvenance),
            firstProvenance
        );
        const second = kernelLambda(
            kernelBinder(
                'renamed',
                kernelFree('A', secondProvenance),
                mode,
                secondProvenance
            ),
            kernelBound(0, secondProvenance),
            secondProvenance
        );
        const expected =
            '(lambda (binder explicit functorial (free "A")) (bound 0))';
        assert.equal(serializeCoreExpression(first), expected);
        assert.equal(serializeCoreExpression(second), expected);
    });

    it('retains generic-call plicity and presentation-only free labels', () => {
        const nodeProvenance = at('call.ts', 2, 'call');
        const expression = kernelCall(
            kernelFree('internal_functor', nodeProvenance),
            [
                {
                    plicity: 'implicit',
                    value: kernelFree('A', nodeProvenance)
                },
                {
                    plicity: 'explicit',
                    value: kernelFree('F', nodeProvenance)
                }
            ],
            nodeProvenance
        );
        assert.equal(
            serializeCoreExpression(expression, {
                freeReferenceLabels: {
                    internal_functor:
                        'emdash.categorical.functor-constructor'
                }
            }),
            '(call ' +
            '(free "emdash.categorical.functor-constructor") ' +
            '(implicit (free "A")) (explicit (free "F")))'
        );
    });

    it('canonicalizes contextual meta sessions by encounter order', () => {
        const nodeProvenance = at('meta.ts', 3, 'meta');
        const first = kernelMeta({
            session: Symbol('first'),
            index: 7
        }, [], nodeProvenance);
        const second = kernelMeta({
            session: Symbol('unrelated-process-session'),
            index: 7
        }, [], nodeProvenance);
        assert.equal(
            serializeCoreExpression(first),
            '(meta 0 7)'
        );
        assert.equal(
            serializeCoreExpression(second),
            '(meta 0 7)'
        );
    });

    it('serializes open terms only under their explicit ambient depth', () => {
        const nodeProvenance = at('open.ts', 4, 'open');
        const expression = kernelBound(1, nodeProvenance);
        assert.equal(
            serializeCoreExpressionAtDepth(expression, 2),
            '(bound 1)'
        );
        assert.throws(
            () => serializeCoreExpressionAtDepth(expression, 1),
            /dangling at binder depth 1/u
        );
        assert.throws(
            () => serializeCoreExpressionAtDepth(expression, -1),
            /ambient depth must be a nonnegative safe integer/u
        );
    });

    it('rejects empty presentation labels without changing Core', () => {
        const expression = kernelFree(
            'A',
            at('label.ts', 4, 'label')
        );
        assert.throws(
            () => serializeCoreExpression(expression, {
                freeReferenceLabels: { A: '' }
            }),
            /labels must be nonempty/
        );
        assert.equal(
            serializeCoreExpression(expression),
            '(free "A")'
        );
    });
});
