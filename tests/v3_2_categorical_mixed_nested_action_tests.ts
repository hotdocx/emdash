/**
 * MIXED-NEST-ACTION-1B existing-conversion result classification.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CoreCategoricalProgram,
    CoreCategoricalProgramError,
    kernelExpressionEquals
} from '../src/v3_2';

const canonicalFixture = (suffix: string) => {
    const emdash = new CoreCategoricalProgram({
        sourceFile:
            `tests/fixtures/categorical-mixed-action-${suffix}.ts`,
        profile: 'fibred-displayed-mixed-nest-1'
    });
    const K = emdash.category(`mixed_action_${suffix}_K`);
    const Z = emdash.category(`mixed_action_${suffix}_Z`);
    const C = emdash.displayedFamily(
        `mixed_action_${suffix}_C`,
        K
    );
    const classifier = emdash.constantDisplayedFamily(
        K,
        emdash.displayedCategoryCategory(Z)
    );
    const Ebar = emdash.section(
        `mixed_action_${suffix}_Ebar`,
        emdash.oppositeDisplayedFamily(classifier)
    );
    const Dbar = emdash.section(
        `mixed_action_${suffix}_Dbar`,
        classifier
    );
    const H = emdash.mixedDisplayedHomFamily(
        classifier,
        Ebar,
        Dbar
    );
    const nested = emdash.displayedFunctor(
        `mixed_action_${suffix}_nested`,
        C,
        H
    );
    const factored = emdash.displayedContextLambda(
        [{ name: 'c', family: C }],
        H,
        ([c]) => {
            const inner = emdash.apply(nested, c);
            return emdash.nestedDisplayedFunctorLambda(
                'z',
                inner,
                z => emdash.apply(inner, z)
            );
        }
    );
    return {
        emdash,
        K,
        Z,
        C,
        Ebar,
        Dbar,
        H,
        nested,
        factored
    };
};

describe('MIXED-NEST-ACTION-1B mixed inner action', () => {
    it('refines an outer base-arrow result and passes it to homd_int',
    () => {
        const {
            emdash,
            K,
            Z,
            C,
            Ebar,
            Dbar,
            factored
        } = canonicalFixture('arrow');
        const x = emdash.object('mixed_action_arrow_x', K);
        const y = emdash.object('mixed_action_arrow_y', K);
        const p = emdash.hom('mixed_action_arrow_p', K, x, y);
        const c = emdash.object(
            'mixed_action_arrow_c',
            emdash.fibre(C, x)
        );
        const move = emdash.apply(factored, p, {
            expectedShape: 'transport-functor'
        });
        const inner = emdash.apply(move, c);
        const factoredCompilation = emdash.compile(factored);
        const moveCompilation = emdash.compile(move);
        const innerCompilation = emdash.compile(inner);
        const sourceAtY = emdash.compile(emdash.apply(Ebar, y));
        const targetAtY = emdash.compile(emdash.apply(Dbar, y));
        const zObject = emdash.compile(
            emdash.object('mixed_action_arrow_z', Z)
        );

        assert.equal(
            factoredCompilation.explicitCore,
            '(free "mixed_action_arrow_nested")'
        );
        assert.match(
            moveCompilation.explicitCore,
            /displayed-functor-transport/u
        );
        assert.equal(
            innerCompilation.surfaceType.tag,
            'displayed-functor'
        );
        if (
            innerCompilation.surfaceType.tag !==
                'displayed-functor' ||
            zObject.surfaceType.tag !== 'object'
        ) {
            assert.fail('Missing internally derived displayed classifier');
        }
        assert.equal(
            kernelExpressionEquals(
                innerCompilation.surfaceType.baseCategory,
                zObject.surfaceType.category
            ),
            true
        );
        assert.equal(
            kernelExpressionEquals(
                innerCompilation.surfaceType.sourceFamily,
                sourceAtY.explicitTerm
            ),
            true
        );
        assert.equal(
            kernelExpressionEquals(
                innerCompilation.surfaceType.targetFamily,
                targetAtY.explicitTerm
            ),
            true
        );
        assert.notEqual(
            innerCompilation.explicitInferredType,
            innerCompilation.explicitExpectedType
        );
        assert.doesNotMatch(
            innerCompilation.explicitCore,
            /coerc|cast/u
        );

        const internalHom = emdash.compile(
            emdash.displayedInternalHom(inner)
        );
        assert.match(internalHom.explicitCore, /homd_int/u);
        assert.match(
            internalHom.explicitCore,
            /displayed-functor-transport/u
        );
        assert.equal(
            internalHom.productionLambdapiDependency,
            false
        );
    });

    it('also refines direct base-object evaluation of the same package',
    () => {
        const {
            emdash,
            K,
            Z,
            C,
            factored
        } = canonicalFixture('object');
        const y = emdash.object('mixed_action_object_y', K);
        const c = emdash.object(
            'mixed_action_object_c',
            emdash.fibre(C, y)
        );
        const atY = emdash.apply(factored, y, {
            expectedShape: 'fibre-functor'
        });
        const inner = emdash.apply(atY, c);
        const compiled = emdash.compile(inner);
        const zObject = emdash.compile(
            emdash.object('mixed_action_object_z', Z)
        );

        assert.equal(compiled.surfaceType.tag, 'displayed-functor');
        if (
            compiled.surfaceType.tag !== 'displayed-functor' ||
            zObject.surfaceType.tag !== 'object'
        ) {
            assert.fail('Missing direct nested displayed classifier');
        }
        assert.equal(
            kernelExpressionEquals(
                compiled.surfaceType.baseCategory,
                zObject.surfaceType.category
            ),
            true
        );
        assert.match(
            emdash.compile(
                emdash.displayedInternalHom(inner)
            ).explicitCore,
            /homd_int/u
        );
    });

    it('retains generic Hom for a non-Catd constant fibre',
    () => {
        const emdash = new CoreCategoricalProgram({
            profile: 'fibred-displayed-mixed-nest-1'
        });
        const K = emdash.category('mixed_action_wrong_K');
        const Q = emdash.category('mixed_action_wrong_Q');
        const C = emdash.displayedFamily('mixed_action_wrong_C', K);
        const classifier = emdash.constantDisplayedFamily(K, Q);
        const Ebar = emdash.section(
            'mixed_action_wrong_Ebar',
            emdash.oppositeDisplayedFamily(classifier)
        );
        const Dbar = emdash.section(
            'mixed_action_wrong_Dbar',
            classifier
        );
        const H = emdash.mixedDisplayedHomFamily(
            classifier,
            Ebar,
            Dbar
        );
        const nested = emdash.displayedFunctor(
            'mixed_action_wrong_nested',
            C,
            H
        );
        const x = emdash.object('mixed_action_wrong_x', K);
        const y = emdash.object('mixed_action_wrong_y', K);
        const p = emdash.hom('mixed_action_wrong_p', K, x, y);
        const c = emdash.object(
            'mixed_action_wrong_c',
            emdash.fibre(C, x)
        );
        const inner = emdash.apply(
            emdash.apply(nested, p, {
                expectedShape: 'transport-functor'
            }),
            c
        );

        assert.equal(
            emdash.compile(inner).surfaceType.tag,
            'hom'
        );
        assert.throws(
            () => emdash.displayedInternalHom(inner),
            (error: unknown) =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'EXPECTED_DISPLAYED_FUNCTOR'
        );
    });
});
