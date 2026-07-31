/**
 * D-DTTLF-USABILITY-029 runtime-backed recursive mixed classifier evidence.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CoreCategoricalProgram,
    kernelExpressionEquals
} from '../src/v3_2';

const fixture = (suffix: string) => {
    const emdash = new CoreCategoricalProgram({
        sourceFile:
            `tests/fixtures/recursive-mixed-${suffix}.ts`,
        profile: 'fibred-displayed-mixed-nest-1'
    });
    const K = emdash.category(`recursive_${suffix}_K`);
    const Z = emdash.category(`recursive_${suffix}_Z`);
    const C = emdash.displayedFamily(`recursive_${suffix}_C`, K);
    const E = emdash.displayedFamily(`recursive_${suffix}_E`, Z);
    const D = emdash.displayedFamily(`recursive_${suffix}_D`, Z);
    const functorCategory = emdash.displayedFunctorCategory(E, D);
    const classifier = emdash.constantDisplayedFamily(
        K,
        functorCategory
    );
    const FFbar = emdash.section(
        `recursive_${suffix}_FFbar`,
        emdash.oppositeDisplayedFamily(classifier)
    );
    const GGbar = emdash.section(
        `recursive_${suffix}_GGbar`,
        classifier
    );
    const nestedTransfd = emdash.mixedDisplayedHomFamily(
        classifier,
        FFbar,
        GGbar
    );
    const nested = emdash.displayedFunctor(
        `recursive_${suffix}_nested`,
        C,
        nestedTransfd
    );
    const x = emdash.object(`recursive_${suffix}_x`, K);
    const y = emdash.object(`recursive_${suffix}_y`, K);
    const p = emdash.hom(`recursive_${suffix}_p`, K, x, y);
    const cx = emdash.object(
        `recursive_${suffix}_cx`,
        emdash.fibre(C, x)
    );
    const cy = emdash.object(
        `recursive_${suffix}_cy`,
        emdash.fibre(C, y)
    );
    const atY = emdash.apply(nested, y, {
        expectedShape: 'fibre-functor'
    });
    const direct = emdash.apply(atY, cy);
    const move = emdash.apply(nested, p, {
        expectedShape: 'transport-functor'
    });
    const transported = emdash.apply(move, cx);
    return {
        emdash,
        K,
        Z,
        C,
        E,
        D,
        FFbar,
        GGbar,
        nestedTransfd,
        nested,
        x,
        y,
        p,
        direct,
        transported
    };
};

describe('D-029 recursive mixed classifier reification', () => {
    it('recovers Nested_transfd at direct and internal base-arrow results',
        () => {
            const {
                emdash,
                Z,
                E,
                direct,
                transported
            } = fixture('projection');
            const directCompilation = emdash.compile(direct);
            const transportedCompilation = emdash.compile(transported);

            assert.equal(
                directCompilation.surfaceType.tag,
                'displayed-transfor'
            );
            assert.equal(
                transportedCompilation.surfaceType.tag,
                'displayed-transfor'
            );
            assert.doesNotMatch(
                directCompilation.explicitCore,
                /coerc|cast/u
            );
            assert.doesNotMatch(
                transportedCompilation.explicitCore,
                /coerc|cast/u
            );
            assert.match(
                transportedCompilation.explicitCore,
                /displayed-functor-transport/u
            );

            const z = emdash.object('recursive_projection_z', Z);
            const w = emdash.object('recursive_projection_w', Z);
            const q = emdash.hom('recursive_projection_q', Z, z, w);
            const u = emdash.object(
                'recursive_projection_u',
                emdash.fibre(E, z)
            );
            const component = emdash.displayedTransforComponent(
                direct,
                z
            );
            const point = emdash.displayedTransforPoint(direct, z, u);
            const naturality = emdash.displayedTransforNaturality(
                direct,
                q,
                u
            );

            assert.equal(emdash.compile(component).surfaceType.tag,
                'transfor');
            assert.equal(emdash.compile(point).surfaceType.tag, 'hom');
            assert.equal(
                emdash.compile(naturality).surfaceType.tag,
                'hom'
            );
            assert.match(
                emdash.compile(naturality).explicitCore,
                /displayed-transfor-higher-cell/u
            );
        });

    it('preserves canonical endpoint fields and reaches the next hom action',
        () => {
            const {
                emdash,
                FFbar,
                GGbar,
                y,
                direct
            } = fixture('next_hom');
            const directCompilation = emdash.compile(direct);
            const FF = emdash.apply(FFbar, y);
            const GG = emdash.apply(GGbar, y);
            const FFCompilation = emdash.compile(FF);
            const GGCompilation = emdash.compile(GG);

            assert.equal(FFCompilation.surfaceType.tag,
                'displayed-functor');
            assert.equal(GGCompilation.surfaceType.tag,
                'displayed-functor');
            assert.equal(
                directCompilation.surfaceType.tag,
                'displayed-transfor'
            );
            if (
                directCompilation.surfaceType.tag !==
                    'displayed-transfor'
            ) {
                assert.fail('Missing recursive displayed-transfor view');
            }
            assert.equal(
                kernelExpressionEquals(
                    directCompilation.surfaceType.sourceFunctor,
                    FFCompilation.explicitTerm
                ),
                true
            );
            assert.equal(
                kernelExpressionEquals(
                    directCompilation.surfaceType.targetFunctor,
                    GGCompilation.explicitTerm
                ),
                true
            );

            const theta = emdash.displayedTransfor(
                'recursive_next_hom_theta',
                FF,
                GG
            );
            const category = emdash.displayedTransforCategory(FF, GG);
            const cell = emdash.hom(
                'recursive_next_hom_cell',
                category,
                direct,
                theta
            );
            const action = emdash.displayedTransforInternalHomAction(
                FF,
                GG
            );
            const objectAction = emdash.apply(action, direct, {
                expectedShape: 'object-value'
            });
            const wholeHomAction = emdash.apply(
                action,
                emdash.homBoundary(category, direct, theta),
                { expectedShape: 'whole-hom-action' }
            );
            const higherCell = emdash.apply(wholeHomAction, cell, {
                expectedShape: 'object-value'
            });

            assert.equal(emdash.compile(cell).surfaceType.tag, 'hom');
            assert.equal(
                emdash.compile(objectAction).surfaceType.tag,
                'displayed-transfor'
            );
            assert.equal(
                emdash.compile(wholeHomAction).surfaceType.tag,
                'functor'
            );
            assert.match(
                emdash.compile(higherCell).explicitCore,
                /tdapp1_int/u
            );
        });

    it('retains a generic Hom view for an unsupported classifier head',
        () => {
            const emdash = new CoreCategoricalProgram({
                profile: 'fibred-displayed-mixed-nest-1'
            });
            const K = emdash.category('recursive_unknown_K');
            const Q = emdash.category('recursive_unknown_Q');
            const C = emdash.displayedFamily('recursive_unknown_C', K);
            const classifier = emdash.constantDisplayedFamily(K, Q);
            const X = emdash.section(
                'recursive_unknown_X',
                emdash.oppositeDisplayedFamily(classifier)
            );
            const Y = emdash.section('recursive_unknown_Y', classifier);
            const H = emdash.mixedDisplayedHomFamily(classifier, X, Y);
            const nested = emdash.displayedFunctor(
                'recursive_unknown_nested',
                C,
                H
            );
            const k = emdash.object('recursive_unknown_k', K);
            const c = emdash.object(
                'recursive_unknown_c',
                emdash.fibre(C, k)
            );
            const inner = emdash.apply(
                emdash.apply(nested, k, {
                    expectedShape: 'fibre-functor'
                }),
                c
            );
            const compiled = emdash.compile(inner);

            assert.equal(compiled.surfaceType.tag, 'hom');
            assert.doesNotMatch(compiled.explicitCore, /coerc|cast/u);
        });
});
