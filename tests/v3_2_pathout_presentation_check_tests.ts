/** Focused semantic tests for the explicit PathOut presentation checker. */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHOUT_PRESENTATION_1F_MANIFEST,
    parseCorePathoutPresentationText
} from '../src/v3_2/pathout_presentation';
import {
    CORE_PATHOUT_PRESENTATION_1F_CHECK_REVISION,
    CorePathoutFreshCheckError,
    CorePathoutFreshCheckResult,
    checkCorePathoutPresentationRequest,
    formatCorePathoutFreshCheck
} from '../src/v3_2/pathout_presentation_check';

const repositoryRoot = resolve(__dirname, '..');
const results = new Map<string, CorePathoutFreshCheckResult>();
const semanticCheckOptions = {
    skip: process.env.EMDASH_RUN_PATHOUT_PRESENTATION_CHECKS === '1'
        ? false
        : 'set EMDASH_RUN_PATHOUT_PRESENTATION_CHECKS=1 for the cold check'
};

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value as object).forEach(key =>
        assertDeepFrozen((value as Record<PropertyKey, unknown>)[key])
    );
};

describe('PATHOUT-LIBRARY-PRESENTATION-1F explicit semantic check', () => {
    it('freshly checks all four forms through one process-cached transfer',
        semanticCheckOptions,
        () => {
            for (const [index, form] of
                CORE_PATHOUT_PRESENTATION_1F_MANIFEST.forms.entries()) {
                const request = parseCorePathoutPresentationText(
                    form.canonicalSource,
                    `${form.id}.emdash`
                );
                const result = checkCorePathoutPresentationRequest(request);
                results.set(form.id, result);
                assertDeepFrozen(result);
                assert.equal(
                    result.revision,
                    CORE_PATHOUT_PRESENTATION_1F_CHECK_REVISION
                );
                assert.equal(result.status, 'freshly-checked');
                assert.equal(
                    result.evidenceClass,
                    'fresh-TypeScript-semantic-check'
                );
                assert.equal(result.request, request);
                assert.equal(result.canonicalSource, form.canonicalSource);
                assert.ok(result.explicitCore.length > 0);
                assert.ok(result.expectedType.length > 0);
                assert.ok(result.checkedType.length > 0);
                assert.equal(result.semanticCheckpoint, '3b113ad');
                assert.equal(result.completionLedger, '10432ba');
                assert.equal(result.productionBackend, 'typescript-emdash');
                assert.equal(
                    result.compilation.adapterCache,
                    index === 0
                        ? 'created-this-call'
                        : 'reused-in-process'
                );
                assert.deepEqual(result.compilation.runtimeRuleIds, [
                    'pathout.transitivity.' +
                        'fixed-source-selected-component-' +
                        'consumer-parent-fusion'
                ]);
            }
            assert.equal(
                results.get('pathout-category')?.normalForm,
                undefined
            );
            assert.equal(
                results.get('canonical-rho')?.normalForm,
                undefined
            );
            assert.equal(
                results.get('fixed-source-induction')?.normalForm,
                undefined
            );
            const composition = results.get('composition-normal-form');
            assert.ok(composition?.normalForm);
            assert.equal(
                composition.normalForm.status,
                'definitionally-equal'
            );
            assert.ok(composition.normalForm.comparisonSteps > 0);
            assert.match(
                composition.normalForm.expression,
                /hom_precomp_along_fapp0/u
            );
        });

    it('rejects incompatible variable roles and endpoints',
        semanticCheckOptions, () => {
        for (const source of [
            'PathOut(Z, Z)',
            'rho(Z, x, y, x)',
            'Ind(Z, x, Z, u)',
            'compose(Z, x, y, z, p, p)'
        ]) {
            const request = parseCorePathoutPresentationText(source);
            assert.throws(
                () => checkCorePathoutPresentationRequest(request),
                error =>
                    error instanceof CorePathoutFreshCheckError &&
                    error.code === 'VARIABLE_ROLE_CONFLICT'
            );
        }
    });

    it('formats only actual fresh semantic evidence',
        semanticCheckOptions, () => {
        const composition = results.get('composition-normal-form');
        assert.ok(composition);
        const formatted = formatCorePathoutFreshCheck(composition);
        assert.match(
            formatted,
            /^FRESH TYPESCRIPT SEMANTIC CHECK: ACCEPTED/u
        );
        assert.match(formatted, /Evidence class: fresh-TypeScript/u);
        assert.match(formatted, /Reviewed normal form:/u);
        assert.match(formatted, /Semantic checkpoint: 3b113ad/u);
        assert.match(formatted, /Lambdapi was not run/u);
        assert.doesNotMatch(formatted, /qualified-at-pinned-checkpoint/u);
    });

    it('is imported only by explicit Node or CLI owners', () => {
        const browserSafe = readFileSync(
            resolve(repositoryRoot, 'src/v3_2/pathout_presentation.ts'),
            'utf8'
        );
        const browserEntry = readFileSync(
            resolve(repositoryRoot, 'emdash-template/src/emdash_api.ts'),
            'utf8'
        );
        assert.doesNotMatch(browserSafe, /pathout_presentation_check/u);
        assert.doesNotMatch(browserEntry, /pathout_presentation_check/u);
        for (const relative of [
            'src/v3_2/index.ts',
            'src/v3_2/package_core.ts',
            'src/v3_2/package_authoring.ts',
            'src/v3_2/package_workspace.ts',
            'src/v3_2/browser.ts'
        ]) {
            assert.doesNotMatch(
                readFileSync(resolve(repositoryRoot, relative), 'utf8'),
                /pathout_presentation_check/u,
                relative
            );
        }
    });
});
