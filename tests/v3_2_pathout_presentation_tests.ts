/** Focused tests for the browser-safe PathOut presentation. */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHOUT_PRESENTATION_1F_MANIFEST,
    CORE_PATHOUT_PRESENTATION_1F_REVISION,
    CorePathoutPresentationError,
    CorePathoutPresentationRequest,
    createCorePathoutQualificationReport,
    formatCorePathoutQualificationReport,
    parseCorePathoutPresentationText,
    serializeCorePathoutPresentationRequest
} from '../src/v3_2/pathout_presentation';

const repositoryRoot = resolve(__dirname, '..');

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value as object).forEach(key =>
        assertDeepFrozen((value as Record<PropertyKey, unknown>)[key])
    );
};

const assertParseError = (
    source: string,
    code: CorePathoutPresentationError['code'],
    line?: number,
    column?: number
): void => {
    assert.throws(
        () => parseCorePathoutPresentationText(source, 'example.emdash'),
        error => {
            if (!(error instanceof CorePathoutPresentationError)) {
                return false;
            }
            assert.equal(error.code, code);
            assert.equal(error.span.file, 'example.emdash');
            if (line !== undefined) assert.equal(error.span.start.line, line);
            if (column !== undefined) {
                assert.equal(error.span.start.column, column);
            }
            return true;
        }
    );
};

describe('PATHOUT-LIBRARY-PRESENTATION-1F browser-safe facade', () => {
    it('publishes an immutable finite manifest with exact evidence class',
        () => {
            const manifest = CORE_PATHOUT_PRESENTATION_1F_MANIFEST;
            assertDeepFrozen(manifest);
            assert.equal(
                manifest.revision,
                'PATHOUT-LIBRARY-PRESENTATION-1F-BROWSER-SAFE-1'
            );
            assert.equal(manifest.forms.length, 4);
            assert.deepEqual(
                manifest.forms.map(form => [
                    form.id,
                    form.head,
                    form.canonicalSource,
                    form.semanticTarget
                ]),
                [
                    [
                        'pathout-category',
                        'PathOut',
                        'PathOut(Z, x)',
                        'PathOut_cat'
                    ],
                    [
                        'canonical-rho',
                        'rho',
                        'rho(Z, x, y, p)',
                        'pathout_refl_arrow'
                    ],
                    [
                        'fixed-source-induction',
                        'Ind',
                        'Ind(Z, x, E, u)',
                        'path_ind_sec'
                    ],
                    [
                        'composition-normal-form',
                        'compose',
                        'compose(Z, x, y, z, p, q)',
                        'path_comp_func-applied-at-q'
                    ]
                ]
            );
            assert.equal(
                manifest.evidenceClass,
                'qualified-at-pinned-checkpoint-not-rerun-in-browser'
            );
            assert.equal(manifest.browser.checksSemantics, false);
            assert.equal(manifest.browser.loadsSemanticTransfer, false);
            assert.deepEqual(manifest.semanticCheckpoints, {
                foundation: '550316a',
                fixedSource: 'a361dc3',
                internalized: 'b6005b3',
                transitivity: '3b113ad',
                ledger: '10432ba'
            });
        });

    it('parses and canonically serializes all four reviewed forms', () => {
        for (const form of CORE_PATHOUT_PRESENTATION_1F_MANIFEST.forms) {
            const request = parseCorePathoutPresentationText(
                form.canonicalSource,
                `${form.id}.emdash`
            );
            assertDeepFrozen(request);
            assert.equal(request.revision,
                CORE_PATHOUT_PRESENTATION_1F_REVISION);
            assert.equal(request.formId, form.id);
            assert.equal(request.head, form.head);
            assert.equal(request.arguments.length, form.argumentRoles.length);
            assert.deepEqual(
                request.arguments.map(argument => argument.role),
                form.argumentRoles
            );
            assert.equal(
                serializeCorePathoutPresentationRequest(request),
                form.canonicalSource
            );
            assert.equal(request.canonicalSource, form.canonicalSource);
        }
    });

    it('supports variable renaming, whitespace, and source spans', () => {
        const request = parseCorePathoutPresentationText(
            '  compose( C, a,\n b, c, f, g )  ',
            'renamed.emdash'
        );
        assert.equal(request.formId, 'composition-normal-form');
        assert.deepEqual(
            request.arguments.map(argument => argument.name),
            ['C', 'a', 'b', 'c', 'f', 'g']
        );
        assert.equal(
            serializeCorePathoutPresentationRequest(request),
            'compose(C, a, b, c, f, g)'
        );
        assert.equal(request.arguments[2]?.span.start.line, 2);
        assert.equal(request.arguments[2]?.span.start.column, 2);
        assert.equal(request.source.file, 'renamed.emdash');
    });

    it('rejects unknown heads, malformed tokens, arity, and trailing input',
        () => {
            assertParseError('J(Z, x)', 'UNKNOWN_HEAD', 1, 1);
            assertParseError('PathOut[Z, x]', 'UNEXPECTED_TOKEN', 1, 8);
            assertParseError('rho(Z, x, y)', 'INVALID_ARITY', 1, 1);
            assertParseError('compose(Z, x, y, z, p, q) extra',
                'TRAILING_INPUT', 1, 27);
            assertParseError('Ind(Z, x, E, )', 'UNEXPECTED_TOKEN');
            assertParseError('', 'UNEXPECTED_END', 1, 1);
        });

    it('formats a visibly non-fresh checkpoint qualification report', () => {
        const request = parseCorePathoutPresentationText(
            'compose(Z, x, y, z, p, q)',
            'composition.emdash'
        );
        const report = createCorePathoutQualificationReport(request);
        assertDeepFrozen(report);
        assert.equal(report.status, 'qualified-at-pinned-checkpoint');
        assert.equal(report.freshSemanticCheck, false);
        assert.equal(report.browserSemanticExecution, false);
        assert.equal(report.productionBackend, 'typescript-emdash');
        assert.equal(report.lambdapiRole, 'bounded-conformance-oracle');
        assert.match(report.boundaryNotice, /did not rerun/u);
        assert.equal(
            report.freshCheckCommand,
            "./scripts/emdash pathout check composition-normal-form " +
                "--source 'compose(Z, x, y, z, p, q)'"
        );
        const formatted = formatCorePathoutQualificationReport(report);
        assert.match(formatted, /^QUALIFIED AT PINNED CHECKPOINT/u);
        assert.match(formatted, /Fresh semantic check in this browser: no/u);
        assert.match(formatted, /TypeScript semantic checkpoint: 3b113ad/u);
        assert.doesNotMatch(formatted, /^CHECKED$/mu);
    });

    it('rejects drifted inert requests before reporting or serializing', () => {
        for (const drift of [
            (request: CorePathoutPresentationRequest) => {
                (request as { head: string }).head = 'rho';
            },
            (request: CorePathoutPresentationRequest) => {
                (request as { canonicalSource: string }).canonicalSource =
                    'PathOut(C, a)';
            },
            (request: CorePathoutPresentationRequest) => {
                (request.arguments[0] as { name: string }).name = 'bad-name';
            },
            (request: CorePathoutPresentationRequest) => {
                (request.arguments[1] as { role: string }).role = 'category';
            }
        ]) {
            const request = JSON.parse(JSON.stringify(
                parseCorePathoutPresentationText('PathOut(Z, x)')
            )) as CorePathoutPresentationRequest;
            drift(request);
            assert.throws(
                () => serializeCorePathoutPresentationRequest(request),
                CorePathoutPresentationError
            );
            assert.throws(
                () => createCorePathoutQualificationReport(request),
                CorePathoutPresentationError
            );
        }
    });

    it('has no transfer, proposal, Node, or public-package dependency', () => {
        const source = readFileSync(
            resolve(repositoryRoot, 'src/v3_2/pathout_presentation.ts'),
            'utf8'
        );
        assert.doesNotMatch(
            source,
            /pathout_(?:foundation|transitivity)_transfer|pathind_.*_transfer/u
        );
        assert.doesNotMatch(source, /pathout_presentation_(?:proposal|review)/u);
        assert.doesNotMatch(source, /from ['"]node:/u);
        for (const relative of [
            'src/v3_2/index.ts',
            'src/v3_2/package_core.ts',
            'src/v3_2/package_authoring.ts',
            'src/v3_2/package_workspace.ts',
            'src/v3_2/browser.ts'
        ]) {
            assert.doesNotMatch(
                readFileSync(resolve(repositoryRoot, relative), 'utf8'),
                /pathout_presentation(?:['"]|;)/u,
                relative
            );
        }
    });
});
