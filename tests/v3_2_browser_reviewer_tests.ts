/**
 * Focused REVIEWER-INTEGRATE-1A integrated browser-entry tests.
 */

import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import {
    existsSync,
    readFileSync
} from 'node:fs';
import {
    dirname,
    resolve
} from 'node:path';
import {
    describe,
    it
} from 'node:test';
import ts from 'typescript';
import {
    CoreCategoricalProgram,
    CoreCategoricalProgramCompilation
} from '../src/v3_2/categorical_program';
import {
    CORE_BROWSER_REVIEWER_BOUNDARY,
    CORE_BROWSER_REVIEWER_PRESETS,
    CoreBrowserReviewerError,
    CoreBrowserReviewerPresetId,
    CoreBrowserReviewerTextAccepted,
    formatCoreBrowserReviewerFullReport,
    runCoreBrowserReviewerFullReport,
    runCoreBrowserReviewerText
} from '../src/v3_2/browser_reviewer';
import * as acquisition from '../src/v3_2/lf_transfer_acquisition';
import * as contract from
    '../src/v3_2/lf_transfer_acquisition_contract';

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(
        assertDeepFrozen
    );
};

const directCompilation = (
    presetId: CoreBrowserReviewerPresetId
): CoreCategoricalProgramCompilation => {
    switch (presetId) {
        case 'pointwise-application':
        case 'nested-exchange':
        case 'fixed-inner-evaluation':
        case 'whole-hom-action': {
            const program = new CoreCategoricalProgram({
                sourceFile: '<browser-reviewer-direct>'
            });
            const A = program.category('review_A');
            const B = program.category('review_B');
            const C = program.category('review_C');
            const functorsBC = program.functorCategory(B, C);
            const functorsAC = program.functorCategory(A, C);
            const H = program.functor('review_H', A, functorsBC);
            const K = program.functor('review_K', A, B);
            const E = program.functor('review_E', B, functorsAC);
            const F = program.functor('review_F', A, functorsBC);
            const G = program.functor('review_G', A, B);
            const y0 = program.object('review_y0', B);
            const x0 = program.object('review_x0', A);
            const x1 = program.object('review_x1', A);
            const pA = program.homBoundary(A, x0, x1);
            if (presetId === 'pointwise-application') {
                return program.compile(program.lambda(
                    'x',
                    A,
                    C,
                    x => program.apply(
                        program.apply(H, x),
                        program.apply(K, x)
                    )
                ));
            }
            if (presetId === 'nested-exchange') {
                return program.compile(program.lambda(
                    'x',
                    A,
                    functorsBC,
                    x => program.lambda(
                        'y',
                        B,
                        C,
                        y => program.apply(
                            program.apply(E, y),
                            x
                        )
                    )
                ));
            }
            if (presetId === 'fixed-inner-evaluation') {
                return program.compile(program.lambda(
                    'x',
                    A,
                    C,
                    x => program.apply(
                        program.apply(F, x),
                        y0
                    )
                ));
            }
            return program.compile(program.apply(G, pA, {
                expectedShape: 'whole-hom-action'
            }));
        }
        case 'indexed-section-composition': {
            const program = new CoreCategoricalProgram({
                sourceFile: '<browser-reviewer-direct>',
                profile: 'usability-dependent-1a'
            });
            const K = program.category('review_K');
            const E = program.displayedFamily('review_E', K);
            const D = program.displayedFamily('review_D', K);
            const FF = program.displayedFunctor('review_FF', E, D);
            const s = program.section('review_s', E);
            return program.compile(program.dependentLambda(
                'k',
                D,
                k => program.apply(
                    program.apply(FF, k),
                    program.apply(s, k)
                )
            ));
        }
        case 'displayed-functor-composition': {
            const program = new CoreCategoricalProgram({
                sourceFile: '<browser-reviewer-direct>',
                profile: 'fibred-binder-1'
            });
            const K = program.category('review_K');
            const E = program.displayedFamily('review_E', K);
            const D = program.displayedFamily('review_D', K);
            const Q = program.displayedFamily('review_Q', K);
            const FF = program.displayedFunctor('review_FF', E, D);
            const GG = program.displayedFunctor('review_GG', D, Q);
            return program.compile(program.displayedFunctorLambda(
                'a',
                E,
                Q,
                a => program.apply(
                    GG,
                    program.apply(FF, a)
                )
            ));
        }
        case 'displayed-functor-weakening': {
            const program = new CoreCategoricalProgram({
                sourceFile: '<browser-reviewer-direct>',
                profile: 'fibred-weaken-reindex-1'
            });
            const K = program.category('review_K');
            const E = program.displayedFamily('review_E', K);
            const D = program.displayedFamily('review_D', K);
            const s = program.section('review_s', D);
            return program.compile(program.displayedFunctorLambda(
                'a',
                E,
                D,
                a => program.apply(s, program.indexOf(a))
            ));
        }
        case 'displayed-sibling-pairing': {
            const program = new CoreCategoricalProgram({
                sourceFile: '<browser-reviewer-direct>',
                profile: 'fibred-displayed-bracket-1'
            });
            const K = program.category('review_K');
            const B = program.displayedFamily('review_B', K);
            const C = program.displayedFamily('review_C', K);
            const D = program.displayedFamily('review_D', K);
            const Q = program.displayedFamily('review_Q', K);
            const FF = program.displayedFunctor('review_FF', B, D);
            const GG = program.displayedFunctor('review_GG', C, Q);
            const target = program.displayedProduct(D, Q);
            return program.compile(program.displayedContextLambda(
                [
                    { name: 'b', family: B },
                    { name: 'c', family: C }
                ],
                target,
                ([b, c]) => program.fibrePair(
                    program.apply(FF, b),
                    program.apply(GG, c)
                )
            ));
        }
        case 'displayed-mixed-telescope': {
            const program = new CoreCategoricalProgram({
                sourceFile: '<browser-reviewer-direct>',
                profile: 'fibred-displayed-chain-2a'
            });
            const K = program.category('review_K');
            const A = program.displayedFamily('review_A', K);
            const sigmaA = program.totalCategory(A);
            const B = program.displayedFamily('review_B', sigmaA);
            const C = program.displayedFamily('review_C', sigmaA);
            const P = program.displayedProduct(B, C);
            const sigmaP = program.totalCategory(P);
            const D = program.displayedFamily('review_D', sigmaP);
            const projectionP = program.sigmaProjection(P);
            const liftedB = program.pullbackFamily(B, projectionP);
            const liftedC = program.pullbackFamily(C, projectionP);
            const target = program.displayedProduct(liftedB, liftedC);
            return program.compile(
                program.displayedDependentContextLambda(
                    [
                        { name: 'a', family: A },
                        { name: 'b', family: B },
                        { name: 'c', family: C },
                        { name: 'd', family: D }
                    ],
                    target,
                    ([, b, c]) => program.fibrePair(b, c)
                )
            );
        }
        case 'displayed-transfor-composition': {
            const program = new CoreCategoricalProgram({
                sourceFile: '<browser-reviewer-direct>',
                profile: 'fibred-transfd-1'
            });
            const K = program.category('review_K');
            const E = program.displayedFamily('review_E', K);
            const D = program.displayedFamily('review_D', K);
            const F0 = program.displayedFunctor('review_F0', E, D);
            const F1 = program.displayedFunctor('review_F1', E, D);
            const F2 = program.displayedFunctor('review_F2', E, D);
            const eta = program.displayedTransfor(
                'review_eta',
                F0,
                F1
            );
            const theta = program.displayedTransfor(
                'review_theta',
                F1,
                F2
            );
            return program.compile(program.displayedTransforLambda(
                'k',
                F0,
                F2,
                k => program.composeCells(
                    program.apply(theta, k),
                    program.apply(eta, k)
                )
            ));
        }
        default: {
            const exhaustive: never = presetId;
            return exhaustive;
        }
    }
};

const nodeBuiltins = new Set([
    'assert',
    'buffer',
    'child_process',
    'crypto',
    'events',
    'fs',
    'http',
    'https',
    'module',
    'net',
    'os',
    'path',
    'perf_hooks',
    'process',
    'stream',
    'timers',
    'tls',
    'tty',
    'url',
    'util',
    'v8',
    'vm',
    'worker_threads',
    'zlib'
]);

const moduleSpecifiers = (
    file: string,
    source: string
): readonly string[] => {
    const syntax = ts.createSourceFile(
        file,
        source,
        ts.ScriptTarget.Latest,
        true,
        file.endsWith('.tsx')
            ? ts.ScriptKind.TSX
            : ts.ScriptKind.TS
    );
    const specifiers: string[] = [];
    const visit = (node: ts.Node): void => {
        if (
            (
                ts.isImportDeclaration(node) ||
                ts.isExportDeclaration(node)
            ) &&
            node.moduleSpecifier !== undefined &&
            ts.isStringLiteral(node.moduleSpecifier)
        ) {
            specifiers.push(node.moduleSpecifier.text);
        }
        if (
            ts.isCallExpression(node) &&
            node.expression.kind === ts.SyntaxKind.ImportKeyword &&
            node.arguments.length === 1 &&
            ts.isStringLiteral(node.arguments[0])
        ) {
            specifiers.push(node.arguments[0].text);
        }
        if (
            ts.isCallExpression(node) &&
            ts.isIdentifier(node.expression) &&
            node.expression.text === 'require' &&
            node.arguments.length === 1 &&
            ts.isStringLiteral(node.arguments[0])
        ) {
            specifiers.push(node.arguments[0].text);
        }
        ts.forEachChild(node, visit);
    };
    visit(syntax);
    return Object.freeze(specifiers);
};

const resolveLocalModule = (
    importingFile: string,
    specifier: string
): string => {
    const unresolved = resolve(dirname(importingFile), specifier);
    const withoutJs = specifier.endsWith('.js')
        ? unresolved.slice(0, -3)
        : unresolved;
    const candidates = [
        withoutJs,
        `${withoutJs}.ts`,
        `${withoutJs}.tsx`,
        resolve(withoutJs, 'index.ts')
    ];
    const resolved = candidates.find(candidate => existsSync(candidate));
    assert.notEqual(
        resolved,
        undefined,
        `Cannot resolve reviewer dependency ${specifier} from ${importingFile}`
    );
    return resolved as string;
};

const collectLocalClosure = (
    entry: string
): ReadonlySet<string> => {
    const pending = [resolve(entry)];
    const visited = new Set<string>();
    while (pending.length > 0) {
        const file = pending.pop() as string;
        if (visited.has(file)) continue;
        visited.add(file);
        const source = readFileSync(file, 'utf8');
        for (const specifier of moduleSpecifiers(file, source)) {
            if (specifier.startsWith('.')) {
                pending.push(resolveLocalModule(file, specifier));
                continue;
            }
            const bare = specifier.startsWith('node:')
                ? specifier.slice('node:'.length)
                : specifier.split('/')[0];
            assert.equal(
                specifier.startsWith('node:') ||
                    nodeBuiltins.has(bare),
                false,
                `Reviewer dependency reaches Node builtin ${specifier} ` +
                    `from ${file}`
            );
        }
    }
    return visited;
};

describe('REVIEWER-INTEGRATE-1A integrated browser entry', () => {
    it('checks every editable preset through the same direct program path', () => {
        assert.deepEqual(
            CORE_BROWSER_REVIEWER_PRESETS.map(preset => preset.id),
            [
                'pointwise-application',
                'nested-exchange',
                'fixed-inner-evaluation',
                'whole-hom-action',
                'indexed-section-composition',
                'displayed-functor-composition',
                'displayed-functor-weakening',
                'displayed-sibling-pairing',
                'displayed-mixed-telescope',
                'displayed-transfor-composition'
            ]
        );
        for (const preset of CORE_BROWSER_REVIEWER_PRESETS) {
            const result = runCoreBrowserReviewerText({
                presetId: preset.id,
                source: preset.source
            });
            assert.equal(result.status, 'accepted');
            if (result.status !== 'accepted') continue;
            const direct = directCompilation(preset.id);
            assert.equal(result.explicitCore, direct.explicitCore);
            assert.equal(
                result.inferredType,
                direct.explicitInferredType
            );
            assert.equal(
                result.expectedType,
                direct.explicitExpectedType
            );
            assert.deepEqual(
                result.structuralPrerequisites,
                direct.structuralPrerequisites
            );
            assert.equal(result.productionLambdapiDependency, false);
            assertDeepFrozen(result);
        }
        const nested = runCoreBrowserReviewerText({
            presetId: 'nested-exchange',
            source: 'λ^f x : A. λ^f y : B. E y x'
        });
        assert.equal(nested.status, 'accepted');
        if (nested.status === 'accepted') {
            assert.ok(
                nested.structuralPrerequisites.includes(
                    'exchange-functor-abstraction'
                )
            );
        }
    });

    it('returns an exact source-located edited-input diagnostic', () => {
        const result = runCoreBrowserReviewerText({
            presetId: 'whole-hom-action',
            source: 'G\n C',
            sourceFile: 'reviewer-input.emdash'
        });
        assert.equal(result.status, 'rejected');
        if (result.status !== 'rejected') return;
        assert.deepEqual(result.diagnostic, {
            phase: 'resolution',
            code: 'EXPECTED_ARGUMENT',
            message:
                "Category 'C' is not an admissible categorical " +
                'application argument at reviewer-input.emdash:2:2',
            detail:
                "Category 'C' is not an admissible categorical " +
                'application argument',
            span: {
                file: 'reviewer-input.emdash',
                start: { line: 2, column: 2 },
                end: { line: 2, column: 3 }
            }
        });
        assertDeepFrozen(result);
    });

    it('fails closed on an unknown runtime preset', () => {
        assert.throws(
            () => runCoreBrowserReviewerText({
                presetId:
                    'not-reviewed' as CoreBrowserReviewerPresetId,
                source: 'G pA'
            }),
            error =>
                error instanceof CoreBrowserReviewerError &&
                error.code === 'UNKNOWN_REVIEWER_PRESET'
        );
    });

    it('publishes the exact deeply frozen capability boundary', () => {
        assert.equal(
            CORE_BROWSER_REVIEWER_BOUNDARY.revision,
            'BOOK-REVIEWER-BRIDGE-1A-BROWSER-REVIEWER-1'
        );
        assert.equal(
            CORE_BROWSER_REVIEWER_BOUNDARY.fullReportExecution,
            'explicit-user-action'
        );
        assert.equal(
            CORE_BROWSER_REVIEWER_BOUNDARY.semanticEffects
                .newCheckerOrEvaluatorBranchCount,
            0
        );
        assert.ok(
            CORE_BROWSER_REVIEWER_BOUNDARY.supported.includes(
                'ten categorical text presets across ^f, ^n, ^fd, and ^nd'
            )
        );
        assert.ok(
            CORE_BROWSER_REVIEWER_BOUNDARY.deferred.includes(
                'whole-library transfer graduation'
            )
        );
        assertDeepFrozen(CORE_BROWSER_REVIEWER_BOUNDARY);
        assertDeepFrozen(CORE_BROWSER_REVIEWER_PRESETS);
    });

    it(
        'executes and formats the unchanged three research candidates',
        { timeout: 180_000 },
        () => {
            const report = runCoreBrowserReviewerFullReport();
            assert.equal(
                report.components.outerDependentLf.profile,
                'emdash-v3.2-dttlf-directed-1'
            );
            assert.equal(
                report.components.ordinaryFunctorialBinding.candidate,
                'emdash-v3.2-usability-1d'
            );
            assert.equal(
                report.components.displayedDependentBinding.candidate,
                'emdash-v3.2-displayed-chain-1a'
            );
            const formatted =
                formatCoreBrowserReviewerFullReport(report);
            assert.match(
                formatted,
                /=== 1\. Outer dependent logical framework ===/u
            );
            assert.match(
                formatted,
                /=== 3\. Displayed dependent binding ===/u
            );
        }
    );

    it('keeps one contract implementation and the Node verifier API', () => {
        assert.equal(
            acquisition.createCoreLfCanonicalSelectionContract,
            contract.createCoreLfCanonicalSelectionContract
        );
        assert.equal(
            acquisition.CoreLfCanonicalAcquisitionError,
            contract.CoreLfCanonicalAcquisitionError
        );
        assert.equal(
            typeof acquisition.acquireCoreLfCanonicalCommands,
            'function'
        );
    });

    it('has a Node-free closure through contracts but not acquisition', () => {
        const closure = collectLocalClosure(
            'src/v3_2/browser_reviewer.ts'
        );
        assert.equal(
            closure.has(resolve('src/v3_2/browser_reviewer.ts')),
            true
        );
        assert.equal(
            closure.has(resolve(
                'src/v3_2/lf_transfer_acquisition_contract.ts'
            )),
            true
        );
        assert.equal(
            closure.has(resolve(
                'src/v3_2/lf_transfer_acquisition.ts'
            )),
            false
        );
        assert.equal(
            closure.has(resolve('src/v3_2/product_review_demo.ts')),
            true
        );
    });

    it('wires one lazy reviewer shell, generated book, and frozen Core', () => {
        const bridge = readFileSync(
            'emdash-template/src/emdash_api.ts',
            'utf8'
        );
        const app = readFileSync(
            'emdash-template/src/App.tsx',
            'utf8'
        );
        const rootPackage = JSON.parse(
            readFileSync('package.json', 'utf8')
        ) as { readonly scripts: Readonly<Record<string, string>> };
        const minimalBrowser = readFileSync(
            'src/v3_2/browser.ts',
            'utf8'
        );

        assert.match(
            bridge,
            /import\(['"]\.\.\/\.\.\/src\/v3_2\/browser_reviewer\.js['"]\)/u
        );
        assert.match(
            bridge,
            /new URL\(\s*['"]\.\.\/\.\.\/docs\/emdash-book\.pdf['"]/u
        );
        assert.doesNotMatch(
            bridge,
            /export \* from ['"]\.\.\/\.\.\/src\/v3_2\/index/u
        );
        assert.match(app, /Categorical expression/u);
        assert.match(app, /Run full research report/u);
        assert.match(app, /Open the emdash book/u);
        assert.match(app, /Minimal Core playground/u);
        assert.equal(
            rootPackage.scripts['check:browser-directed'],
            rootPackage.scripts['check:browser-reviewer']
        );
        assert.equal(
            createHash('sha256').update(minimalBrowser).digest('hex'),
            '9923a7a85672d6fbf6441f23f69f1062c702764167338ee40e1a65be9e42cfcc'
        );
        assert.equal(existsSync('docs/emdash-book.pdf'), true);
    });
});
