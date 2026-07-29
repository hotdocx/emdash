/**
 * SCALE-KIND-PI-1 outer-LF product-sort audit and proposal evidence.
 */

import assert from 'node:assert/strict';
import {
    mkdtempSync,
    readFileSync,
    rmSync,
    writeFileSync
} from 'node:fs';
import {
    join,
    resolve
} from 'node:path';
import {
    spawnSync
} from 'node:child_process';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_LF_SCALE_KIND_PI_AUDIT,
    CoreChecker,
    CoreCheckerError,
    CoreDeclarationEnvironment,
    CoreElaborationSession,
    KernelExpression,
    binderMode,
    isCoreKind,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelFree,
    kernelPi,
    kernelUniverse,
    provenance,
    validateCoreLfScaleKindPiAudit
} from '../src/v3_2';

const explicit = binderMode('explicit', 'functorial');
const at = (detail: string) => provenance('surface', detail);

const pi = (
    name: string,
    domain: KernelExpression,
    body: KernelExpression,
    detail: string
): KernelExpression => kernelPi(
    kernelBinder(name, domain, explicit, at(`${detail} binder`)),
    body,
    at(detail)
);

const expectExpectedType = (action: () => unknown): void => {
    assert.throws(
        action,
        error =>
            error instanceof CoreCheckerError &&
            error.code === 'EXPECTED_TYPE' &&
            /checker sort KIND, not TYPE/u.test(error.message)
    );
};

const basicChecker = (): CoreChecker => {
    const environment = CoreDeclarationEnvironment.empty().extend({
        name: 'sort_A',
        type: kernelUniverse(at('sort A type')),
        mode: explicit,
        provenance: at('sort A declaration')
    });
    return new CoreChecker(new CoreElaborationSession(environment));
};

const encodedUniverseChecker = (): CoreChecker => {
    let environment = CoreDeclarationEnvironment.empty();
    environment = environment.extend({
        name: 'sort_Type',
        type: kernelUniverse(at('code universe type')),
        mode: explicit,
        provenance: at('code universe declaration')
    });
    environment = environment.extend({
        name: 'sort_El',
        type: pi(
            'code',
            kernelFree('sort_Type', at('code universe occurrence')),
            kernelUniverse(at('decoded family universe')),
            'decoding family type'
        ),
        mode: explicit,
        provenance: at('decoding family declaration')
    });
    const checker = new CoreChecker(
        new CoreElaborationSession(environment)
    );
    checker.validateEnvironment();
    return checker;
};

const lambdapiPackageRoot = resolve('emdash2');

const runLambdapiSource = (source: string) => {
    const directory = mkdtempSync(join(
        lambdapiPackageRoot,
        'tmp',
        'scale-kind-pi-'
    ));
    const path = join(directory, 'probe.lp');
    try {
        writeFileSync(path, source, 'utf8');
        return spawnSync(
            'lambdapi',
            ['check', '-w', path],
            {
                cwd: lambdapiPackageRoot,
                encoding: 'utf8',
                timeout: 20_000,
                killSignal: 'SIGINT',
                maxBuffer: 4 * 1024 * 1024
            }
        );
    } finally {
        rmSync(directory, { recursive: true, force: true });
    }
};

describe('SCALE-KIND-PI-1 product-sort audit', () => {
    it('freezes the exact Lambdapi lambda-Pi product matrix', () => {
        const audit = validateCoreLfScaleKindPiAudit();
        assert.deepEqual(
            audit.productSortMatrix.map(cell => ({
                domain: cell.domainAnnotationSort,
                body: cell.bodySort,
                accepted: cell.accepted,
                result: cell.resultSort,
                rejection: cell.rejection
            })),
            [
                {
                    domain: 'TYPE',
                    body: 'TYPE',
                    accepted: true,
                    result: 'TYPE',
                    rejection: undefined
                },
                {
                    domain: 'TYPE',
                    body: 'KIND',
                    accepted: true,
                    result: 'KIND',
                    rejection: undefined
                },
                {
                    domain: 'KIND',
                    body: 'TYPE',
                    accepted: false,
                    result: undefined,
                    rejection: 'KIND-domain-annotation'
                },
                {
                    domain: 'KIND',
                    body: 'KIND',
                    accepted: false,
                    result: undefined,
                    rejection: 'KIND-domain-annotation'
                }
            ]
        );
        assert.equal(
            audit.verdict,
            'preserve-current-checker-and-use-explicit-code-universes'
        );
        assert.equal(audit.nativeUniverseAxiom.typeInType, false);
    });

    it('matches both accepted product-sort cells in TypeScript', () => {
        const checker = basicChecker();
        const A = kernelFree('sort_A', at('A occurrence'));
        const typeType = checker.infer(
            checker.rootContext,
            pi('x', A, A, 'TYPE/TYPE product')
        );
        assert.equal(isCoreKind(typeType.type), false);
        if (!isCoreKind(typeType.type)) {
            assert.equal(typeType.type.tag, 'universe');
        }

        const typeKind = checker.infer(
            checker.rootContext,
            pi(
                'x',
                A,
                kernelUniverse(at('TYPE/KIND body')),
                'TYPE/KIND product'
            )
        );
        assert.equal(isCoreKind(typeKind.type), true);
    });

    it('rejects both KIND-domain cells and a higher-kind annotation', () => {
        const checker = basicChecker();
        const A = kernelFree('sort_A', at('A occurrence'));
        expectExpectedType(() => checker.infer(
            checker.rootContext,
            pi(
                'X',
                kernelUniverse(at('KIND/TYPE domain')),
                kernelBound(0, at('KIND/TYPE body')),
                'KIND/TYPE product'
            )
        ));
        expectExpectedType(() => checker.infer(
            checker.rootContext,
            pi(
                'X',
                kernelUniverse(at('KIND/KIND domain')),
                kernelUniverse(at('KIND/KIND body')),
                'KIND/KIND product'
            )
        ));
        const higherKind = pi(
            'x',
            A,
            kernelUniverse(at('higher-kind result')),
            'higher-kind annotation'
        );
        expectExpectedType(() => checker.infer(
            checker.rootContext,
            pi(
                'F',
                higherKind,
                kernelUniverse(at('higher-kind product body')),
                'higher-kind product'
            )
        ));
    });

    it('uses an explicit code universe without checker changes', () => {
        const checker = encodedUniverseChecker();
        const decoded = kernelCall(
            kernelFree('sort_El', at('El occurrence')),
            [{
                plicity: 'explicit',
                value: kernelBound(0, at('code occurrence'))
            }],
            at('El application')
        );
        const encodedProduct = pi(
            'code',
            kernelFree('sort_Type', at('Type occurrence')),
            decoded,
            'encoded polymorphic product'
        );
        const inferred = checker.infer(
            checker.rootContext,
            encodedProduct
        );
        assert.equal(isCoreKind(inferred.type), false);
        if (!isCoreKind(inferred.type)) {
            assert.equal(inferred.type.tag, 'universe');
        }
        assert.deepEqual(
            CORE_LF_SCALE_KIND_PI_AUDIT
                .explicitCodeUniverse.activeEmdashAnalogue,
            ['Grpd : TYPE', 'τ : Grpd -> TYPE']
        );
    });

    it('is deeply frozen and keeps every semantic expansion withheld', () => {
        const visit = (value: unknown): void => {
            if (value === null || typeof value !== 'object') return;
            assert.equal(Object.isFrozen(value), true);
            Object.values(value as Record<string, unknown>).forEach(visit);
        };
        visit(CORE_LF_SCALE_KIND_PI_AUDIT);
        assert.deepEqual(
            CORE_LF_SCALE_KIND_PI_AUDIT.doesNotAuthorize,
            [
                'TYPE-in-TYPE',
                'KIND-domain-products',
                'native-higher-kinded-quantification',
                'implicit-code-universe-invention',
                'checker-or-Core-semantic-change',
                'generated-eliminator-semantics',
                'Lambdapi-source-change',
                'browser-or-release-promotion',
                'bulk-transfer-or-parser-work',
                'remote-or-history-rewriting-Git-operation'
            ]
        );
        assert.equal(
            readFileSync('src/v3_2/browser.ts', 'utf8')
                .includes('scale_kind_pi'),
            false
        );
    });

    it('fails closed if the audited product matrix is broadened', () => {
        const clone = structuredClone(CORE_LF_SCALE_KIND_PI_AUDIT);
        const cells = clone.productSortMatrix.map(cell => ({ ...cell }));
        cells[2] = {
            domainAnnotationSort: 'KIND',
            bodySort: 'TYPE',
            accepted: true,
            resultSort: 'TYPE'
        };
        assert.throws(
            () => validateCoreLfScaleKindPiAudit({
                ...clone,
                productSortMatrix:
                    cells as unknown as typeof clone.productSortMatrix
            }),
            /product-sort matrix drifted/u
        );
    });

    it(
        'matches the four cells and TYPE axiom in live Lambdapi',
        {
            skip:
                process.env.EMDASH_RUN_LAMBDAPI_SCALE_KIND_PI_PROBES !==
                '1'
        },
        () => {
            const positive = runLambdapiSource([
                'constant symbol A : TYPE;',
                'constant symbol pi_type_type : Π (x : A), A;',
                'constant symbol pi_type_kind : Π (x : A), TYPE;',
                ''
            ].join('\n'));
            assert.equal(positive.error, undefined);
            assert.equal(positive.status, 0, positive.stderr);

            const rejected = [
                'constant symbol bad : Π (X : TYPE), X → X;',
                'constant symbol bad : Π (X : TYPE), TYPE;',
                [
                    'constant symbol A : TYPE;',
                    'constant symbol bad :',
                    '  Π (F : Π (x : A), TYPE), TYPE;'
                ].join('\n')
            ].map(runLambdapiSource);
            for (const result of rejected) {
                assert.notEqual(result.status, 0);
                assert.match(
                    `${result.stdout}\n${result.stderr}`,
                    /KIND[\s\S]*TYPE/u
                );
            }

            const typeInType = runLambdapiSource(
                'assert ⊢ TYPE : TYPE;\n'
            );
            assert.notEqual(typeInType.status, 0);
            assert.match(
                `${typeInType.stdout}\n${typeInType.stderr}`,
                /Assertion failed/u
            );
        }
    );
});
