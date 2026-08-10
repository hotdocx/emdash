/** Focused SIMP-5B0 tests for the proof-document conversion boundary. */

import assert from 'node:assert';
import { describe, it } from 'node:test';
import {
    CORE_PROOF_CHECKER_PROFILE,
    CORE_PROOF_DOCUMENT_PROFILE,
    CoreCheckerError,
    CoreLfDeclarationEnvironment,
    KernelExpression,
    binderMode,
    compileCoreProofDocument,
    coreProofPlanExact,
    createCoreProofArtifactFingerprint,
    createCoreProofChecker,
    kernelApplication,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelFree,
    kernelLambda,
    kernelPi,
    provenance,
    sourceSpan
} from '../src/v3_2';

const fixture = 'tests/fixtures/v3_2_proof_checker.surface.ts';
const at = (line: number) => sourceSpan(fixture, line, 1, line, 2);
const because = (line: number, detail: string) =>
    provenance('surface', detail, at(line));
const explicitFunctorial = binderMode('explicit', 'functorial');

const groupoidUniverse = (line: number): KernelExpression =>
    kernelApplication(
        'groupoid-universe',
        [],
        because(line, 'SIMP-5B0 groupoid universe')
    );

const decode = (
    classifier: KernelExpression,
    line: number
): KernelExpression => kernelApplication(
    'decode',
    [{ value: classifier }],
    because(line, 'SIMP-5B0 decoded groupoid')
);

const free = (name: string, line: number): KernelExpression =>
    kernelFree(name, because(line, `SIMP-5B0 reference ${name}`));

const call = (
    callee: KernelExpression,
    values: readonly KernelExpression[],
    line: number,
    detail: string
): KernelExpression => kernelCall(
    callee,
    values.map(value => ({ plicity: 'explicit' as const, value })),
    because(line, detail)
);

const pi = (
    name: string,
    type: KernelExpression,
    body: KernelExpression,
    line: number
): KernelExpression => kernelPi(
    kernelBinder(
        name,
        type,
        explicitFunctorial,
        because(line, `SIMP-5B0 binder ${name}`)
    ),
    body,
    because(line, `SIMP-5B0 Pi ${name}`)
);

interface TransportFixture {
    readonly environment: CoreLfDeclarationEnvironment;
    readonly term: KernelExpression;
    readonly target: KernelExpression;
    readonly lambdaCalleeCall: KernelExpression;
}

const transportFixture = (): TransportFixture => {
    let environment = CoreLfDeclarationEnvironment.empty();
    const assume = (
        name: string,
        type: KernelExpression,
        line: number
    ): void => {
        environment = environment.extend({
            name,
            type,
            mode: explicitFunctorial,
            provenance: because(line, `SIMP-5B0 declaration ${name}`)
        });
    };

    assume('ProofA', groupoidUniverse(1), 1);
    const A = free('ProofA', 2);
    const decodedA = decode(A, 2);
    assume(
        'ProofEq',
        pi('left', decodedA, pi(
            'right', decodedA,
            groupoidUniverse(2),
            2
        ), 2),
        2
    );
    assume('proof_x', decodedA, 3);
    assume('proof_y', decodedA, 4);
    const x = free('proof_x', 5);
    const y = free('proof_y', 5);
    assume(
        'proof_p',
        decode(
            call(free('ProofEq', 5), [x, y], 5, 'SIMP-5B0 path'),
            5
        ),
        5
    );
    const familyType = pi(
        'value',
        decodedA,
        groupoidUniverse(6),
        6
    );
    assume('ProofQ', familyType, 6);
    environment = environment.extend({
        name: 'ProofQAlias',
        type: familyType,
        body: free('ProofQ', 7),
        transparency: 'transparent',
        mode: explicitFunctorial,
        provenance: because(7, 'SIMP-5B0 transparent family alias')
    });
    assume(
        'proof_u',
        decode(
            call(free('ProofQ', 8), [x], 8, 'SIMP-5B0 base case'),
            8
        ),
        8
    );

    const equalityUnderXY = decode(
        call(
            free('ProofEq', 9),
            [
                kernelBound(1, because(9, 'SIMP-5B0 transport x')),
                kernelBound(0, because(9, 'SIMP-5B0 transport y'))
            ],
            9,
            'SIMP-5B0 transport equality'
        ),
        9
    );
    const motiveType = pi(
        'value',
        decodedA,
        groupoidUniverse(9),
        9
    );
    const baseType = decode(
        call(
            kernelBound(0, because(9, 'SIMP-5B0 motive at x')),
            [kernelBound(3, because(9, 'SIMP-5B0 bound x'))],
            9,
            'SIMP-5B0 motive base call'
        ),
        9
    );
    const resultType = decode(
        call(
            kernelBound(1, because(9, 'SIMP-5B0 result motive')),
            [kernelBound(3, because(9, 'SIMP-5B0 bound y'))],
            9,
            'SIMP-5B0 motive result call'
        ),
        9
    );
    assume(
        'proof_transport',
        pi('x', decodedA, pi('y', decodedA, pi(
            'path',
            equalityUnderXY,
            pi('motive', motiveType, pi(
                'base',
                baseType,
                resultType,
                9
            ), 9),
            9
        ), 9), 9),
        9
    );

    const motive = kernelLambda(
        kernelBinder(
            'value',
            decodedA,
            explicitFunctorial,
            because(10, 'SIMP-5B0 explicit lambda motive')
        ),
        call(
            free('ProofQ', 10),
            [kernelBound(0, because(10, 'SIMP-5B0 motive value'))],
            10,
            'SIMP-5B0 family motive body'
        ),
        because(10, 'SIMP-5B0 lambda motive')
    );
    const term = call(
        free('proof_transport', 11),
        [x, y, free('proof_p', 11), motive, free('proof_u', 11)],
        11,
        'SIMP-5B0 transport proof'
    );
    const target = decode(
        call(
            free('ProofQAlias', 12),
            [y],
            12,
            'SIMP-5B0 user target'
        ),
        12
    );
    const lambdaCalleeCall = call(
        motive,
        [x],
        13,
        'SIMP-5B0 forbidden lambda-callee inference'
    );
    return { environment, term, target, lambdaCalleeCall };
};

describe('TypeScript v3.2 SIMP-5B0 proof checker', () => {
    it('replays a transport motive through bounded beta and exact delta', () => {
        const fixture_ = transportFixture();
        const checker = createCoreProofChecker(fixture_.environment);
        assert.doesNotThrow(() => checker.check(
            checker.rootContext,
            fixture_.term,
            fixture_.target
        ));
        const reductions = checker.checkerComparisonRecords.flatMap(
            result => result.trace.map(entry => entry.reduction.kind)
        );
        assert.ok(reductions.includes('beta'));
        assert.ok(reductions.includes('delta'));

        const fingerprint = createCoreProofArtifactFingerprint({
            source: {
                id: 'tests/fixtures/v3_2_proof_checker.surface.ts',
                sha256: `sha256:${'a'.repeat(64)}`
            },
            profileSha256: `sha256:${'b'.repeat(64)}`
        });
        const compiled = compileCoreProofDocument({
            moduleId: 'proof.checker.fixture',
            declarationId: 'transport_beta_delta',
            environment: fixture_.environment,
            type: fixture_.target,
            plan: coreProofPlanExact(fixture_.term),
            provenance: because(14, 'SIMP-5B0 proof root'),
            fingerprint
        });
        assert.equal(compiled.artifact.state.status, 'complete');
        assert.ok(compiled.checkedTerm);
        assert.match(compiled.artifact.checkedCore ?? '', /proof_transport/u);
    });

    it('keeps annotated lambda-callee inference closed', () => {
        const fixture_ = transportFixture();
        const checker = createCoreProofChecker(fixture_.environment);
        assert.throws(
            () => checker.infer(
                checker.rootContext,
                fixture_.lambdaCalleeCall
            ),
            (error: unknown) => {
                assert.ok(error instanceof CoreCheckerError);
                assert.equal(error.code, 'CANNOT_INFER_LAMBDA');
                return true;
            }
        );
        assert.equal(
            CORE_PROOF_CHECKER_PROFILE.permitsAnnotatedLambdaInference,
            false
        );
        assert.equal(CORE_PROOF_CHECKER_PROFILE.acceptsCatalogRuntime, false);
        assert.equal(
            CORE_PROOF_DOCUMENT_PROFILE.checkerProfileRevision,
            CORE_PROOF_CHECKER_PROFILE.revision
        );
        assert.equal(Object.isFrozen(CORE_PROOF_CHECKER_PROFILE), true);
    });
});
