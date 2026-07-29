/**
 * Focused ELAB-2A3B tests for structural bidirectional Core checking.
 */

import assert from 'node:assert';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_OWNER_SCHEMAS,
    CoreChecker,
    CoreCheckerError,
    CoreCheckerErrorCode,
    CoreContextError,
    CoreDeclarationEnvironment,
    CoreElaborationSession,
    CoreOwnerId,
    KernelExpression,
    KernelProbe,
    LAMBDAPI_V32_MODULE,
    binderMode,
    checkLambdapiProbe,
    coreOwnerResultType,
    coreOwnerSignatureType,
    coreOwnerSlotType,
    isCoreKind,
    kernelApplication,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    kernelLambda,
    kernelPi,
    kernelUniverse,
    provenance,
    serializeKernelExpression,
    serializeKernelProbe,
    sourceSpan
} from '../src/v3_2';

const fixture = 'tests/fixtures/v3_2_core_checker.surface.ts';
const at = (line: number, startColumn = 1, endColumn = startColumn + 1) =>
    sourceSpan(fixture, line, startColumn, line, endColumn);

const because = (line: number, detail: string) =>
    provenance('surface', detail, at(line));

const explicitFunctorial = binderMode('explicit', 'functorial');
const implicitFunctorial = binderMode('implicit', 'functorial');
const explicitNatural = binderMode('explicit', 'natural');

const free = (name: string, line: number): KernelExpression =>
    kernelFree(name, because(line, `ELAB-2A3B free occurrence ${name}`));

const bound = (index: number, line: number): KernelExpression =>
    kernelBound(index, because(
        line,
        `ELAB-2A3B bound occurrence ${index}`
    ));

const owner = (
    ownerId: CoreOwnerId,
    arguments_: readonly KernelExpression[],
    line: number
): KernelExpression => kernelApplication(
    ownerId,
    arguments_.map(value => ({ value })),
    because(line, `ELAB-2A3B ${ownerId}`)
);

const categoryUniverse = (line: number): KernelExpression =>
    owner('category-universe', [], line);

const groupoidUniverse = (line: number): KernelExpression =>
    owner('groupoid-universe', [], line);

const decoded = (
    classifier: KernelExpression,
    line: number
): KernelExpression => owner('decode', [classifier], line);

const objectType = (
    category: KernelExpression,
    line: number
): KernelExpression => decoded(
    owner('object-classifier', [category], line),
    line
);

const functorType = (
    source: KernelExpression,
    target: KernelExpression,
    line: number
): KernelExpression => decoded(
    owner('functor-classifier', [source, target], line),
    line
);

const homType = (
    category: KernelExpression,
    source: KernelExpression,
    target: KernelExpression,
    line: number
): KernelExpression => decoded(
    owner('hom-classifier', [category, source, target], line),
    line
);

const categoryIdentityType = (line: number): KernelExpression => {
    const nodeProvenance = because(
        line,
        'ELAB-2A3B category-polymorphic identity type'
    );
    return kernelPi(
        kernelBinder(
            'A',
            categoryUniverse(line),
            implicitFunctorial,
            nodeProvenance
        ),
        kernelPi(
            kernelBinder(
                'x',
                objectType(bound(0, line), line),
                explicitFunctorial,
                nodeProvenance
            ),
            objectType(bound(1, line), line),
            nodeProvenance
        ),
        nodeProvenance
    );
};

const categoryChooserType = (line: number): KernelExpression => {
    const nodeProvenance = because(
        line,
        'ELAB-2A3B underconstrained category chooser type'
    );
    return kernelPi(
        kernelBinder(
            'unused',
            categoryUniverse(line),
            implicitFunctorial,
            nodeProvenance
        ),
        kernelPi(
            kernelBinder(
                'category',
                categoryUniverse(line),
                explicitFunctorial,
                nodeProvenance
            ),
            categoryUniverse(line),
            nodeProvenance
        ),
        nodeProvenance
    );
};

const doubleCategoryIdentityType = (line: number): KernelExpression => {
    const nodeProvenance = because(
        line,
        'ELAB-2A3B doubly category-polymorphic function type'
    );
    return kernelPi(
        kernelBinder(
            'A',
            categoryUniverse(line),
            implicitFunctorial,
            nodeProvenance
        ),
        kernelPi(
            kernelBinder(
                'x',
                objectType(bound(0, line), line),
                explicitFunctorial,
                nodeProvenance
            ),
            kernelPi(
                kernelBinder(
                    'B',
                    categoryUniverse(line),
                    implicitFunctorial,
                    nodeProvenance
                ),
                kernelPi(
                    kernelBinder(
                        'y',
                        objectType(bound(0, line), line),
                        explicitFunctorial,
                        nodeProvenance
                    ),
                    objectType(bound(1, line), line),
                    nodeProvenance
                ),
                nodeProvenance
            ),
            nodeProvenance
        ),
        nodeProvenance
    );
};

const extend = (
    environment: CoreDeclarationEnvironment,
    name: string,
    type: KernelExpression,
    line: number
): CoreDeclarationEnvironment => environment.extend({
    name,
    type,
    mode: explicitFunctorial,
    provenance: because(line, `ELAB-2A3B declaration ${name}`)
});

interface OrdinaryFixture {
    environment: CoreDeclarationEnvironment;
    checker: CoreChecker;
    session: CoreElaborationSession;
}

const ordinaryFixture = (): OrdinaryFixture => {
    let environment = CoreDeclarationEnvironment.empty();
    environment = extend(
        environment,
        'checker_TypeCode',
        kernelUniverse(because(9, 'ELAB-2A3B KIND-level declaration type')),
        9
    );
    environment = extend(
        environment,
        'checker_A',
        categoryUniverse(10),
        10
    );
    environment = extend(
        environment,
        'checker_B',
        categoryUniverse(11),
        11
    );
    environment = extend(
        environment,
        'checker_C',
        categoryUniverse(12),
        12
    );
    environment = extend(
        environment,
        'checker_F',
        functorType(
            free('checker_A', 13),
            free('checker_B', 13),
            13
        ),
        13
    );
    environment = extend(
        environment,
        'checker_X',
        objectType(free('checker_A', 14), 14),
        14
    );
    environment = extend(
        environment,
        'checker_Y',
        objectType(free('checker_A', 15), 15),
        15
    );
    environment = extend(
        environment,
        'checker_XC',
        objectType(free('checker_C', 16), 16),
        16
    );
    environment = extend(
        environment,
        'checker_f',
        homType(
            free('checker_A', 17),
            free('checker_X', 17),
            free('checker_Y', 17),
            17
        ),
        17
    );
    environment = extend(
        environment,
        'checker_poly',
        categoryIdentityType(18),
        18
    );
    environment = extend(
        environment,
        'checker_XB',
        objectType(free('checker_B', 19), 19),
        19
    );
    environment = extend(
        environment,
        'checker_double_poly',
        doubleCategoryIdentityType(20),
        20
    );
    environment = extend(
        environment,
        'checker_choose',
        categoryChooserType(21),
        21
    );
    const session = new CoreElaborationSession(environment);
    return {
        environment,
        session,
        checker: new CoreChecker(session)
    };
};

const expectCheckerError = (
    action: () => unknown,
    code: CoreCheckerErrorCode
): CoreCheckerError => {
    let captured: CoreCheckerError | undefined;
    assert.throws(action, error => {
        assert.ok(error instanceof CoreCheckerError);
        assert.equal(error.code, code);
        captured = error;
        return true;
    });
    return captured!;
};

describe('TypeScript v3.2 ELAB-2A3B Core checker', () => {
    it('tracks lambda-Pi sorts and rejects KIND-domain products', () => {
        const session = new CoreElaborationSession();
        const checker = new CoreChecker(session);

        const category = checker.infer(
            checker.rootContext,
            categoryUniverse(20)
        );
        assert.equal(category.type.tag, 'universe');

        const universe = checker.infer(
            checker.rootContext,
            kernelUniverse(because(21, 'universe inference'))
        );
        assert.equal(isCoreKind(universe.type), true);

        const familyKind = kernelPi(
            kernelBinder(
                'classifier',
                groupoidUniverse(22),
                explicitFunctorial,
                because(22, 'kind-level family binder')
            ),
            kernelUniverse(because(22, 'kind-level family result')),
            because(22, 'kind-level family')
        );
        assert.equal(
            isCoreKind(checker.infer(
                checker.rootContext,
                familyKind
            ).type),
            true
        );

        const kindDomainProduct = kernelPi(
            kernelBinder(
                'T',
                kernelUniverse(because(23, 'KIND-sorted domain')),
                explicitFunctorial,
                because(23, 'forbidden KIND-domain binder')
            ),
            kernelUniverse(because(23, 'KIND-sorted body')),
            because(23, 'forbidden KIND-domain Pi')
        );
        const error = expectCheckerError(
            () => checker.infer(
                checker.rootContext,
                kindDomainProduct
            ),
            'EXPECTED_TYPE'
        );
        assert.match(error.message, /checker sort KIND, not TYPE/);
        assert.equal(error.provenance.span?.start.line, 23);
    });

    it('validates declaration types at both TYPE and KIND levels', () => {
        const fixture_ = ordinaryFixture();
        assert.doesNotThrow(() => fixture_.checker.validateEnvironment());

        const invalidEnvironment = extend(
            fixture_.environment,
            'checker_bad_type',
            free('checker_A', 25),
            25
        );
        const invalidChecker = new CoreChecker(
            new CoreElaborationSession(invalidEnvironment)
        );
        const error = expectCheckerError(
            () => invalidChecker.validateEnvironment(),
            'INVALID_DECLARATION_TYPE'
        );
        assert.match(error.message, /checker_bad_type/);
        assert.equal(error.provenance.span?.start.line, 25);
    });

    it('checks a dependent identity while preserving binder modes', () => {
        const checker = new CoreChecker(new CoreElaborationSession());
        const expected = categoryIdentityType(30);
        const term = kernelLambda(
            kernelBinder(
                'Category',
                categoryUniverse(30),
                implicitFunctorial,
                because(30, 'outer identity lambda')
            ),
            kernelLambda(
                kernelBinder(
                    'value',
                    objectType(bound(0, 30), 30),
                    explicitFunctorial,
                    because(30, 'inner identity lambda')
                ),
                bound(0, 30),
                because(30, 'identity body lambda')
            ),
            because(30, 'dependent identity lambda')
        );

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

    it('recovers a generic implicit from a dependent explicit argument', () => {
        const fixture_ = ordinaryFixture();
        const call = kernelCall(
            free('checker_poly', 40),
            [{
                plicity: 'explicit',
                value: free('checker_X', 40),
                provenance: because(40, 'explicit identity argument')
            }],
            because(40, 'implicit-recovering generic call')
        );
        const inferred = fixture_.checker.infer(
            fixture_.checker.rootContext,
            call
        );

        assert.equal(
            serializeKernelExpression(inferred.term),
            '@checker_poly checker_A checker_X'
        );
        assert.equal(
            serializeKernelExpression(inferred.type as KernelExpression),
            'τ (Obj checker_A)'
        );
        assert.equal(inferred.term.tag, 'call');
        if (inferred.term.tag !== 'call') {
            throw new Error('Expected checked generic call');
        }
        assert.equal(inferred.term.arguments.length, 2);
        assert.deepEqual(
            inferred.term.arguments.map(argument => argument.plicity),
            ['implicit', 'explicit']
        );
    });

    it('preserves partial calls so an outer call can recover later implicits', () => {
        const fixture_ = ordinaryFixture();
        const inner = kernelCall(
            free('checker_double_poly', 42),
            [{
                plicity: 'explicit',
                value: free('checker_X', 42)
            }],
            because(42, 'inner partial generic call')
        );
        const outer = kernelCall(
            inner,
            [{
                plicity: 'explicit',
                value: free('checker_XB', 43)
            }],
            because(43, 'outer completing generic call')
        );
        const inferred = fixture_.checker.infer(
            fixture_.checker.rootContext,
            outer
        );

        assert.equal(
            serializeKernelExpression(inferred.term),
            '@checker_double_poly checker_A checker_X ' +
            'checker_B checker_XB'
        );
        assert.equal(
            serializeKernelExpression(inferred.type as KernelExpression),
            'τ (Obj checker_B)'
        );
    });

    it('recovers owner categories solely through the signature catalog', () => {
        const fixture_ = ordinaryFixture();
        const inferred = fixture_.checker.inferOwnerApplication(
            fixture_.checker.rootContext,
            'functor-object',
            [{
                plicity: 'explicit',
                value: free('checker_F', 45)
            }, {
                plicity: 'explicit',
                value: free('checker_X', 45)
            }],
            because(45, 'implicit-recovering owner application')
        );

        assert.equal(
            serializeKernelExpression(inferred.term),
            '@fapp0 checker_A checker_B checker_F checker_X'
        );
        assert.equal(
            serializeKernelExpression(inferred.type as KernelExpression),
            'τ (Obj checker_B)'
        );
        assert.equal(inferred.term.tag, 'application');
        if (inferred.term.tag !== 'application') {
            throw new Error('Expected checked owner application');
        }
        assert.deepEqual(
            inferred.term.arguments.map(argument => argument.plicity),
            ['implicit', 'implicit', 'explicit', 'explicit']
        );
    });

    it('checks every current owner through one uniform signature path', () => {
        let environment = CoreDeclarationEnvironment.empty();
        const applications: {
            owner: CoreOwnerId;
            term: KernelExpression;
            type: KernelExpression;
        }[] = [];
        let line = 50;

        for (const ownerId of Object.keys(
            CORE_OWNER_SCHEMAS
        ) as CoreOwnerId[]) {
            const arguments_: KernelExpression[] = [];
            const slots: readonly { readonly name: string }[] =
                CORE_OWNER_SCHEMAS[ownerId].slots;
            slots.forEach((slot, index) => {
                const nodeProvenance = because(
                    line,
                    `${ownerId} checker slot ${slot.name}`
                );
                const name =
                    `checked_${ownerId.replace(/-/g, '_')}_` +
                    `${slot.name}_${index}`;
                environment = extend(
                    environment,
                    name,
                    coreOwnerSlotType(
                        ownerId,
                        index,
                        arguments_,
                        nodeProvenance
                    ),
                    line
                );
                arguments_.push(free(name, line));
                line++;
            });
            const nodeProvenance = because(
                line,
                `${ownerId} checked saturated application`
            );
            applications.push({
                owner: ownerId,
                term: owner(ownerId, arguments_, line),
                type: coreOwnerResultType(
                    ownerId,
                    arguments_,
                    nodeProvenance
                )
            });
            line++;
        }

        const checker = new CoreChecker(
            new CoreElaborationSession(environment)
        );
        checker.validateEnvironment();
        for (const application of applications) {
            const signature = checker.infer(
                checker.rootContext,
                coreOwnerSignatureType(
                    application.owner,
                    because(line, `${application.owner} checked signature`)
                )
            );
            assert.equal(
                isCoreKind(signature.type) ||
                signature.type.tag === 'universe',
                true,
                `Expected a valid declaration sort for ${application.owner}`
            );
            const inferred = checker.infer(
                checker.rootContext,
                application.term
            );
            assert.equal(isCoreKind(inferred.type), false);
            assert.equal(
                kernelExpressionEquals(
                    inferred.type as KernelExpression,
                    application.type
                ),
                true,
                `Expected exact inferred type for ${application.owner}`
            );
        }
        assert.equal(
            applications.length,
            Object.keys(CORE_OWNER_SCHEMAS).length
        );
    });

    it('reports a rigid owner argument mismatch at the supplied source', () => {
        const fixture_ = ordinaryFixture();
        const error = expectCheckerError(
            () => fixture_.checker.inferOwnerApplication(
                fixture_.checker.rootContext,
                'functor-object',
                [{
                    plicity: 'explicit',
                    value: free('checker_F', 100)
                }, {
                    plicity: 'explicit',
                    value: free('checker_XC', 101),
                    provenance: because(101, 'wrong-category object')
                }],
                because(100, 'bad owner application')
            ),
            'TYPE_MISMATCH'
        );
        assert.equal(error.provenance.span?.start.line, 101);
        assert.match(error.message, /free name 'checker_C'.*checker_A/);
    });

    it('rejects wrong plicity, missing explicit slots, and non-functions', () => {
        const wrongPlicityFixture = ordinaryFixture();
        const plicity = expectCheckerError(
            () => wrongPlicityFixture.checker.inferGenericCall(
                wrongPlicityFixture.checker.rootContext,
                free('checker_poly', 110),
                [{
                    plicity: 'implicit',
                    value: free('checker_A', 110)
                }, {
                    plicity: 'implicit',
                    value: free('checker_X', 111),
                    provenance: because(111, 'wrong explicit plicity')
                }],
                because(110, 'wrong-plicity call')
            ),
            'PLICITY_MISMATCH'
        );
        assert.equal(plicity.provenance.span?.start.line, 111);

        const missingFixture = ordinaryFixture();
        expectCheckerError(
            () => missingFixture.checker.inferOwnerApplication(
                missingFixture.checker.rootContext,
                'functor-object',
                [{
                    plicity: 'explicit',
                    value: free('checker_F', 112)
                }],
                because(112, 'missing owner object')
            ),
            'MISSING_EXPLICIT_ARGUMENT'
        );

        const nonFunctionFixture = ordinaryFixture();
        const nonFunction = expectCheckerError(
            () => nonFunctionFixture.checker.inferGenericCall(
                nonFunctionFixture.checker.rootContext,
                free('checker_X', 113),
                [{
                    plicity: 'explicit',
                    value: free('checker_X', 113)
                }],
                because(113, 'non-function call')
            ),
            'EXPECTED_FUNCTION'
        );
        assert.equal(nonFunction.provenance.span?.start.line, 113);

        const emptyFixture = ordinaryFixture();
        expectCheckerError(
            () => emptyFixture.checker.inferGenericCall(
                emptyFixture.checker.rootContext,
                free('checker_poly', 114),
                [],
                because(114, 'empty generic call')
            ),
            'EMPTY_GENERIC_CALL'
        );
    });

    it('rejects lambda mode mismatch and inference without an expected Pi', () => {
        const expected = kernelPi(
            kernelBinder(
                'A',
                categoryUniverse(120),
                explicitFunctorial,
                because(120, 'expected lambda binder')
            ),
            categoryUniverse(120),
            because(120, 'expected lambda type')
        );
        const wrongMode = kernelLambda(
            kernelBinder(
                'A',
                categoryUniverse(121),
                explicitNatural,
                because(121, 'wrong lambda mode')
            ),
            categoryUniverse(121),
            because(121, 'wrong-mode lambda')
        );

        const checker = new CoreChecker(new CoreElaborationSession());
        expectCheckerError(
            () => checker.check(checker.rootContext, wrongMode, expected),
            'BINDER_MODE_MISMATCH'
        );

        const freshChecker = new CoreChecker(new CoreElaborationSession());
        expectCheckerError(
            () => freshChecker.infer(freshChecker.rootContext, wrongMode),
            'CANNOT_INFER_LAMBDA'
        );
    });

    it('rejects unresolved and flex-flex implicit recovery', () => {
        const unresolvedFixture = ordinaryFixture();
        const unresolved = expectCheckerError(
            () => unresolvedFixture.checker.inferGenericCall(
                unresolvedFixture.checker.rootContext,
                free('checker_choose', 130),
                [{
                    plicity: 'explicit',
                    value: free('checker_B', 130)
                }],
                because(130, 'underconstrained generic call')
            ),
            'UNRESOLVED_METAVARIABLE'
        );
        assert.match(unresolved.message, /\?m0/);

        const ambiguousFixture = ordinaryFixture();
        const actualCategory = ambiguousFixture.session.freshMeta(
            ambiguousFixture.checker.rootContext,
            categoryUniverse(131),
            because(131, 'ambiguous actual category')
        );
        const actualValue = ambiguousFixture.session.freshMeta(
            ambiguousFixture.checker.rootContext,
            objectType(actualCategory, 132),
            because(132, 'ambiguous actual value')
        );
        const ambiguous = expectCheckerError(
            () => ambiguousFixture.checker.inferGenericCall(
                ambiguousFixture.checker.rootContext,
                free('checker_poly', 133),
                [{
                    plicity: 'explicit',
                    value: actualValue
                }],
                because(133, 'ambiguous implicit call')
            ),
            'UNRESOLVED_CONSTRAINTS'
        );
        assert.equal(
            ambiguous.constraint?.reason,
            'AMBIGUOUS_FLEX_FLEX'
        );
    });

    it('propagates occurs rejection and scope failure without guessing', () => {
        const session = new CoreElaborationSession();
        const checker = new CoreChecker(session);
        const typeMeta = session.freshMeta(
            checker.rootContext,
            kernelUniverse(because(140, 'occurs type meta kind')),
            because(140, 'occurs type meta')
        );
        const termMeta = session.freshMeta(
            checker.rootContext,
            typeMeta,
            because(141, 'occurs term meta')
        );
        const recursiveExpected = kernelPi(
            kernelBinder(
                'loop',
                typeMeta,
                explicitFunctorial,
                because(142, 'occurs expected binder')
            ),
            typeMeta,
            because(142, 'occurs expected type')
        );
        const occurs = expectCheckerError(
            () => checker.check(
                checker.rootContext,
                termMeta,
                recursiveExpected
            ),
            'CONSTRAINT_REJECTED'
        );
        assert.equal(occurs.sessionError?.code, 'META_OCCURS_CHECK');

        const scopeChecker = new CoreChecker(new CoreElaborationSession());
        assert.throws(
            () => scopeChecker.infer(
                scopeChecker.rootContext,
                bound(0, 143)
            ),
            error => {
                assert.ok(error instanceof CoreContextError);
                assert.equal(error.code, 'ILL_SCOPED_EXPRESSION');
                assert.equal(error.provenance.span?.start.line, 143);
                return true;
            }
        );
    });

    it(
        'emits checked implicit applications accepted by Lambdapi',
        { skip: process.env.EMDASH_RUN_LAMBDAPI_PROBES !== '1' },
        () => {
            const fixture_ = ordinaryFixture();
            fixture_.checker.validateEnvironment();
            const generic = fixture_.checker.inferGenericCall(
                fixture_.checker.rootContext,
                free('checker_poly', 150),
                [{
                    plicity: 'explicit',
                    value: free('checker_X', 150)
                }],
                because(150, 'checked generic oracle call')
            );
            const projection = fixture_.checker.inferOwnerApplication(
                fixture_.checker.rootContext,
                'functor-object',
                [{
                    plicity: 'explicit',
                    value: free('checker_F', 151)
                }, {
                    plicity: 'explicit',
                    value: free('checker_X', 151)
                }],
                because(151, 'checked projection oracle call')
            );
            if (
                isCoreKind(generic.type) ||
                isCoreKind(projection.type)
            ) {
                throw new Error('Expected term-level oracle result types');
            }

            const probe: KernelProbe = {
                requiredModule: LAMBDAPI_V32_MODULE,
                declarations: fixture_.environment.declarations.map(
                    declaration => ({
                        name: declaration.name,
                        type: declaration.type,
                        span: declaration.provenance.span!
                    })
                ),
                assertions: [{
                    label: 'ELAB-2A3B checked generic implicit insertion',
                    term: generic.term,
                    type: generic.type,
                    span: at(150, 1, 50)
                }, {
                    label: 'ELAB-2A3B checked owner implicit insertion',
                    term: projection.term,
                    type: projection.type,
                    span: at(151, 1, 50)
                }]
            };
            const serialized = serializeKernelProbe(probe);
            assert.match(
                serialized.source,
                /@checker_poly checker_A checker_X/
            );
            assert.match(
                serialized.source,
                /@fapp0 checker_A checker_B checker_F checker_X/
            );
            const result = checkLambdapiProbe(serialized, {
                packageRoot: resolve(__dirname, '../emdash2'),
                timeoutMs: 30_000
            });
            assert.equal(
                result.accepted,
                true,
                `Expected checked-output acceptance:\n` +
                `${result.diagnostics}\n${serialized.source}`
            );
            assert.equal(result.timedOut, false);
        }
    );
});
