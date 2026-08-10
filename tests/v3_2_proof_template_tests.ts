/** Focused PLAN-DECOMPOSE-3C1 proof-template macro tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CORE_PROOF_REFINE_TEMPLATE_PROFILE,
    BinderMode,
    CoreBindingInput,
    CoreChecker,
    CoreDeclarationEnvironment,
    CoreElaborationSession,
    CoreProofPlanError,
    CoreProofRefineTemplateError,
    CoreProofRefiner,
    KernelExpression,
    binderMode,
    coreProofPlanExact,
    coreProofPlanHave,
    coreProofPlanHole,
    coreProofPlanIntro,
    coreProofPlanRefine,
    coreProofTemplateApplication,
    coreProofTemplateBinding,
    coreProofTemplateCall,
    coreProofTemplateCore,
    coreProofTemplateLambda,
    coreProofTemplatePlaceholder,
    executeCoreProofPlan,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelFree,
    kernelPi,
    kernelUniverse,
    provenance,
    sourceSpan
} from '../src/v3_2';

const fixture = 'tests/fixtures/v3_2_proof_template.surface.ts';
const because = (line: number, detail: string) => provenance(
    'surface',
    detail,
    sourceSpan(fixture, line, 1, line, 2)
);

const explicitFunctorial = binderMode('explicit', 'functorial');
const explicitNatural = binderMode('explicit', 'natural');

const free = (name: string, line: number, detail: string) =>
    kernelFree(name, because(line, detail));

const bound = (index: number, line: number, detail: string) =>
    kernelBound(index, because(line, detail));

const typeA = (line: number) =>
    free('template_A', line, 'PLAN-DECOMPOSE-3C1 type A');

const typeB = (line: number) =>
    free('template_B', line, 'PLAN-DECOMPOSE-3C1 type B');

const pi = (
    name: string,
    type: KernelExpression,
    mode: BinderMode,
    body: KernelExpression,
    line: number,
    detail: string
) => kernelPi(
    kernelBinder(name, type, mode, because(line, `${detail} binder`)),
    body,
    because(line, detail)
);

const declaration = (
    name: string,
    type: KernelExpression,
    line: number
): CoreBindingInput => ({
    name,
    type,
    mode: explicitFunctorial,
    provenance: because(line, `PLAN-DECOMPOSE-3C1 declaration ${name}`)
});

const proofEnvironment = (): CoreDeclarationEnvironment => {
    let environment = CoreDeclarationEnvironment.empty();
    environment = environment.extend(declaration(
        'template_A',
        kernelUniverse(because(1, 'PLAN-DECOMPOSE-3C1 universe A')),
        1
    ));
    environment = environment.extend(declaration(
        'template_B',
        kernelUniverse(because(2, 'PLAN-DECOMPOSE-3C1 universe B')),
        2
    ));
    environment = environment.extend(declaration('template_z', typeA(3), 3));
    environment = environment.extend(declaration('template_b', typeB(4), 4));
    environment = environment.extend(declaration(
        'template_const',
        pi(
            'left',
            typeA(5),
            explicitFunctorial,
            pi(
                'right',
                typeB(5),
                explicitFunctorial,
                typeA(5),
                5,
                'PLAN-DECOMPOSE-3C1 const right'
            ),
            5,
            'PLAN-DECOMPOSE-3C1 const left'
        ),
        5
    ));
    environment = environment.extend(declaration(
        'template_dup',
        pi(
            'left',
            typeA(6),
            explicitFunctorial,
            pi(
                'right',
                typeA(6),
                explicitFunctorial,
                typeA(6),
                6,
                'PLAN-DECOMPOSE-3C1 dup right'
            ),
            6,
            'PLAN-DECOMPOSE-3C1 dup left'
        ),
        6
    ));
    environment = environment.extend(declaration(
        'template_id',
        functionType(7),
        7
    ));
    return environment;
};

const proofFixture = () => {
    const session = new CoreElaborationSession(proofEnvironment());
    const checker = new CoreChecker(session);
    checker.validateEnvironment();
    return { session, checker };
};

const functionType = (line: number) => pi(
    'value',
    typeA(line),
    explicitNatural,
    typeA(line),
    line,
    'PLAN-DECOMPOSE-3C1 endofunction'
);

const identityPlan = (line: number) => coreProofPlanIntro(
    coreProofPlanExact(bound(
        0,
        line + 1,
        'PLAN-DECOMPOSE-3C1 identity body'
    )),
    {
        name: 'value',
        provenance: because(line, 'PLAN-DECOMPOSE-3C1 identity intro')
    }
);

const identityReferencePlan = (line: number) => coreProofPlanExact(free(
    'template_id',
    line,
    'PLAN-DECOMPOSE-3C1 declared identity proof'
));

const higherOrderTemplate = (line: number) => coreProofTemplateCall(
    coreProofTemplatePlaceholder(
        'function',
        because(line, 'PLAN-DECOMPOSE-3C1 callee placeholder')
    ),
    [{
        plicity: 'explicit',
        value: coreProofTemplateCore(free(
            'template_z',
            line,
            'PLAN-DECOMPOSE-3C1 fixed argument'
        ))
    }],
    because(line, 'PLAN-DECOMPOSE-3C1 higher-order template')
);

describe('PLAN-DECOMPOSE-3C1 proof-template macro', () => {
    it('lowers byte-for-structure to nested have plus exact', () => {
        const template = higherOrderTemplate(20);
        const binder = kernelBinder(
            'function',
            functionType(21),
            explicitFunctorial,
            because(21, 'PLAN-DECOMPOSE-3C1 function binding')
        );
        const proof = identityPlan(22);
        const options = {
            id: 'refine_function',
            provenance: because(20, 'PLAN-DECOMPOSE-3C1 refine root')
        };
        const macro = coreProofPlanRefine(
            template,
            [coreProofTemplateBinding(binder, proof)],
            options
        );
        const direct = coreProofPlanHave(
            binder,
            proof,
            coreProofPlanExact(kernelCall(
                bound(0, 20, 'PLAN-DECOMPOSE-3C1 callee placeholder'),
                [{
                    plicity: 'explicit',
                    value: free(
                        'template_z',
                        20,
                        'PLAN-DECOMPOSE-3C1 fixed argument'
                    )
                }],
                because(20, 'PLAN-DECOMPOSE-3C1 higher-order template')
            )),
            options
        );

        assert.deepEqual(macro, direct);
        assert.equal(macro.tag, 'have');
        assert.equal(
            CORE_PROOF_REFINE_TEMPLATE_PROFILE.addsProofPlanTags,
            false
        );
        assert.equal(
            CORE_PROOF_REFINE_TEMPLATE_PROFILE.lowering,
            'nested-have-then-exact'
        );
        assert.equal(
            CORE_PROOF_REFINE_TEMPLATE_PROFILE.allowsTypePlaceholders,
            false
        );
        assert.equal(Object.isFrozen(template), true);
    });

    it('checks complete and open higher-order callee templates', () => {
        const completeFixture = proofFixture();
        const completeRoot = completeFixture.session.freshMeta(
            completeFixture.session.rootContext,
            typeA(30),
            because(30, 'PLAN-DECOMPOSE-3C1 complete root')
        );
        const completePlan = coreProofPlanRefine(
            higherOrderTemplate(31),
            [coreProofTemplateBinding(
                kernelBinder(
                    'function',
                    functionType(32),
                    explicitFunctorial,
                    because(32, 'PLAN-DECOMPOSE-3C1 complete binding')
                ),
                identityReferencePlan(33)
            )]
        );
        const complete = executeCoreProofPlan(
            new CoreProofRefiner(completeFixture.checker, completeRoot),
            completeRoot.identity,
            completePlan
        );
        assert.equal(complete.snapshot.status, 'complete');
        assert.deepEqual(
            complete.trace.map(step => step.operation),
            ['have', 'exact', 'exact']
        );
        assert.doesNotThrow(() => completeFixture.checker.check(
            completeFixture.session.rootContext,
            complete.term,
            typeA(34)
        ));

        const openFixture = proofFixture();
        const openRoot = openFixture.session.freshMeta(
            openFixture.session.rootContext,
            typeA(35),
            because(35, 'PLAN-DECOMPOSE-3C1 open root')
        );
        const openPlan = coreProofPlanRefine(
            higherOrderTemplate(36),
            [coreProofTemplateBinding(
                kernelBinder(
                    'function',
                    functionType(37),
                    explicitFunctorial,
                    because(37, 'PLAN-DECOMPOSE-3C1 open binding')
                ),
                coreProofPlanHole('function_goal', {
                    provenance: because(
                        38,
                        'PLAN-DECOMPOSE-3C1 open function goal'
                    )
                })
            )]
        );
        const open = executeCoreProofPlan(
            new CoreProofRefiner(openFixture.checker, openRoot),
            openRoot.identity,
            openPlan
        );
        assert.equal(open.snapshot.status, 'incomplete');
        assert.deepEqual(
            open.snapshot.goals.map(goal => [
                goal.id,
                goal.reachability,
                goal.occurrenceCount
            ]),
            [['function_goal', 'term-reachable', 1]]
        );
    });

    it('shares repeated occurrences of one explicit placeholder', () => {
        const { session, checker } = proofFixture();
        const root = session.freshMeta(
            session.rootContext,
            typeA(40),
            because(40, 'PLAN-DECOMPOSE-3C1 shared root')
        );
        const shared = coreProofTemplatePlaceholder(
            'shared',
            because(41, 'PLAN-DECOMPOSE-3C1 shared placeholder')
        );
        const plan = coreProofPlanRefine(
            coreProofTemplateCall(
                coreProofTemplateCore(free(
                    'template_dup',
                    41,
                    'PLAN-DECOMPOSE-3C1 duplicate callee'
                )),
                [
                    { plicity: 'explicit', value: shared },
                    { plicity: 'explicit', value: shared }
                ],
                because(41, 'PLAN-DECOMPOSE-3C1 shared template')
            ),
            [coreProofTemplateBinding(
                kernelBinder(
                    'shared',
                    typeA(42),
                    explicitFunctorial,
                    because(42, 'PLAN-DECOMPOSE-3C1 shared binding')
                ),
                coreProofPlanHole('shared_goal', {
                    provenance: because(
                        43,
                        'PLAN-DECOMPOSE-3C1 shared goal'
                    )
                })
            )]
        );
        const execution = executeCoreProofPlan(
            new CoreProofRefiner(checker, root),
            root.identity,
            plan
        );

        assert.deepEqual(
            execution.snapshot.goals.map(goal => [
                goal.id,
                goal.occurrenceCount
            ]),
            [['shared_goal', 2]]
        );
        assert.match(
            execution.snapshot.term,
            /\?shared_goal\[\].*\?shared_goal\[\]/u
        );
    });

    it('preserves explicit two-binding goal order', () => {
        const { session, checker } = proofFixture();
        const root = session.freshMeta(
            session.rootContext,
            typeA(50),
            because(50, 'PLAN-DECOMPOSE-3C1 ordered root')
        );
        const plan = coreProofPlanRefine(
            coreProofTemplateCall(
                coreProofTemplateCore(free(
                    'template_const',
                    51,
                    'PLAN-DECOMPOSE-3C1 ordered callee'
                )),
                [
                    {
                        plicity: 'explicit',
                        value: coreProofTemplatePlaceholder(
                            'left',
                            because(51, 'PLAN-DECOMPOSE-3C1 left use')
                        )
                    },
                    {
                        plicity: 'explicit',
                        value: coreProofTemplatePlaceholder(
                            'right',
                            because(51, 'PLAN-DECOMPOSE-3C1 right use')
                        )
                    }
                ],
                because(51, 'PLAN-DECOMPOSE-3C1 ordered template')
            ),
            [
                coreProofTemplateBinding(
                    kernelBinder(
                        'left',
                        typeA(52),
                        explicitFunctorial,
                        because(52, 'PLAN-DECOMPOSE-3C1 left binding')
                    ),
                    coreProofPlanHole('left_goal', {
                        provenance: because(52, 'PLAN-DECOMPOSE-3C1 left goal')
                    })
                ),
                coreProofTemplateBinding(
                    kernelBinder(
                        'right',
                        typeB(53),
                        explicitFunctorial,
                        because(53, 'PLAN-DECOMPOSE-3C1 right binding')
                    ),
                    coreProofPlanHole('right_goal', {
                        provenance: because(
                            53,
                            'PLAN-DECOMPOSE-3C1 right goal'
                        )
                    })
                )
            ]
        );
        const execution = executeCoreProofPlan(
            new CoreProofRefiner(checker, root),
            root.identity,
            plan
        );
        assert.deepEqual(
            execution.snapshot.goals.map(goal => goal.id),
            ['left_goal', 'right_goal']
        );
        assert.deepEqual(
            execution.snapshot.goals.map(goal => goal.contextDepth),
            [0, 1]
        );
    });

    it('shifts root context beneath template-local binders', () => {
        const { session, checker } = proofFixture();
        const target = pi(
            'root',
            typeA(60),
            explicitNatural,
            pi(
                'local',
                typeA(60),
                explicitNatural,
                typeA(60),
                60,
                'PLAN-DECOMPOSE-3C1 local result'
            ),
            60,
            'PLAN-DECOMPOSE-3C1 shifted target'
        );
        const root = session.freshMeta(
            session.rootContext,
            target,
            because(60, 'PLAN-DECOMPOSE-3C1 shifted root')
        );
        const template = coreProofTemplateLambda(
            kernelBinder(
                'local',
                typeA(62),
                explicitNatural,
                because(62, 'PLAN-DECOMPOSE-3C1 template local')
            ),
            coreProofTemplateCall(
                coreProofTemplatePlaceholder(
                    'function',
                    because(63, 'PLAN-DECOMPOSE-3C1 shifted function')
                ),
                [{
                    plicity: 'explicit',
                    value: coreProofTemplateCore(bound(
                        1,
                        63,
                        'PLAN-DECOMPOSE-3C1 root under local binder'
                    ))
                }],
                because(63, 'PLAN-DECOMPOSE-3C1 shifted call')
            )
        );
        const plan = coreProofPlanIntro(
            coreProofPlanRefine(
                template,
                [coreProofTemplateBinding(
                    kernelBinder(
                        'function',
                        functionType(64),
                        explicitFunctorial,
                        because(64, 'PLAN-DECOMPOSE-3C1 shifted binding')
                    ),
                    identityReferencePlan(65)
                )]
            ),
            {
                name: 'root',
                provenance: because(61, 'PLAN-DECOMPOSE-3C1 root intro')
            }
        );
        const execution = executeCoreProofPlan(
            new CoreProofRefiner(checker, root),
            root.identity,
            plan
        );
        assert.equal(execution.snapshot.status, 'complete');
        assert.doesNotThrow(() => checker.check(
            session.rootContext,
            execution.term,
            target
        ));
    });

    it('lowers owner applications without adding a template tag', () => {
        const plan = coreProofPlanRefine(
            coreProofTemplateApplication(
                'decode',
                [{
                    value: coreProofTemplatePlaceholder(
                        'classifier',
                        because(71, 'PLAN-DECOMPOSE-3C1 owner argument')
                    )
                }],
                because(71, 'PLAN-DECOMPOSE-3C1 owner application')
            ),
            [coreProofTemplateBinding(
                kernelBinder(
                    'classifier',
                    kernelUniverse(because(
                        72,
                        'PLAN-DECOMPOSE-3C1 classifier type'
                    )),
                    explicitFunctorial,
                    because(72, 'PLAN-DECOMPOSE-3C1 classifier binding')
                ),
                coreProofPlanExact(typeA(72))
            )]
        );

        assert.equal(plan.tag, 'have');
        assert.equal(plan.body.tag, 'exact');
        if (plan.body.tag !== 'exact') throw new Error('expected exact body');
        assert.equal(plan.body.solution.tag, 'application');
        if (plan.body.solution.tag !== 'application') {
            throw new Error('expected owner application');
        }
        assert.equal(plan.body.solution.owner, 'decode');
        assert.deepEqual(
            plan.body.solution.arguments.map(argument => argument.value.tag),
            ['bound']
        );
    });

    it('rejects malformed templates before returning a plan', () => {
        const binding = () => coreProofTemplateBinding(
            kernelBinder(
                'value',
                typeA(70),
                explicitFunctorial,
                because(70, 'PLAN-DECOMPOSE-3C1 rejected binding')
            ),
            coreProofPlanExact(free(
                'template_z',
                70,
                'PLAN-DECOMPOSE-3C1 rejected proof'
            ))
        );
        const expectTemplateError = (
            action: () => unknown,
            code: CoreProofRefineTemplateError['code']
        ) => assert.throws(action, (error: unknown) => {
            assert.ok(error instanceof CoreProofRefineTemplateError);
            assert.equal(error.code, code);
            return true;
        });

        expectTemplateError(
            () => coreProofPlanRefine(
                coreProofTemplatePlaceholder(
                    'missing',
                    because(71, 'PLAN-DECOMPOSE-3C1 unknown placeholder')
                ),
                []
            ),
            'UNKNOWN_PLACEHOLDER'
        );
        expectTemplateError(
            () => coreProofPlanRefine(
                coreProofTemplateCore(free(
                    'template_z',
                    72,
                    'PLAN-DECOMPOSE-3C1 unused template'
                )),
                [binding()]
            ),
            'UNUSED_BINDING'
        );
        expectTemplateError(
            () => coreProofPlanRefine(
                coreProofTemplatePlaceholder(
                    'value',
                    because(73, 'PLAN-DECOMPOSE-3C1 duplicate placeholder')
                ),
                [binding(), binding()]
            ),
            'DUPLICATE_BINDING'
        );

        const cyclic: any = {
            tag: 'call',
            provenance: because(74, 'PLAN-DECOMPOSE-3C1 cyclic template'),
            arguments: [{
                plicity: 'explicit',
                value: coreProofTemplateCore(free(
                    'template_z',
                    74,
                    'PLAN-DECOMPOSE-3C1 cyclic argument'
                )),
                provenance: because(74, 'PLAN-DECOMPOSE-3C1 cyclic argument')
            }]
        };
        cyclic.callee = cyclic;
        expectTemplateError(
            () => coreProofPlanRefine(cyclic, []),
            'CYCLIC_TEMPLATE'
        );

        const { session } = proofFixture();
        const hidden = session.freshMeta(
            session.rootContext,
            typeA(75),
            because(75, 'PLAN-DECOMPOSE-3C1 hidden meta')
        );
        expectTemplateError(
            () => coreProofPlanRefine(coreProofTemplateCore(hidden), []),
            'NON_SERIALIZABLE_EXPRESSION'
        );
        expectTemplateError(
            () => coreProofPlanRefine(
                coreProofTemplateApplication(
                    'decode',
                    [],
                    because(76, 'PLAN-DECOMPOSE-3C1 wrong owner arity')
                ),
                []
            ),
            'INVALID_TEMPLATE'
        );
        expectTemplateError(
            () => coreProofPlanRefine(
                coreProofTemplateApplication(
                    '__proto__' as any,
                    [],
                    because(77, 'PLAN-DECOMPOSE-3C1 unknown owner')
                ),
                []
            ),
            'INVALID_TEMPLATE'
        );
        expectTemplateError(
            () => coreProofPlanRefine(
                coreProofTemplateCall(
                    coreProofTemplateCore(free(
                        'template_id',
                        78,
                        'PLAN-DECOMPOSE-3C1 invalid-plicity callee'
                    )),
                    [{
                        plicity: 'automatic' as any,
                        value: coreProofTemplateCore(free(
                            'template_z',
                            78,
                            'PLAN-DECOMPOSE-3C1 invalid-plicity argument'
                        ))
                    }],
                    because(78, 'PLAN-DECOMPOSE-3C1 invalid plicity')
                ),
                []
            ),
            'INVALID_TEMPLATE'
        );
        expectTemplateError(
            () => coreProofPlanRefine(
                coreProofTemplateLambda(
                    kernelBinder(
                        'value',
                        typeA(79),
                        {
                            plicity: 'explicit',
                            variation: 'arbitrary'
                        } as any,
                        because(79, 'PLAN-DECOMPOSE-3C1 invalid mode')
                    ),
                    coreProofTemplateCore(bound(
                        0,
                        79,
                        'PLAN-DECOMPOSE-3C1 invalid-mode body'
                    ))
                ),
                []
            ),
            'INVALID_TEMPLATE'
        );

        assert.throws(
            () => coreProofPlanRefine(
                coreProofTemplatePlaceholder(
                    'value',
                    because(80, 'PLAN-DECOMPOSE-3C1 bad child placeholder')
                ),
                [coreProofTemplateBinding(
                    kernelBinder(
                        'value',
                        typeA(80),
                        explicitFunctorial,
                        because(80, 'PLAN-DECOMPOSE-3C1 bad child binding')
                    ),
                    coreProofPlanHole('not portable', {
                        provenance: because(
                            80,
                            'PLAN-DECOMPOSE-3C1 bad child plan'
                        )
                    })
                )]
            ),
            (error: unknown) => error instanceof CoreProofPlanError &&
                error.code === 'INVALID_ID'
        );
    });

    it('keeps scope failures atomic at ordinary have checking', () => {
        const { session, checker } = proofFixture();
        const root = session.freshMeta(
            session.rootContext,
            typeA(80),
            because(80, 'PLAN-DECOMPOSE-3C1 scope root')
        );
        const plan = coreProofPlanRefine(
            coreProofTemplatePlaceholder(
                'bad',
                because(81, 'PLAN-DECOMPOSE-3C1 scope placeholder')
            ),
            [coreProofTemplateBinding(
                kernelBinder(
                    'bad',
                    bound(0, 81, 'PLAN-DECOMPOSE-3C1 dangling type'),
                    explicitFunctorial,
                    because(81, 'PLAN-DECOMPOSE-3C1 scope binding')
                ),
                coreProofPlanExact(free(
                    'template_z',
                    82,
                    'PLAN-DECOMPOSE-3C1 scope proof'
                ))
            )]
        );
        const refiner = new CoreProofRefiner(checker, root);
        assert.throws(() => executeCoreProofPlan(
            refiner,
            root.identity,
            plan
        ));
        assert.equal(session.metavariables.length, 1);
        assert.equal(session.metavariable(root).solution, undefined);
        assert.deepEqual(
            refiner.inspect().goals.map(goal => goal.identity.index),
            [root.identity.index]
        );
    });
});
