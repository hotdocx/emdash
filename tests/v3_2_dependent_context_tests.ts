/**
 * Focused ELAB-2B tests for the bounded dependent-first context experiment.
 */

import assert from 'node:assert';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_DEPENDENT_BRIDGE_SCHEMAS,
    CORE_OWNER_SCHEMAS,
    CoreChecker,
    CoreCheckerError,
    CoreContext,
    CoreDeclarationEnvironment,
    CoreElaborationSession,
    CoreOwnerId,
    KernelExpression,
    KernelProbe,
    LAMBDAPI_V32_MODULE,
    LAMBDAPI_V32_OWNER_BINDINGS,
    binderMode,
    checkLambdapiProbe,
    coreConstantDisplayedFamily,
    coreDisplayedFamilyType,
    coreOrdinaryFunctorType,
    coreOwnerResultType,
    coreOwnerSignatureType,
    coreReindexDisplayedFamily,
    coreSectionCategory,
    coreSectionType,
    kernelApplication,
    kernelBound,
    kernelExpressionEquals,
    kernelFree,
    kernelSubstitute,
    provenance,
    serializeKernelExpression,
    serializeKernelProbe,
    sourceSpan
} from '../src/v3_2';

const fixture = 'tests/fixtures/v3_2_dependent_context.surface.ts';
const at = (line: number, startColumn = 1, endColumn = startColumn + 1) =>
    sourceSpan(fixture, line, startColumn, line, endColumn);

const because = (line: number, detail: string) =>
    provenance('surface', detail, at(line));

const explicitFunctorial = binderMode('explicit', 'functorial');

const free = (name: string, line: number): KernelExpression =>
    kernelFree(name, because(line, `ELAB-2B free occurrence ${name}`));

const owner = (
    ownerId: CoreOwnerId,
    arguments_: readonly KernelExpression[],
    line: number
): KernelExpression => kernelApplication(
    ownerId,
    arguments_.map(value => ({ value })),
    because(line, `ELAB-2B ${ownerId}`)
);

const categoryUniverse = (line: number): KernelExpression =>
    owner('category-universe', [], line);

const extend = (
    environment: CoreDeclarationEnvironment,
    name: string,
    type: KernelExpression,
    line: number
): CoreDeclarationEnvironment => environment.extend({
    name,
    type,
    mode: explicitFunctorial,
    provenance: because(line, `ELAB-2B declaration ${name}`)
});

interface DependentFixture {
    environment: CoreDeclarationEnvironment;
    checker: CoreChecker;
    gamma: KernelExpression;
    delta: KernelExpression;
    fibre: KernelExpression;
    family: KernelExpression;
    substitution: KernelExpression;
    constantFamily: KernelExpression;
}

const dependentFixture = (): DependentFixture => {
    let environment = CoreDeclarationEnvironment.empty();
    environment = extend(
        environment,
        'dep_Gamma',
        categoryUniverse(10),
        10
    );
    environment = extend(
        environment,
        'dep_Delta',
        categoryUniverse(11),
        11
    );
    environment = extend(
        environment,
        'dep_A',
        categoryUniverse(12),
        12
    );

    const gamma = free('dep_Gamma', 13);
    const delta = free('dep_Delta', 13);
    const fibre = free('dep_A', 13);

    environment = extend(
        environment,
        'dep_E',
        coreDisplayedFamilyType(
            gamma,
            because(13, 'displayed family over Gamma')
        ),
        13
    );
    environment = extend(
        environment,
        'dep_sigma',
        coreOrdinaryFunctorType(
            delta,
            gamma,
            because(14, 'substitution Delta to Gamma')
        ),
        14
    );
    environment = extend(
        environment,
        'dep_wrong_sigma',
        coreOrdinaryFunctorType(
            gamma,
            delta,
            because(15, 'wrong-direction substitution')
        ),
        15
    );

    const family = free('dep_E', 16);
    const substitution = free('dep_sigma', 16);
    const constantFamily = coreConstantDisplayedFamily(
        gamma,
        fibre,
        because(16, 'constant family over Gamma')
    );

    environment = extend(
        environment,
        'dep_general_section',
        coreSectionType(
            gamma,
            family,
            because(17, 'general dependent section')
        ),
        17
    );
    environment = extend(
        environment,
        'dep_constant_section',
        coreSectionType(
            gamma,
            constantFamily,
            because(18, 'constant displayed section')
        ),
        18
    );
    environment = extend(
        environment,
        'dep_ordinary_section',
        coreOrdinaryFunctorType(
            gamma,
            fibre,
            because(19, 'ordinary functor route')
        ),
        19
    );

    return {
        environment,
        checker: new CoreChecker(new CoreElaborationSession(environment)),
        gamma,
        delta,
        fibre,
        family,
        substitution,
        constantFamily
    };
};

const collectOwners = (
    expression: KernelExpression,
    result: CoreOwnerId[] = []
): readonly CoreOwnerId[] => {
    switch (expression.tag) {
        case 'universe':
        case 'reference':
        case 'bound':
            return result;
        case 'meta':
            expression.spine.forEach(item => collectOwners(item, result));
            return result;
        case 'application':
            result.push(expression.owner);
            expression.arguments.forEach(argument =>
                collectOwners(argument.value, result)
            );
            return result;
        case 'call':
            collectOwners(expression.callee, result);
            expression.arguments.forEach(argument =>
                collectOwners(argument.value, result)
            );
            return result;
        case 'pi':
        case 'lambda':
            collectOwners(expression.binder.type, result);
            collectOwners(expression.body, result);
            return result;
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

const expectCheckerError = (
    action: () => unknown,
    code: CoreCheckerError['code']
): CoreCheckerError => {
    try {
        action();
    } catch (error: unknown) {
        assert.ok(error instanceof CoreCheckerError);
        assert.equal(error.code, code);
        return error;
    }
    assert.fail(`Expected CoreCheckerError ${code}`);
};

const declarationsForProbe = (
    environment: CoreDeclarationEnvironment
): KernelProbe['declarations'] => environment.declarations.map(
    declaration => ({
        name: declaration.name,
        type: declaration.type,
        span: declaration.provenance.span!
    })
);

const constantBridgeProbe = (
    fixture_: DependentFixture
): KernelProbe => {
    const pullback = coreReindexDisplayedFamily(
        fixture_.delta,
        fixture_.gamma,
        fixture_.constantFamily,
        fixture_.substitution,
        because(150, 'constant family pullback')
    );
    const constantOverDelta = coreConstantDisplayedFamily(
        fixture_.delta,
        fixture_.fibre,
        because(150, 'constant family over Delta')
    );
    const displayedSectionCategory = coreSectionCategory(
        fixture_.gamma,
        fixture_.constantFamily,
        because(151, 'constant section category')
    );
    const categoryOfCategories = owner(
        'category-of-categories',
        [],
        151
    );
    const categoryClassifier = owner(
        'object-classifier',
        [categoryOfCategories],
        151
    );
    const ordinarySectionCategory = owner(
        'hom-category',
        [categoryOfCategories, fixture_.gamma, fixture_.fibre],
        151
    );

    return {
        requiredModule: LAMBDAPI_V32_MODULE,
        declarations: declarationsForProbe(fixture_.environment),
        assertions: [{
            label: 'ELAB-2B checked displayed pullback',
            term: coreReindexDisplayedFamily(
                fixture_.delta,
                fixture_.gamma,
                fixture_.family,
                fixture_.substitution,
                because(152, 'general family pullback')
            ),
            type: coreDisplayedFamilyType(
                fixture_.delta,
                because(152, 'family type over Delta')
            ),
            span: at(152, 1, 50)
        }, {
            label: 'ELAB-2B constant section at ordinary functor type',
            term: free('dep_constant_section', 153),
            type: coreOrdinaryFunctorType(
                fixture_.gamma,
                fixture_.fibre,
                because(153, 'ordinary constant-section type')
            ),
            span: at(153, 1, 50)
        }],
        conversions: [{
            label: 'ELAB-2B constant pullback runtime reduction',
            left: pullback,
            right: constantOverDelta,
            span: at(154, 1, 50)
        }],
        proofTimeComparisons: [{
            label: 'ELAB-2B constant section proof-time comparison',
            classifier: categoryClassifier,
            left: displayedSectionCategory,
            right: ordinarySectionCategory,
            span: at(155, 1, 50)
        }],
        nonConversions: [{
            label: 'ELAB-2B section facade does not runtime collapse',
            left: displayedSectionCategory,
            right: ordinarySectionCategory,
            span: at(156, 1, 50)
        }]
    };
};

describe('TypeScript v3.2 ELAB-2B dependent-first context', () => {
    it('adds only the three indispensable active dependent owners', () => {
        assert.equal(Object.keys(CORE_OWNER_SCHEMAS).length, 24);
        assert.deepEqual(
            CORE_OWNER_SCHEMAS['displayed-pullback'].slots.map(
                slot => [slot.name, slot.plicity]
            ),
            [
                ['A', 'implicit'],
                ['B', 'implicit'],
                ['E', 'explicit'],
                ['F', 'explicit']
            ]
        );
        assert.deepEqual(
            CORE_OWNER_SCHEMAS['constant-displayed-family'].slots.map(
                slot => [slot.name, slot.plicity]
            ),
            [
                ['K', 'explicit'],
                ['A', 'explicit']
            ]
        );
        assert.deepEqual(
            CORE_OWNER_SCHEMAS['section-category'].slots.map(
                slot => [slot.name, slot.plicity]
            ),
            [
                ['K', 'implicit'],
                ['E', 'explicit']
            ]
        );
        assert.equal(
            LAMBDAPI_V32_OWNER_BINDINGS['displayed-pullback']
                .serializedName,
            'Pullback_catd'
        );
        assert.equal(
            LAMBDAPI_V32_OWNER_BINDINGS['constant-displayed-family']
                .serializedName,
            'Const_catd'
        );
        assert.equal(
            LAMBDAPI_V32_OWNER_BINDINGS['section-category'].serializedName,
            'Pi_cat'
        );

        const signature = serializeKernelExpression(
            coreOwnerSignatureType(
                'displayed-pullback',
                because(30, 'displayed pullback signature')
            )
        );
        assert.match(signature, /^Π \[v0 : Cat\], Π \[v1 : Cat\]/);
        assert.match(signature, /τ \(Obj \(Catd_cat v1\)\)/);
        assert.match(signature, /τ \(Functor v0 v1\)/);
        assert.match(signature, /τ \(Obj \(Catd_cat v0\)\)$/);
        assert.equal(
            Object.prototype.hasOwnProperty.call(
                CORE_OWNER_SCHEMAS,
                'total-category'
            ),
            false
        );
    });

    it('constructs exact displayed judgments and bridge paths', () => {
        const fixture_ = dependentFixture();
        const pullback = coreReindexDisplayedFamily(
            fixture_.delta,
            fixture_.gamma,
            fixture_.family,
            fixture_.substitution,
            because(40, 'displayed reindexing')
        );
        assert.equal(
            serializeKernelExpression(
                coreDisplayedFamilyType(
                    fixture_.gamma,
                    because(40, 'displayed family type')
                )
            ),
            'τ (Obj (Catd_cat dep_Gamma))'
        );
        assert.equal(
            serializeKernelExpression(pullback),
            '@Pullback_catd dep_Delta dep_Gamma dep_E dep_sigma'
        );
        assert.equal(
            serializeKernelExpression(fixture_.constantFamily),
            'Const_catd dep_Gamma dep_A'
        );
        assert.equal(
            serializeKernelExpression(
                coreSectionCategory(
                    fixture_.gamma,
                    fixture_.family,
                    because(41, 'section category')
                )
            ),
            '@Pi_cat dep_Gamma dep_E'
        );

        assert.deepEqual(
            CORE_DEPENDENT_BRIDGE_SCHEMAS[
                'constant-family-reindexing'
            ],
            {
                displayedOwnerPath: [
                    'displayed-pullback',
                    'constant-displayed-family'
                ],
                ordinaryOwnerPath: ['constant-displayed-family'],
                authority: 'runtime-reduction',
                requiredNonCollapse: null
            }
        );
        assert.equal(
            CORE_DEPENDENT_BRIDGE_SCHEMAS[
                'constant-family-sections'
            ].authority,
            'proof-time-unification'
        );
        assert.equal(
            CORE_DEPENDENT_BRIDGE_SCHEMAS[
                'general-dependent-sections'
            ].ordinaryOwnerPath,
            null
        );
    });

    it('checks reindexing, constant families, and sections uniformly', () => {
        const fixture_ = dependentFixture();
        fixture_.checker.validateEnvironment();

        const reindexed = fixture_.checker.inferOwnerApplication(
            fixture_.checker.rootContext,
            'displayed-pullback',
            [{
                plicity: 'explicit',
                value: fixture_.family
            }, {
                plicity: 'explicit',
                value: fixture_.substitution
            }],
            because(50, 'checker-recovered displayed pullback')
        );
        assert.equal(
            serializeKernelExpression(reindexed.term),
            '@Pullback_catd dep_Delta dep_Gamma dep_E dep_sigma'
        );
        assert.equal(
            serializeKernelExpression(reindexed.type as KernelExpression),
            'τ (Obj (Catd_cat dep_Delta))'
        );

        const constant = fixture_.checker.infer(
            fixture_.checker.rootContext,
            fixture_.constantFamily
        );
        assert.equal(
            serializeKernelExpression(constant.type as KernelExpression),
            'τ (Obj (Catd_cat dep_Gamma))'
        );

        const section = fixture_.checker.inferOwnerApplication(
            fixture_.checker.rootContext,
            'section-category',
            [{
                plicity: 'explicit',
                value: fixture_.family
            }],
            because(51, 'checker-recovered section base')
        );
        assert.equal(
            serializeKernelExpression(section.term),
            '@Pi_cat dep_Gamma dep_E'
        );
        assert.equal(
            serializeKernelExpression(section.type as KernelExpression),
            'Cat'
        );
    });

    it('uses a persistent local telescope for a dependent section', () => {
        const fixture_ = dependentFixture();
        const root = CoreContext.empty(fixture_.environment);
        const withFamily = root.extend({
            name: 'local_family',
            type: coreDisplayedFamilyType(
                fixture_.gamma,
                because(60, 'local displayed-family type')
            ),
            mode: explicitFunctorial,
            provenance: because(60, 'local displayed family')
        });
        const withSection = withFamily.extend({
            name: 'local_section',
            type: coreSectionType(
                fixture_.gamma,
                kernelBound(
                    0,
                    because(61, 'nearest local displayed family')
                ),
                because(61, 'local dependent section type')
            ),
            mode: explicitFunctorial,
            provenance: because(61, 'local dependent section')
        });

        assert.equal(root.depth, 0);
        assert.equal(withFamily.depth, 1);
        assert.equal(withSection.depth, 2);

        const inferred = fixture_.checker.infer(
            withSection,
            kernelBound(0, because(62, 'local section occurrence'))
        );
        const lookup = withSection.lookupIndex(0);
        assert.ok(lookup);
        assert.equal(
            kernelExpressionEquals(
                inferred.type as KernelExpression,
                lookup.type
            ),
            true
        );
        const ownerPath = collectOwners(inferred.type as KernelExpression);
        assert.ok(ownerPath.includes('section-category'));
        assert.equal(ownerPath.includes('displayed-pullback'), false);
    });

    it('keeps telescope substitution distinct from displayed reindexing', () => {
        const fixture_ = dependentFixture();
        const openSectionType = coreSectionType(
            fixture_.gamma,
            kernelBound(0, because(70, 'open family parameter')),
            because(70, 'open section type')
        );
        const metaLevelSubstitution = kernelSubstitute(
            openSectionType,
            0,
            fixture_.constantFamily
        );
        const internalReindexing = coreReindexDisplayedFamily(
            fixture_.delta,
            fixture_.gamma,
            fixture_.family,
            fixture_.substitution,
            because(71, 'internal displayed reindexing')
        );

        assert.equal(
            collectOwners(metaLevelSubstitution).includes(
                'displayed-pullback'
            ),
            false
        );
        assert.equal(
            collectOwners(internalReindexing).includes(
                'displayed-pullback'
            ),
            true
        );
        assert.equal(
            kernelExpressionEquals(
                metaLevelSubstitution,
                internalReindexing
            ),
            false
        );
    });

    it('rejects a reversed substitution at its supplied source', () => {
        const fixture_ = dependentFixture();
        const error = expectCheckerError(
            () => fixture_.checker.inferOwnerApplication(
                fixture_.checker.rootContext,
                'displayed-pullback',
                [{
                    plicity: 'explicit',
                    value: fixture_.family
                }, {
                    plicity: 'explicit',
                    value: free('dep_wrong_sigma', 81),
                    provenance: because(81, 'reversed substitution')
                }],
                because(80, 'invalid displayed pullback')
            ),
            'TYPE_MISMATCH'
        );
        assert.equal(error.provenance.span?.start.line, 81);
        assert.match(error.message, /dep_Delta.*dep_Gamma|dep_Gamma.*dep_Delta/);
    });

    it('preserves the proof-time-only constant-section boundary', () => {
        const fixture_ = dependentFixture();
        const displayedType = coreSectionType(
            fixture_.gamma,
            fixture_.constantFamily,
            because(90, 'displayed constant-section type')
        );
        const ordinaryType = coreOrdinaryFunctorType(
            fixture_.gamma,
            fixture_.fibre,
            because(90, 'ordinary constant-section type')
        );

        assert.equal(
            kernelExpressionEquals(displayedType, ordinaryType),
            false
        );
        expectCheckerError(
            () => fixture_.checker.check(
                fixture_.checker.rootContext,
                free('dep_constant_section', 91),
                ordinaryType
            ),
            'TYPE_MISMATCH'
        );
        assert.doesNotThrow(() =>
            fixture_.checker.check(
                fixture_.checker.rootContext,
                free('dep_ordinary_section', 92),
                ordinaryType
            )
        );
    });

    it('serializes proof-time and non-conversion evidence separately', () => {
        const serialized = serializeKernelProbe(
            constantBridgeProbe(dependentFixture())
        );
        assert.match(
            serialized.source,
            /assert ⊢ @eq_refl \(Obj \(Cat_cat\)\) \(@Pi_cat/
        );
        assert.match(
            serialized.source,
            /assertnot ⊢ @Pi_cat/
        );
        assert.equal(
            serialized.sourceMap.filter(
                entry => entry.kind === 'proof-time-comparison'
            ).length,
            1
        );
        assert.equal(
            serialized.sourceMap.filter(
                entry => entry.kind === 'non-conversion'
            ).length,
            1
        );
    });

    it(
        'passes the warning-enabled active owner routes and non-collapse',
        { skip: process.env.EMDASH_RUN_LAMBDAPI_PROBES !== '1' },
        () => {
            const fixture_ = dependentFixture();
            fixture_.checker.validateEnvironment();
            const serialized = serializeKernelProbe(
                constantBridgeProbe(fixture_)
            );
            const result = checkLambdapiProbe(serialized, {
                packageRoot: resolve(__dirname, '../emdash2'),
                timeoutMs: 60_000,
                warningsEnabled: true
            });
            assert.equal(
                result.accepted,
                true,
                `Expected dependent bridge acceptance:\n` +
                `${result.diagnostics}\n${serialized.source}`
            );
            assert.equal(result.timedOut, false);

            const invalidProbe: KernelProbe = {
                requiredModule: LAMBDAPI_V32_MODULE,
                declarations: declarationsForProbe(fixture_.environment),
                assertions: [{
                    label: 'ELAB-2B arbitrary family is not ordinary',
                    term: free('dep_general_section', 160),
                    type: coreOrdinaryFunctorType(
                        fixture_.gamma,
                        fixture_.fibre,
                        because(160, 'invalid ordinary section type')
                    ),
                    span: at(160, 1, 50)
                }]
            };
            const invalid = checkLambdapiProbe(
                serializeKernelProbe(invalidProbe),
                {
                    packageRoot: resolve(__dirname, '../emdash2'),
                    timeoutMs: 30_000
                }
            );
            assert.equal(invalid.accepted, false);
            assert.equal(invalid.timedOut, false);
            assert.match(
                invalid.diagnostics,
                /Assertion failed|does not have type|unification problem/
            );
        }
    );

    it('materializes exact result types for all three new owners', () => {
        const fixture_ = dependentFixture();
        assert.equal(
            serializeKernelExpression(
                coreOwnerResultType(
                    'displayed-pullback',
                    [
                        fixture_.delta,
                        fixture_.gamma,
                        fixture_.family,
                        fixture_.substitution
                    ],
                    because(170, 'pullback result')
                )
            ),
            'τ (Obj (Catd_cat dep_Delta))'
        );
        assert.equal(
            serializeKernelExpression(
                coreOwnerResultType(
                    'constant-displayed-family',
                    [fixture_.gamma, fixture_.fibre],
                    because(171, 'constant-family result')
                )
            ),
            'τ (Obj (Catd_cat dep_Gamma))'
        );
        assert.equal(
            serializeKernelExpression(
                coreOwnerResultType(
                    'section-category',
                    [fixture_.gamma, fixture_.family],
                    because(172, 'section-category result')
                )
            ),
            'Cat'
        );
    });
});
