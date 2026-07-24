/**
 * Focused ELAB-2C tests for dependent telescope structural maps.
 */

import assert from 'node:assert';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CoreBindingInput,
    CoreChecker,
    CoreContext,
    CoreContextError,
    CoreDeclarationEnvironment,
    CoreElaborationSession,
    CoreLocalLookup,
    CoreOwnerId,
    KernelExpression,
    KernelProbe,
    KernelScopeError,
    LAMBDAPI_V32_MODULE,
    binderMode,
    checkLambdapiProbe,
    coreDisplayedFamilyType,
    coreSectionType,
    coreTelescopeContraction,
    coreTelescopeExchange,
    coreTelescopeWeakening,
    kernelApplication,
    kernelAssertScoped,
    kernelBinder,
    kernelBound,
    kernelExpressionEquals,
    kernelFree,
    kernelLambda,
    kernelRemapAmbientIndices,
    provenance,
    serializeKernelProbe,
    sourceSpan
} from '../src/v3_2';

const fixture = 'tests/fixtures/v3_2_telescope_structural.surface.ts';
const at = (line: number, startColumn = 1, endColumn = startColumn + 1) =>
    sourceSpan(fixture, line, startColumn, line, endColumn);

const because = (line: number, detail: string) =>
    provenance('surface', detail, at(line));

const explicitFunctorial = binderMode('explicit', 'functorial');
const implicitNatural = binderMode('implicit', 'natural');

const categoryUniverse = (line: number): KernelExpression =>
    kernelApplication(
        'category-universe',
        [],
        because(line, 'ELAB-2C category universe')
    );

const local = (
    name: string,
    type: KernelExpression,
    line: number,
    mode = explicitFunctorial
): CoreBindingInput => ({
    name,
    type,
    mode,
    provenance: because(line, `ELAB-2C local ${name}`)
});

const bound = (index: number, line: number, detail: string) =>
    kernelBound(index, because(line, detail));

interface StructuralFixture {
    readonly environment: CoreDeclarationEnvironment;
    readonly checker: CoreChecker;
    readonly gamma: KernelExpression;
    readonly familyType: KernelExpression;
}

const structuralFixture = (): StructuralFixture => {
    const environment = CoreDeclarationEnvironment.empty().extend({
        name: 'struct_Gamma',
        type: categoryUniverse(10),
        mode: explicitFunctorial,
        provenance: because(10, 'ELAB-2C base category declaration')
    });
    const gamma = kernelFree(
        'struct_Gamma',
        because(11, 'ELAB-2C base category use')
    );
    return {
        environment,
        checker: new CoreChecker(new CoreElaborationSession(environment)),
        gamma,
        familyType: coreDisplayedFamilyType(
            gamma,
            because(11, 'ELAB-2C displayed-family type')
        )
    };
};

const dependentSectionContext = (
    fixture_: StructuralFixture,
    familyLine: number,
    sectionLine: number,
    occurrenceLine = sectionLine
): CoreContext => CoreContext.empty(fixture_.environment)
    .extend(local(
        'struct_family',
        fixture_.familyType,
        familyLine
    ))
    .extend(local(
        'struct_section',
        coreSectionType(
            fixture_.gamma,
            bound(
                0,
                occurrenceLine,
                'ELAB-2C dependent family occurrence'
            ),
            because(sectionLine, 'ELAB-2C dependent section type')
        ),
        sectionLine
    ));

const exchangeContext = (
    fixture_: StructuralFixture
): CoreContext => CoreContext.empty(fixture_.environment)
    .extend(local('exchange_family', fixture_.familyType, 40))
    .extend(local('exchange_marker', categoryUniverse(41), 41))
    .extend(local(
        'exchange_section',
        coreSectionType(
            fixture_.gamma,
            bound(1, 42, 'ELAB-2C family across independent marker'),
            because(42, 'ELAB-2C exchanged suffix section type')
        ),
        42
    ));

const contractionContext = (
    fixture_: StructuralFixture
): CoreContext => CoreContext.empty(fixture_.environment)
    .extend(local('contract_family_left', fixture_.familyType, 60))
    .extend(local('contract_family_right', fixture_.familyType, 61))
    .extend(local(
        'contract_section',
        coreSectionType(
            fixture_.gamma,
            bound(0, 62, 'ELAB-2C right family occurrence'),
            because(62, 'ELAB-2C contracted suffix section type')
        ),
        62
    ));

const localLookup = (
    context: CoreContext,
    name: string,
    line: number
): CoreLocalLookup => {
    const result = context.resolve(
        name,
        because(line, `ELAB-2C lookup ${name}`)
    );
    assert.equal(result.kind, 'local');
    if (result.kind !== 'local') {
        throw new Error(`Expected local lookup for ${name}`);
    }
    return result;
};

const expectBoundIndex = (
    expression: KernelExpression,
    expected: number
): void => {
    assert.equal(expression.tag, 'bound');
    assert.equal(
        expression.tag === 'bound' ? expression.index : undefined,
        expected
    );
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

const declarationsForProbe = (
    environment: CoreDeclarationEnvironment
): KernelProbe['declarations'] => environment.declarations.map(
    declaration => ({
        name: declaration.name,
        type: declaration.type,
        span: declaration.provenance.span!
    })
);

const structuralProbe = (): KernelProbe => {
    const fixture_ = structuralFixture();

    const weakeningSource = dependentSectionContext(fixture_, 100, 101);
    const weakening = coreTelescopeWeakening(
        weakeningSource,
        local('weakening_unused', categoryUniverse(102), 102)
    );
    const weakenedSection = localLookup(
        weakeningSource,
        'struct_section',
        103
    );

    const exchangeSource = exchangeContext(fixture_);
    const exchange = coreTelescopeExchange(
        exchangeSource,
        0,
        because(104, 'ELAB-2C permitted exchange probe')
    );
    const exchangedSection = localLookup(
        exchangeSource,
        'exchange_section',
        104
    );

    const contractionSource = contractionContext(fixture_);
    const contraction = coreTelescopeContraction(
        contractionSource,
        0,
        because(105, 'ELAB-2C contraction probe')
    );
    const contractedSection = localLookup(
        contractionSource,
        'contract_section',
        105
    );

    return {
        requiredModule: LAMBDAPI_V32_MODULE,
        declarations: declarationsForProbe(fixture_.environment),
        assertions: [{
            label: 'ELAB-2C dependent weakening',
            term: weakening.target.abstractLambda(
                weakening.apply(weakenedSection.term)
            ),
            type: weakening.target.abstractPi(
                weakening.apply(weakenedSection.type)
            ),
            span: at(103, 1, 50)
        }, {
            label: 'ELAB-2C permitted dependent exchange',
            term: exchange.target.abstractLambda(
                exchange.apply(exchangedSection.term)
            ),
            type: exchange.target.abstractPi(
                exchange.apply(exchangedSection.type)
            ),
            span: at(104, 1, 50)
        }, {
            label: 'ELAB-2C dependent contraction',
            term: contraction.target.abstractLambda(
                contraction.apply(contractedSection.term)
            ),
            type: contraction.target.abstractPi(
                contraction.apply(contractedSection.type)
            ),
            span: at(105, 1, 50)
        }]
    };
};

describe('TypeScript v3.2 ELAB-2C telescope structure', () => {
    it('remaps ambient indices beneath binders without losing provenance', () => {
        const ambientOccurrence = bound(
            1,
            20,
            'ELAB-2C ambient occurrence beneath a lambda'
        );
        const openLambda = kernelLambda(
            kernelBinder(
                'inner',
                categoryUniverse(19),
                explicitFunctorial,
                because(19, 'ELAB-2C inner binder')
            ),
            ambientOccurrence,
            because(19, 'ELAB-2C open lambda')
        );
        const mapped = kernelRemapAmbientIndices(openLambda, 2, [1]);

        assert.equal(mapped.tag, 'lambda');
        if (mapped.tag !== 'lambda') {
            throw new Error('Expected a mapped lambda');
        }
        expectBoundIndex(mapped.body, 2);
        assert.equal(mapped.body.provenance.span?.start.line, 20);
        assert.doesNotThrow(() => kernelAssertScoped(mapped, 2));

        assert.throws(
            () => kernelRemapAmbientIndices(openLambda, 0, [null]),
            (error: unknown) => {
                assert.ok(error instanceof KernelScopeError);
                assert.equal(error.code, 'DROPPED_BOUND_VARIABLE');
                assert.equal(error.provenance.span?.start.line, 20);
                return true;
            }
        );
        assert.throws(
            () => kernelRemapAmbientIndices(ambientOccurrence, 1, [1, 0]),
            (error: unknown) => {
                assert.ok(error instanceof KernelScopeError);
                assert.equal(error.code, 'INVALID_AMBIENT_INDEX_MAP');
                return true;
            }
        );
    });

    it('weakens a dependent section under one unused local binder', () => {
        const fixture_ = structuralFixture();
        const source = dependentSectionContext(fixture_, 30, 31);
        const weakening = coreTelescopeWeakening(
            source,
            local('weakening_unused', categoryUniverse(32), 32)
        );

        assert.equal(weakening.kind, 'weakening');
        assert.deepEqual(weakening.ambientIndexMap, [1, 2]);
        assert.deepEqual(
            weakening.target.telescope.map(binding => binding.name),
            ['struct_family', 'struct_section', 'weakening_unused']
        );
        assert.equal(source.depth, 2);

        const sourceFamily = localLookup(source, 'struct_family', 33);
        const sourceSection = localLookup(source, 'struct_section', 34);
        const targetSection = localLookup(
            weakening.target,
            'struct_section',
            35
        );
        const mappedSection = weakening.apply(sourceSection.term);
        const mappedSectionType = weakening.apply(sourceSection.type);

        expectBoundIndex(weakening.apply(sourceFamily.term), 2);
        expectBoundIndex(mappedSection, 1);
        assert.equal(
            kernelExpressionEquals(mappedSectionType, targetSection.type),
            true
        );
        const inferred = fixture_.checker.infer(
            weakening.target,
            mappedSection
        );
        assert.equal(
            kernelExpressionEquals(
                inferred.type as KernelExpression,
                mappedSectionType
            ),
            true
        );
        assert.ok(collectOwners(mappedSectionType).includes(
            'section-category'
        ));
        assert.equal(
            collectOwners(mappedSectionType).includes('displayed-pullback'),
            false
        );
    });

    it('exchanges independent binders and transports a dependent suffix', () => {
        const fixture_ = structuralFixture();
        const source = exchangeContext(fixture_);
        const exchange = coreTelescopeExchange(
            source,
            0,
            because(43, 'ELAB-2C permitted exchange')
        );

        assert.equal(exchange.kind, 'exchange');
        assert.deepEqual(exchange.ambientIndexMap, [0, 2, 1]);
        assert.deepEqual(
            exchange.target.telescope.map(binding => binding.name),
            ['exchange_marker', 'exchange_family', 'exchange_section']
        );

        const sourceFamily = localLookup(source, 'exchange_family', 44);
        const sourceMarker = localLookup(source, 'exchange_marker', 45);
        const sourceSection = localLookup(source, 'exchange_section', 46);
        const targetSection = localLookup(
            exchange.target,
            'exchange_section',
            47
        );
        const mappedSection = exchange.apply(sourceSection.term);
        const mappedSectionType = exchange.apply(sourceSection.type);

        expectBoundIndex(exchange.apply(sourceFamily.term), 1);
        expectBoundIndex(exchange.apply(sourceMarker.term), 2);
        expectBoundIndex(mappedSection, 0);
        assert.equal(
            kernelExpressionEquals(mappedSectionType, targetSection.type),
            true
        );
        const inferred = fixture_.checker.infer(
            exchange.target,
            mappedSection
        );
        assert.equal(
            kernelExpressionEquals(
                inferred.type as KernelExpression,
                mappedSectionType
            ),
            true
        );
    });

    it('rejects exchange at the exact dependency occurrence', () => {
        const fixture_ = structuralFixture();
        const source = dependentSectionContext(fixture_, 50, 51, 52);

        assert.throws(
            () => coreTelescopeExchange(
                source,
                0,
                because(53, 'ELAB-2C forbidden exchange')
            ),
            (error: unknown) => {
                assert.ok(error instanceof CoreContextError);
                assert.equal(error.code, 'DEPENDENT_EXCHANGE');
                assert.equal(error.provenance.span?.start.line, 52);
                assert.equal(
                    error.scopeError?.code,
                    'DROPPED_BOUND_VARIABLE'
                );
                assert.match(
                    error.message,
                    /struct_section.*depends on.*struct_family/
                );
                return true;
            }
        );
        assert.deepEqual(
            source.telescope.map(binding => binding.name),
            ['struct_family', 'struct_section']
        );
    });

    it('contracts duplicate binders through an explicit diagonal map', () => {
        const fixture_ = structuralFixture();
        const source = contractionContext(fixture_);
        const contraction = coreTelescopeContraction(
            source,
            0,
            because(63, 'ELAB-2C valid contraction')
        );

        assert.equal(contraction.kind, 'contraction');
        assert.deepEqual(contraction.ambientIndexMap, [0, 1, 1]);
        assert.deepEqual(
            contraction.target.telescope.map(binding => binding.name),
            ['contract_family_left', 'contract_section']
        );

        const left = localLookup(source, 'contract_family_left', 64);
        const right = localLookup(source, 'contract_family_right', 65);
        const section = localLookup(source, 'contract_section', 66);
        const targetSection = localLookup(
            contraction.target,
            'contract_section',
            67
        );
        const mappedLeft = contraction.apply(left.term);
        const mappedRight = contraction.apply(right.term);
        const mappedSection = contraction.apply(section.term);
        const mappedSectionType = contraction.apply(section.type);

        expectBoundIndex(mappedLeft, 1);
        expectBoundIndex(mappedRight, 1);
        expectBoundIndex(mappedSection, 0);
        assert.equal(
            kernelExpressionEquals(mappedLeft, mappedRight),
            true
        );
        assert.equal(
            kernelExpressionEquals(mappedSectionType, targetSection.type),
            true
        );
        const inferred = fixture_.checker.infer(
            contraction.target,
            mappedSection
        );
        assert.equal(
            kernelExpressionEquals(
                inferred.type as KernelExpression,
                mappedSectionType
            ),
            true
        );
        assert.equal(
            collectOwners(mappedSectionType).includes('displayed-pullback'),
            false
        );
    });

    it('preserves a dependent prefix at a nonzero structural position', () => {
        const fixture_ = structuralFixture();
        const exchangeSource = CoreContext.empty(fixture_.environment)
            .extend(local('nested_base', categoryUniverse(68), 68))
            .extend(local(
                'nested_family',
                coreDisplayedFamilyType(
                    bound(0, 69, 'ELAB-2C exchange base occurrence'),
                    because(69, 'ELAB-2C exchange family type')
                ),
                69
            ))
            .extend(local(
                'nested_marker',
                coreDisplayedFamilyType(
                    bound(1, 70, 'ELAB-2C marker base occurrence'),
                    because(70, 'ELAB-2C independent marker type')
                ),
                70
            ))
            .extend(local(
                'nested_section',
                coreSectionType(
                    bound(2, 71, 'ELAB-2C section base occurrence'),
                    bound(1, 71, 'ELAB-2C section family occurrence'),
                    because(71, 'ELAB-2C nested exchange suffix')
                ),
                71
            ));
        const exchange = coreTelescopeExchange(
            exchangeSource,
            1,
            because(72, 'ELAB-2C nested exchange')
        );
        assert.deepEqual(exchange.ambientIndexMap, [0, 2, 1, 3]);
        assert.deepEqual(
            exchange.target.telescope.map(binding => binding.name),
            [
                'nested_base',
                'nested_marker',
                'nested_family',
                'nested_section'
            ]
        );
        const exchangeSection = localLookup(
            exchangeSource,
            'nested_section',
            73
        );
        const exchangedSection = exchange.apply(exchangeSection.term);
        const exchangedType = exchange.apply(exchangeSection.type);
        const inferredExchange = fixture_.checker.infer(
            exchange.target,
            exchangedSection
        );
        assert.equal(
            kernelExpressionEquals(
                inferredExchange.type as KernelExpression,
                exchangedType
            ),
            true
        );

        const contractionSource = CoreContext.empty(fixture_.environment)
            .extend(local('nested_contract_base', categoryUniverse(74), 74))
            .extend(local(
                'nested_contract_left',
                coreDisplayedFamilyType(
                    bound(0, 75, 'ELAB-2C contraction base occurrence'),
                    because(75, 'ELAB-2C left contraction type')
                ),
                75
            ))
            .extend(local(
                'nested_contract_right',
                coreDisplayedFamilyType(
                    bound(1, 76, 'ELAB-2C weakened contraction base'),
                    because(76, 'ELAB-2C right contraction type')
                ),
                76
            ))
            .extend(local(
                'nested_contract_section',
                coreSectionType(
                    bound(2, 77, 'ELAB-2C contracted section base'),
                    bound(0, 77, 'ELAB-2C contracted section family'),
                    because(77, 'ELAB-2C nested contraction suffix')
                ),
                77
            ));
        const contraction = coreTelescopeContraction(
            contractionSource,
            1,
            because(78, 'ELAB-2C nested contraction')
        );
        assert.deepEqual(contraction.ambientIndexMap, [0, 1, 1, 2]);
        assert.deepEqual(
            contraction.target.telescope.map(binding => binding.name),
            [
                'nested_contract_base',
                'nested_contract_left',
                'nested_contract_section'
            ]
        );
        const contractionSection = localLookup(
            contractionSource,
            'nested_contract_section',
            79
        );
        const contractedSection = contraction.apply(
            contractionSection.term
        );
        const contractedType = contraction.apply(
            contractionSection.type
        );
        const inferredContraction = fixture_.checker.infer(
            contraction.target,
            contractedSection
        );
        assert.equal(
            kernelExpressionEquals(
                inferredContraction.type as KernelExpression,
                contractedType
            ),
            true
        );
    });

    it('rejects contraction without matching type and mode data', () => {
        const fixture_ = structuralFixture();
        const dependent = dependentSectionContext(fixture_, 84, 85);
        assert.throws(
            () => coreTelescopeContraction(
                dependent,
                0,
                because(86, 'ELAB-2C invalid typed contraction')
            ),
            (error: unknown) => {
                assert.ok(error instanceof CoreContextError);
                assert.equal(error.code, 'INVALID_CONTRACTION');
                assert.equal(error.provenance.span?.start.line, 85);
                assert.match(error.message, /not the weakened type/);
                return true;
            }
        );

        const modeMismatch = CoreContext.empty(fixture_.environment)
            .extend(local(
                'mode_left',
                fixture_.familyType,
                87,
                explicitFunctorial
            ))
            .extend(local(
                'mode_right',
                fixture_.familyType,
                88,
                implicitNatural
            ));
        assert.throws(
            () => coreTelescopeContraction(
                modeMismatch,
                0,
                because(89, 'ELAB-2C invalid mode contraction')
            ),
            (error: unknown) => {
                assert.ok(error instanceof CoreContextError);
                assert.equal(error.code, 'INVALID_CONTRACTION');
                assert.equal(error.provenance.span?.start.line, 88);
                assert.match(error.message, /binder modes differ/);
                return true;
            }
        );
    });

    it('rejects structural positions that do not select an adjacent pair', () => {
        const fixture_ = structuralFixture();
        const source = dependentSectionContext(fixture_, 80, 81);
        assert.throws(
            () => coreTelescopeExchange(
                source,
                1,
                because(82, 'ELAB-2C invalid exchange position')
            ),
            (error: unknown) => {
                assert.ok(error instanceof CoreContextError);
                assert.equal(error.code, 'INVALID_STRUCTURAL_POSITION');
                assert.equal(error.provenance.span?.start.line, 82);
                return true;
            }
        );
        assert.throws(
            () => coreTelescopeContraction(
                source,
                -1,
                because(83, 'ELAB-2C invalid contraction position')
            ),
            (error: unknown) => {
                assert.ok(error instanceof CoreContextError);
                assert.equal(error.code, 'INVALID_STRUCTURAL_POSITION');
                assert.equal(error.provenance.span?.start.line, 83);
                return true;
            }
        );
    });

    it('serializes the three maps without internal structural owners', () => {
        const serialized = serializeKernelProbe(structuralProbe());
        assert.doesNotMatch(
            serialized.source,
            /Const_func_func|sym_func_func|diag_func_func/
        );
        assert.doesNotMatch(serialized.source, /Pullback_catd/);
        assert.equal(
            serialized.sourceMap.filter(entry =>
                entry.kind === 'assertion'
            ).length,
            3
        );
    });

    it(
        'passes all three dependent structural consumers in Lambdapi',
        { skip: process.env.EMDASH_RUN_LAMBDAPI_PROBES !== '1' },
        () => {
            const serialized = serializeKernelProbe(structuralProbe());
            const result = checkLambdapiProbe(serialized, {
                packageRoot: resolve(__dirname, '../emdash2'),
                timeoutMs: 60_000,
                warningsEnabled: true
            });
            assert.equal(
                result.accepted,
                true,
                `Expected structural-map acceptance:\n` +
                `${result.diagnostics}\n${serialized.source}`
            );
            assert.equal(result.timedOut, false);
        }
    );
});
