/**
 * Executable end-user demonstration of FIBRED-DEPENDENT-TARGET-1.
 *
 * The notation is explanatory; the executable input is the typed TypeScript
 * API. No string parser or production Lambdapi process is involved.
 */

import {
    CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_TRANSFER_BOUNDARY
} from './categorical_fibred_dependent_target_transfer';
import {
    CoreCategoricalDiagnostic,
    CoreCategoricalProgram,
    CoreCategoricalProgramCompilation,
    coreCategoricalDiagnosticFromError
} from './categorical_program';

export const
CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_DEMO_REVISION =
    'FIBRED-DEPENDENT-TARGET-1-DEMO-1' as const;

export interface CoreCategoricalFibredDependentTargetDemoResult {
    readonly revision:
        typeof CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_DEMO_REVISION;
    readonly candidate: 'emdash-v3.2-fibred-dependent-target-1';
    readonly construction: 'direct-typescript-categorical-program';
    readonly assumptions: readonly string[];
    readonly target: {
        readonly motive:
            'Pullback_catd(Catd_cat_func,demo_G)';
        readonly family:
            'Sigma_catd_functord_catd(Pi_pullback_funcd(demo_G))';
        readonly context:
            'Σ k :^n demo_K, M :^f Catd(demo_G[k])';
    };
    readonly fibre: {
        readonly input: 'demo_B[(demo_k,demo_M)]';
        readonly output: 'Pi_cat(demo_G[demo_k],demo_M)';
        readonly runtimeStatus: 'equal';
        readonly runtimeRuleIds: readonly string[];
        readonly proofStatus: 'solved';
        readonly categoryPresentationRuntimeCollapse: false;
    };
    readonly eta: {
        readonly input:
            'λ z :^n Σ(k,M). demo_target_section[z]';
        readonly output: 'demo_target_section';
        readonly compilation: CoreCategoricalProgramCompilation;
        readonly callbackCount: 1;
    };
    readonly subjectValidation: {
        readonly directlyCheckedRuntimeRules: 8;
        readonly proofCheckedRuntimeRules: 2;
        readonly proofRule:
            'categorical.dependent-target.category-presentation';
        readonly externalOracleUsed: false;
    };
    readonly rejectedInput: 'dependentSectionMotive(demo_wrong_G)';
    readonly negativeDiagnostic: CoreCategoricalDiagnostic;
    readonly newLambdapiMathematicalOwnerOrRule: false;
    readonly arbitraryCoherentSectionSynthesis: false;
    readonly stringParserDependency: false;
    readonly productionLambdapiDependency: false;
    readonly boundary:
        typeof CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_TRANSFER_BOUNDARY;
}

export function runCoreCategoricalFibredDependentTargetDemo():
CoreCategoricalFibredDependentTargetDemoResult {
    const emdash = new CoreCategoricalProgram({
        sourceFile:
            'examples/v3_2_categorical_fibred_dependent_target_demo.ts',
        profile: 'fibred-dependent-target-1'
    });
    const K = emdash.category('demo_K', { line: 1 });
    const G = emdash.contravariantCategoryFamily(
        'demo_G',
        K,
        { line: 2 }
    );
    const motive = emdash.dependentSectionMotive(G, { line: 3 });
    const target = emdash.dependentSectionTarget(G, { line: 4 });
    const k = emdash.object('demo_k', K, { line: 5 });
    const M = emdash.object(
        'demo_M',
        emdash.fibre(motive, k),
        { line: 6 }
    );
    const pair = emdash.dependentPair(
        motive,
        k,
        M,
        { line: 7 }
    );
    const actualFibre = emdash.fibre(target, pair, { line: 8 });
    const expectedFibre = emdash.dependentSectionCategoryAt(
        G,
        k,
        M,
        { line: 9 }
    );
    const fibreCompatibility =
        emdash.dependentTargetCategoryCompatibility(
            actualFibre,
            expectedFibre
        );
    if (
        fibreCompatibility.runtime.status !== 'equal' ||
        fibreCompatibility.proofTime.status !== 'solved'
    ) {
        throw new Error(
            'Dependent target fibre did not compute to its Pi category'
        );
    }

    const section = emdash.section(
        'demo_target_section',
        target,
        { line: 12 }
    );
    let callbackCount = 0;
    const eta = emdash.dependentLambda(
        'z',
        target,
        z => {
            callbackCount += 1;
            return emdash.apply(section, z, {
                expectedShape: 'dependent-object',
                source: { line: 17 }
            });
        },
        {
            variation: 'natural',
            dependency: 'displayed',
            source: { line: 14 }
        }
    );
    const etaCompilation = emdash.compile(eta);
    if (
        callbackCount !== 1 ||
        etaCompilation.explicitCore !==
            '(free "demo_target_section")'
    ) {
        throw new Error('Dependent target eta drifted');
    }

    let negativeDiagnostic: CoreCategoricalDiagnostic | undefined;
    try {
        emdash.dependentSectionMotive(
            emdash.functor('demo_wrong_G', K, K),
            {
                line: 30,
                detail: 'wrong dependent-target codomain'
            }
        );
    } catch (error: unknown) {
        negativeDiagnostic =
            coreCategoricalDiagnosticFromError(error);
        if (negativeDiagnostic === undefined) throw error;
    }
    if (negativeDiagnostic === undefined) {
        throw new Error(
            'Dependent target unexpectedly accepted a covariant family'
        );
    }

    return Object.freeze({
        revision:
            CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_DEMO_REVISION,
        candidate: 'emdash-v3.2-fibred-dependent-target-1',
        construction: 'direct-typescript-categorical-program',
        assumptions: Object.freeze([
            'demo_K : Cat',
            'demo_G : demo_K ⊢ Op(Cat_cat)',
            'demo_k : Obj demo_K',
            'demo_M : Catd(demo_G[demo_k])',
            'demo_target_section : Π z :^n Σ(k,M), demo_B[z]'
        ]),
        target: Object.freeze({
            motive:
                'Pullback_catd(Catd_cat_func,demo_G)' as const,
            family:
                'Sigma_catd_functord_catd(Pi_pullback_funcd(demo_G))' as const,
            context:
                'Σ k :^n demo_K, M :^f Catd(demo_G[k])' as const
        }),
        fibre: Object.freeze({
            input: 'demo_B[(demo_k,demo_M)]' as const,
            output:
                'Pi_cat(demo_G[demo_k],demo_M)' as const,
            runtimeStatus: 'equal' as const,
            runtimeRuleIds: Object.freeze(
                fibreCompatibility.runtime.trace.flatMap(entry =>
                    entry.reduction.kind === 'runtime'
                        ? [entry.reduction.ruleId]
                        : []
                )
            ),
            proofStatus: 'solved' as const,
            categoryPresentationRuntimeCollapse: false as const
        }),
        eta: Object.freeze({
            input:
                'λ z :^n Σ(k,M). demo_target_section[z]' as const,
            output: 'demo_target_section' as const,
            compilation: etaCompilation,
            callbackCount: 1 as const
        }),
        subjectValidation: Object.freeze({
            directlyCheckedRuntimeRules: 8 as const,
            proofCheckedRuntimeRules: 2 as const,
            proofRule:
                'categorical.dependent-target.category-presentation' as const,
            externalOracleUsed: false as const
        }),
        rejectedInput:
            'dependentSectionMotive(demo_wrong_G)' as const,
        negativeDiagnostic,
        newLambdapiMathematicalOwnerOrRule: false,
        arbitraryCoherentSectionSynthesis: false,
        stringParserDependency: false,
        productionLambdapiDependency: false,
        boundary:
            CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_TRANSFER_BOUNDARY
    });
}

export function formatCoreCategoricalFibredDependentTargetDemo(
    result: CoreCategoricalFibredDependentTargetDemoResult =
        runCoreCategoricalFibredDependentTargetDemo()
): string {
    return [
        result.candidate,
        `Input path: ${result.construction}`,
        '',
        'Dependent target:',
        `  Context: ${result.target.context}`,
        `  Motive: ${result.target.motive}`,
        `  Family: ${result.target.family}`,
        '',
        'Computed fibre:',
        `  ${result.fibre.input}`,
        `      ↦ ${result.fibre.output}`,
        `  Runtime: ${result.fibre.runtimeStatus}`,
        `  Rules: ${result.fibre.runtimeRuleIds.join(', ')}`,
        '',
        'Total-context eta:',
        `  Input: ${result.eta.input}`,
        `  Core/output: ${result.eta.compilation.explicitCore}`,
        `  Callback evaluations: ${result.eta.callbackCount}`,
        '',
        'Transfer subject validation:',
        '  Direct runtime subjects: ' +
            result.subjectValidation.directlyCheckedRuntimeRules,
        '  Proof-assisted runtime subjects: ' +
            result.subjectValidation.proofCheckedRuntimeRules,
        `  Proof rule: ${result.subjectValidation.proofRule}`,
        '',
        'Rejected wrong-family input:',
        `  ${result.rejectedInput}`,
        `  ${result.negativeDiagnostic.code}: ` +
            result.negativeDiagnostic.message,
        '',
        'New Lambdapi mathematical owner/rule: no',
        'Arbitrary coherent-section synthesis: no',
        'String parser dependency: no',
        'Production Lambdapi dependency: no'
    ].join('\n');
}
