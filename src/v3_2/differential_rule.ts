/**
 * Shared TSK-3B differential cases for the reviewed runtime-rule boundary.
 *
 * Each row uses one Core redex/reduct pair in both engines, adds a rigid
 * well-typed near miss, and records a malformed manifest candidate. Lambdapi
 * witnesses the absence of a broader conversion; it does not validate the
 * TypeScript manifest grammar.
 */

import {
    CoreDeclarationEnvironment
} from './context';
import {
    CORE_MVP_DIFFERENTIAL_SCOPE,
    CoreMvpDifferentialError,
    validateCoreMvpDifferentialScope
} from './differential';
import {
    ElaboratedSurfaceTerm,
    elaborateSurfaceTerm
} from './elaborator';
import {
    KernelApplication,
    KernelExpression,
    SourceSpan,
    binderMode,
    kernelExpressionEquals,
    provenance,
    sourceSpan
} from './kernel';
import {
    LAMBDAPI_V32_MODULE
} from './lambdapi';
import {
    CORE_MVP_MANIFEST,
    CoreManifestRuleInput
} from './manifest';
import {
    KernelProbe,
    KernelProbeDeclaration,
    declarationsFromSurfaceContext
} from './probe';
import {
    CORE_MVP_RUNTIME_PROGRAM,
    CoreRuntimeCompilationErrorCode
} from './runtime';
import {
    SurfaceContext,
    SurfaceTerm,
    categoryType,
    coreTypeToKernelType,
    functorType,
    homType,
    objectType,
    surfaceBinding,
    surfaceFapp0,
    surfaceFapp1,
    surfaceFapp1Func,
    surfaceReference,
    surfaceTapp0,
    surfaceTapp0Func,
    surfaceTapp1,
    surfaceTapp1Func,
    transforType
} from './surface';

export interface CoreMvpRuleAbsenceWitness {
    /**
     * The malformed manifest grammar itself is checked only in TypeScript.
     */
    readonly interpretation:
        'oracle-rejects-erased-full-projection-conversion';
    readonly malformedRuleId: string;
    readonly left: KernelExpression;
    readonly right: KernelExpression;
}

export interface CoreMvpMalformedRuleDifferentialCase {
    readonly mutation: 'erase-required-full-projection';
    readonly candidate: CoreManifestRuleInput;
    readonly expectedError: CoreRuntimeCompilationErrorCode;
    readonly oracleAbsenceWitness: CoreMvpRuleAbsenceWitness;
}

export interface CoreMvpRuleNearMissTypingEvidence {
    readonly method:
        'same-classifier-substitution-into-surface-elaborated-redex';
    readonly originalFunctor: KernelExpression;
    readonly originalFunctorType: KernelExpression;
    readonly replacementFunctor: KernelExpression;
    readonly replacementFunctorType: KernelExpression;
    readonly resultType: KernelExpression;
    /**
     * H-04 deliberately did not add the active classifier equations needed
     * to replay the full evaluator application in the standalone checker.
     */
    readonly standaloneCheckerBoundary:
        'withheld-active-classifier-computation';
}

export interface CoreMvpRuleDifferentialCase {
    readonly order: number;
    readonly ruleId: string;
    readonly redex: KernelExpression;
    readonly reduct: KernelExpression;
    readonly redexType: KernelExpression;
    readonly reductType: KernelExpression;
    readonly nearMiss: KernelExpression;
    readonly nearMissType: KernelExpression;
    readonly nearMissFunctorName: string;
    readonly nearMissTyping: CoreMvpRuleNearMissTypingEvidence;
    readonly span: SourceSpan;
    readonly malformed: CoreMvpMalformedRuleDifferentialCase;
}

export interface CoreMvpRuleDifferentialCorpus {
    readonly manifestRevision: string;
    readonly manifestContentHash: string;
    readonly ruleIds: readonly string[];
    readonly environment: CoreDeclarationEnvironment;
    readonly declarations: readonly KernelProbeDeclaration[];
    readonly cases: readonly CoreMvpRuleDifferentialCase[];
    readonly probe: KernelProbe;
}

interface SurfaceRuleCase {
    readonly ruleId: string;
    readonly fullFunctor: SurfaceTerm;
    readonly redex: SurfaceTerm;
    readonly reduct: SurfaceTerm;
}

const corpusSource =
    'generated/v3_2_mvp_rule_differential.core.ts';

const spanAt = (line: number): SourceSpan =>
    sourceSpan(corpusSource, line, 1, line, 80);

const because = (line: number, detail: string) =>
    provenance('derived', detail, spanAt(line));

const ref = (name: string, line: number): SurfaceTerm =>
    surfaceReference(name, spanAt(line));

const ruleSurfaceContext = (): SurfaceContext => new SurfaceContext([
    surfaceBinding('differential_rule_A', categoryType(), spanAt(1)),
    surfaceBinding('differential_rule_B', categoryType(), spanAt(2)),
    surfaceBinding(
        'differential_rule_x',
        objectType('differential_rule_A'),
        spanAt(3)
    ),
    surfaceBinding(
        'differential_rule_y',
        objectType('differential_rule_A'),
        spanAt(4)
    ),
    surfaceBinding(
        'differential_rule_F',
        functorType('differential_rule_A', 'differential_rule_B'),
        spanAt(5)
    ),
    surfaceBinding(
        'differential_rule_G',
        functorType('differential_rule_A', 'differential_rule_B'),
        spanAt(6)
    ),
    surfaceBinding(
        'differential_rule_f',
        homType(
            'differential_rule_A',
            'differential_rule_x',
            'differential_rule_y'
        ),
        spanAt(7)
    ),
    surfaceBinding(
        'differential_rule_eta',
        transforType(
            'differential_rule_A',
            'differential_rule_B',
            'differential_rule_F',
            'differential_rule_G'
        ),
        spanAt(8),
        binderMode('implicit', 'natural')
    )
]);

const ruleSurfaceCases = (): readonly SurfaceRuleCase[] => {
    const fullFunctorHom = surfaceFapp1Func(
        ref('differential_rule_F', 20),
        ref('differential_rule_x', 20),
        ref('differential_rule_y', 20),
        spanAt(20)
    );
    const fullTransforComponent = surfaceTapp0Func(
        ref('differential_rule_F', 21),
        ref('differential_rule_G', 21),
        ref('differential_rule_y', 21),
        spanAt(21)
    );
    const fullTransforHom = surfaceTapp1Func(
        ref('differential_rule_eta', 22),
        ref('differential_rule_x', 22),
        ref('differential_rule_y', 22),
        spanAt(22)
    );

    return [{
        ruleId: 'projection.functor-hom.evaluate',
        fullFunctor: fullFunctorHom,
        redex: surfaceFapp0(
            fullFunctorHom,
            ref('differential_rule_f', 23),
            spanAt(23)
        ),
        reduct: surfaceFapp1(
            ref('differential_rule_F', 24),
            ref('differential_rule_f', 24),
            spanAt(24)
        )
    }, {
        ruleId: 'projection.transfor-component.evaluate',
        fullFunctor: fullTransforComponent,
        redex: surfaceFapp0(
            fullTransforComponent,
            ref('differential_rule_eta', 25),
            spanAt(25)
        ),
        reduct: surfaceTapp0(
            ref('differential_rule_eta', 26),
            ref('differential_rule_y', 26),
            spanAt(26)
        )
    }, {
        ruleId: 'projection.transfor-hom.evaluate',
        fullFunctor: fullTransforHom,
        redex: surfaceFapp0(
            fullTransforHom,
            ref('differential_rule_f', 27),
            spanAt(27)
        ),
        reduct: surfaceTapp1(
            ref('differential_rule_eta', 28),
            ref('differential_rule_f', 28),
            spanAt(28)
        )
    }];
};

const environmentFromSurfaceContext = (
    context: SurfaceContext
): CoreDeclarationEnvironment => {
    let environment = CoreDeclarationEnvironment.empty();
    for (const binding of context.bindings) {
        environment = environment.extend({
            name: binding.name,
            type: binding.kernelType,
            mode: binding.mode,
            provenance: provenance(
                'surface',
                `TSK-3B surface declaration ${binding.name}`,
                binding.span
            )
        });
    }
    return environment;
};

const replaceApplicationArgument = (
    expression: KernelExpression,
    index: number,
    value: KernelExpression
): KernelApplication => {
    if (expression.tag !== 'application') {
        throw new CoreMvpDifferentialError(
            'DIFFERENTIAL_SCOPE_MISMATCH',
            'TSK-3B near miss expected an owner application'
        );
    }
    return {
        ...expression,
        arguments: expression.arguments.map((argument, argumentIndex) =>
            argumentIndex === index
                ? { ...argument, value }
                : argument
        )
    };
};

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Object.values(value as Record<string, unknown>).forEach(item =>
            deepFreeze(item)
        );
        Object.freeze(value);
    }
    return value;
};

const cloneMalformedRule = (
    rule: CoreManifestRuleInput
): CoreManifestRuleInput => {
    const candidate = JSON.parse(
        JSON.stringify(rule)
    ) as CoreManifestRuleInput & {
        variables: string[];
        left: {
            tag: 'owner-application';
            owner: string;
            arguments: CoreManifestRuleInput['left'][];
        };
    };
    candidate.variables.push('H');
    candidate.left.arguments[2] = {
        tag: 'variable',
        name: 'H'
    };
    return deepFreeze(candidate);
};

const elaborateRuleCase = (
    context: SurfaceContext,
    input: SurfaceRuleCase
): {
    readonly fullFunctor: ElaboratedSurfaceTerm;
    readonly redex: ElaboratedSurfaceTerm;
    readonly reduct: ElaboratedSurfaceTerm;
} => ({
    fullFunctor: elaborateSurfaceTerm(context, input.fullFunctor),
    redex: elaborateSurfaceTerm(context, input.redex),
    reduct: elaborateSurfaceTerm(context, input.reduct)
});

/**
 * Build the exact three rule rows shared by TypeScript and Lambdapi.
 *
 * A fresh rigid functor with the full projection's exact classifier replaces
 * that projection in each redex. The resulting term is well typed but cannot
 * match the reviewed rule, so it also serves as the oracle-side absence
 * witness paired with the malformed candidate.
 */
export function buildCoreMvpRuleDifferentialCorpus(
): CoreMvpRuleDifferentialCorpus {
    validateCoreMvpDifferentialScope(CORE_MVP_DIFFERENTIAL_SCOPE);

    const context = ruleSurfaceContext();
    let environment = environmentFromSurfaceContext(context);
    const declarations: KernelProbeDeclaration[] = [
        ...declarationsFromSurfaceContext(context)
    ];
    const cases: CoreMvpRuleDifferentialCase[] = [];
    const surfaceCases = ruleSurfaceCases();

    CORE_MVP_DIFFERENTIAL_SCOPE.ruleCases.forEach(
        (requirement, order) => {
            const manifestRule = CORE_MVP_MANIFEST.rules[order];
            const runtimeRule = CORE_MVP_RUNTIME_PROGRAM.rules[order];
            const surfaceCase = surfaceCases[order];
            if (
                requirement.order !== order ||
                requirement.ruleId !== manifestRule?.id ||
                requirement.ruleId !== runtimeRule?.id ||
                requirement.ruleId !== surfaceCase?.ruleId
            ) {
                throw new CoreMvpDifferentialError(
                    'DIFFERENTIAL_SCOPE_MISMATCH',
                    `TSK-3B rule order ${order} does not match the ` +
                    'reviewed manifest, runtime program, and surface corpus'
                );
            }

            const elaborated = elaborateRuleCase(context, surfaceCase);
            if (
                elaborated.fullFunctor.type.tag !== 'functor' ||
                elaborated.redex.term.tag !== 'application' ||
                elaborated.redex.term.owner !== 'functor-object' ||
                !kernelExpressionEquals(
                    elaborated.redex.term.arguments[2].value,
                    elaborated.fullFunctor.term
                )
            ) {
                throw new CoreMvpDifferentialError(
                    'DIFFERENTIAL_SCOPE_MISMATCH',
                    `TSK-3B rule '${requirement.ruleId}' no longer has the ` +
                    'reviewed evaluator/full-projection shape'
                );
            }

            const fullFunctorType = coreTypeToKernelType(
                elaborated.fullFunctor.type,
                elaborated.fullFunctor.sourceSpan,
                `TSK-3B near-miss functor type for ${requirement.ruleId}`
            );
            const redexType = coreTypeToKernelType(
                elaborated.redex.type,
                elaborated.redex.sourceSpan,
                `TSK-3B redex type for ${requirement.ruleId}`
            );
            const reductType = coreTypeToKernelType(
                elaborated.reduct.type,
                elaborated.reduct.sourceSpan,
                `TSK-3B reduct type for ${requirement.ruleId}`
            );
            if (!kernelExpressionEquals(redexType, reductType)) {
                throw new CoreMvpDifferentialError(
                    'DIFFERENTIAL_SCOPE_MISMATCH',
                    `TSK-3B rule '${requirement.ruleId}' redex and reduct ` +
                    'classifiers disagree'
                );
            }

            const nearMissLine = 40 + order;
            const nearMissFunctorName =
                `differential_rule_near_${order}`;
            const nearMissProvenance = because(
                nearMissLine,
                `TSK-3B rigid near-miss functor for ${requirement.ruleId}`
            );
            environment = environment.extend({
                name: nearMissFunctorName,
                type: fullFunctorType,
                mode: binderMode('explicit', 'functorial'),
                provenance: nearMissProvenance
            });
            const nearMissDeclaration =
                environment.lookup(nearMissFunctorName);
            if (!nearMissDeclaration) {
                throw new CoreMvpDifferentialError(
                    'DIFFERENTIAL_SCOPE_MISMATCH',
                    `TSK-3B failed to declare ${nearMissFunctorName}`
                );
            }
            declarations.push({
                name: nearMissFunctorName,
                type: fullFunctorType,
                span: spanAt(nearMissLine)
            });
            const nearMiss = replaceApplicationArgument(
                elaborated.redex.term,
                2,
                nearMissDeclaration.reference
            );
            const nearMissTyping:
                CoreMvpRuleNearMissTypingEvidence = Object.freeze({
                    method:
                        'same-classifier-substitution-into-surface-elaborated-redex',
                    originalFunctor: elaborated.fullFunctor.term,
                    originalFunctorType: fullFunctorType,
                    replacementFunctor: nearMissDeclaration.reference,
                    replacementFunctorType: nearMissDeclaration.type,
                    resultType: redexType,
                    standaloneCheckerBoundary:
                        'withheld-active-classifier-computation'
                });

            const malformedCandidate = cloneMalformedRule(manifestRule);
            const absenceWitness: CoreMvpRuleAbsenceWitness = Object.freeze({
                interpretation:
                    'oracle-rejects-erased-full-projection-conversion',
                malformedRuleId: requirement.ruleId,
                left: nearMiss,
                right: elaborated.reduct.term
            });
            cases.push(Object.freeze({
                order,
                ruleId: requirement.ruleId,
                redex: elaborated.redex.term,
                reduct: elaborated.reduct.term,
                redexType,
                reductType,
                nearMiss,
                nearMissType: reductType,
                nearMissFunctorName,
                nearMissTyping,
                span: elaborated.redex.sourceSpan,
                malformed: Object.freeze({
                    mutation: 'erase-required-full-projection',
                    candidate: malformedCandidate,
                    expectedError: order === 2
                        ? 'INVALID_COMPILED_VARIABLES'
                        : 'INVALID_PROJECTION_DECREASE',
                    oracleAbsenceWitness: absenceWitness
                })
            }));
        }
    );

    const probe: KernelProbe = Object.freeze({
        requiredModule: LAMBDAPI_V32_MODULE,
        declarations: Object.freeze([...declarations]),
        assertions: Object.freeze([]),
        conversions: Object.freeze(cases.map(testCase => ({
            label: `TSK-3 rule conversion ${testCase.ruleId}`,
            left: testCase.redex,
            right: testCase.reduct,
            span: testCase.span
        }))),
        nonConversions: Object.freeze(cases.map(testCase => ({
            label: `TSK-3 rule near-miss absence ${testCase.ruleId}`,
            left: testCase.malformed.oracleAbsenceWitness.left,
            right: testCase.malformed.oracleAbsenceWitness.right,
            span: testCase.span
        })))
    });

    return Object.freeze({
        manifestRevision: CORE_MVP_MANIFEST.revision,
        manifestContentHash: CORE_MVP_MANIFEST.contentHash,
        ruleIds: Object.freeze(cases.map(testCase => testCase.ruleId)),
        environment,
        declarations: probe.declarations,
        cases: Object.freeze(cases),
        probe
    });
}
