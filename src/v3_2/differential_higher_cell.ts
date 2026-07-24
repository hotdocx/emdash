/**
 * Shared TSK-3C higher-cell corpus and frozen parity-completion record.
 *
 * Higher cells reuse ordinary full/capped projection owners recursively.
 * This module adds no dimension-specific Core node and invokes Lambdapi only
 * through the generated probe consumed by opt-in conformance tests.
 */

import {
    CORE_MVP_DIFFERENTIAL_SCOPE,
    CoreMvpDifferentialError,
    CoreMvpHigherCellDifferentialRequirement,
    validateCoreMvpDifferentialScope
} from './differential';
import {
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
    KernelProbe,
    KernelProbeDeclaration,
    declarationsFromSurfaceContext
} from './probe';
import {
    CoreOwnerId
} from './schema';
import {
    SurfaceContext,
    SurfaceTerm,
    categoryType,
    coreTypeToKernelType,
    functorType,
    homCategory,
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

export type CoreMvpHigherCellPackageId =
    | 'recursive-functor-hom-2-cell'
    | 'transfor-component-and-hom-levels';

export interface CoreMvpHigherCellPositiveCase {
    readonly id: string;
    readonly packageId: CoreMvpHigherCellPackageId;
    readonly surfaceTerm: SurfaceTerm;
    readonly term: KernelExpression;
    readonly type: KernelExpression;
    readonly span: SourceSpan;
}

export interface CoreMvpHigherCellWrongEndpointCase {
    readonly id: string;
    readonly packageId: CoreMvpHigherCellPackageId;
    readonly surfaceTerm: SurfaceTerm;
    readonly expectedError: 'CATEGORY_MISMATCH';
    readonly expectedErrorSpan: SourceSpan;
    readonly validPositiveId: string;
    readonly validTerm: KernelExpression;
    readonly corruptedTerm: KernelExpression;
    readonly expectedType: KernelExpression;
    readonly corruptedOwner: CoreOwnerId;
    readonly corruptedSlot: number;
    readonly suppliedBindingName: string;
    readonly span: SourceSpan;
}

export interface CoreMvpHigherCellConversionCase {
    readonly id: string;
    readonly packageId: CoreMvpHigherCellPackageId;
    readonly ruleId: string;
    readonly leftPositiveId: string;
    readonly rightPositiveId: string;
    readonly left: KernelExpression;
    readonly right: KernelExpression;
    readonly leftType: KernelExpression;
    readonly rightType: KernelExpression;
    readonly span: SourceSpan;
}

export interface CoreMvpHigherCellPackage {
    readonly order: number;
    readonly id: CoreMvpHigherCellPackageId;
    readonly ownerIds: readonly CoreOwnerId[];
    readonly ruleIds: readonly string[];
    readonly required: readonly string[];
    readonly positives: readonly CoreMvpHigherCellPositiveCase[];
    readonly wrongEndpoints:
        readonly CoreMvpHigherCellWrongEndpointCase[];
    readonly conversions: readonly CoreMvpHigherCellConversionCase[];
}

export interface CoreMvpHigherCellDifferentialCorpus {
    readonly manifestRevision: string;
    readonly manifestContentHash: string;
    readonly context: SurfaceContext;
    readonly declarations: readonly KernelProbeDeclaration[];
    readonly packages: readonly CoreMvpHigherCellPackage[];
    readonly probe: KernelProbe;
}

export interface CoreMvpCompletedDifferentialCase {
    readonly order: number;
    readonly id: string;
    readonly completed: readonly string[];
    readonly evidence: string;
}

export interface CoreMvpDifferentialCompletionInput {
    readonly status: string;
    readonly manifestRevision: string;
    readonly manifestContentHash: string;
    readonly oraclePolicy: string;
    readonly ownerCases: readonly CoreMvpCompletedDifferentialCase[];
    readonly ruleCases: readonly CoreMvpCompletedDifferentialCase[];
    readonly higherCellCases:
        readonly CoreMvpCompletedDifferentialCase[];
    readonly unclosedRows: readonly string[];
}

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

const expectedCompletion: CoreMvpDifferentialCompletionInput = {
    status: 'frozen-fragment-parity-complete',
    manifestRevision: CORE_MVP_DIFFERENTIAL_SCOPE.manifestRevision,
    manifestContentHash: CORE_MVP_DIFFERENTIAL_SCOPE.manifestContentHash,
    oraclePolicy: CORE_MVP_DIFFERENTIAL_SCOPE.status,
    ownerCases: CORE_MVP_DIFFERENTIAL_SCOPE.ownerCases.map(entry => ({
        order: entry.order,
        id: entry.owner,
        completed: [...entry.required],
        evidence: 'TSK-3A-shared-owner-corpus'
    })),
    ruleCases: CORE_MVP_DIFFERENTIAL_SCOPE.ruleCases.map(entry => ({
        order: entry.order,
        id: entry.ruleId,
        completed: [...entry.required],
        evidence: 'TSK-3B-shared-rule-boundary'
    })),
    higherCellCases:
        CORE_MVP_DIFFERENTIAL_SCOPE.higherCellCases.map((entry, order) => ({
            order,
            id: entry.id,
            completed: [...entry.required],
            evidence: `TSK-3C-${entry.id}`
        })),
    unclosedRows: []
};

const sameCompletion = (
    left: CoreMvpDifferentialCompletionInput,
    right: CoreMvpDifferentialCompletionInput
): boolean => JSON.stringify(left) === JSON.stringify(right);

export function validateCoreMvpDifferentialCompletion(
    input: CoreMvpDifferentialCompletionInput
): void {
    validateCoreMvpDifferentialScope(CORE_MVP_DIFFERENTIAL_SCOPE);
    if (!sameCompletion(input, expectedCompletion)) {
        throw new CoreMvpDifferentialError(
            'DIFFERENTIAL_SCOPE_MISMATCH',
            'TSK-3 differential completion drifted from the frozen exit matrix'
        );
    }
}

/**
 * Completion here means every TSK-3 row has shared TypeScript/Lambdapi
 * evidence. Lambdapi remains required until the separately recorded
 * graduation gate; migration and product graduation are not implied.
 */
export const CORE_MVP_DIFFERENTIAL_COMPLETION = deepFreeze(
    expectedCompletion
);

validateCoreMvpDifferentialCompletion(
    CORE_MVP_DIFFERENTIAL_COMPLETION
);

const corpusSource =
    'generated/v3_2_mvp_higher_cell_differential.core.ts';

const spanAt = (line: number): SourceSpan =>
    sourceSpan(corpusSource, line, 1, line, 80);

const ref = (name: string, line: number): SurfaceTerm =>
    surfaceReference(name, spanAt(line));

const higherCellContext = (): SurfaceContext => new SurfaceContext([
    surfaceBinding('differential_higher_A', categoryType(), spanAt(1)),
    surfaceBinding('differential_higher_B', categoryType(), spanAt(2)),
    surfaceBinding('differential_higher_C', categoryType(), spanAt(3)),
    surfaceBinding(
        'differential_higher_x',
        objectType('differential_higher_A'),
        spanAt(4)
    ),
    surfaceBinding(
        'differential_higher_y',
        objectType('differential_higher_A'),
        spanAt(5)
    ),
    surfaceBinding(
        'differential_higher_u',
        objectType('differential_higher_C'),
        spanAt(6)
    ),
    surfaceBinding(
        'differential_higher_v',
        objectType('differential_higher_C'),
        spanAt(7)
    ),
    surfaceBinding(
        'differential_higher_F',
        functorType('differential_higher_A', 'differential_higher_B'),
        spanAt(8)
    ),
    surfaceBinding(
        'differential_higher_G',
        functorType('differential_higher_A', 'differential_higher_B'),
        spanAt(9)
    ),
    surfaceBinding(
        'differential_higher_f',
        homType(
            'differential_higher_A',
            'differential_higher_x',
            'differential_higher_y'
        ),
        spanAt(10)
    ),
    surfaceBinding(
        'differential_higher_g',
        homType(
            'differential_higher_A',
            'differential_higher_x',
            'differential_higher_y'
        ),
        spanAt(11)
    ),
    surfaceBinding(
        'differential_higher_h',
        homType(
            'differential_higher_C',
            'differential_higher_u',
            'differential_higher_v'
        ),
        spanAt(12)
    ),
    surfaceBinding(
        'differential_higher_eta',
        transforType(
            'differential_higher_A',
            'differential_higher_B',
            'differential_higher_F',
            'differential_higher_G'
        ),
        spanAt(13),
        binderMode('implicit', 'natural')
    ),
    surfaceBinding(
        'differential_higher_alpha',
        homType(
            homCategory(
                'differential_higher_A',
                'differential_higher_x',
                'differential_higher_y'
            ),
            'differential_higher_f',
            'differential_higher_g'
        ),
        spanAt(14)
    )
]);

const replaceApplicationArgument = (
    expression: KernelExpression,
    index: number,
    value: KernelExpression
): KernelApplication => {
    if (expression.tag !== 'application') {
        throw new CoreMvpDifferentialError(
            'DIFFERENTIAL_SCOPE_MISMATCH',
            'TSK-3C endpoint corruption expected an owner application'
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

const requirement = (
    id: CoreMvpHigherCellPackageId
): CoreMvpHigherCellDifferentialRequirement => {
    const row = CORE_MVP_DIFFERENTIAL_SCOPE.higherCellCases.find(
        entry => entry.id === id
    );
    if (!row) {
        throw new CoreMvpDifferentialError(
            'DIFFERENTIAL_SCOPE_MISMATCH',
            `TSK-3C package '${id}' is absent from the frozen exit matrix`
        );
    }
    return row;
};

const compilePositive = (
    context: SurfaceContext,
    packageId: CoreMvpHigherCellPackageId,
    id: string,
    surfaceTerm: SurfaceTerm
): CoreMvpHigherCellPositiveCase => {
    const elaborated = elaborateSurfaceTerm(context, surfaceTerm);
    return Object.freeze({
        id,
        packageId,
        surfaceTerm,
        term: elaborated.term,
        type: coreTypeToKernelType(
            elaborated.type,
            elaborated.sourceSpan,
            `TSK-3C positive type for ${id}`
        ),
        span: elaborated.sourceSpan
    });
};

const positiveById = (
    positives: readonly CoreMvpHigherCellPositiveCase[],
    id: string
): CoreMvpHigherCellPositiveCase => {
    const result = positives.find(testCase => testCase.id === id);
    if (!result) {
        throw new CoreMvpDifferentialError(
            'DIFFERENTIAL_SCOPE_MISMATCH',
            `TSK-3C positive case '${id}' is missing`
        );
    }
    return result;
};

const compileConversion = (
    packageId: CoreMvpHigherCellPackageId,
    id: string,
    ruleId: string,
    left: CoreMvpHigherCellPositiveCase,
    right: CoreMvpHigherCellPositiveCase
): CoreMvpHigherCellConversionCase => {
    if (!kernelExpressionEquals(left.type, right.type)) {
        throw new CoreMvpDifferentialError(
            'DIFFERENTIAL_SCOPE_MISMATCH',
            `TSK-3C conversion '${id}' has unequal surface classifiers`
        );
    }
    return Object.freeze({
        id,
        packageId,
        ruleId,
        leftPositiveId: left.id,
        rightPositiveId: right.id,
        left: left.term,
        right: right.term,
        leftType: left.type,
        rightType: right.type,
        span: left.span
    });
};

const compileWrongEndpoint = (
    context: SurfaceContext,
    packageId: CoreMvpHigherCellPackageId,
    id: string,
    surfaceTerm: SurfaceTerm,
    expectedErrorSpan: SourceSpan,
    valid: CoreMvpHigherCellPositiveCase,
    corruptedSlot: number,
    suppliedBindingName: string
): CoreMvpHigherCellWrongEndpointCase => {
    const supplied = context.lookup(suppliedBindingName);
    if (!supplied || valid.term.tag !== 'application') {
        throw new CoreMvpDifferentialError(
            'DIFFERENTIAL_SCOPE_MISMATCH',
            `TSK-3C wrong-endpoint case '${id}' lacks its valid Core shape`
        );
    }
    return Object.freeze({
        id,
        packageId,
        surfaceTerm,
        expectedError: 'CATEGORY_MISMATCH',
        expectedErrorSpan,
        validPositiveId: valid.id,
        validTerm: valid.term,
        corruptedTerm: replaceApplicationArgument(
            valid.term,
            corruptedSlot,
            supplied.reference
        ),
        expectedType: valid.type,
        corruptedOwner: valid.term.owner,
        corruptedSlot,
        suppliedBindingName,
        span: surfaceTerm.span
    });
};

const freezePackage = (
    order: number,
    row: CoreMvpHigherCellDifferentialRequirement,
    positives: readonly CoreMvpHigherCellPositiveCase[],
    wrongEndpoints: readonly CoreMvpHigherCellWrongEndpointCase[],
    conversions: readonly CoreMvpHigherCellConversionCase[]
): CoreMvpHigherCellPackage => Object.freeze({
    order,
    id: row.id as CoreMvpHigherCellPackageId,
    ownerIds: Object.freeze([...row.ownerIds]),
    ruleIds: Object.freeze([...row.ruleIds]),
    required: Object.freeze([...row.required]),
    positives: Object.freeze([...positives]),
    wrongEndpoints: Object.freeze([...wrongEndpoints]),
    conversions: Object.freeze([...conversions])
});

/**
 * Build the two exact higher-cell packages from direct TypeScript surface AST.
 */
export function buildCoreMvpHigherCellDifferentialCorpus(
): CoreMvpHigherCellDifferentialCorpus {
    validateCoreMvpDifferentialScope(CORE_MVP_DIFFERENTIAL_SCOPE);
    validateCoreMvpDifferentialCompletion(
        CORE_MVP_DIFFERENTIAL_COMPLETION
    );

    const context = higherCellContext();
    const recursiveId: CoreMvpHigherCellPackageId =
        'recursive-functor-hom-2-cell';
    const transforId: CoreMvpHigherCellPackageId =
        'transfor-component-and-hom-levels';

    const innerFull = surfaceFapp1Func(
        ref('differential_higher_F', 20),
        ref('differential_higher_x', 20),
        ref('differential_higher_y', 20),
        spanAt(20)
    );
    const recursiveFull = surfaceFapp1Func(
        innerFull,
        ref('differential_higher_f', 21),
        ref('differential_higher_g', 21),
        spanAt(21)
    );
    const recursiveRedex = surfaceFapp0(
        recursiveFull,
        ref('differential_higher_alpha', 22),
        spanAt(22)
    );
    const recursiveCapped = surfaceFapp1(
        innerFull,
        ref('differential_higher_alpha', 23),
        spanAt(23)
    );

    const componentFull = surfaceTapp0Func(
        ref('differential_higher_F', 30),
        ref('differential_higher_G', 30),
        ref('differential_higher_x', 30),
        spanAt(30)
    );
    const componentRedex = surfaceFapp0(
        componentFull,
        ref('differential_higher_eta', 31),
        spanAt(31)
    );
    const componentCapped = surfaceTapp0(
        ref('differential_higher_eta', 32),
        ref('differential_higher_x', 32),
        spanAt(32)
    );
    const homFull = surfaceTapp1Func(
        ref('differential_higher_eta', 33),
        ref('differential_higher_x', 33),
        ref('differential_higher_y', 33),
        spanAt(33)
    );
    const homRedex = surfaceFapp0(
        homFull,
        ref('differential_higher_f', 34),
        spanAt(34)
    );
    const homCapped = surfaceTapp1(
        ref('differential_higher_eta', 35),
        ref('differential_higher_f', 35),
        spanAt(35)
    );

    const recursivePositives = [
        compilePositive(
            context,
            recursiveId,
            'recursive-full-functor',
            recursiveFull
        ),
        compilePositive(
            context,
            recursiveId,
            'recursive-evaluator-redex',
            recursiveRedex
        ),
        compilePositive(
            context,
            recursiveId,
            'recursive-capped-action',
            recursiveCapped
        )
    ];
    const transforPositives = [
        compilePositive(
            context,
            transforId,
            'transfor-component-full',
            componentFull
        ),
        compilePositive(
            context,
            transforId,
            'transfor-component-redex',
            componentRedex
        ),
        compilePositive(
            context,
            transforId,
            'transfor-component-capped',
            componentCapped
        ),
        compilePositive(
            context,
            transforId,
            'transfor-hom-full',
            homFull
        ),
        compilePositive(
            context,
            transforId,
            'transfor-hom-redex',
            homRedex
        ),
        compilePositive(
            context,
            transforId,
            'transfor-hom-capped',
            homCapped
        )
    ];

    const recursiveWrongSurface = surfaceFapp1Func(
        innerFull,
        ref('differential_higher_f', 70),
        ref('differential_higher_h', 71),
        spanAt(70)
    );
    const componentWrongSurface = surfaceTapp0Func(
        ref('differential_higher_F', 72),
        ref('differential_higher_G', 72),
        ref('differential_higher_u', 73),
        spanAt(72)
    );
    const homWrongSurface = surfaceTapp1Func(
        ref('differential_higher_eta', 74),
        ref('differential_higher_x', 74),
        ref('differential_higher_u', 75),
        spanAt(74)
    );

    const recursiveWrong = compileWrongEndpoint(
        context,
        recursiveId,
        'recursive-wrong-inner-target',
        recursiveWrongSurface,
        spanAt(71),
        positiveById(recursivePositives, 'recursive-full-functor'),
        4,
        'differential_higher_h'
    );
    const componentWrong = compileWrongEndpoint(
        context,
        transforId,
        'transfor-component-wrong-object',
        componentWrongSurface,
        spanAt(73),
        positiveById(transforPositives, 'transfor-component-full'),
        4,
        'differential_higher_u'
    );
    const homWrong = compileWrongEndpoint(
        context,
        transforId,
        'transfor-hom-wrong-target',
        homWrongSurface,
        spanAt(75),
        positiveById(transforPositives, 'transfor-hom-full'),
        5,
        'differential_higher_u'
    );

    const recursiveConversion = compileConversion(
        recursiveId,
        'recursive-functor-hom-evaluation',
        'projection.functor-hom.evaluate',
        positiveById(recursivePositives, 'recursive-evaluator-redex'),
        positiveById(recursivePositives, 'recursive-capped-action')
    );
    const componentConversion = compileConversion(
        transforId,
        'transfor-component-evaluation',
        'projection.transfor-component.evaluate',
        positiveById(transforPositives, 'transfor-component-redex'),
        positiveById(transforPositives, 'transfor-component-capped')
    );
    const homConversion = compileConversion(
        transforId,
        'transfor-hom-evaluation',
        'projection.transfor-hom.evaluate',
        positiveById(transforPositives, 'transfor-hom-redex'),
        positiveById(transforPositives, 'transfor-hom-capped')
    );

    const packages: readonly CoreMvpHigherCellPackage[] = Object.freeze([
        freezePackage(
            0,
            requirement(recursiveId),
            recursivePositives,
            [recursiveWrong],
            [recursiveConversion]
        ),
        freezePackage(
            1,
            requirement(transforId),
            transforPositives,
            [componentWrong, homWrong],
            [componentConversion, homConversion]
        )
    ]);

    const positives = packages.flatMap(package_ => package_.positives);
    const wrongEndpoints = packages.flatMap(
        package_ => package_.wrongEndpoints
    );
    const conversions = packages.flatMap(
        package_ => package_.conversions
    );
    const declarations = Object.freeze([
        ...declarationsFromSurfaceContext(context)
    ]);
    const probe: KernelProbe = Object.freeze({
        requiredModule: LAMBDAPI_V32_MODULE,
        declarations,
        assertions: Object.freeze(positives.map(testCase => ({
            label:
                `TSK-3 higher positive ${testCase.packageId} ` +
                testCase.id,
            term: testCase.term,
            type: testCase.type,
            span: testCase.span
        }))),
        negativeAssertions: Object.freeze(
            wrongEndpoints.map(testCase => ({
                label:
                    `TSK-3 higher wrong endpoint ${testCase.packageId} ` +
                    testCase.id,
                term: testCase.corruptedTerm,
                type: testCase.expectedType,
                span: testCase.span
            }))
        ),
        conversions: Object.freeze(conversions.map(testCase => ({
            label:
                `TSK-3 higher conversion ${testCase.packageId} ` +
                testCase.ruleId,
            left: testCase.left,
            right: testCase.right,
            span: testCase.span
        })))
    });

    return Object.freeze({
        manifestRevision: CORE_MVP_DIFFERENTIAL_SCOPE.manifestRevision,
        manifestContentHash:
            CORE_MVP_DIFFERENTIAL_SCOPE.manifestContentHash,
        context,
        declarations,
        packages,
        probe
    });
}
