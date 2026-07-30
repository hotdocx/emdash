/**
 * Narrow browser entry for the integrated external-reviewer workbench.
 *
 * This composes the existing ordinary categorical text adapter and product
 * report. It owns no parser, action table, checker, evaluator, Core node, or
 * mathematical rule.
 */

import {
    CoreCategoricalCategory,
    CoreCategoricalProgram
} from './categorical_program';
import {
    CoreCategoricalHomBoundary,
    CoreCategoricalTerm
} from './categorical_surface';
import {
    CoreCategoricalTextBinding,
    CoreCategoricalTextError,
    CoreCategoricalTextExpected,
    elaborateCoreCategoricalText
} from './categorical_text';
import {
    CoreProductReviewDemoResult,
    formatCoreProductReviewDemo,
    runCoreProductReviewDemo
} from './product_review_demo';

export const CORE_BROWSER_REVIEWER_REVISION =
    'REVIEWER-INTEGRATE-1A-BROWSER-1' as const;

export type CoreBrowserReviewerPresetId =
    | 'pointwise-application'
    | 'fixed-inner-evaluation'
    | 'whole-hom-action';

export type CoreBrowserReviewerExpectedMode =
    | {
        readonly kind: 'ordinary-functor';
        readonly binderMode: 'f';
        readonly source: 'A';
        readonly target: 'C';
    }
    | {
        readonly kind: 'term';
        readonly applicationShape: 'whole-hom-action';
    };

export interface CoreBrowserReviewerPreset {
    readonly id: CoreBrowserReviewerPresetId;
    readonly label: string;
    readonly source: string;
    readonly description: string;
    readonly expectedMode: CoreBrowserReviewerExpectedMode;
    readonly assumptions: readonly string[];
}

export interface CoreBrowserReviewerTextRequest {
    readonly presetId: CoreBrowserReviewerPresetId;
    readonly source: string;
    readonly sourceFile?: string;
}

export interface CoreBrowserReviewerTextInput {
    readonly presetId: CoreBrowserReviewerPresetId;
    readonly source: string;
    readonly sourceFile: string;
}

export interface CoreBrowserReviewerTextDiagnostic {
    readonly phase: CoreCategoricalTextError['phase'];
    readonly code: CoreCategoricalTextError['code'];
    readonly message: string;
    readonly detail: string;
    readonly span: CoreCategoricalTextError['span'];
}

interface CoreBrowserReviewerTextResultBase {
    readonly revision: typeof CORE_BROWSER_REVIEWER_REVISION;
    readonly input: CoreBrowserReviewerTextInput;
    readonly expectedMode: CoreBrowserReviewerExpectedMode;
    readonly productionLambdapiDependency: false;
}

export interface CoreBrowserReviewerTextAccepted
    extends CoreBrowserReviewerTextResultBase {
    readonly status: 'accepted';
    readonly explicitCore: string;
    readonly inferredType: string;
    readonly expectedType: string;
    readonly structuralPrerequisites: readonly string[];
    readonly diagnostic: undefined;
}

export interface CoreBrowserReviewerTextRejected
    extends CoreBrowserReviewerTextResultBase {
    readonly status: 'rejected';
    readonly diagnostic: CoreBrowserReviewerTextDiagnostic;
}

export type CoreBrowserReviewerTextResult =
    | CoreBrowserReviewerTextAccepted
    | CoreBrowserReviewerTextRejected;

export type CoreBrowserReviewerErrorCode =
    'UNKNOWN_REVIEWER_PRESET';

export class CoreBrowserReviewerError extends Error {
    constructor(
        public readonly code: CoreBrowserReviewerErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreBrowserReviewerError';
    }
}

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Object.values(value as Record<string, unknown>).forEach(deepFreeze);
        Object.freeze(value);
    }
    return value;
};

export const CORE_BROWSER_REVIEWER_PRESETS:
readonly CoreBrowserReviewerPreset[] = deepFreeze([
    {
        id: 'pointwise-application',
        label: 'Pointwise application',
        source: 'λ^f x. (H x) (K x)',
        description:
            'A recursively elaborated functorial binder used in both ' +
            'function and argument positions.',
        expectedMode: {
            kind: 'ordinary-functor',
            binderMode: 'f',
            source: 'A',
            target: 'C'
        },
        assumptions: [
            'A, B, C : Cat',
            'H : Functor A (Functor_cat B C)',
            'K : Functor A B'
        ]
    },
    {
        id: 'fixed-inner-evaluation',
        label: 'Fixed inner evaluation',
        source: 'λ^f x. F x y0',
        description:
            'Abstraction after evaluation at a constant inner object.',
        expectedMode: {
            kind: 'ordinary-functor',
            binderMode: 'f',
            source: 'A',
            target: 'C'
        },
        assumptions: [
            'A, B, C : Cat',
            'F : Functor A (Functor_cat B C)',
            'y0 : Obj B'
        ]
    },
    {
        id: 'whole-hom-action',
        label: 'Whole Hom action',
        source: 'G pA',
        description:
            'Expected typing selects a full Hom-category action from the ' +
            'same neutral application syntax.',
        expectedMode: {
            kind: 'term',
            applicationShape: 'whole-hom-action'
        },
        assumptions: [
            'A, B : Cat',
            'G : Functor A B',
            'pA : Hom_cat A x0 x1'
        ]
    }
]);

export const CORE_BROWSER_REVIEWER_BOUNDARY = deepFreeze({
    revision: CORE_BROWSER_REVIEWER_REVISION,
    candidate: 'emdash-v3.2-integrated-reviewer-1',
    construction: 'browser-input-adapter-over-existing-core',
    initialView: 'ordinary-categorical-text',
    fullReportExecution: 'explicit-user-action',
    pipeline: [
        'ordinary categorical text',
        'existing recursive contextual elaboration',
        'backend-neutral explicit emdash Core',
        'existing generic LF checker, evaluator, and runtime',
        'optional Node-side Lambdapi conformance oracle'
    ],
    supported: [
        'three ordinary categorical text presets',
        'edited ordinary categorical text with source diagnostics',
        'existing outer-LF, ordinary, and displayed three-panel report',
        'generated emdash book',
        'preserved minimal explicit-Core playground'
    ],
    deferred: [
        'displayed categorical text syntax',
        'additional binder modes',
        'arbitrary displayed telescope depth',
        'browser-side source acquisition',
        'production Lambdapi dependency',
        'systematic groupoidal closure',
        'whole-library transfer graduation'
    ],
    semanticEffects: {
        newMathematicalOwnerCount: 0,
        newRuntimeRuleCount: 0,
        newProofRuleCount: 0,
        newCheckerOrEvaluatorBranchCount: 0,
        newParserOrResolverCount: 0
    }
} as const);

interface CoreBrowserReviewerFixture {
    readonly program: CoreCategoricalProgram;
    readonly A: CoreCategoricalCategory;
    readonly C: CoreCategoricalCategory;
    readonly environment: readonly CoreCategoricalTextBinding[];
}

const categoryBinding = (
    name: string,
    value: CoreCategoricalCategory
): CoreCategoricalTextBinding => Object.freeze({
    name,
    kind: 'category' as const,
    value
});

const termBinding = (
    name: string,
    value: CoreCategoricalTerm
): CoreCategoricalTextBinding => Object.freeze({
    name,
    kind: 'term' as const,
    value
});

const boundaryBinding = (
    name: string,
    value: CoreCategoricalHomBoundary
): CoreCategoricalTextBinding => Object.freeze({
    name,
    kind: 'hom-boundary' as const,
    value
});

const createFixture = (
    sourceFile: string
): CoreBrowserReviewerFixture => {
    const program = new CoreCategoricalProgram({ sourceFile });
    const A = program.category('review_A');
    const B = program.category('review_B');
    const C = program.category('review_C');
    const functorsBC = program.functorCategory(B, C);
    const H = program.functor('review_H', A, functorsBC);
    const K = program.functor('review_K', A, B);
    const F = program.functor('review_F', A, functorsBC);
    const G = program.functor('review_G', A, B);
    const y0 = program.object('review_y0', B);
    const x0 = program.object('review_x0', A);
    const x1 = program.object('review_x1', A);
    const pA = program.homBoundary(A, x0, x1);

    return Object.freeze({
        program,
        A,
        C,
        environment: Object.freeze([
            categoryBinding('A', A),
            categoryBinding('B', B),
            categoryBinding('C', C),
            termBinding('H', H),
            termBinding('K', K),
            termBinding('F', F),
            termBinding('G', G),
            termBinding('y0', y0),
            boundaryBinding('pA', pA)
        ])
    });
};

const findPreset = (
    presetId: CoreBrowserReviewerPresetId
): CoreBrowserReviewerPreset => {
    const preset = CORE_BROWSER_REVIEWER_PRESETS.find(
        candidate => candidate.id === presetId
    );
    if (preset === undefined) {
        throw new CoreBrowserReviewerError(
            'UNKNOWN_REVIEWER_PRESET',
            `Unknown browser reviewer preset '${String(presetId)}'`
        );
    }
    return preset;
};

const textExpected = (
    fixture: CoreBrowserReviewerFixture,
    mode: CoreBrowserReviewerExpectedMode
): CoreCategoricalTextExpected =>
    mode.kind === 'ordinary-functor'
        ? {
            kind: mode.kind,
            source: fixture.A,
            target: fixture.C
        }
        : {
            kind: mode.kind,
            applicationShape: mode.applicationShape
        };

/**
 * Run one editable ordinary categorical expression through the existing text
 * adapter and categorical program. Expected typing is fixed by the selected
 * reviewed preset; the source itself remains editable.
 */
export function runCoreBrowserReviewerText(
    request: CoreBrowserReviewerTextRequest
): CoreBrowserReviewerTextResult {
    const preset = findPreset(request.presetId);
    const sourceFile =
        request.sourceFile ?? '<browser-reviewer>';
    const input = Object.freeze({
        presetId: preset.id,
        source: request.source,
        sourceFile
    });
    const fixture = createFixture(sourceFile);

    try {
        const term = elaborateCoreCategoricalText(
            fixture.program,
            {
                source: request.source,
                sourceFile,
                environment: fixture.environment,
                expected: textExpected(
                    fixture,
                    preset.expectedMode
                )
            }
        );
        const compilation = fixture.program.compile(term);
        return deepFreeze({
            revision: CORE_BROWSER_REVIEWER_REVISION,
            status: 'accepted' as const,
            input,
            expectedMode: preset.expectedMode,
            explicitCore: compilation.explicitCore,
            inferredType: compilation.explicitInferredType,
            expectedType: compilation.explicitExpectedType,
            structuralPrerequisites: [
                ...compilation.structuralPrerequisites
            ],
            diagnostic: undefined,
            productionLambdapiDependency: false as const
        });
    } catch (error: unknown) {
        if (!(error instanceof CoreCategoricalTextError)) throw error;
        return deepFreeze({
            revision: CORE_BROWSER_REVIEWER_REVISION,
            status: 'rejected' as const,
            input,
            expectedMode: preset.expectedMode,
            diagnostic: {
                phase: error.phase,
                code: error.code,
                message: error.message,
                detail: error.detail,
                span: error.span
            },
            productionLambdapiDependency: false as const
        });
    }
}

/**
 * Execute the unchanged, comparatively heavy three-panel research report.
 * Browser callers should invoke this only after an explicit user action.
 */
export function runCoreBrowserReviewerFullReport():
CoreProductReviewDemoResult {
    return runCoreProductReviewDemo();
}

export function formatCoreBrowserReviewerFullReport(
    result?: CoreProductReviewDemoResult
): string {
    return result === undefined
        ? formatCoreProductReviewDemo()
        : formatCoreProductReviewDemo(result);
}
