/**
 * Narrow browser entry for the integrated external-reviewer workbench.
 *
 * This composes the existing categorical text adapter and product
 * report. It owns no parser, action table, checker, evaluator, Core node, or
 * mathematical rule.
 */

import {
    CoreCategoricalCategory,
    CoreCategoricalDisplayedFamily,
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
    'SYNTAX-PARITY-1B3-BROWSER-REVIEWER-1' as const;

export type CoreBrowserReviewerPresetId =
    | 'pointwise-application'
    | 'fixed-inner-evaluation'
    | 'whole-hom-action'
    | 'indexed-section-composition'
    | 'displayed-functor-composition'
    | 'displayed-functor-weakening'
    | 'displayed-sibling-pairing'
    | 'displayed-mixed-telescope'
    | 'displayed-transfor-composition';

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
    }
    | {
        readonly kind: 'dependent-section';
        readonly binderMode: 'n';
        readonly base: 'K';
        readonly target: 'D';
    }
    | {
        readonly kind: 'displayed-functor';
        readonly binderMode: 'fd';
        readonly source: 'E';
        readonly target: 'D' | 'Q';
    }
    | {
        readonly kind: 'displayed-context-functor';
        readonly binderMode: 'fd';
        readonly sources: readonly ['B', 'C'];
        readonly target: 'Productd(D,Q)';
    }
    | {
        readonly kind: 'displayed-dependent-context-functor';
        readonly binderMode: 'fd';
        readonly levels: 'A; B,C; D';
        readonly target: 'Productd(B↑,C↑)';
    }
    | {
        readonly kind: 'displayed-transfor';
        readonly binderMode: 'nd';
        readonly base: 'K';
        readonly source: 'F0';
        readonly target: 'F2';
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
    },
    {
        id: 'indexed-section-composition',
        label: 'Natural indexed composition',
        source: 'λ^n k : K. (FF k) (s k)',
        description:
            'A natural base binder recursively composes a displayed ' +
            'functor action with an indexed section.',
        expectedMode: {
            kind: 'dependent-section',
            binderMode: 'n',
            base: 'K',
            target: 'D'
        },
        assumptions: [
            'K : Cat',
            'E, D : Catd K',
            'FF : Functord E D',
            's : Π k :^n K, E[k]'
        ]
    },
    {
        id: 'displayed-functor-composition',
        label: 'Displayed functor composition',
        source: 'λ^fd a : E. GG (FF a)',
        description:
            'A displayed functorial binder recursively factors a finite ' +
            'composition through the existing internalized owner.',
        expectedMode: {
            kind: 'displayed-functor',
            binderMode: 'fd',
            source: 'E',
            target: 'Q'
        },
        assumptions: [
            'K : Cat',
            'E, D, Q : Catd K',
            'FF : Functord E D',
            'GG : Functord D Q'
        ]
    },
    {
        id: 'displayed-functor-weakening',
        label: 'Displayed weakening',
        source: 'λ^fd a : E. s (indexOf a)',
        description:
            'A displayed variable exposes its hidden base index through the ' +
            'existing contextual operation, making section weakening ' +
            'explicit and checked.',
        expectedMode: {
            kind: 'displayed-functor',
            binderMode: 'fd',
            source: 'E',
            target: 'D'
        },
        assumptions: [
            'K : Cat',
            'E, D : Catd K',
            's : Π k :^n K, D[k]'
        ]
    },
    {
        id: 'displayed-sibling-pairing',
        label: 'Displayed sibling pairing',
        source:
            'λ^fd (b : B, c : C). fibrePair (FF b) (GG c)',
        description:
            'One displayed binder group combines independent fibrewise ' +
            'siblings through the existing contextual compiler and ' +
            'internalized product pairing.',
        expectedMode: {
            kind: 'displayed-context-functor',
            binderMode: 'fd',
            sources: ['B', 'C'],
            target: 'Productd(D,Q)'
        },
        assumptions: [
            'K : Cat',
            'B, C, D, Q : Catd K',
            'FF : Functord B D',
            'GG : Functord C Q'
        ]
    },
    {
        id: 'displayed-mixed-telescope',
        label: 'Displayed mixed telescope',
        source:
            'λ^fd (a : A; b : B, c : C; d : D). fibrePair b c',
        description:
            'Semicolons present two genuine dependency transitions while ' +
            'the comma retains an independent middle sibling group; the ' +
            'existing contextual compiler derives all family-base edges.',
        expectedMode: {
            kind: 'displayed-dependent-context-functor',
            binderMode: 'fd',
            levels: 'A; B,C; D',
            target: 'Productd(B↑,C↑)'
        },
        assumptions: [
            'K : Cat',
            'A : Catd K',
            'B, C : Catd (Sigma_cat A)',
            'D : Catd (Sigma_cat (Productd B C))'
        ]
    },
    {
        id: 'displayed-transfor-composition',
        label: 'Displayed natural composition',
        source:
            'λ^nd k : K. composeCells (theta k) (eta k)',
        description:
            'A displayed natural binder recursively factors typed component ' +
            'composition into a genuine coherent outer transformation.',
        expectedMode: {
            kind: 'displayed-transfor',
            binderMode: 'nd',
            base: 'K',
            source: 'F0',
            target: 'F2'
        },
        assumptions: [
            'K : Cat',
            'E, D : Catd K',
            'F0, F1, F2 : Functord E D',
            'eta : Transfd F0 F1',
            'theta : Transfd F1 F2'
        ]
    }
]);

export const CORE_BROWSER_REVIEWER_BOUNDARY = deepFreeze({
    revision: CORE_BROWSER_REVIEWER_REVISION,
    candidate: 'emdash-v3.2-integrated-reviewer-1',
    construction: 'browser-input-adapter-over-existing-core',
    initialView: 'categorical-text',
    fullReportExecution: 'explicit-user-action',
    pipeline: [
        'ordinary, natural, and displayed categorical text',
        'existing recursive contextual elaboration',
        'backend-neutral explicit emdash Core',
        'existing generic LF checker, evaluator, and runtime',
        'optional Node-side Lambdapi conformance oracle'
    ],
    supported: [
        'nine categorical text presets across ^f, ^n, ^fd, and ^nd',
        'edited categorical text with source diagnostics',
        'existing outer-LF, ordinary, and displayed three-panel report',
        'generated emdash book',
        'preserved minimal explicit-Core playground'
    ],
    deferred: [
        'nested and arbitrary-depth categorical text',
        'remaining displayed context and structural-constructor syntax',
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
    readonly environment: readonly CoreCategoricalTextBinding[];
    readonly expected: CoreCategoricalTextExpected;
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

const familyBinding = (
    name: string,
    value: CoreCategoricalDisplayedFamily
): CoreCategoricalTextBinding => Object.freeze({
    name,
    kind: 'displayed-family' as const,
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
    sourceFile: string,
    presetId: CoreBrowserReviewerPresetId
): CoreBrowserReviewerFixture => {
    if (
        presetId === 'pointwise-application' ||
        presetId === 'fixed-inner-evaluation' ||
        presetId === 'whole-hom-action'
    ) {
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
            ]),
            expected: presetId === 'whole-hom-action'
                ? {
                    kind: 'term' as const,
                    applicationShape: 'whole-hom-action' as const
                }
                : {
                    kind: 'ordinary-functor' as const,
                    source: A,
                    target: C
                }
        });
    }

    if (presetId === 'indexed-section-composition') {
        const program = new CoreCategoricalProgram({
            sourceFile,
            profile: 'usability-dependent-1a'
        });
        const K = program.category('review_K');
        const E = program.displayedFamily('review_E', K);
        const D = program.displayedFamily('review_D', K);
        const FF = program.displayedFunctor('review_FF', E, D);
        const s = program.section('review_s', E);
        return Object.freeze({
            program,
            environment: Object.freeze([
                categoryBinding('K', K),
                familyBinding('E', E),
                familyBinding('D', D),
                termBinding('FF', FF),
                termBinding('s', s)
            ]),
            expected: {
                kind: 'dependent-section' as const,
                base: K,
                target: D
            }
        });
    }

    if (presetId === 'displayed-functor-composition') {
        const program = new CoreCategoricalProgram({
            sourceFile,
            profile: 'fibred-binder-1'
        });
        const K = program.category('review_K');
        const E = program.displayedFamily('review_E', K);
        const D = program.displayedFamily('review_D', K);
        const Q = program.displayedFamily('review_Q', K);
        const FF = program.displayedFunctor('review_FF', E, D);
        const GG = program.displayedFunctor('review_GG', D, Q);
        return Object.freeze({
            program,
            environment: Object.freeze([
                categoryBinding('K', K),
                familyBinding('E', E),
                familyBinding('D', D),
                familyBinding('Q', Q),
                termBinding('FF', FF),
                termBinding('GG', GG)
            ]),
            expected: {
                kind: 'displayed-functor' as const,
                source: E,
                target: Q
            }
        });
    }

    if (presetId === 'displayed-functor-weakening') {
        const program = new CoreCategoricalProgram({
            sourceFile,
            profile: 'fibred-weaken-reindex-1'
        });
        const K = program.category('review_K');
        const E = program.displayedFamily('review_E', K);
        const D = program.displayedFamily('review_D', K);
        const s = program.section('review_s', D);
        return Object.freeze({
            program,
            environment: Object.freeze([
                categoryBinding('K', K),
                familyBinding('E', E),
                familyBinding('D', D),
                termBinding('s', s)
            ]),
            expected: {
                kind: 'displayed-functor' as const,
                source: E,
                target: D
            }
        });
    }

    if (presetId === 'displayed-sibling-pairing') {
        const program = new CoreCategoricalProgram({
            sourceFile,
            profile: 'fibred-displayed-bracket-1'
        });
        const K = program.category('review_K');
        const B = program.displayedFamily('review_B', K);
        const C = program.displayedFamily('review_C', K);
        const D = program.displayedFamily('review_D', K);
        const Q = program.displayedFamily('review_Q', K);
        const FF = program.displayedFunctor('review_FF', B, D);
        const GG = program.displayedFunctor('review_GG', C, Q);
        const target = program.displayedProduct(D, Q);
        return Object.freeze({
            program,
            environment: Object.freeze([
                categoryBinding('K', K),
                familyBinding('B', B),
                familyBinding('C', C),
                familyBinding('D', D),
                familyBinding('Q', Q),
                termBinding('FF', FF),
                termBinding('GG', GG)
            ]),
            expected: {
                kind: 'displayed-context-functor' as const,
                sources: [B, C],
                target
            }
        });
    }

    if (presetId === 'displayed-mixed-telescope') {
        const program = new CoreCategoricalProgram({
            sourceFile,
            profile: 'fibred-displayed-chain-2a'
        });
        const K = program.category('review_K');
        const A = program.displayedFamily('review_A', K);
        const sigmaA = program.totalCategory(A);
        const B = program.displayedFamily('review_B', sigmaA);
        const C = program.displayedFamily('review_C', sigmaA);
        const P = program.displayedProduct(B, C);
        const sigmaP = program.totalCategory(P);
        const D = program.displayedFamily('review_D', sigmaP);
        const projectionP = program.sigmaProjection(P);
        const liftedB = program.pullbackFamily(B, projectionP);
        const liftedC = program.pullbackFamily(C, projectionP);
        const target = program.displayedProduct(liftedB, liftedC);
        return Object.freeze({
            program,
            environment: Object.freeze([
                categoryBinding('K', K),
                familyBinding('A', A),
                familyBinding('B', B),
                familyBinding('C', C),
                familyBinding('D', D)
            ]),
            expected: {
                kind:
                    'displayed-dependent-context-functor' as const,
                sourceGroups: [[A], [B, C], [D]],
                target
            }
        });
    }

    if (presetId !== 'displayed-transfor-composition') {
        const exhaustive: never = presetId;
        return exhaustive;
    }
    const program = new CoreCategoricalProgram({
        sourceFile,
        profile: 'fibred-transfd-1'
    });
    const K = program.category('review_K');
    const E = program.displayedFamily('review_E', K);
    const D = program.displayedFamily('review_D', K);
    const F0 = program.displayedFunctor('review_F0', E, D);
    const F1 = program.displayedFunctor('review_F1', E, D);
    const F2 = program.displayedFunctor('review_F2', E, D);
    const eta = program.displayedTransfor('review_eta', F0, F1);
    const theta = program.displayedTransfor(
        'review_theta',
        F1,
        F2
    );
    return Object.freeze({
        program,
        environment: Object.freeze([
            categoryBinding('K', K),
            familyBinding('E', E),
            familyBinding('D', D),
            termBinding('F0', F0),
            termBinding('F1', F1),
            termBinding('F2', F2),
            termBinding('eta', eta),
            termBinding('theta', theta)
        ]),
        expected: {
            kind: 'displayed-transfor' as const,
            base: K,
            source: F0,
            target: F2
        }
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

/**
 * Run one editable categorical expression through the existing text
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
    const fixture = createFixture(sourceFile, preset.id);

    try {
        const term = elaborateCoreCategoricalText(
            fixture.program,
            {
                source: request.source,
                sourceFile,
                environment: fixture.environment,
                expected: fixture.expected
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
