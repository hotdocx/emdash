/**
 * Candidate checker/session integration for combined outer-LF conversion.
 *
 * Subclass hooks leave the released CoreChecker and CoreElaborationSession
 * defaults unchanged. Candidate checking records every conversion result and
 * permits inference of explicitly annotated lambdas, enabling direct beta
 * redexes without adding an ascription node to Core.
 */

import {
    CoreChecker,
    CoreCheckerConversionResult
} from './checker';
import {
    KernelExpression,
    provenance
} from './kernel';
import {
    CoreLfEvaluationError
} from './lf';
import {
    CoreLfDeclarationEnvironment
} from './lf_declarations';
import {
    CoreLfCombinedNextStep,
    CoreLfComparisonResult,
    coreLfDefinitionalCompare
} from './lf_conversion';
import {
    CoreElaborationSession,
    CoreSessionConstraintConversionResult
} from './session';

export const CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT = 256;

const assertStepLimit = (
    environment: CoreLfDeclarationEnvironment,
    stepLimit: number
): void => {
    if (Number.isSafeInteger(stepLimit) && stepLimit >= 0) return;
    const nodeProvenance =
        environment.declarations[0]?.provenance ??
        provenance('derived', 'empty Core LF candidate environment');
    throw new CoreLfEvaluationError(
        'INVALID_STEP_LIMIT',
        nodeProvenance,
        `Core LF candidate comparison step limit must be a nonnegative ` +
        `safe integer; received ${stepLimit}`
    );
};

const formatNextStep = (next: CoreLfCombinedNextStep): string => {
    switch (next.kind) {
        case 'zonk':
            return 'candidate zonk step';
        case 'beta':
            return `candidate beta step (${next.argumentPlicity})`;
        case 'delta':
            return `candidate delta step '${next.declarationName}'`;
        case 'runtime':
            return `candidate runtime rule '${next.ruleId}'`;
        default: {
            const exhaustive: never = next;
            return exhaustive;
        }
    }
};

/**
 * Candidate session that can close revisited rigid constraints by combined
 * conversion after ordinary zonking and Miller-pattern assignment.
 */
export class CoreLfElaborationSession extends CoreElaborationSession {
    private readonly constraintComparisonRecords_:
        CoreLfComparisonResult[] = [];

    constructor(
        public readonly lfEnvironment: CoreLfDeclarationEnvironment,
        public readonly comparisonStepLimit =
            CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT
    ) {
        assertStepLimit(lfEnvironment, comparisonStepLimit);
        super(lfEnvironment.coreEnvironment);
    }

    get constraintComparisonRecords():
        readonly CoreLfComparisonResult[] {
        return Object.freeze([...this.constraintComparisonRecords_]);
    }

    protected compareConstraint(
        left: KernelExpression,
        right: KernelExpression
    ): CoreSessionConstraintConversionResult {
        // CoreElaborationSession has already zonked both sides. Passing no
        // session avoids counting a redundant administrative zonk.
        const result = coreLfDefinitionalCompare(
            this.lfEnvironment,
            left,
            right,
            this.comparisonStepLimit
        );
        this.constraintComparisonRecords_.push(result);
        return { status: result.status };
    }
}

/**
 * Bidirectional candidate checker using the combined LF conversion relation.
 */
export class CoreLfChecker extends CoreChecker {
    private readonly checkerComparisonRecords_:
        CoreLfComparisonResult[] = [];

    constructor(public readonly lfSession: CoreLfElaborationSession) {
        super(lfSession);
    }

    get checkerComparisonRecords():
        readonly CoreLfComparisonResult[] {
        return Object.freeze([...this.checkerComparisonRecords_]);
    }

    protected permitsAnnotatedLambdaInference(): boolean {
        return true;
    }

    protected conversionDiagnosticName(): string {
        return 'Combined Core LF conversion';
    }

    protected compareDefinitions(
        left: KernelExpression,
        right: KernelExpression,
        stepLimit: number
    ): CoreCheckerConversionResult {
        const result = coreLfDefinitionalCompare(
            this.lfSession.lfEnvironment,
            left,
            right,
            stepLimit,
            this.lfSession
        );
        this.checkerComparisonRecords_.push(result);

        if (result.status === 'step-limit-exceeded') {
            return {
                status: 'step-limit-exceeded',
                path: result.path,
                nextStep: formatNextStep(result.next)
            };
        }
        return { status: result.status };
    }
}

export function createCoreLfChecker(
    environment: CoreLfDeclarationEnvironment,
    comparisonStepLimit = CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT
): CoreLfChecker {
    return new CoreLfChecker(
        new CoreLfElaborationSession(
            environment,
            comparisonStepLimit
        )
    );
}
