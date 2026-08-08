/**
 * Deterministic selection of an explicit checked global LF dictionary.
 *
 * The caller supplies the complete finite candidate scope. This module does
 * not discover declarations, execute proof rules, recurse through premises,
 * retain callbacks, or perform I/O. A successful result is an ordinary Core
 * reference checked by a fresh TypeScript LF checker.
 */

import {
    CoreCheckerError
} from './checker';
import {
    serializeCoreExpression
} from './core_serialization';
import {
    CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT,
    createCoreLfChecker
} from './lf_checker';
import {
    CoreLfMixedDeclarationBaseContext
} from './lf_transfer_mixed';
import {
    CoreLfQualifiedSymbol
} from './lf_transfer';
import {
    KernelExpression,
    KernelReference,
    kernelFree,
    kernelUniverse,
    provenance
} from './kernel';

export const CORE_LF_DICTIONARY_SYNTHESIS_PROFILE = Object.freeze({
    revision: 'emdash-lf-dictionary-synthesis-v1' as const,
    comparisonStepLimit: CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT
});

export type CoreLfDictionarySynthesisErrorCode =
    | 'INVALID_TARGET'
    | 'INVALID_CANDIDATE_SCOPE'
    | 'DUPLICATE_CANDIDATE'
    | 'UNAVAILABLE_CANDIDATE'
    | 'UNSUPPORTED_CANDIDATE'
    | 'CANDIDATE_CHECK_FAILED'
    | 'NO_MATCHING_DICTIONARY'
    | 'AMBIGUOUS_DICTIONARY';

export interface CoreLfDictionaryCandidateRejection {
    readonly checkerCode: CoreCheckerError['code'];
    readonly diagnostic: string;
}

export interface CoreLfDictionaryCandidateTrace {
    readonly candidate: CoreLfQualifiedSymbol;
    readonly term: string;
    readonly declaredType: string;
    readonly outcome: 'matched' | 'rejected';
    readonly rejection?: CoreLfDictionaryCandidateRejection;
}

export interface CoreLfDictionarySynthesisReport {
    readonly revision:
        typeof CORE_LF_DICTIONARY_SYNTHESIS_PROFILE.revision;
    readonly comparisonStepLimit: number;
    readonly target: string;
    readonly candidates: readonly CoreLfDictionaryCandidateTrace[];
    readonly matches: readonly CoreLfQualifiedSymbol[];
}

export interface CoreLfDictionarySynthesisResult {
    readonly revision:
        typeof CORE_LF_DICTIONARY_SYNTHESIS_PROFILE.revision;
    readonly selected: CoreLfQualifiedSymbol;
    readonly term: KernelReference;
    readonly type: KernelExpression;
    readonly report: CoreLfDictionarySynthesisReport;
}

export interface CoreLfDictionarySynthesisInput {
    readonly declarations: CoreLfMixedDeclarationBaseContext;
    readonly target: KernelExpression;
    readonly candidates: readonly CoreLfQualifiedSymbol[];
}

export class CoreLfDictionarySynthesisError extends Error {
    constructor(
        public readonly code: CoreLfDictionarySynthesisErrorCode,
        public readonly path: string,
        message: string,
        public readonly report?: CoreLfDictionarySynthesisReport,
        public readonly underlying?: Error
    ) {
        super(message);
        this.name = 'CoreLfDictionarySynthesisError';
    }
}

const MODULE_ID =
    /^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$/u;

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

const cloneData = <T>(value: T): T => {
    if (Array.isArray(value)) {
        return value.map(cloneData) as T;
    }
    if (value !== null && typeof value === 'object') {
        return Object.fromEntries(
            Object.entries(value as Record<string, unknown>).map(
                ([key, entry]) => [key, cloneData(entry)]
            )
        ) as T;
    }
    return value;
};

const freezeData = <T>(value: T): T => deepFreeze(cloneData(value));

const fail = (
    code: CoreLfDictionarySynthesisErrorCode,
    path: string,
    message: string,
    report?: CoreLfDictionarySynthesisReport,
    underlying?: Error
): never => {
    throw new CoreLfDictionarySynthesisError(
        code,
        path,
        message,
        report,
        underlying
    );
};

const symbolKey = (value: CoreLfQualifiedSymbol): string =>
    `${value.moduleId}\u0000${value.name}`;

const displaySymbol = (value: CoreLfQualifiedSymbol): string =>
    `${value.moduleId}.${value.name}`;

const sameSymbol = (
    left: CoreLfQualifiedSymbol,
    right: CoreLfQualifiedSymbol
): boolean =>
    left.moduleId === right.moduleId && left.name === right.name;

const validateSymbol = (
    value: CoreLfQualifiedSymbol,
    path: string
): void => {
    if (
        value === null ||
        typeof value !== 'object' ||
        typeof value.moduleId !== 'string' ||
        !MODULE_ID.test(value.moduleId) ||
        typeof value.name !== 'string' ||
        value.name.length === 0 ||
        value.name.trim() !== value.name ||
        /[\s\u0000-\u001f\u007f]/u.test(value.name)
    ) {
        fail(
            'INVALID_CANDIDATE_SCOPE',
            path,
            'Dictionary candidate must be a valid exact qualified symbol'
        );
    }
};

const canonicalCandidates = (
    input: readonly CoreLfQualifiedSymbol[]
): readonly CoreLfQualifiedSymbol[] => {
    if (!Array.isArray(input)) {
        return fail(
            'INVALID_CANDIDATE_SCOPE',
            'candidates',
            'Dictionary candidates must be a finite array'
        );
    }
    input.forEach((candidate, index) =>
        validateSymbol(candidate, `candidates[${index}]`)
    );
    const candidates = input
        .map(candidate => ({ ...candidate }))
        .sort((left, right) => {
            const leftKey = symbolKey(left);
            const rightKey = symbolKey(right);
            return leftKey < rightKey ? -1 : leftKey > rightKey ? 1 : 0;
        });
    for (let index = 1; index < candidates.length; index++) {
        if (symbolKey(candidates[index - 1]) === symbolKey(candidates[index])) {
            return fail(
                'DUPLICATE_CANDIDATE',
                `candidates[${index}]`,
                `Dictionary candidate '${displaySymbol(candidates[index])}' ` +
                    'is repeated in the explicit scope'
            );
        }
    }
    return Object.freeze(candidates.map(candidate => Object.freeze(candidate)));
};

interface AdmissibleCandidate {
    readonly symbol: CoreLfQualifiedSymbol;
    readonly term: KernelReference;
    readonly termText: string;
    readonly declaredType: string;
}

const resolveCandidate = (
    declarations: CoreLfMixedDeclarationBaseContext,
    candidate: CoreLfQualifiedSymbol,
    index: number
): AdmissibleCandidate => {
    const declaration = declarations.declaration(candidate);
    if (declaration === undefined) {
        return fail(
            'UNAVAILABLE_CANDIDATE',
            `candidates[${index}]`,
            `Dictionary candidate '${displaySymbol(candidate)}' is not ` +
                'available in the supplied checked declaration context'
        );
    }
    if (
        !sameSymbol(declaration.symbol, candidate) ||
        !sameSymbol(declaration.link.symbol, candidate) ||
        declaration.link.kind !== 'free-declaration' ||
        !declaration.status.startsWith('installed-')
    ) {
        return fail(
            'UNSUPPORTED_CANDIDATE',
            `candidates[${index}]`,
            `Dictionary candidate '${displaySymbol(candidate)}' is not an ` +
                'installed ordinary free declaration'
        );
    }
    try {
        const term = kernelFree(
            declaration.link.coreName,
            provenance(
                'derived',
                `explicit dictionary candidate ${displaySymbol(candidate)}`
            )
        );
        return Object.freeze({
            symbol: candidate,
            term,
            termText: serializeCoreExpression(term),
            declaredType: serializeCoreExpression(declaration.type)
        });
    } catch (error: unknown) {
        return fail(
            'UNSUPPORTED_CANDIDATE',
            `candidates[${index}]`,
            `Dictionary candidate '${displaySymbol(candidate)}' has an ` +
                'invalid checked Core representation',
            undefined,
            error instanceof Error ? error : undefined
        );
    }
};

const validateTarget = (
    declarations: CoreLfMixedDeclarationBaseContext,
    target: KernelExpression
): KernelExpression => {
    try {
        const checker = createCoreLfChecker(declarations.environment);
        return checker.check(
            checker.rootContext,
            target,
            kernelUniverse(provenance(
                'derived',
                'explicit dictionary synthesis target must inhabit TYPE'
            ))
        ).term;
    } catch (error: unknown) {
        return fail(
            'INVALID_TARGET',
            'target',
            'Dictionary synthesis target is not a closed meta-free Core type',
            undefined,
            error instanceof Error ? error : undefined
        );
    }
};

const makeReport = (
    target: string,
    candidates: readonly CoreLfDictionaryCandidateTrace[]
): CoreLfDictionarySynthesisReport => freezeData({
    revision: CORE_LF_DICTIONARY_SYNTHESIS_PROFILE.revision,
    comparisonStepLimit:
        CORE_LF_DICTIONARY_SYNTHESIS_PROFILE.comparisonStepLimit,
    target,
    candidates,
    matches: candidates
        .filter(candidate => candidate.outcome === 'matched')
        .map(candidate => candidate.candidate)
});

/** Select one explicit checked global dictionary from an exact finite scope. */
export function synthesizeCoreLfGlobalDictionary(
    input: CoreLfDictionarySynthesisInput
): CoreLfDictionarySynthesisResult {
    const candidates = canonicalCandidates(input.candidates);
    const checkedTarget = validateTarget(input.declarations, input.target);
    const targetText = serializeCoreExpression(checkedTarget);
    const admissible = candidates.map((candidate, index) =>
        resolveCandidate(input.declarations, candidate, index)
    );
    const checkedTerms = new Map<string, KernelReference>();
    const trace: CoreLfDictionaryCandidateTrace[] = [];

    admissible.forEach((candidate, index) => {
        const checker = createCoreLfChecker(input.declarations.environment);
        let checked: ReturnType<typeof checker.check>;
        try {
            checked = checker.check(
                checker.rootContext,
                candidate.term,
                checkedTarget
            );
        } catch (error: unknown) {
            if (
                error instanceof CoreCheckerError &&
                error.code === 'TYPE_MISMATCH'
            ) {
                trace.push({
                    candidate: candidate.symbol,
                    term: candidate.termText,
                    declaredType: candidate.declaredType,
                    outcome: 'rejected',
                    rejection: {
                        checkerCode: error.code,
                        diagnostic: error.message
                    }
                });
                return;
            }
            return fail(
                'CANDIDATE_CHECK_FAILED',
                `candidates[${index}]`,
                `Dictionary candidate '${displaySymbol(candidate.symbol)}' ` +
                    'could not be classified as a match or type mismatch',
                undefined,
                error instanceof Error ? error : undefined
            );
        }
        if (checked.term.tag !== 'reference') {
            return fail(
                'CANDIDATE_CHECK_FAILED',
                `candidates[${index}]`,
                `Checked dictionary candidate ` +
                    `'${displaySymbol(candidate.symbol)}' did not remain ` +
                    'an explicit Core reference'
            );
        }
        checkedTerms.set(symbolKey(candidate.symbol), checked.term);
        trace.push({
            candidate: candidate.symbol,
            term: candidate.termText,
            declaredType: candidate.declaredType,
            outcome: 'matched'
        });
    });

    const report = makeReport(targetText, trace);
    if (report.matches.length === 0) {
        return fail(
            'NO_MATCHING_DICTIONARY',
            'candidates',
            `No candidate in the explicit scope checks against ${targetText}`,
            report
        );
    }
    if (report.matches.length > 1) {
        return fail(
            'AMBIGUOUS_DICTIONARY',
            'candidates',
            `Multiple candidates in the explicit scope check against ` +
                `${targetText}: ${report.matches.map(displaySymbol).join(', ')}`,
            report
        );
    }

    const selected = report.matches[0];
    const checkedTerm = checkedTerms.get(symbolKey(selected));
    if (checkedTerm === undefined) {
        return fail(
            'CANDIDATE_CHECK_FAILED',
            'candidates',
            'Dictionary synthesis lost its unique checked Core reference',
            report
        );
    }
    return freezeData({
        revision: CORE_LF_DICTIONARY_SYNTHESIS_PROFILE.revision,
        selected,
        term: checkedTerm,
        type: checkedTarget,
        report
    });
}
