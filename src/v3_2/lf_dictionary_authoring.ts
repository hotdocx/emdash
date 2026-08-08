/**
 * Direct-TypeScript authoring adapter for one leading global dictionary.
 *
 * The adapter derives the target from a checked global callee and erases to
 * an ordinary explicit transfer argument. It owns no parser, registry,
 * workspace mutation, local-binder search, recursive search, or I/O.
 */

import {
    CoreLfDictionarySynthesisResult,
    synthesizeCoreLfGlobalDictionary
} from './lf_dictionary_synthesis';
import {
    CoreLfMixedDeclarationBaseContext
} from './lf_transfer_mixed';
import {
    CoreLfQualifiedSymbol,
    CoreLfTransferArgument
} from './lf_transfer';

export const CORE_LF_DICTIONARY_AUTHORING_PROFILE = Object.freeze({
    revision: 'emdash-lf-dictionary-authoring-v1' as const
});

export type CoreLfDictionaryAuthoringErrorCode =
    | 'INVALID_CALLEE'
    | 'UNAVAILABLE_CALLEE'
    | 'UNSUPPORTED_CALLEE'
    | 'EXPECTED_LEADING_IMPLICIT_BINDER';

export interface CoreLfLeadingDictionaryAuthoringInput {
    readonly declarations: CoreLfMixedDeclarationBaseContext;
    readonly callee: CoreLfQualifiedSymbol;
    readonly candidates: readonly CoreLfQualifiedSymbol[];
}

export interface CoreLfLeadingDictionaryAuthoringResult {
    readonly revision:
        typeof CORE_LF_DICTIONARY_AUTHORING_PROFILE.revision;
    readonly callee: CoreLfQualifiedSymbol;
    readonly binderName: string;
    readonly argument: CoreLfTransferArgument;
    readonly synthesis: CoreLfDictionarySynthesisResult;
}

export class CoreLfDictionaryAuthoringError extends Error {
    constructor(
        public readonly code: CoreLfDictionaryAuthoringErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfDictionaryAuthoringError';
    }
}

const MODULE_ID =
    /^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$/u;

const fail = (
    code: CoreLfDictionaryAuthoringErrorCode,
    path: string,
    message: string
): never => {
    throw new CoreLfDictionaryAuthoringError(code, path, message);
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

const sameSymbol = (
    left: CoreLfQualifiedSymbol,
    right: CoreLfQualifiedSymbol
): boolean =>
    left.moduleId === right.moduleId && left.name === right.name;

const displaySymbol = (value: CoreLfQualifiedSymbol): string =>
    `${value.moduleId}.${value.name}`;

const validateCallee = (callee: CoreLfQualifiedSymbol): void => {
    if (
        callee === null ||
        typeof callee !== 'object' ||
        typeof callee.moduleId !== 'string' ||
        !MODULE_ID.test(callee.moduleId) ||
        typeof callee.name !== 'string' ||
        callee.name.length === 0 ||
        callee.name.trim() !== callee.name ||
        /[\s\u0000-\u001f\u007f]/u.test(callee.name)
    ) {
        fail(
            'INVALID_CALLEE',
            'callee',
            'Dictionary authoring callee must be a valid exact qualified symbol'
        );
    }
};

/**
 * Derive and synthesize the first implicit argument of a checked global call.
 *
 * The returned transfer argument is ordinary explicit source data. The caller
 * remains responsible for placing it in a call and declaring exact source
 * availability/provider metadata in the eventual module or workspace.
 */
export function synthesizeCoreLfLeadingDictionaryArgument(
    input: CoreLfLeadingDictionaryAuthoringInput
): CoreLfLeadingDictionaryAuthoringResult {
    validateCallee(input.callee);
    const declaration = input.declarations.declaration(input.callee);
    if (declaration === undefined) {
        return fail(
            'UNAVAILABLE_CALLEE',
            'callee',
            `Dictionary authoring callee ` +
                `'${displaySymbol(input.callee)}' is not available in the ` +
                'supplied checked declaration context'
        );
    }
    if (
        !sameSymbol(declaration.symbol, input.callee) ||
        !sameSymbol(declaration.link.symbol, input.callee) ||
        declaration.link.kind !== 'free-declaration' ||
        !declaration.status.startsWith('installed-')
    ) {
        return fail(
            'UNSUPPORTED_CALLEE',
            'callee',
            `Dictionary authoring callee ` +
                `'${displaySymbol(input.callee)}' is not an installed ` +
                'ordinary free declaration'
        );
    }
    if (
        declaration.type.tag !== 'pi' ||
        declaration.type.binder.mode.plicity !== 'implicit'
    ) {
        return fail(
            'EXPECTED_LEADING_IMPLICIT_BINDER',
            'callee',
            `Dictionary authoring callee ` +
                `'${displaySymbol(input.callee)}' does not expose a direct ` +
                'leading implicit Pi binder'
        );
    }

    const synthesis = synthesizeCoreLfGlobalDictionary({
        declarations: input.declarations,
        target: declaration.type.binder.type,
        candidates: input.candidates
    });
    return deepFreeze(cloneData({
        revision: CORE_LF_DICTIONARY_AUTHORING_PROFILE.revision,
        callee: input.callee,
        binderName: declaration.type.binder.name,
        argument: {
            plicity: 'implicit' as const,
            value: {
                tag: 'global' as const,
                symbol: synthesis.selected
            }
        },
        synthesis
    }));
}
