/**
 * Frozen TSK-3 differential scope and deterministic owner corpus.
 *
 * The common fragment is exactly the H-03-reviewed manifest. This module
 * constructs backend-neutral Core cases; invoking Lambdapi remains an opt-in
 * conformance-test responsibility rather than a product runtime dependency.
 */

import {
    CORE_MVP_MANIFEST
} from './manifest';
import {
    CORE_OWNER_SCHEMAS,
    CoreOwnerId
} from './schema';
import {
    KernelExpression,
    SourceSpan,
    binderMode,
    kernelApplication,
    kernelFree,
    kernelUniverse,
    provenance,
    sourceSpan
} from './kernel';
import {
    CoreDeclarationEnvironment
} from './context';
import {
    coreOwnerResultType,
    coreOwnerSlotType
} from './signature';
import {
    KernelProbe,
    KernelProbeDeclaration
} from './probe';
import {
    LAMBDAPI_V32_MODULE
} from './lambdapi';

export interface CoreMvpOwnerDifferentialRequirement {
    readonly order: number;
    readonly owner: CoreOwnerId;
    readonly required: readonly string[];
}

export interface CoreMvpRuleDifferentialRequirement {
    readonly order: number;
    readonly ruleId: string;
    readonly required: readonly string[];
}

export interface CoreMvpHigherCellDifferentialRequirement {
    readonly id: string;
    readonly ownerIds: readonly CoreOwnerId[];
    readonly ruleIds: readonly string[];
    readonly required: readonly string[];
}

export interface CoreMvpDifferentialScopeInput {
    readonly status: string;
    readonly manifestRevision: string;
    readonly manifestContentHash: string;
    readonly ownerCases:
        readonly CoreMvpOwnerDifferentialRequirement[];
    readonly ruleCases:
        readonly CoreMvpRuleDifferentialRequirement[];
    readonly higherCellCases:
        readonly CoreMvpHigherCellDifferentialRequirement[];
}

export type CoreMvpDifferentialErrorCode =
    'DIFFERENTIAL_SCOPE_MISMATCH';

export class CoreMvpDifferentialError extends Error {
    constructor(
        public readonly code: CoreMvpDifferentialErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreMvpDifferentialError';
    }
}

const ownerIds = CORE_MVP_MANIFEST.owners.map(
    entry => entry.owner as CoreOwnerId
);

const expectedScope: CoreMvpDifferentialScopeInput = {
    status: 'required-until-graduation',
    manifestRevision: CORE_MVP_MANIFEST.revision,
    manifestContentHash: CORE_MVP_MANIFEST.contentHash,
    ownerCases: ownerIds.map((owner, order) => ({
        order,
        owner,
        required: [
            'positive-typing',
            'negative-result-typing'
        ]
    })),
    ruleCases: CORE_MVP_MANIFEST.rules.map((rule, order) => ({
        order,
        ruleId: rule.id,
        required: [
            'positive-conversion',
            'well-typed-near-miss-non-conversion',
            'malformed-rule-rejection'
        ]
    })),
    higherCellCases: [{
        id: 'recursive-functor-hom-2-cell',
        ownerIds: [
            'hom-category',
            'functor-object',
            'functor-hom-full',
            'functor-hom-capped'
        ],
        ruleIds: ['projection.functor-hom.evaluate'],
        required: [
            'positive-typing',
            'wrong-endpoint-negative',
            'runtime-conversion'
        ]
    }, {
        id: 'transfor-component-and-hom-levels',
        ownerIds: [
            'transfor-category',
            'transfor-component-full',
            'transfor-component-capped',
            'transfor-hom-full',
            'transfor-hom-capped'
        ],
        ruleIds: [
            'projection.transfor-component.evaluate',
            'projection.transfor-hom.evaluate'
        ],
        required: [
            'positive-typing',
            'wrong-endpoint-negative',
            'runtime-conversion'
        ]
    }]
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

const sameScope = (
    left: CoreMvpDifferentialScopeInput,
    right: CoreMvpDifferentialScopeInput
): boolean => JSON.stringify(left) === JSON.stringify(right);

export function validateCoreMvpDifferentialScope(
    scope: CoreMvpDifferentialScopeInput
): void {
    if (!sameScope(scope, expectedScope)) {
        throw new CoreMvpDifferentialError(
            'DIFFERENTIAL_SCOPE_MISMATCH',
            'TSK-3 differential scope differs from the exact H-03-reviewed ' +
            'owner, rule, or higher-cell matrix'
        );
    }
}

/**
 * Required differential coverage for the exact common frozen fragment.
 *
 * This is an exit matrix, not a claim that every row is already complete.
 */
export const CORE_MVP_DIFFERENTIAL_SCOPE = deepFreeze(expectedScope);

validateCoreMvpDifferentialScope(CORE_MVP_DIFFERENTIAL_SCOPE);

export interface CoreMvpOwnerDifferentialCase {
    readonly order: number;
    readonly owner: CoreOwnerId;
    readonly arguments: readonly KernelExpression[];
    readonly term: KernelExpression;
    readonly expectedType: KernelExpression;
    readonly rejectedType: KernelExpression;
    readonly span: SourceSpan;
}

export interface CoreMvpOwnerDifferentialCorpus {
    readonly manifestRevision: string;
    readonly manifestContentHash: string;
    readonly ownerIds: readonly CoreOwnerId[];
    readonly environment: CoreDeclarationEnvironment;
    readonly declarations: readonly KernelProbeDeclaration[];
    readonly cases: readonly CoreMvpOwnerDifferentialCase[];
    readonly probe: KernelProbe;
}

const corpusSource =
    'generated/v3_2_mvp_owner_differential.core.ts';

const spanAt = (line: number): SourceSpan =>
    sourceSpan(corpusSource, line, 1, line, 80);

const because = (line: number, detail: string) =>
    provenance('derived', detail, spanAt(line));

const safeName = (value: string): string =>
    value.replace(/-/g, '_');

/**
 * Build one shared set of terms for both the TypeScript checker and Lambdapi.
 *
 * Every selected owner receives one exact positive judgment and one
 * deliberately wrong result-type judgment. The latter remains well-scoped
 * and is suitable for Lambdapi's `assertnot ⊢ term : type` command.
 */
export function buildCoreMvpOwnerDifferentialCorpus(
): CoreMvpOwnerDifferentialCorpus {
    validateCoreMvpDifferentialScope(CORE_MVP_DIFFERENTIAL_SCOPE);

    let environment = CoreDeclarationEnvironment.empty();
    const declarations: KernelProbeDeclaration[] = [];
    const declarationMode = binderMode('explicit', 'functorial');

    const declare = (
        name: string,
        type: KernelExpression,
        line: number
    ): KernelExpression => {
        const nodeProvenance = because(
            line,
            `TSK-3 differential declaration ${name}`
        );
        environment = environment.extend({
            name,
            type,
            mode: declarationMode,
            provenance: nodeProvenance
        });
        declarations.push({
            name,
            type,
            span: spanAt(line)
        });
        return kernelFree(name, nodeProvenance);
    };

    let line = 1;
    const rejectedType = declare(
        'differential_wrong_type',
        kernelUniverse(because(line, 'TSK-3 wrong result-type universe')),
        line++
    );
    const cases: CoreMvpOwnerDifferentialCase[] = [];

    CORE_MVP_MANIFEST.owners.forEach((entry, order) => {
        const owner = entry.owner as CoreOwnerId;
        if (!Object.prototype.hasOwnProperty.call(
            CORE_OWNER_SCHEMAS,
            owner
        )) {
            throw new CoreMvpDifferentialError(
                'DIFFERENTIAL_SCOPE_MISMATCH',
                `Reviewed differential owner '${entry.owner}' is unknown`
            );
        }

        const arguments_: KernelExpression[] = [];
        const slots: readonly { readonly name: string }[] =
            CORE_OWNER_SCHEMAS[owner].slots;
        slots.forEach((slot, slotIndex) => {
            const slotType = coreOwnerSlotType(
                owner,
                slotIndex,
                arguments_,
                because(line, `${owner} slot ${slot.name}`)
            );
            const name =
                `differential_${order}_${safeName(owner)}_` +
                `${safeName(slot.name)}_${slotIndex}`;
            arguments_.push(declare(name, slotType, line++));
        });

        const caseSpan = spanAt(line);
        const caseProvenance = because(
            line,
            `TSK-3 owner differential ${owner}`
        );
        const term = kernelApplication(
            owner,
            arguments_.map(value => ({ value })),
            caseProvenance
        );
        cases.push({
            order,
            owner,
            arguments: Object.freeze([...arguments_]),
            term,
            expectedType: coreOwnerResultType(
                owner,
                arguments_,
                caseProvenance
            ),
            rejectedType,
            span: caseSpan
        });
        line++;
    });

    const probe: KernelProbe = {
        requiredModule: LAMBDAPI_V32_MODULE,
        declarations: Object.freeze([...declarations]),
        assertions: cases.map(testCase => ({
            label: `TSK-3 owner positive ${testCase.owner}`,
            term: testCase.term,
            type: testCase.expectedType,
            span: testCase.span
        })),
        negativeAssertions: cases.map(testCase => ({
            label: `TSK-3 owner negative ${testCase.owner}`,
            term: testCase.term,
            type: testCase.rejectedType,
            span: testCase.span
        }))
    };

    return Object.freeze({
        manifestRevision: CORE_MVP_MANIFEST.revision,
        manifestContentHash: CORE_MVP_MANIFEST.contentHash,
        ownerIds: Object.freeze(cases.map(testCase => testCase.owner)),
        environment,
        declarations: probe.declarations,
        cases: Object.freeze(cases),
        probe: Object.freeze(probe)
    });
}
