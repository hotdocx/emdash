/** Assumption-explicit Core realization of principal localizations and charts. */

import {
    KernelExpression,
    kernelCall,
    kernelFree,
    provenance
} from './kernel';
import { serializeCoreExpression } from './core_serialization';
import { AlgebraElement, AlgebraParent } from './algebra_parent';
import {
    AlgebraPresentedAlgebra,
    algebraPresentedAlgebraEquals
} from './algebra_presented_algebra';
import { AlgebraQuotientElement } from './algebra_quotient';
import { AlgebraPrincipalLocalization } from './algebra_localization';
import {
    AffineFormalAlgebraRealization,
    AffineFormalCoverRealization,
    AffineFormalRealizationStatus,
    validateAffineFormalCoreTerm
} from './algebra_formal_realization';
import {
    AffineFormalCoverTerms,
    buildAffineFormalCoverTerms,
    buildAffineFormalFamily
} from './algebra_formal_cover';

export const ALGEBRA_FORMAL_LOCALIZATION_PROFILE = Object.freeze({
    revision: 'emdash-affine-formal-localization-v1' as const,
    universalPropertySource: 'supplied-formal-term' as const,
    trustedProducesFormalEvidence: false as const,
    addsCoreOwner: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export const AFFINE_FORMAL_LOCALIZATION_BINDINGS = Object.freeze({
    bridge_comm_ring_hom_apply: 'comm_ring_hom_apply',
    bridge_comm_ring_unit_intro: 'comm_ring_unit_intro',
    bridge_comm_ring_localization_property_intro:
        'comm_ring_localization_property_intro',
    bridge_comm_ring_localization_intro: 'comm_ring_localization_intro',
    bridge_affine_spec_basic_open_chart: 'affine_spec_basic_open_chart',
    bridge_comm_ring_localization_family_nil:
        'comm_ring_localization_family_nil',
    bridge_comm_ring_localization_family_cons:
        'comm_ring_localization_family_cons',
    bridge_comm_ring_zariski_cover_family_intro:
        'comm_ring_zariski_cover_family_intro'
});

export type AlgebraFormalLocalizationErrorCode =
    | 'INVALID_STATUS'
    | 'FOREIGN_LOCALIZATION_SOURCE'
    | 'FOREIGN_LOCALIZATION_TARGET'
    | 'COMPUTATIONAL_INVERSE_FAILURE'
    | 'NONDETERMINISTIC_LOCALIZATION_REIFIER'
    | 'MISSING_INVERSE_LAW'
    | 'TRUSTED_FORMAL_LOCALIZATION_EVIDENCE'
    | 'FORMAL_UNIT_UNAVAILABLE'
    | 'FORMAL_LOCALIZATION_UNAVAILABLE'
    | 'COVER_LOCALIZATION_ARITY_MISMATCH'
    | 'FOREIGN_COVER_LOCALIZATION'
    | 'FORMAL_COVER_SOURCE_MISMATCH'
    | 'FORMAL_COVER_ELEMENT_MISMATCH';

export class AlgebraFormalLocalizationError extends Error {
    constructor(
        public readonly code: AlgebraFormalLocalizationErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraFormalLocalizationError';
    }
}

const fail = (
    code: AlgebraFormalLocalizationErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraFormalLocalizationError(code, path, message);
};

const selectStatus = (value: unknown): AffineFormalRealizationStatus => {
    if (value === 'explicit-data' || value === 'trusted-computation' ||
        value === 'checked') return value;
    return fail(
        'INVALID_STATUS',
        'formalLocalization.status',
        'Expected explicit-data, trusted-computation, or checked status'
    );
};

const nodeProvenance = provenance('derived', 'affine formal localization');

type LocalizationBinding = keyof typeof AFFINE_FORMAL_LOCALIZATION_BINDINGS;

interface CallArgument {
    readonly plicity: 'explicit' | 'implicit';
    readonly value: KernelExpression;
}

const call = (
    name: LocalizationBinding,
    arguments_: readonly CallArgument[]
): KernelExpression => kernelCall(
    kernelFree(name, nodeProvenance),
    arguments_,
    nodeProvenance
);

const sameTerm = (left: KernelExpression, right: KernelExpression): boolean =>
    serializeCoreExpression(left) === serializeCoreExpression(right);

const reifyDeterministically = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    realization: AffineFormalAlgebraRealization<P, C, I>,
    element: AlgebraQuotientElement<P, C, I>,
    path: string
): KernelExpression => {
    const first = realization.reifyElement(element);
    const second = realization.reifyElement(element);
    if (!sameTerm(first, second)) {
        return fail(
            'NONDETERMINISTIC_LOCALIZATION_REIFIER',
            path,
            'Localization element reifier returned different explicit Core terms'
        );
    }
    return first;
};

export interface AffineFormalLocalizationRealizationInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly localization: AlgebraPrincipalLocalization<P, C, I>;
    readonly source: AffineFormalAlgebraRealization<P, C, I>;
    readonly target: AffineFormalAlgebraRealization<P, C, I>;
    readonly formalMap: KernelExpression;
    readonly status: AffineFormalRealizationStatus;
    readonly inverseLawTerm?: KernelExpression;
    readonly universalTerm?: KernelExpression;
}

export interface AffineFormalLocalizationRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision: typeof ALGEBRA_FORMAL_LOCALIZATION_PROFILE.revision;
    readonly localization: AlgebraPrincipalLocalization<P, C, I>;
    readonly source: AffineFormalAlgebraRealization<P, C, I>;
    readonly target: AffineFormalAlgebraRealization<P, C, I>;
    readonly status: AffineFormalRealizationStatus;
    readonly formalMap: KernelExpression;
    readonly elementTerm: KernelExpression;
    readonly inverseTerm: KernelExpression;
    readonly elementImageTerm: KernelExpression;
    readonly inverseLawTerm?: KernelExpression;
    readonly universalTerm?: KernelExpression;
    readonly computationalInverseEquationHolds: true;
    readonly formalUnitAvailable: boolean;
    readonly formalLocalizationAvailable: boolean;
}

export function defineAffineFormalLocalizationRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    input: AffineFormalLocalizationRealizationInput<P, C, I>
): AffineFormalLocalizationRealization<P, C, I> {
    if (!algebraPresentedAlgebraEquals(input.localization.source, input.source.algebra)) {
        return fail(
            'FOREIGN_LOCALIZATION_SOURCE',
            'formalLocalization.source',
            'Localization source and formal source realization differ'
        );
    }
    if (!algebraPresentedAlgebraEquals(input.localization.algebra, input.target.algebra)) {
        return fail(
            'FOREIGN_LOCALIZATION_TARGET',
            'formalLocalization.target',
            'Localization target and formal target realization differ'
        );
    }
    if (input.localization.inverseEquation !== true) {
        return fail(
            'COMPUTATIONAL_INVERSE_FAILURE',
            'formalLocalization.localization.inverseEquation',
            'Computational localization does not satisfy its inverse equation'
        );
    }
    const selectedStatus = selectStatus(input.status);
    const formalMap = validateAffineFormalCoreTerm(
        input.formalMap,
        'formalLocalization.formalMap'
    );
    const elementTerm = reifyDeterministically(
        input.source,
        input.localization.element,
        'formalLocalization.element'
    );
    const inverseTerm = reifyDeterministically(
        input.target,
        input.localization.inverse,
        'formalLocalization.inverse'
    );
    const elementImageTerm = reifyDeterministically(
        input.target,
        input.localization.elementImage,
        'formalLocalization.elementImage'
    );
    let inverseLawTerm: KernelExpression | undefined;
    let universalTerm: KernelExpression | undefined;
    if (selectedStatus === 'trusted-computation') {
        if (input.inverseLawTerm !== undefined || input.universalTerm !== undefined) {
            return fail(
                'TRUSTED_FORMAL_LOCALIZATION_EVIDENCE',
                'formalLocalization.evidence',
                'Trusted computation metadata must not carry formal localization evidence'
            );
        }
    } else {
        if (input.inverseLawTerm === undefined) {
            return fail(
                'MISSING_INVERSE_LAW',
                'formalLocalization.inverseLawTerm',
                'Explicit or checked localization requires a formal inverse law'
            );
        }
        inverseLawTerm = validateAffineFormalCoreTerm(
            input.inverseLawTerm,
            'formalLocalization.inverseLawTerm'
        );
        if (input.universalTerm !== undefined) {
            universalTerm = validateAffineFormalCoreTerm(
                input.universalTerm,
                'formalLocalization.universalTerm'
            );
        }
    }
    return Object.freeze({
        profileRevision: ALGEBRA_FORMAL_LOCALIZATION_PROFILE.revision,
        localization: input.localization,
        source: input.source,
        target: input.target,
        status: selectedStatus,
        formalMap,
        elementTerm,
        inverseTerm,
        elementImageTerm,
        ...(inverseLawTerm === undefined ? {} : { inverseLawTerm }),
        ...(universalTerm === undefined ? {} : { universalTerm }),
        computationalInverseEquationHolds: true,
        formalUnitAvailable: inverseLawTerm !== undefined,
        formalLocalizationAvailable:
            inverseLawTerm !== undefined && universalTerm !== undefined
    });
}

export interface AffineFormalLocalizationUnitTerms<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly realization: AffineFormalLocalizationRealization<P, C, I>;
    readonly mappedElement: KernelExpression;
    readonly unit: KernelExpression;
}

export function buildAffineFormalLocalizationUnitTerms<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    realization: AffineFormalLocalizationRealization<P, C, I>
): AffineFormalLocalizationUnitTerms<P, C, I> {
    if (realization.inverseLawTerm === undefined) {
        return fail(
            'FORMAL_UNIT_UNAVAILABLE',
            'formalLocalizationTerms.unit',
            'Formal unit construction requires an actual inverse law'
        );
    }
    const sourceRing = realization.source.formalRing;
    const targetRing = realization.target.formalRing;
    const mappedElement = call('bridge_comm_ring_hom_apply', [
        { plicity: 'implicit', value: sourceRing },
        { plicity: 'implicit', value: targetRing },
        { plicity: 'explicit', value: realization.formalMap },
        { plicity: 'explicit', value: realization.elementTerm }
    ]);
    const unit = call('bridge_comm_ring_unit_intro', [
        { plicity: 'implicit', value: targetRing },
        { plicity: 'implicit', value: mappedElement },
        { plicity: 'explicit', value: realization.inverseTerm },
        { plicity: 'explicit', value: realization.inverseLawTerm }
    ]);
    return Object.freeze({ realization, mappedElement, unit });
}

export interface AffineFormalLocalizationTerms<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> extends AffineFormalLocalizationUnitTerms<P, C, I> {
    readonly property: KernelExpression;
    readonly localization: KernelExpression;
    readonly chart: KernelExpression;
}

export function buildAffineFormalLocalizationTerms<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    realization: AffineFormalLocalizationRealization<P, C, I>
): AffineFormalLocalizationTerms<P, C, I> {
    if (realization.universalTerm === undefined) {
        return fail(
            'FORMAL_LOCALIZATION_UNAVAILABLE',
            'formalLocalizationTerms.localization',
            'Whole localization construction requires supplied universal data'
        );
    }
    const unitTerms = buildAffineFormalLocalizationUnitTerms(realization);
    const sourceRing = realization.source.formalRing;
    const targetRing = realization.target.formalRing;
    const property = call('bridge_comm_ring_localization_property_intro', [
        { plicity: 'implicit', value: sourceRing },
        { plicity: 'implicit', value: realization.elementTerm },
        { plicity: 'implicit', value: targetRing },
        { plicity: 'implicit', value: realization.formalMap },
        { plicity: 'explicit', value: unitTerms.unit },
        { plicity: 'explicit', value: realization.universalTerm }
    ]);
    const localization = call('bridge_comm_ring_localization_intro', [
        { plicity: 'implicit', value: sourceRing },
        { plicity: 'implicit', value: realization.elementTerm },
        { plicity: 'explicit', value: targetRing },
        { plicity: 'explicit', value: realization.formalMap },
        { plicity: 'explicit', value: property }
    ]);
    const chart = call('bridge_affine_spec_basic_open_chart', [
        { plicity: 'implicit', value: sourceRing },
        { plicity: 'implicit', value: realization.elementTerm },
        { plicity: 'explicit', value: localization }
    ]);
    return Object.freeze({
        ...unitTerms,
        property,
        localization,
        chart
    });
}

export interface AffineFormalCoverLocalizationTerms<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly cover: AffineFormalCoverTerms<P, C, I>;
    readonly realizations: readonly AffineFormalLocalizationRealization<P, C, I>[];
    readonly localizations: readonly AffineFormalLocalizationTerms<P, C, I>[];
    readonly localizationFamily: KernelExpression;
    readonly coverFamily: KernelExpression;
    readonly charts: readonly KernelExpression[];
}

export function buildAffineFormalCoverLocalizationTerms<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    coverRealization: AffineFormalCoverRealization<P, C, I>,
    realizationInput: readonly AffineFormalLocalizationRealization<P, C, I>[]
): AffineFormalCoverLocalizationTerms<P, C, I> {
    if (realizationInput.length !== coverRealization.cover.charts.length) {
        return fail(
            'COVER_LOCALIZATION_ARITY_MISMATCH',
            'formalCoverLocalizations.realizations',
            'Formal localization count differs from the computational cover'
        );
    }
    const cover = buildAffineFormalCoverTerms(coverRealization);
    const sourceRing = coverRealization.algebra.formalRing;
    const carrier = cover.carrier;
    const realizations = Object.freeze(realizationInput.map((realization, index) => {
        const expected = coverRealization.cover.charts[index].chart.localization;
        if (realization.localization !== expected) {
            return fail(
                'FOREIGN_COVER_LOCALIZATION',
                `formalCoverLocalizations.realizations[${index}]`,
                'Formal realization does not own the retained computational chart'
            );
        }
        if (!sameTerm(realization.source.formalRing, sourceRing)) {
            return fail(
                'FORMAL_COVER_SOURCE_MISMATCH',
                `formalCoverLocalizations.realizations[${index}].source`,
                'Formal localization and formal cover use different source rings'
            );
        }
        if (!sameTerm(realization.elementTerm, coverRealization.generatorTerms[index])) {
            return fail(
                'FORMAL_COVER_ELEMENT_MISMATCH',
                `formalCoverLocalizations.realizations[${index}].element`,
                'Formal localization and formal cover realize the generator differently'
            );
        }
        return realization;
    }));
    const localizations = Object.freeze(realizations.map(
        realization => buildAffineFormalLocalizationTerms(realization)
    ));
    let localizationFamily = call('bridge_comm_ring_localization_family_nil', [
        { plicity: 'explicit', value: sourceRing }
    ]);
    for (let index = localizations.length - 1; index >= 0; index--) {
        const tail = buildAffineFormalFamily(
            carrier,
            coverRealization.generatorTerms.slice(index + 1)
        );
        localizationFamily = call('bridge_comm_ring_localization_family_cons', [
            { plicity: 'implicit', value: sourceRing },
            { plicity: 'implicit', value: tail.length },
            { plicity: 'implicit', value: coverRealization.generatorTerms[index] },
            { plicity: 'implicit', value: tail.family },
            { plicity: 'explicit', value: localizations[index].localization },
            { plicity: 'explicit', value: localizationFamily }
        ]);
    }
    const coverFamily = call('bridge_comm_ring_zariski_cover_family_intro', [
        { plicity: 'implicit', value: sourceRing },
        { plicity: 'explicit', value: cover.cover },
        { plicity: 'explicit', value: localizationFamily }
    ]);
    return Object.freeze({
        cover,
        realizations,
        localizations,
        localizationFamily,
        coverFamily,
        charts: Object.freeze(localizations.map(value => value.chart))
    });
}
