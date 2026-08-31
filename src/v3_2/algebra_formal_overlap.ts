/** Ordered formal product-localization simplices and universal face factors. */

import {
    KernelExpression,
    kernelCall,
    kernelFree,
    provenance
} from './kernel';
import { serializeCoreExpression } from './core_serialization';
import { AlgebraElement, AlgebraParent } from './algebra_parent';
import {
    AlgebraCechFace,
    AlgebraCechSimplex
} from './algebra_cech';
import {
    AffineFormalCoverRealization,
    validateAffineFormalCoreTerm
} from './algebra_formal_realization';
import {
    AffineFormalLocalizationRealization,
    AffineFormalLocalizationTerms,
    buildAffineFormalLocalizationTerms
} from './algebra_formal_localization';

export const ALGEBRA_FORMAL_OVERLAP_PROFILE = Object.freeze({
    revision: 'emdash-affine-formal-overlap-v1' as const,
    faceMapSource: 'localization-universal-factor' as const,
    handwrittenFaceMap: false as const,
    handwrittenTriangle: false as const,
    addsCechOwner: false as const,
    addsCoreOwner: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export const AFFINE_FORMAL_OVERLAP_BINDINGS = Object.freeze({
    bridge_CommRingLocalizationFactor: 'CommRingLocalizationFactor',
    bridge_comm_ring_localization_factorization_is_contr:
        'comm_ring_localization_factorization_is_contr',
    bridge_is_contr_center: 'is_contr_center',
    bridge_comm_ring_localization_factor_map:
        'comm_ring_localization_factor_map',
    bridge_comm_ring_localization_factor_agreement:
        'comm_ring_localization_factor_agreement'
});

export type AlgebraFormalOverlapErrorCode =
    | 'FOREIGN_SIMPLEX'
    | 'SIMPLEX_LOCALIZATION_MISMATCH'
    | 'SIMPLEX_FORMAL_SOURCE_MISMATCH'
    | 'SIMPLEX_PRODUCT_MISMATCH'
    | 'FORMAL_SIMPLEX_LOCALIZATION_UNAVAILABLE'
    | 'SIMPLEX_ARITY_MISMATCH'
    | 'FACE_EVIDENCE_ARITY_MISMATCH'
    | 'MISSING_FACE_TARGET';

export class AlgebraFormalOverlapError extends Error {
    constructor(
        public readonly code: AlgebraFormalOverlapErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraFormalOverlapError';
    }
}

const fail = (
    code: AlgebraFormalOverlapErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraFormalOverlapError(code, path, message);
};

const nodeProvenance = provenance('derived', 'affine formal overlap');

type OverlapBinding = keyof typeof AFFINE_FORMAL_OVERLAP_BINDINGS;

interface CallArgument {
    readonly plicity: 'explicit' | 'implicit';
    readonly value: KernelExpression;
}

const call = (
    name: OverlapBinding,
    arguments_: readonly CallArgument[]
): KernelExpression => kernelCall(
    kernelFree(name, nodeProvenance),
    arguments_,
    nodeProvenance
);

const sameTerm = (left: KernelExpression, right: KernelExpression): boolean =>
    serializeCoreExpression(left) === serializeCoreExpression(right);

const key = (indices: readonly number[]): string => indices.join(',');

export interface AffineFormalCechSimplexLocalization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly cover: AffineFormalCoverRealization<P, C, I>;
    readonly simplex: AlgebraCechSimplex<P, C, I>;
    readonly localization: AffineFormalLocalizationRealization<P, C, I>;
    readonly productTerm: KernelExpression;
    readonly terms: AffineFormalLocalizationTerms<P, C, I>;
}

export function defineAffineFormalCechSimplexLocalization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    cover: AffineFormalCoverRealization<P, C, I>,
    simplex: AlgebraCechSimplex<P, C, I>,
    localization: AffineFormalLocalizationRealization<P, C, I>
): AffineFormalCechSimplexLocalization<P, C, I> {
    if (!cover.cover.simplices.includes(simplex)) {
        return fail(
            'FOREIGN_SIMPLEX',
            'formalCechSimplex.simplex',
            'Simplex is not retained by the selected computational cover'
        );
    }
    if (localization.localization !== simplex.chart.chart.localization) {
        return fail(
            'SIMPLEX_LOCALIZATION_MISMATCH',
            'formalCechSimplex.localization',
            'Formal localization does not own the retained simplex chart'
        );
    }
    if (!sameTerm(localization.source.formalRing, cover.algebra.formalRing)) {
        return fail(
            'SIMPLEX_FORMAL_SOURCE_MISMATCH',
            'formalCechSimplex.source',
            'Simplex localization and cover use different formal source rings'
        );
    }
    const productTerm = cover.algebra.reifyElement(simplex.product);
    const repeatedProductTerm = cover.algebra.reifyElement(simplex.product);
    if (!sameTerm(productTerm, repeatedProductTerm) ||
        !sameTerm(productTerm, localization.elementTerm)) {
        return fail(
            'SIMPLEX_PRODUCT_MISMATCH',
            'formalCechSimplex.product',
            'Simplex product and formal localization use different Core terms'
        );
    }
    if (!localization.formalLocalizationAvailable) {
        return fail(
            'FORMAL_SIMPLEX_LOCALIZATION_UNAVAILABLE',
            'formalCechSimplex.localization',
            'Formal simplex requires a whole universal localization realization'
        );
    }
    return Object.freeze({
        cover,
        simplex,
        localization,
        productTerm,
        terms: buildAffineFormalLocalizationTerms(localization)
    });
}

export interface AffineFormalCechFaceFactor<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly simplex: AffineFormalCechSimplexLocalization<P, C, I>;
    readonly face: AlgebraCechFace<P, C, I>;
    /** Coordinate-ring domain: the lower-dimensional face chart. */
    readonly domain: AffineFormalCechSimplexLocalization<P, C, I>;
    /** Coordinate-ring codomain: the containing product chart. */
    readonly codomain: AffineFormalCechSimplexLocalization<P, C, I>;
    readonly invertsDomainElement: KernelExpression;
    readonly factorType: KernelExpression;
    readonly contractible: KernelExpression;
    readonly factor: KernelExpression;
    readonly map: KernelExpression;
    readonly agreement: KernelExpression;
}

export interface AffineFormalCechOverlapTerms<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly cover: AffineFormalCoverRealization<P, C, I>;
    readonly simplices: readonly AffineFormalCechSimplexLocalization<P, C, I>[];
    readonly faces: readonly AffineFormalCechFaceFactor<P, C, I>[];
}

export function buildAffineFormalCechOverlapTerms<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    cover: AffineFormalCoverRealization<P, C, I>,
    simplexInput: readonly AffineFormalCechSimplexLocalization<P, C, I>[],
    faceInversionInput: readonly (readonly KernelExpression[])[]
): AffineFormalCechOverlapTerms<P, C, I> {
    if (simplexInput.length !== cover.cover.simplices.length) {
        return fail(
            'SIMPLEX_ARITY_MISMATCH',
            'formalCechOverlap.simplices',
            'Formal simplex count differs from the computational cover'
        );
    }
    if (faceInversionInput.length !== simplexInput.length) {
        return fail(
            'FACE_EVIDENCE_ARITY_MISMATCH',
            'formalCechOverlap.faceInversions',
            'Face-inversion rows differ from formal simplex rows'
        );
    }
    const simplices = Object.freeze(simplexInput.map((simplex, index) => {
        if (simplex.cover !== cover || simplex.simplex !== cover.cover.simplices[index]) {
            return fail(
                'FOREIGN_SIMPLEX',
                `formalCechOverlap.simplices[${index}]`,
                'Formal simplices must preserve the retained cover order'
            );
        }
        if (faceInversionInput[index].length !== simplex.simplex.faces.length) {
            return fail(
                'FACE_EVIDENCE_ARITY_MISMATCH',
                `formalCechOverlap.faceInversions[${index}]`,
                'Face-inversion evidence count differs from the simplex faces'
            );
        }
        return simplex;
    }));
    const byIndices = new Map(simplices.map(simplex => [
        key(simplex.simplex.indices),
        simplex
    ]));
    const sourceRing = cover.algebra.formalRing;
    const faces: AffineFormalCechFaceFactor<P, C, I>[] = [];
    simplices.forEach((codomain, simplexIndex) => {
        codomain.simplex.faces.forEach((face, faceIndex) => {
            const domain = byIndices.get(key(face.targetIndices));
            if (domain === undefined) {
                return fail(
                    'MISSING_FACE_TARGET',
                    `formalCechOverlap.simplices[${simplexIndex}].faces[${faceIndex}]`,
                    'Retained simplex collection has no lower-dimensional face target'
                );
            }
            const invertsDomainElement = validateAffineFormalCoreTerm(
                faceInversionInput[simplexIndex][faceIndex],
                `formalCechOverlap.faceInversions[${simplexIndex}][${faceIndex}]`
            );
            const domainRing = domain.localization.target.formalRing;
            const codomainRing = codomain.localization.target.formalRing;
            const domainMap = domain.localization.formalMap;
            const codomainMap = codomain.localization.formalMap;
            const factorType = call('bridge_CommRingLocalizationFactor', [
                { plicity: 'implicit', value: sourceRing },
                { plicity: 'implicit', value: domainRing },
                { plicity: 'implicit', value: codomainRing },
                { plicity: 'explicit', value: domainMap },
                { plicity: 'explicit', value: codomainMap }
            ]);
            const contractible = call(
                'bridge_comm_ring_localization_factorization_is_contr',
                [
                    { plicity: 'implicit', value: sourceRing },
                    { plicity: 'implicit', value: domain.productTerm },
                    { plicity: 'implicit', value: domainRing },
                    { plicity: 'implicit', value: domainMap },
                    { plicity: 'explicit', value: domain.terms.property },
                    { plicity: 'explicit', value: codomainRing },
                    { plicity: 'explicit', value: codomainMap },
                    { plicity: 'explicit', value: invertsDomainElement }
                ]
            );
            const factor = call('bridge_is_contr_center', [
                { plicity: 'implicit', value: factorType },
                { plicity: 'explicit', value: contractible }
            ]);
            const factorArguments: readonly CallArgument[] = [
                { plicity: 'implicit', value: sourceRing },
                { plicity: 'implicit', value: domainRing },
                { plicity: 'implicit', value: codomainRing },
                { plicity: 'implicit', value: domainMap },
                { plicity: 'implicit', value: codomainMap },
                { plicity: 'explicit', value: factor }
            ];
            faces.push(Object.freeze({
                simplex: codomain,
                face,
                domain,
                codomain,
                invertsDomainElement,
                factorType,
                contractible,
                factor,
                map: call('bridge_comm_ring_localization_factor_map', factorArguments),
                agreement: call(
                    'bridge_comm_ring_localization_factor_agreement',
                    factorArguments
                )
            }));
        });
    });
    return Object.freeze({
        cover,
        simplices,
        faces: Object.freeze(faces)
    });
}
