/** Degreewise internal finite presentation of realized affine Cech data. */

import {
    KernelExpression,
    binderMode,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelFree,
    kernelLambda,
    provenance
} from './kernel';
import { AlgebraElement, AlgebraParent } from './algebra_parent';
import {
    AffineFormalFamilyTerms,
    buildAffineFormalFamily
} from './algebra_formal_cover';
import {
    AffineFormalCechFaceFactor,
    AffineFormalCechOverlapTerms,
    AffineFormalCechSimplexLocalization
} from './algebra_formal_overlap';

export const ALGEBRA_FORMAL_CECH_PROFILE = Object.freeze({
    revision: 'emdash-affine-formal-cech-v1' as const,
    representation: 'packed-degreewise-finite-presentation' as const,
    positiveSign: 'true' as const,
    claimsCosimplicialIdentities: false as const,
    claimsDifferential: false as const,
    claimsCohomology: false as const,
    addsCechOwner: false as const,
    addsCoreOwner: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export const AFFINE_FORMAL_CECH_BINDINGS = Object.freeze({
    bridge_tau: 'τ',
    bridge_Grpd_grpd: 'Grpd_grpd',
    bridge_Sigma_grpd: 'Σ_',
    bridge_Struct_sigma: 'Struct_sigma',
    bridge_Product_grpd: 'Product_grpd',
    bridge_Product_pair_grpd: 'Product_pair_grpd',
    bridge_Bool_grpd: 'Bool_grpd',
    bridge_bool_positive: 'true',
    bridge_bool_negative: 'false',
    bridge_FiniteFamily: 'FiniteFamily',
    bridge_AffineSpecBigSlice_cat: 'AffineSpecBigSlice_cat',
    bridge_Obj: 'Obj'
});

export type AlgebraFormalCechErrorCode =
    | 'DEGREE_ORDER_MISMATCH'
    | 'SIMPLEX_ORDER_MISMATCH'
    | 'FACE_ORDER_MISMATCH';

export class AlgebraFormalCechError extends Error {
    constructor(
        public readonly code: AlgebraFormalCechErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraFormalCechError';
    }
}

const fail = (
    code: AlgebraFormalCechErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraFormalCechError(code, path, message);
};

const nodeProvenance = provenance('derived', 'affine formal Cech presentation');

type CechBinding = keyof typeof AFFINE_FORMAL_CECH_BINDINGS;

interface CallArgument {
    readonly plicity: 'explicit' | 'implicit';
    readonly value: KernelExpression;
}

const reference = (name: CechBinding): KernelExpression =>
    kernelFree(name, nodeProvenance);

const call = (
    name: CechBinding,
    arguments_: readonly CallArgument[]
): KernelExpression => kernelCall(
    reference(name),
    arguments_,
    nodeProvenance
);

const lambda = (
    name: string,
    type: KernelExpression,
    body: KernelExpression
): KernelExpression => kernelLambda(
    kernelBinder(
        name,
        type,
        binderMode('explicit', 'object-only'),
        nodeProvenance
    ),
    body,
    nodeProvenance
);

const packedElementMotive = (): KernelExpression => lambda(
    'A',
    call('bridge_tau', [{
        plicity: 'explicit',
        value: reference('bridge_Grpd_grpd')
    }]),
    kernelBound(0, nodeProvenance)
);

const packedElementType = (): KernelExpression => call('bridge_Sigma_grpd', [
    { plicity: 'implicit', value: reference('bridge_Grpd_grpd') },
    { plicity: 'explicit', value: packedElementMotive() }
]);

const packElement = (
    type: KernelExpression,
    value: KernelExpression
): KernelExpression => call('bridge_Struct_sigma', [
    { plicity: 'implicit', value: reference('bridge_Grpd_grpd') },
    { plicity: 'implicit', value: packedElementMotive() },
    { plicity: 'explicit', value: type },
    { plicity: 'explicit', value }
]);

const productType = (
    left: KernelExpression,
    right: KernelExpression
): KernelExpression => call('bridge_Product_grpd', [
    { plicity: 'explicit', value: left },
    { plicity: 'explicit', value: right }
]);

const productPair = (
    leftType: KernelExpression,
    rightType: KernelExpression,
    left: KernelExpression,
    right: KernelExpression
): KernelExpression => call('bridge_Product_pair_grpd', [
    { plicity: 'implicit', value: leftType },
    { plicity: 'implicit', value: rightType },
    { plicity: 'explicit', value: left },
    { plicity: 'explicit', value: right }
]);

const finiteFamilyType = (
    carrier: KernelExpression,
    length: KernelExpression
): KernelExpression => call('bridge_FiniteFamily', [
    { plicity: 'explicit', value: carrier },
    { plicity: 'explicit', value: length }
]);

const signedFactorType = (): KernelExpression => productType(
    packedElementType(),
    reference('bridge_Bool_grpd')
);

const signedFactor = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(face: AffineFormalCechFaceFactor<P, C, I>): KernelExpression => productPair(
    packedElementType(),
    reference('bridge_Bool_grpd'),
    packElement(face.factorType, face.factor),
    reference(face.face.sign === 1 ? 'bridge_bool_positive' : 'bridge_bool_negative')
);

export interface AffineFormalCechDegreeTerms<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly degree: number;
    readonly simplices: readonly AffineFormalCechSimplexLocalization<P, C, I>[];
    readonly faces: readonly AffineFormalCechFaceFactor<P, C, I>[];
    readonly chartCarrier: KernelExpression;
    readonly charts: AffineFormalFamilyTerms;
    readonly signedFactorCarrier: KernelExpression;
    readonly signedFactors: AffineFormalFamilyTerms;
    readonly presentationType: KernelExpression;
    readonly presentation: KernelExpression;
    readonly packedPresentation: KernelExpression;
}

export interface AffineFormalCechPresentation<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision: typeof ALGEBRA_FORMAL_CECH_PROFILE.revision;
    readonly overlap: AffineFormalCechOverlapTerms<P, C, I>;
    readonly packedCarrier: KernelExpression;
    readonly degrees: readonly AffineFormalCechDegreeTerms<P, C, I>[];
    readonly degreePresentations: AffineFormalFamilyTerms;
}

export function buildAffineFormalCechPresentation<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    overlap: AffineFormalCechOverlapTerms<P, C, I>
): AffineFormalCechPresentation<P, C, I> {
    const computationalDegrees = overlap.cover.cover.cochainDegrees;
    if (computationalDegrees.some((degree, index) => degree.degree !== index)) {
        return fail(
            'DEGREE_ORDER_MISMATCH',
            'formalCechPresentation.degrees',
            'Computational Cech degrees are not retained in ascending order'
        );
    }
    const sourceRing = overlap.cover.algebra.formalRing;
    const chartCarrier = call('bridge_Obj', [{
        plicity: 'explicit',
        value: call('bridge_AffineSpecBigSlice_cat', [{
            plicity: 'explicit',
            value: sourceRing
        }])
    }]);
    const factorCarrier = signedFactorType();
    const packedCarrier = packedElementType();
    const degrees = Object.freeze(computationalDegrees.map(computationalDegree => {
        const simplices = Object.freeze(overlap.simplices.filter(
            simplex => simplex.simplex.degree === computationalDegree.degree
        ));
        if (simplices.length !== computationalDegree.simplices.length ||
            simplices.some((simplex, index) =>
                simplex.simplex !== computationalDegree.simplices[index])) {
            return fail(
                'SIMPLEX_ORDER_MISMATCH',
                `formalCechPresentation.degrees[${computationalDegree.degree}].simplices`,
                'Formal simplex order differs from the computational cochain degree'
            );
        }
        const faces = Object.freeze(overlap.faces.filter(
            face => face.domain.simplex.degree === computationalDegree.degree
        ));
        if (faces.length !== computationalDegree.incomingFaces.length ||
            faces.some((face, index) =>
                face.face !== computationalDegree.incomingFaces[index])) {
            return fail(
                'FACE_ORDER_MISMATCH',
                `formalCechPresentation.degrees[${computationalDegree.degree}].faces`,
                'Formal face order differs from the computational cochain degree'
            );
        }
        const charts = buildAffineFormalFamily(
            chartCarrier,
            simplices.map(simplex => simplex.terms.chart)
        );
        const signedFactors = buildAffineFormalFamily(
            factorCarrier,
            faces.map(signedFactor)
        );
        const chartFamilyType = finiteFamilyType(chartCarrier, charts.length);
        const factorFamilyType = finiteFamilyType(
            factorCarrier,
            signedFactors.length
        );
        const presentationType = productType(chartFamilyType, factorFamilyType);
        const presentation = productPair(
            chartFamilyType,
            factorFamilyType,
            charts.family,
            signedFactors.family
        );
        return Object.freeze({
            degree: computationalDegree.degree,
            simplices,
            faces,
            chartCarrier,
            charts,
            signedFactorCarrier: factorCarrier,
            signedFactors,
            presentationType,
            presentation,
            packedPresentation: packElement(presentationType, presentation)
        });
    }));
    const degreePresentations = buildAffineFormalFamily(
        packedCarrier,
        degrees.map(degree => degree.packedPresentation)
    );
    return Object.freeze({
        profileRevision: ALGEBRA_FORMAL_CECH_PROFILE.revision,
        overlap,
        packedCarrier,
        degrees,
        degreePresentations
    });
}
