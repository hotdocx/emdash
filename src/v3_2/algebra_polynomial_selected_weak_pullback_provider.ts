/** Executable factor providers bound to retained polynomial weak pullbacks. */

import { AlgebraElement, AlgebraParent, sameAlgebraParent } from './algebra_parent';
import { AlgebraPolynomialRing, algebraPolynomialText } from './algebra_polynomial';
import { AlgebraPolynomialFreeModule, AlgebraPolynomialModuleVector } from './algebra_polynomial_module';
import {
    AlgebraPolynomialModuleMap, algebraPolynomialModuleMapCompose,
    algebraPolynomialModuleMapIsZero, algebraPolynomialModuleMapNegate
} from './algebra_polynomial_presentation';
import { algebraPolynomialModuleMapEquals, algebraPolynomialPresentationRelationMap } from './algebra_polynomial_presentation_morphism';
import {
    AlgebraPolynomialWeakKernelFactorOptions, AlgebraPolynomialWeakKernelFactorization,
    algebraPolynomialWeakKernelFactor
} from './algebra_polynomial_weak_kernel';
import {
    AlgebraPolynomialWeakPullback, AlgebraPolynomialWeakPullbackFactorization,
    algebraPolynomialWeakPullbackFactor
} from './algebra_polynomial_weak_pullback';
import { AlgebraPolynomialFreydKernel } from './algebra_polynomial_freyd_kernel';
import { serializeAlgebraPolynomialFreydKernel } from './algebra_formal_freyd_preabelian';
import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';

export const ALGEBRA_POLYNOMIAL_SELECTED_WEAK_PULLBACK_PROVIDER_PROFILE = Object.freeze({
    revision: 'emdash-selected-polynomial-weak-pullback-provider-v1' as const,
    algorithmRevision: 'retained-original-syzygy-basis-factor-v1' as const,
    selection: 'actual-retained-weak-pullback' as const,
    factorDomain: 'every-admissible-test-over-the-represented-native-ring' as const,
    formalAuthority: 'requires-explicit-trusted-presentation-semantics' as const,
    resourceFailuresAreNegativeMathematics: false as const,
    reselectsWeakKernels: false as const,
    performsIo: false as const
});

export type AlgebraSelectedWeakPullbackProviderErrorCode =
    | 'INVALID_SELECTION' | 'FOREIGN_RING' | 'FOREIGN_CHOICE' | 'UNKNOWN_PROVIDER' | 'STALE_PROVIDER';

export class AlgebraSelectedWeakPullbackProviderError extends Error {
    constructor(public readonly code: AlgebraSelectedWeakPullbackProviderErrorCode, message: string) {
        super(message);
        this.name = 'AlgebraSelectedWeakPullbackProviderError';
    }
}

const fail = (code: AlgebraSelectedWeakPullbackProviderErrorCode, message: string): never => {
    throw new AlgebraSelectedWeakPullbackProviderError(code, message);
};

type FreeModule<P extends AlgebraParent, C extends AlgebraElement<P>, I> = AlgebraPolynomialFreeModule<P, C, I>;
type Map<P extends AlgebraParent, C extends AlgebraElement<P>, I> = AlgebraPolynomialModuleMap<P, C, I>;
type Pullback<P extends AlgebraParent, C extends AlgebraElement<P>, I> = AlgebraPolynomialWeakPullback<P, C, I>;

const moduleData = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(value: FreeModule<P, C, I>): unknown => ({
    identity: value.identity, rank: value.rank, termOrder: value.termOrder,
    schreyer: value.schreyerData === undefined ? null : {
        target: moduleData(value.schreyerData.targetModule),
        leadingTerms: value.schreyerData.leadingTerms.map(term => ({
            position: term.position, coefficient: value.ring.coefficientDomain.text(term.coefficient),
            exponents: term.monomial.exponents.map(String)
        }))
    }
});
const vectorData = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(value: AlgebraPolynomialModuleVector<P, C, I>) =>
    value.components.map(algebraPolynomialText);
const mapData = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(value: Map<P, C, I>) => ({
    source: moduleData(value.source), target: moduleData(value.target), columns: value.columns.map(vectorData)
});

/** Includes the actual division basis, not just the finite annihilation equation. */
export function serializeAlgebraPolynomialSelectedWeakPullback<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    value: Pullback<P, C, I>
): string {
    return serializeCoreLfWorkspaceCanonicalJson({
        ring: { identity: value.left.source.ring.identity, coefficientDomain: value.left.source.ring.coefficientDomain.parent.identity,
            variables: value.left.source.ring.variables, monomialOrder: value.left.source.ring.monomialOrder },
        object: moduleData(value.object), left: mapData(value.left), right: mapData(value.right),
        difference: mapData(value.difference), combined: mapData(value.combinedMorphism),
        projectionLeft: mapData(value.projectionLeft), projectionRight: mapData(value.projectionRight),
        compatibilityLeft: mapData(value.compatibilityLeft), compatibilityRight: mapData(value.compatibilityRight),
        weakKernel: { object: moduleData(value.weakKernel.object), map: mapData(value.weakKernel.map),
            morphism: mapData(value.weakKernel.morphism), annihilation: mapData(value.weakKernel.annihilation),
            syzygyModule: moduleData(value.weakKernel.syzygies.module),
            divisionBasis: value.weakKernel.syzygies.basis.basis.map(vectorData),
            basisModule: moduleData(value.weakKernel.syzygies.basis.submodule.module) }
    }, 'selectedPolynomialWeakPullback');
}

const selectionReferences = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(value: Pullback<P, C, I>): readonly object[] => [
    value.object, value.left, value.right, value.biproduct, value.difference, value.combinedMorphism,
    value.projectionLeft, value.projectionRight, value.weakKernel, value.weakKernel.syzygies,
    value.weakKernel.syzygies.basis, value.left.source.ring, value.left.source.ring.coefficientDomain
];

const validateSelection = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    value: Pullback<P, C, I>, ring: AlgebraPolynomialRing<P, C, I>
): void => {
    if (!value || value.kind !== 'algebra-polynomial-weak-pullback' || !value.compatible ||
        value.claimsUniqueLifts !== false || value.object !== value.weakKernel.object ||
        value.combinedMorphism !== value.weakKernel.morphism || value.difference !== value.weakKernel.map) {
        fail('INVALID_SELECTION', 'A whole retained weak pullback and its original weak-kernel data are required');
    }
    const maps = [value.left, value.right, value.difference, value.combinedMorphism, value.projectionLeft, value.projectionRight];
    if (maps.some(map => !sameAlgebraParent(map.source.ring, ring) || !sameAlgebraParent(map.target.ring, ring))) {
        fail('FOREIGN_RING', 'Selected weak pullback must belong to the represented native ring');
    }
    if (!sameAlgebraParent(value.left.target, value.right.target) ||
        !sameAlgebraParent(value.biproduct.left, value.left.source) ||
        !sameAlgebraParent(value.biproduct.right, value.right.source) ||
        !sameAlgebraParent(value.combinedMorphism.source, value.object) ||
        !sameAlgebraParent(value.combinedMorphism.target, value.biproduct.object) ||
        value.object.rank !== value.weakKernel.syzygies.basis.basis.length) {
        fail('INVALID_SELECTION', 'Selected ranks, cospan, biproduct, and division basis do not agree');
    }
    const negativeRight = algebraPolynomialModuleMapNegate(value.right);
    const expectedColumns = [...value.left.columns, ...negativeRight.columns];
    if (value.difference.columns.length !== expectedColumns.length ||
        value.difference.columns.some((column, index) => JSON.stringify(vectorData(column)) !== JSON.stringify(vectorData(expectedColumns[index]))) ||
        !algebraPolynomialModuleMapEquals(value.projectionLeft,
            algebraPolynomialModuleMapCompose(value.biproduct.projectionLeft, value.combinedMorphism)) ||
        !algebraPolynomialModuleMapEquals(value.projectionRight,
            algebraPolynomialModuleMapCompose(value.biproduct.projectionRight, value.combinedMorphism)) ||
        !algebraPolynomialModuleMapEquals(algebraPolynomialModuleMapCompose(value.left, value.projectionLeft),
            algebraPolynomialModuleMapCompose(value.right, value.projectionRight)) ||
        !algebraPolynomialModuleMapIsZero(algebraPolynomialModuleMapCompose(value.difference, value.combinedMorphism)) ||
        value.combinedMorphism.columns.some((column, index) =>
            JSON.stringify(vectorData(column)) !== JSON.stringify(vectorData(value.weakKernel.syzygies.basis.basis[index])))) {
        fail('INVALID_SELECTION', 'Selected projections or syzygy columns differ from the original difference construction');
    }
};

export interface AlgebraPolynomialSelectedWeakPullbackProvider<P extends AlgebraParent, C extends AlgebraElement<P>, I> {
    readonly profileRevision: typeof ALGEBRA_POLYNOMIAL_SELECTED_WEAK_PULLBACK_PROVIDER_PROFILE.revision;
    readonly id: string;
    readonly algorithmRevision: typeof ALGEBRA_POLYNOMIAL_SELECTED_WEAK_PULLBACK_PROVIDER_PROFILE.algorithmRevision;
    readonly ring: AlgebraPolynomialRing<P, C, I>;
    readonly selected: Pullback<P, C, I>;
    /** Exact canonical fingerprint; this is not a mathematical certificate. */
    readonly selectionData: string;
    readonly factorCombined: (test: Map<P, C, I>, options?: AlgebraPolynomialWeakKernelFactorOptions) => AlgebraPolynomialWeakKernelFactorization<P, C, I>;
    readonly factorPair: (left: Map<P, C, I>, right: Map<P, C, I>, options?: AlgebraPolynomialWeakKernelFactorOptions) => AlgebraPolynomialWeakPullbackFactorization<P, C, I>;
}

const issuedProviders = new WeakMap<object, () => void>();

export function assertAlgebraPolynomialSelectedWeakPullbackProviderCurrent<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    provider: AlgebraPolynomialSelectedWeakPullbackProvider<P, C, I>, expected?: Pullback<P, C, I>
): void {
    const validate = issuedProviders.get(provider);
    if (!validate) fail('UNKNOWN_PROVIDER', 'Use an issued selected weak-pullback provider handle');
    if (expected !== undefined && expected !== provider.selected) fail('FOREIGN_CHOICE', 'Provider belongs to another retained weak pullback');
    validate();
}

/** The callback consumes the retained basis; it never invokes weak-kernel selection. */
export function createAlgebraPolynomialSelectedWeakPullbackProvider<P extends AlgebraParent, C extends AlgebraElement<P>, I>(input: {
    readonly id: string; readonly ring: AlgebraPolynomialRing<P, C, I>; readonly selected: Pullback<P, C, I>;
}): AlgebraPolynomialSelectedWeakPullbackProvider<P, C, I> {
    if (!/^[A-Za-z][A-Za-z0-9._/-]*$/u.test(input.id)) fail('INVALID_SELECTION', 'A stable selected-provider ID is required');
    const { selected, ring } = input;
    validateSelection(selected, ring);
    const selectionData = serializeAlgebraPolynomialSelectedWeakPullback(selected);
    const references = selectionReferences(selected);
    const current = () => {
        if (selectionReferences(selected).some((value, index) => value !== references[index]) ||
            serializeAlgebraPolynomialSelectedWeakPullback(selected) !== selectionData) {
            fail('STALE_PROVIDER', 'Retained weak-pullback data or factor basis changed after provider preparation');
        }
        validateSelection(selected, ring);
    };
    const provider: AlgebraPolynomialSelectedWeakPullbackProvider<P, C, I> = Object.freeze({
        profileRevision: ALGEBRA_POLYNOMIAL_SELECTED_WEAK_PULLBACK_PROVIDER_PROFILE.revision,
        id: input.id, algorithmRevision: ALGEBRA_POLYNOMIAL_SELECTED_WEAK_PULLBACK_PROVIDER_PROFILE.algorithmRevision,
        ring, selected, selectionData,
        factorCombined(test: Map<P, C, I>, options: AlgebraPolynomialWeakKernelFactorOptions = {}) {
            current();
            const result = algebraPolynomialWeakKernelFactor(selected.weakKernel, test, options);
            current();
            return result;
        },
        factorPair(left: Map<P, C, I>, right: Map<P, C, I>, options: AlgebraPolynomialWeakKernelFactorOptions = {}) {
            current();
            const result = algebraPolynomialWeakPullbackFactor(selected, left, right, options);
            current();
            return result;
        }
    });
    issuedProviders.set(provider, current);
    return provider;
}

/** Preserve the two literal stages and the original native kernel object. */
export function createAlgebraPolynomialFreydKernelChoiceProviders<P extends AlgebraParent, C extends AlgebraElement<P>, I>(input: {
    readonly id: string; readonly ring: AlgebraPolynomialRing<P, C, I>; readonly kernel: AlgebraPolynomialFreydKernel<P, C, I>;
}) {
    const { kernel } = input;
    const first = createAlgebraPolynomialSelectedWeakPullbackProvider({ id: input.id + '/first', ring: input.ring, selected: kernel.firstWeakPullback });
    const second = createAlgebraPolynomialSelectedWeakPullbackProvider({ id: input.id + '/second', ring: input.ring, selected: kernel.secondWeakPullback });
    const snapshot = serializeAlgebraPolynomialFreydKernel(kernel);
    const current = () => {
        assertAlgebraPolynomialSelectedWeakPullbackProviderCurrent(first, kernel.firstWeakPullback);
        assertAlgebraPolynomialSelectedWeakPullbackProviderCurrent(second, kernel.secondWeakPullback);
        if (serializeAlgebraPolynomialFreydKernel(kernel) !== snapshot) fail('STALE_PROVIDER', 'The retained native kernel changed');
        if (first.selected.left !== kernel.morphism.map || second.selected.left !== first.selected.projectionLeft ||
            kernel.object.ambient !== first.selected.object || kernel.embedding.source !== kernel.object ||
            kernel.embedding.map !== first.selected.projectionLeft ||
            !algebraPolynomialModuleMapEquals(first.selected.right, algebraPolynomialPresentationRelationMap(kernel.morphism.target)) ||
            !algebraPolynomialModuleMapEquals(second.selected.right, algebraPolynomialPresentationRelationMap(kernel.morphism.source)) ||
            !algebraPolynomialModuleMapEquals(algebraPolynomialPresentationRelationMap(kernel.object), second.selected.projectionLeft)) {
            fail('FOREIGN_CHOICE', 'Kernel providers must use both original stages and the original relation presentation');
        }
    };
    current();
    return Object.freeze({ kernel, first, second, selectionData: snapshot, assertCurrent: current });
}

export type AlgebraPolynomialFreydKernelChoiceProviders<P extends AlgebraParent, C extends AlgebraElement<P>, I> =
    ReturnType<typeof createAlgebraPolynomialFreydKernelChoiceProviders<P, C, I>>;
