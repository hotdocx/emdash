/** Computational weak kernels of polynomial finite-free module maps. */

import {
    AlgebraElement,
    AlgebraParent,
    sameAlgebraParent
} from './algebra_parent';
import {
    AlgebraComputationContextInput,
    normalizeAlgebraComputationContext
} from './algebra_engine';
import {
    ALGEBRA_POLYNOMIAL_MODULE_PROFILE,
    AlgebraPolynomialModuleDivision,
    AlgebraPolynomialModuleGroebnerOptions,
    AlgebraPolynomialModuleOriginalSyzygies,
    algebraPolynomialFreeModule,
    algebraPolynomialModuleDivide,
    algebraPolynomialModuleLeadingTerm,
    algebraPolynomialModuleOriginalSyzygies,
    algebraPolynomialModuleVector,
    algebraPolynomialSubmodule
} from './algebra_polynomial_module';
import {
    AlgebraPolynomialModuleMap,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleMapCompose,
    algebraPolynomialModuleMapIsZero
} from './algebra_polynomial_presentation';
import {
    algebraPolynomialModuleMapEquals
} from './algebra_polynomial_presentation_morphism';

export const ALGEBRA_POLYNOMIAL_WEAK_KERNEL_PROFILE = Object.freeze({
    revision: 'emdash-algebra-polynomial-weak-kernel-v1' as const,
    notion: 'selected-nonunique-factorization' as const,
    syzygies: 'original-ordered-columns' as const,
    nativeAuthority: 'typescript-module-groebner' as const,
    externalOracle: 'optional-differential-only' as const,
    claimsKernel: false as const,
    claimsAbelianStructure: false as const,
    performsIo: false as const
});

export type AlgebraPolynomialWeakKernelErrorCode =
    | 'INVALID_WEAK_KERNEL'
    | 'FOREIGN_TEST_MAP'
    | 'NON_ANNIHILATED_TEST'
    | 'FACTORIZATION_FAILED'
    | 'INVALID_FACTORIZATION_LIMIT'
    | 'CANCELLED';

export class AlgebraPolynomialWeakKernelError extends Error {
    constructor(
        public readonly code: AlgebraPolynomialWeakKernelErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraPolynomialWeakKernelError';
    }
}

const fail = (
    code: AlgebraPolynomialWeakKernelErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraPolynomialWeakKernelError(code, path, message);
};

export interface AlgebraPolynomialWeakKernel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-weak-kernel';
    readonly map: AlgebraPolynomialModuleMap<P, C, I>;
    readonly syzygies: AlgebraPolynomialModuleOriginalSyzygies<P, C, I>;
    readonly object: ReturnType<typeof algebraPolynomialFreeModule<P, C, I>>;
    readonly morphism: AlgebraPolynomialModuleMap<P, C, I>;
    readonly annihilation: AlgebraPolynomialModuleMap<P, C, I>;
    readonly annihilates: true;
    readonly claimsUniqueLifts: false;
}

export interface AlgebraPolynomialWeakKernelFactorization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-weak-kernel-factorization';
    readonly weakKernel: AlgebraPolynomialWeakKernel<P, C, I>;
    readonly test: AlgebraPolynomialModuleMap<P, C, I>;
    readonly testAnnihilation: AlgebraPolynomialModuleMap<P, C, I>;
    readonly divisions: readonly AlgebraPolynomialModuleDivision<P, C, I>[];
    readonly lift: AlgebraPolynomialModuleMap<P, C, I>;
    readonly reconstruction: AlgebraPolynomialModuleMap<P, C, I>;
    readonly reconstructs: true;
    readonly reductionSteps: number;
}

export interface AlgebraPolynomialWeakKernelFactorOptions {
    readonly maximumReductionSteps?: number;
    readonly context?: AlgebraComputationContextInput;
}

/** Compute K -> source(F) from the complete original-column syzygy basis. */
export function algebraPolynomialModuleMapWeakKernel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    map: AlgebraPolynomialModuleMap<P, C, I>,
    options: AlgebraPolynomialModuleGroebnerOptions = {}
): AlgebraPolynomialWeakKernel<P, C, I> {
    const syzygies = algebraPolynomialModuleOriginalSyzygies(
        algebraPolynomialSubmodule(map.target, map.columns),
        options
    );
    const object = algebraPolynomialFreeModule(
        map.source.ring,
        syzygies.basis.basis.length,
        'term-over-position'
    );
    const morphism = algebraPolynomialModuleMap(
        object,
        map.source,
        syzygies.basis.basis.map(relation =>
            algebraPolynomialModuleVector(map.source, relation.components)
        )
    );
    const annihilation = algebraPolynomialModuleMapCompose(map, morphism);
    if (!algebraPolynomialModuleMapIsZero(annihilation)) {
        return fail(
            'INVALID_WEAK_KERNEL',
            'weakKernel.annihilation',
            'Selected original-column syzygies do not annihilate the map'
        );
    }
    return Object.freeze({
        kind: 'algebra-polynomial-weak-kernel',
        map,
        syzygies,
        object,
        morphism,
        annihilation,
        annihilates: true,
        claimsUniqueLifts: false
    });
}

/** Select and verify one lift of an annihilated test map through K. */
export function algebraPolynomialWeakKernelFactor<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    weakKernel: AlgebraPolynomialWeakKernel<P, C, I>,
    test: AlgebraPolynomialModuleMap<P, C, I>,
    options: AlgebraPolynomialWeakKernelFactorOptions = {}
): AlgebraPolynomialWeakKernelFactorization<P, C, I> {
    const maximumReductionSteps = options.maximumReductionSteps ??
        ALGEBRA_POLYNOMIAL_MODULE_PROFILE.maximumReductionStepsPerPair;
    if (!Number.isSafeInteger(maximumReductionSteps) || maximumReductionSteps <= 0) {
        return fail(
            'INVALID_FACTORIZATION_LIMIT',
            'weakKernelFactor.maximumReductionSteps',
            'Weak-kernel factorization limit must be a positive safe integer'
        );
    }
    const context = normalizeAlgebraComputationContext(options.context);
    if (!sameAlgebraParent(test.target, weakKernel.map.source)) {
        return fail(
            'FOREIGN_TEST_MAP',
            'weakKernelFactor.test',
            'Test map must target the source of the weak-kernel map'
        );
    }
    const testAnnihilation = algebraPolynomialModuleMapCompose(
        weakKernel.map,
        test
    );
    if (!algebraPolynomialModuleMapIsZero(testAnnihilation)) {
        return fail(
            'NON_ANNIHILATED_TEST',
            'weakKernelFactor.test',
            'Test map is not annihilated by the selected map'
        );
    }
    const divisions = test.columns.map((column, index) => {
        if (context.cancellation?.requested()) {
            return fail(
                'CANCELLED',
                `weakKernelFactor.test.columns[${index}]`,
                context.cancellation.reason?.() ??
                    'Weak-kernel factorization cancelled'
            );
        }
        context.onProgress?.({
            phase: 'algebra.polynomial-weak-kernel.factor',
            completed: index + 1,
            total: test.columns.length
        });
        const relation = algebraPolynomialModuleVector(
            weakKernel.syzygies.module,
            column.components
        );
        const division = algebraPolynomialModuleDivide(
            relation,
            weakKernel.syzygies.basis.basis,
            maximumReductionSteps
        );
        if (algebraPolynomialModuleLeadingTerm(division.remainder) !== undefined) {
            return fail(
                'FACTORIZATION_FAILED',
                `weakKernelFactor.test.columns[${index}]`,
                'An annihilated test column is absent from the syzygy basis'
            );
        }
        return division;
    });
    const lift = algebraPolynomialModuleMap(
        test.source,
        weakKernel.object,
        divisions.map(division => algebraPolynomialModuleVector(
            weakKernel.object,
            division.quotients
        ))
    );
    const reconstruction = algebraPolynomialModuleMapCompose(
        weakKernel.morphism,
        lift
    );
    if (!algebraPolynomialModuleMapEquals(reconstruction, test)) {
        return fail(
            'FACTORIZATION_FAILED',
            'weakKernelFactor.reconstruction',
            'Selected weak-kernel lift does not reconstruct the test map'
        );
    }
    return Object.freeze({
        kind: 'algebra-polynomial-weak-kernel-factorization',
        weakKernel,
        test,
        testAnnihilation,
        divisions: Object.freeze(divisions),
        lift,
        reconstruction,
        reconstructs: true,
        reductionSteps: divisions.reduce(
            (total, division) => total + division.steps,
            0
        )
    });
}
