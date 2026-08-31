/** Affine quasi-coherent module presentations and basic-open realizations. */

import {
    AlgebraElement,
    AlgebraParent,
    sameAlgebraParent
} from './algebra_parent';
import {
    AlgebraRuntimeSchema,
    defineAlgebraRuntimeSchema
} from './algebra_engine';
import { AlgebraGroebnerOptions } from './algebra_ideal';
import { AlgebraQuotientElement } from './algebra_quotient';
import {
    AlgebraAffineScheme,
    AlgebraBasicOpenAffineSubscheme,
    algebraAffineSchemeEquals,
    algebraBasicOpenAffineSubscheme
} from './algebra_affine_scheme';
import {
    algebraPresentedAlgebraEquals
} from './algebra_presented_algebra';
import {
    AlgebraPresentedAlgebraModule,
    AlgebraPresentedAlgebraModuleOptions
} from './algebra_presented_module';
import {
    AlgebraPresentedModuleBaseChange,
    algebraPresentedModuleBaseChange
} from './algebra_presented_module_base_change';

export const ALGEBRA_AFFINE_QUASICOHERENT_PROFILE = Object.freeze({
    revision: 'emdash-affine-quasicoherent-presentation-v1' as const,
    chartValue: 'module-base-change-along-retained-localization-map' as const,
    claimsSheafEquivalence: false as const,
    claimsDescentEffectiveness: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraAffineQuasiCoherentErrorCode =
    | 'FOREIGN_MODULE_ALGEBRA'
    | 'FOREIGN_BASIC_OPEN_CHART';

export class AlgebraAffineQuasiCoherentError extends Error {
    constructor(
        public readonly code: AlgebraAffineQuasiCoherentErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraAffineQuasiCoherentError';
    }
}

const fail = (
    code: AlgebraAffineQuasiCoherentErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraAffineQuasiCoherentError(code, path, message);
};

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

export interface AlgebraAffineQuasiCoherentPresentation<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-affine-quasicoherent-presentation';
    readonly scheme: AlgebraAffineScheme<P, C, I>;
    readonly module: AlgebraPresentedAlgebraModule<P, C, I>;
}

export function algebraAffineQuasiCoherentPresentation<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    scheme: AlgebraAffineScheme<P, C, I>,
    module: AlgebraPresentedAlgebraModule<P, C, I>
): AlgebraAffineQuasiCoherentPresentation<P, C, I> {
    if (!algebraPresentedAlgebraEquals(
        scheme.coordinateAlgebra,
        module.freeModule.algebra
    )) {
        return fail(
            'FOREIGN_MODULE_ALGEBRA',
            'quasicoherent.module',
            'Module is not defined over the affine coordinate algebra'
        );
    }
    return Object.freeze({
        kind: 'algebra-affine-quasicoherent-presentation',
        scheme,
        module
    });
}

export interface AlgebraAffineQuasiCoherentChart<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-affine-quasicoherent-chart';
    readonly presentation: AlgebraAffineQuasiCoherentPresentation<P, C, I>;
    readonly chart: AlgebraBasicOpenAffineSubscheme<P, C, I>;
    readonly baseChange: AlgebraPresentedModuleBaseChange<P, C, I>;
    readonly module: AlgebraPresentedAlgebraModule<P, C, I>;
}

export function algebraAffineQuasiCoherentOnBasicOpen<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    presentation: AlgebraAffineQuasiCoherentPresentation<P, C, I>,
    chart: AlgebraBasicOpenAffineSubscheme<P, C, I>,
    options: AlgebraPresentedAlgebraModuleOptions = {}
): AlgebraAffineQuasiCoherentChart<P, C, I> {
    if (!algebraAffineSchemeEquals(presentation.scheme, chart.ambient)) {
        return fail(
            'FOREIGN_BASIC_OPEN_CHART',
            'quasicoherentChart.chart',
            'Basic-open chart belongs to a foreign affine scheme'
        );
    }
    const baseChange = algebraPresentedModuleBaseChange(
        chart.chart.localization.canonicalMap,
        presentation.module,
        options
    );
    return Object.freeze({
        kind: 'algebra-affine-quasicoherent-chart',
        presentation,
        chart,
        baseChange,
        module: baseChange.target
    });
}

export interface AlgebraAffineQuasiCoherentBasicOpenOptions {
    readonly chart?: AlgebraGroebnerOptions;
    readonly module?: AlgebraPresentedAlgebraModuleOptions;
}

export function algebraAffineQuasiCoherentBasicOpen<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    presentation: AlgebraAffineQuasiCoherentPresentation<P, C, I>,
    element: AlgebraQuotientElement<P, C, I>,
    options: AlgebraAffineQuasiCoherentBasicOpenOptions = {}
): AlgebraAffineQuasiCoherentChart<P, C, I> {
    return algebraAffineQuasiCoherentOnBasicOpen(
        presentation,
        algebraBasicOpenAffineSubscheme(
            presentation.scheme,
            element,
            options.chart
        ),
        options.module
    );
}

export function algebraAffineQuasiCoherentPresentationSchema<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    scheme: AlgebraAffineScheme<P, C, I>,
    module: AlgebraPresentedAlgebraModule<P, C, I>
): AlgebraRuntimeSchema<AlgebraAffineQuasiCoherentPresentation<P, C, I>> {
    return defineAlgebraRuntimeSchema({
        id: `algebra.affine-quasicoherent/${module.identity.id}`,
        revision: ALGEBRA_AFFINE_QUASICOHERENT_PROFILE.revision,
        normalize(value: unknown, path: string) {
            if (
                !record(value) ||
                value.kind !== 'algebra-affine-quasicoherent-presentation' ||
                !record(value.module) ||
                !sameAlgebraParent(value.module as unknown as AlgebraParent, module)
            ) throw new Error(`affine quasi-coherent presentation expected at ${path}`);
            return algebraAffineQuasiCoherentPresentation(scheme, module);
        }
    });
}

export const serializeAlgebraAffineQuasiCoherentPresentation = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(presentation: AlgebraAffineQuasiCoherentPresentation<P, C, I>): string =>
    `${JSON.stringify({
        revision: ALGEBRA_AFFINE_QUASICOHERENT_PROFILE.revision,
        kind: presentation.kind,
        coordinateAlgebra: presentation.scheme.coordinateAlgebra.quotient.identity,
        module: presentation.module.identity
    })}\n`;

export const serializeAlgebraAffineQuasiCoherentChart = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(chart: AlgebraAffineQuasiCoherentChart<P, C, I>): string =>
    `${JSON.stringify({
        revision: ALGEBRA_AFFINE_QUASICOHERENT_PROFILE.revision,
        kind: chart.kind,
        presentationModule: chart.presentation.module.identity,
        localizedElement: chart.chart.chart.element.representative.terms.map(term => ({
            coefficient: chart.chart.chart.element.parent.polynomialRing
                .coefficientDomain.text(term.coefficient),
            exponents: term.monomial.exponents.map(String)
        })),
        coordinateAlgebra: chart.chart.scheme.coordinateAlgebra.quotient.identity,
        module: chart.module.identity
    })}\n`;
