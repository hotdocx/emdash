/** Model-independent preparation of one already selected rational CAS result. */
import { AlgebraRational, AlgebraRationalField, AlgebraRationalInput, RATIONAL_DOMAIN } from './algebra_exact';
import { algebraPolynomialIdeal } from './algebra_ideal';
import { algebraPolynomialQuotientRing } from './algebra_quotient';
import { algebraPresentedAlgebra } from './algebra_presented_algebra';
import { AffineFormalPolynomialReifier, defineAffineFormalPolynomialReifier } from './algebra_formal_reifier';
import { AlgebraPolynomialRing } from './algebra_polynomial';
import { AlgebraPolynomialFreydLongExactSnakeReferences } from './algebra_polynomial_freyd_long_exact_reference_operations';
import { algebraFormalFreydLongExactDelegationBundle } from './algebra_formal_freyd_long_exact';
import { prepareAlgebraFormalFreydLongExactHomology } from './algebra_formal_freyd_long_exact_homology';
import { prepareAlgebraFormalFreydRawWitnesses } from './algebra_formal_freyd_raw_witnesses';
import { prepareAlgebraFormalFreydLongExactModel } from './algebra_formal_freyd_long_exact_model_preparation';
import { kernelFree, provenance, sourceSpan } from './kernel';

export type AlgebraFormalFreydRationalSelectedResult = AlgebraPolynomialFreydLongExactSnakeReferences<
    AlgebraRationalField, AlgebraRational, AlgebraRationalInput>;

/** Shared coefficient preparation; each consumer collects its inventory before sealing. */
export function prepareAlgebraFormalFreydRationalInventory<T>(input: {
    readonly backend: { readonly id: string; readonly revision: string };
    readonly ring: AlgebraPolynomialRing<AlgebraRationalField, AlgebraRational, AlgebraRationalInput>;
    readonly namePrefix: string;
    readonly prepare: (reifier: AffineFormalPolynomialReifier<AlgebraRationalField, AlgebraRational, AlgebraRationalInput>) => T;
}) {
    if (typeof input.namePrefix !== 'string' || !/^[A-Za-z][A-Za-z0-9_]{0,127}$/u.test(input.namePrefix)) {
        throw new Error('A simple identifier of at most 128 characters is required for the model name prefix');
    }
    const ring = input.ring;
    if (ring.coefficientDomain !== RATIONAL_DOMAIN) {
        throw new Error('This model context supports the registered rational polynomial coefficient domain only');
    }
    const prefix = input.namePrefix;
    const p = provenance('surface', 'supplied rational Freyd context ' + input.backend.id + '@' + input.backend.revision,
        sourceSpan('generated/' + prefix + '-model-inputs.ts', 1, 1));
    const formalRing = kernelFree(prefix + '_R', p);
    const generatorTerms = Object.freeze(ring.variables.map((_, i) => kernelFree(prefix + '_g_' + i, p)));
    const formalModel = kernelFree(prefix + '_model', p);
    const normality = kernelFree(prefix + '_normality', p);
    const coefficientTerms = new Map<string, ReturnType<typeof kernelFree>>();
    let sealed = false;
    const reifier = defineAffineFormalPolynomialReifier({
        algebra: algebraPresentedAlgebra(algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, []))),
        formalRing, generatorTerms,
        coefficientReifier: coefficient => {
            const key = RATIONAL_DOMAIN.text(coefficient);
            const previous = coefficientTerms.get(key);
            if (previous) return previous;
            if (sealed) throw new Error('Rational coefficient ' + key + ' was not included in this prepared model context');
            const encoded = [...key].map(c => c.codePointAt(0)!.toString(16)).join('_');
            const term = kernelFree(prefix + '_c_' + encoded, p);
            coefficientTerms.set(key, term);
            return term;
        },
        status: 'trusted-computation'
    });
    const inventory = input.prepare(reifier);
    sealed = true;
    const coefficients = Object.freeze([...coefficientTerms].sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0)
        .map(([value, term]) => Object.freeze({ value, term })));
    return Object.freeze({ formalRing, generatorTerms, formalModel, normality, coefficients,
        reifier, inventory });
}

/** Preserve the existing LES preparation and its original selection inventories. */
export function prepareAlgebraFormalFreydRationalInputs(input: {
    readonly backend: { readonly id: string; readonly revision: string };
    readonly selected: AlgebraFormalFreydRationalSelectedResult;
    readonly namePrefix: string;
    readonly anchorId?: string;
}) {
    const { inventory, ...context } = prepareAlgebraFormalFreydRationalInventory({
        ...input, ring: input.selected.result.sequence.ring,
        prepare: reifier => {
            const bundle = algebraFormalFreydLongExactDelegationBundle({ reifier, selected: input.selected, anchorId: input.anchorId });
            return { bundle, preparedHomology: prepareAlgebraFormalFreydLongExactHomology(bundle),
                preparedRaw: prepareAlgebraFormalFreydRawWitnesses(bundle), preparedModel: prepareAlgebraFormalFreydLongExactModel(bundle) };
        }
    });
    return Object.freeze({ ...context, ...inventory });
}
