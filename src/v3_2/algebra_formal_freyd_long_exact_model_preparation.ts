/** The retained H-point, induced-map and connecting inventory of one bounded result. */
import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AlgebraFormalFreydLongExactDelegationBundle } from './algebra_formal_freyd_long_exact';
import { AlgebraPolynomialFreydLongExactSnakeReferences } from './algebra_polynomial_freyd_long_exact_reference_operations';
import { AlgebraPolynomialFreydHomologyAt } from './algebra_polynomial_freyd_homology';
import { prepareAlgebraFormalFreydKernelChoiceProviders } from './algebra_formal_freyd_kernel_choice_providers';
import { createAlgebraPolynomialFreydKernelChoiceProviders } from './algebra_polynomial_selected_weak_pullback_provider';
import { defineAlgebraFormalFreydActualHomologyRealization } from './algebra_formal_freyd_actual_homology';
import { algebraFormalFreydRetainedHomologyPresentation } from './algebra_formal_freyd_model_observation';
import { prepareAlgebraFormalFreydModelMap } from './algebra_formal_freyd_model_map_preparation';
import { createFormalFreydRawWitnessProofEnvironment } from './algebra_formal_freyd_raw_witnesses';
import { FORMAL_FREYD_MODEL_MAP_SIGNATURE_BINDINGS } from './algebra_formal_freyd_model_map_signatures';
import { FORMAL_FREYD_MODEL_SIGNATURE_BINDINGS } from './algebra_formal_freyd_model_signatures';
import { createFormalFreydModelConnectingProofEnvironment, FORMAL_FREYD_MODEL_CONNECTING_SIGNATURE_BINDINGS } from './algebra_formal_freyd_model_connecting_signatures';
import { prepareAlgebraFormalFreydModelConnecting } from './algebra_formal_freyd_model_connecting_preparation';
import { AffineFormalZariskiInputDeclaration } from './algebra_formal_zariski_signatures';
import { binderMode, provenance, sourceSpan } from './kernel';
import { serializeCoreExpression } from './core_serialization';
import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';

/** Compose the existing private mirrors; introduce no new mathematical signature. */
export function createFormalFreydLongExactModelProofEnvironment(inputs: readonly AffineFormalZariskiInputDeclaration[]) {
    let environment = createFormalFreydRawWitnessProofEnvironment([]);
    const models = createFormalFreydModelConnectingProofEnvironment([]);
    for (const name of Object.keys({ ...FORMAL_FREYD_MODEL_SIGNATURE_BINDINGS, ...FORMAL_FREYD_MODEL_MAP_SIGNATURE_BINDINGS,
        ...FORMAL_FREYD_MODEL_CONNECTING_SIGNATURE_BINDINGS })) {
        environment = environment.extend(models.lookup(name)!);
    }
    inputs.forEach((input, index) => {
        environment = environment.extend({ ...input, mode: input.mode ?? binderMode('explicit', 'functorial'),
            provenance: provenance('surface', 'bounded model input ' + input.name,
                sourceSpan('generated/bounded-model-inputs.ts', index + 1, 1)) });
    });
    return environment;
}

/** Read the stored degrees/maps/interiors, never call a homology or universal algorithm. */
export function algebraFormalFreydLongExactModelInventory<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    bundle: AlgebraFormalFreydLongExactDelegationBundle<P, C, I>, selected: AlgebraPolynomialFreydLongExactSnakeReferences<P, C, I>
) {
    const result = selected.result, reifier = bundle.reifier;
    if (result.degrees.length !== result.topDegree + 3 || result.interior.length !== 3 * (result.topDegree + 1) ||
        result.terms.length !== result.interior.length + 2 || result.arrows.length !== result.terms.length - 1 ||
        result.windows.length !== result.topDegree + 2) {
        throw new Error('The bounded model inventory must retain every degree and displayed interior');
    }
    const point = (key: string, kind: 'degree' | 'interior', degree: number, role: 'A' | 'B' | 'C',
        position: number | undefined, homology: AlgebraPolynomialFreydHomologyAt<P, C, I>) => {
        const providers = prepareAlgebraFormalFreydKernelChoiceProviders({ reifier,
            selected: createAlgebraPolynomialFreydKernelChoiceProviders({ id: 'model/' + key,
                ring: result.sequence.ring, kernel: homology.cycles }) });
        const actual = defineAlgebraFormalFreydActualHomologyRealization({ reifier, selected: homology, providers });
        const nativePoint = algebraFormalFreydRetainedHomologyPresentation(actual);
        return Object.freeze({ key, kind, degree, role, position, actual, nativePoint });
    };
    const degreePoints = result.degrees.flatMap((entry, index) => {
        if (entry.degree !== index - 1) throw new Error('A retained degree label changed');
        return (['A', 'B', 'C'] as const).map(role => {
            const view = entry[role];
            const complex = role === 'A' ? result.sequence.subcomplex : role === 'B' ? result.sequence.middleComplex : result.sequence.quotientComplex;
            if (view.degree !== entry.degree || view.complex !== complex) throw new Error('A retained degree/complex selection changed');
            return point('degree/' + entry.degree + '/' + role, 'degree', entry.degree, role, undefined, view.homology);
        });
    });
    result.terms.forEach((term, position) => {
        if (term.position !== position || term.view !== result.degrees[term.degree + 1]?.[term.role]) {
            throw new Error('A displayed term must retain its original degree view');
        }
    });
    const interiorPoints = result.interior.map((entry, index) => {
        if (entry.term !== result.terms[index + 1] || entry.term.position !== index + 1 ||
            entry.pair.dNext !== result.arrows[index] || entry.pair.d !== result.arrows[index + 1] ||
            entry.exactness.homology.pair !== entry.pair || !entry.exactness.exact) {
            throw new Error('A model interior must retain its displayed pair and actual homology');
        }
        return point('interior/' + entry.term.position, 'interior', entry.term.degree, entry.term.role,
            entry.term.position, entry.exactness.homology);
    });
    const maps = Object.freeze(result.degrees.flatMap(entry => (['inclusion', 'projection'] as const).map(role => {
        const map = entry[role], from = role === 'inclusion' ? 'A' : 'B', to = role === 'inclusion' ? 'B' : 'C';
        if (map.chainMap.source !== entry[from].homology || map.chainMap.target !== entry[to].homology) {
            throw new Error('An induced map must retain its original degree homologies');
        }
        const position = entry.degree < 0 || entry.degree > result.topDegree ? undefined :
            1 + 3 * (result.topDegree - entry.degree) + (role === 'inclusion' ? 0 : 1);
        if (position !== undefined && map.homologyMap !== result.arrows[position]) {
            throw new Error('A displayed induced map must retain its original degree selection');
        }
        return Object.freeze({ key: 'degree/' + entry.degree + '/' + role, degree: entry.degree, role, position,
            sourceKey: 'degree/' + entry.degree + '/' + from, targetKey: 'degree/' + entry.degree + '/' + to,
            prepared: prepareAlgebraFormalFreydModelMap({ reifier, selected: map }) });
    })));
    const points = Object.freeze([...degreePoints, ...interiorPoints]);
    const connectings = Object.freeze(result.windows.map((window, degree) => {
        const connecting = window.connecting, position = 3 * (result.topDegree + 1 - degree);
        if (window.degree !== degree || window.sequence !== result.sequence ||
            connecting.degree !== degree || connecting.sequence !== result.sequence ||
            connecting.source !== result.degrees[degree + 1].C.homology ||
            connecting.target !== result.degrees[degree].A.homology ||
            connecting.homologyMap !== result.arrows[position] ||
            result.terms[position].view.homology !== connecting.source ||
            result.terms[position + 1].view.homology !== connecting.target) {
            throw new Error('A connecting window must retain its degree H selections and displayed arrow');
        }
        return Object.freeze({ key: 'degree/' + degree + '/connecting', degree, position,
            sourceKey: 'degree/' + degree + '/C', targetKey: 'degree/' + (degree - 1) + '/A',
            prepared: prepareAlgebraFormalFreydModelConnecting({ reifier, selected: connecting }) });
    }));
    const data = serializeCoreLfWorkspaceCanonicalJson({
        points: points.map(p => ({ key: p.key, kind: p.kind, degree: p.degree, role: p.role, position: p.position ?? null,
            actual: p.actual.formalData, native: serializeCoreExpression(p.nativePoint) })),
        maps: maps.map(m => ({ key: m.key, position: m.position ?? null,
            source: m.sourceKey, target: m.targetKey, actual: m.prepared.formalData })),
        connectings: connectings.map(m => ({ key: m.key, position: m.position,
            source: m.sourceKey, target: m.targetKey, actual: m.prepared.formalData }))
    }, 'boundedModelInventory');
    return Object.freeze({ points, maps, connectings, data });
}

const preparations = new WeakMap<object, () => void>();

/** Fix all coefficients before building the document's immutable environment. */
export function prepareAlgebraFormalFreydLongExactModel<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    bundle: AlgebraFormalFreydLongExactDelegationBundle<P, C, I>
) {
    const inventory = algebraFormalFreydLongExactModelInventory(bundle, bundle.selected);
    const prepared = Object.freeze({ bundle, inventory, equationsData: bundle.equationsData });
    preparations.set(prepared, () => {
        if (prepared.equationsData !== bundle.equationsData ||
            algebraFormalFreydLongExactModelInventory(bundle, bundle.selected).data !== inventory.data) {
            throw new Error('The prepared bounded model inventory changed');
        }
    });
    return prepared;
}

export type AlgebraFormalFreydLongExactModelPreparation<P extends AlgebraParent, C extends AlgebraElement<P>, I> =
    ReturnType<typeof prepareAlgebraFormalFreydLongExactModel<P, C, I>>;

export function assertAlgebraFormalFreydLongExactModelPreparationCurrent(prepared: object): void {
    const current = preparations.get(prepared);
    if (!current) throw new Error('Use the issued bounded model preparation');
    current();
}
