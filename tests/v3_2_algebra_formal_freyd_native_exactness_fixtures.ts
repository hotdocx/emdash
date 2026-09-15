/** Check exactness with its actual declaration dependencies, preserving their terms. */
import { KernelExpression } from '../src/v3_2/kernel';
import { CoreLfDeclarationEnvironment } from '../src/v3_2/lf_declarations';
import { serializeCoreLfKernelProbe } from '../src/v3_2/lf_probe';
import { FREYD_NATIVE_MODEL_PROBE_BINDINGS } from './v3_2_algebra_formal_freyd_native_model_fixtures';

function exactnessClosure(environment: CoreLfDeclarationEnvironment,
    assertions: Parameters<typeof serializeCoreLfKernelProbe>[0]['assertions'], allowDefinitions: boolean) {
    if (environment.intrinsicDefinitions.length !== 0) throw new Error('This exactness fixture expects the existing signature-only environment');
    const needed = new Set<string>();
    const visit = (term: KernelExpression): void => {
        switch (term.tag) {
            case 'universe': case 'bound': return;
            case 'reference': {
                if (term.namespace !== 'free' || needed.has(term.name)) return;
                const declaration = environment.lookup(term.name);
                if (!declaration) throw new Error('Missing exactness dependency ' + term.name);
                needed.add(term.name);
                visit(declaration.type);
                if (declaration.body) visit(declaration.body);
                return;
            }
            case 'meta': throw new Error('Exactness conformance must be meta-free');
            case 'application': term.arguments.forEach(a => visit(a.value)); return;
            case 'call': visit(term.callee); term.arguments.forEach(a => visit(a.value)); return;
            case 'pi': case 'lambda': visit(term.binder.type); visit(term.body); return;
        }
    };
    assertions.forEach(a => { visit(a.term); visit(a.type); });
    const declarations = environment.declarations.filter(d => needed.has(d.name));
    if (!allowDefinitions && declarations.some(d => d.body !== undefined)) throw new Error('This fixture must preserve body-free source declarations');
    let selected = CoreLfDeclarationEnvironment.empty();
    let pending: typeof declarations = [];
    for (const declaration of declarations) {
        if (declaration.body === undefined) { pending.push(declaration); continue; }
        if (declaration.transparency !== 'transparent') throw new Error('Point observation definitions must retain their checked bodies');
        selected = selected.extendOpaqueBatch(pending).extend(declaration);
        pending = [];
    }
    selected = selected.extendOpaqueBatch(pending);
    const bindings = Object.fromEntries(Object.entries(FREYD_NATIVE_MODEL_PROBE_BINDINGS).filter(([name]) => selected.lookup(name)));
    return { selected, bindings, count: declarations.length };
}

export function freydNativeExactnessProbe(environment: CoreLfDeclarationEnvironment,
    assertions: Parameters<typeof serializeCoreLfKernelProbe>[0]['assertions']) {
    const { selected, bindings, count } = exactnessClosure(environment, assertions, false);
    const source = serializeCoreLfKernelProbe({ environment: selected, assertions, externalFreeReferences: bindings }).source.replace(
        'require open emdash.emdash3_2;',
        'require open emdash.emdash3_2_commutative_algebra_freyd_chain_map_introduction;\n' +
        'require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_model_exactness_observations;');
    return { environment: selected, source, declarations: count };
}

/** The point-data owner is checked before the concrete matrix inputs. */
export function freydNativeExactnessPointProbe(environment: CoreLfDeclarationEnvironment,
    assertions: Parameters<typeof serializeCoreLfKernelProbe>[0]['assertions']) {
    const { selected, bindings, count } = exactnessClosure(environment, assertions, true);
    const source = serializeCoreLfKernelProbe({ environment: selected, assertions, externalFreeReferences: bindings }).source.replace(
        'require open emdash.emdash3_2;',
        'require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_model_point_exactness;\n' +
        'require open emdash.emdash3_2_commutative_algebra_freyd_chain_map_introduction;');
    return { environment: selected, source, declarations: count };
}
