/** Explicit native whole-row and whole-δ interpretations at retained H objects. */
import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AlgebraFormalFreydModelConnectingPreparation, algebraFormalFreydConnectingRowMapTerm,
    assertAlgebraFormalFreydModelConnectingPreparationCurrent } from './algebra_formal_freyd_model_connecting_preparation';
import { algebraFormalFreydModelHomologyObservationBundle, algebraFormalFreydNativeModelHomologyObservationBundle,
    ALGEBRA_FORMAL_FREYD_MODEL_OBSERVATION_PROFILE, ALGEBRA_FORMAL_FREYD_NATIVE_MODEL_OBSERVATION_PROFILE } from './algebra_formal_freyd_model_observation';
import { algebraFormalFreydChainPairTerm, algebraFormalFreydMorphismTerm } from './algebra_formal_freyd_chain_pair';
import { algebraFormalFreydModelConnectingObservationTerm, algebraFormalFreydModelNormalityType,
    createFormalFreydModelConnectingProofEnvironment, FORMAL_FREYD_MODEL_CONNECTING_SIGNATURE_BINDINGS }
    from './algebra_formal_freyd_model_connecting_signatures';
import { algebraFormalFreydModelType, FORMAL_FREYD_MODEL_SIGNATURE_BINDINGS } from './algebra_formal_freyd_model_signatures';
import { FORMAL_FREYD_MODEL_MAP_SIGNATURE_BINDINGS } from './algebra_formal_freyd_model_map_signatures';
import { CoreLfDeclarationEnvironment } from './lf_declarations';
import { CoreLfScopedBuilder } from './lf_builder';
import { createCoreProofChecker } from './proof_checker';
import { KernelExpression, KernelReference, kernelExpressionEquals, kernelFree, provenance } from './kernel';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';
import { serializeCoreExpression } from './core_serialization';
import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';
import { algebraAlgorithmIdentity, defineAlgebraOperation, defineAlgebraRuntimeSchema } from './algebra_engine';
import { createAlgebraTypeScriptReferenceEngine, defineAlgebraReferenceImplementation } from './algebra_reference_engine';
import { AlgebraFormalDelegationError, defineAlgebraFormalComputationAdapter } from './algebra_formal_delegation';
import { encodeAlgebraFormalFreydLongExactData } from './algebra_formal_freyd_long_exact_encoding';
import { algebraFormalFreydNativeModelType, algebraFormalFreydNativeModelNormalityType, FORMAL_FREYD_NATIVE_MODEL_SIGNATURE_BINDINGS } from './algebra_formal_freyd_native_model_signatures';
import { FORMAL_FREYD_NATIVE_MODEL_OBSERVATION_SIGNATURE_BINDINGS } from './algebra_formal_freyd_native_model_observation_signatures';
import { createFormalFreydNativeConnectingProofEnvironment, algebraFormalFreydNativeConnectingObservationTerm, FORMAL_FREYD_NATIVE_CONNECTING_SIGNATURE_BINDINGS } from './algebra_formal_freyd_native_connecting_signatures';

type Point<P extends AlgebraParent, C extends AlgebraElement<P>, I> =
    ReturnType<typeof algebraFormalFreydModelHomologyObservationBundle<P, C, I>> |
    ReturnType<typeof algebraFormalFreydNativeModelHomologyObservationBundle<P, C, I>>;
export interface AlgebraFormalFreydConnectingRowLaws {
    readonly above: KernelExpression;
    readonly below: KernelExpression;
    readonly chain: KernelExpression;
    readonly exact: KernelExpression;
}

export const ALGEBRA_FORMAL_FREYD_MODEL_CONNECTING_OBSERVATION_PROFILE = Object.freeze({
    revision: 'emdash-formal-freyd-model-connecting-observations-v3' as const,
    classification: 'trusted-presentation-semantics' as const,
    requiresSuppliedNormality: true as const,
    constructsModel: false as const, claimsClosedQuotientEffectiveness: false as const,
    reselectsHomology: false as const, endpointCasts: false as const,
    endpointComparisons: 'original-selected-categorical-equivalences' as const,
    nativeWholeConnectingObservation: true as const,
    rowUniversality: 'native-whole-PQ' as const,
    payloadTransport: 'lossless-shared-json-table-v1' as const,
    replaysConnecting: false as const, addsCoreOwner: false as const
});

export const ALGEBRA_FORMAL_FREYD_NATIVE_CONNECTING_OBSERVATION_PROFILE = Object.freeze({
    ...ALGEBRA_FORMAL_FREYD_MODEL_CONNECTING_OBSERVATION_PROFILE,
    revision: 'emdash-formal-freyd-native-connecting-observations-v1' as const,
    endpointComparisons: 'native-column-input-comparisons' as const,
    requiresLegacyModel: false as const
});

interface ConnectingOwner<Profile extends { readonly revision: string }> {
    readonly profile: Profile;
    readonly pointProfile: string;
    readonly createEnvironment: () => CoreLfDeclarationEnvironment;
    readonly bindings: Readonly<Record<string, string>>;
    readonly modelType: (R: KernelExpression) => KernelExpression;
    readonly normalityType: (R: KernelExpression, M: KernelExpression) => KernelExpression;
    readonly rowOwner: string;
    readonly connectingTerm: (values: Readonly<Record<string, KernelExpression>>) => KernelExpression;
    readonly operationPrefix: string;
}
const legacyOwner = Object.freeze({
    profile: ALGEBRA_FORMAL_FREYD_MODEL_CONNECTING_OBSERVATION_PROFILE,
    pointProfile: ALGEBRA_FORMAL_FREYD_MODEL_OBSERVATION_PROFILE.revision,
    createEnvironment: () => createFormalFreydModelConnectingProofEnvironment([]),
    bindings: { ...FORMAL_FREYD_MODEL_SIGNATURE_BINDINGS, ...FORMAL_FREYD_MODEL_MAP_SIGNATURE_BINDINGS,
        ...FORMAL_FREYD_MODEL_CONNECTING_SIGNATURE_BINDINGS },
    modelType: algebraFormalFreydModelType, normalityType: algebraFormalFreydModelNormalityType,
    rowOwner: 'bridge_FreydHomologyModelNativeShortExact', connectingTerm: algebraFormalFreydModelConnectingObservationTerm,
    operationPrefix: 'proof-cas.freyd-model/'
});
const nativeOwner = Object.freeze({
    profile: ALGEBRA_FORMAL_FREYD_NATIVE_CONNECTING_OBSERVATION_PROFILE,
    pointProfile: ALGEBRA_FORMAL_FREYD_NATIVE_MODEL_OBSERVATION_PROFILE.revision,
    createEnvironment: () => createFormalFreydNativeConnectingProofEnvironment([]),
    bindings: { ...FORMAL_FREYD_NATIVE_MODEL_SIGNATURE_BINDINGS, ...FORMAL_FREYD_NATIVE_MODEL_OBSERVATION_SIGNATURE_BINDINGS,
        ...FORMAL_FREYD_NATIVE_CONNECTING_SIGNATURE_BINDINGS },
    modelType: algebraFormalFreydNativeModelType, normalityType: algebraFormalFreydNativeModelNormalityType,
    rowOwner: 'bridge_FreydAdjunctionModelRowShortExact', connectingTerm: algebraFormalFreydNativeConnectingObservationTerm,
    operationPrefix: 'proof-cas.freyd-native-model/'
});

function modelContext(environment: CoreLfDeclarationEnvironment, R: KernelExpression, M: KernelExpression,
    owner: ConnectingOwner<{ readonly revision: string }>) {
    if (M.tag !== 'reference' || M.namespace !== 'free') throw new Error('A named supplied coherent model is required');
    const model: KernelReference = Object.freeze(kernelFree(M.name, M.provenance));
    const expected = (() => {
        const signatures = owner.createEnvironment();
        return Object.keys(owner.bindings)
            .map(name => signatures.lookup(name)!);
    })();
    const check = (env: CoreLfDeclarationEnvironment) => {
        for (const signature of expected) {
            const value = env.lookup(signature.name);
            if (!value || value.body !== undefined || !kernelExpressionEquals(value.type, signature.type)) {
                throw new Error('Changed model connecting signature ' + signature.name);
            }
        }
        const declaration = env.lookup(model.name);
        if (!declaration || declaration.body !== undefined || !kernelExpressionEquals(declaration.type, owner.modelType(R))) {
            throw new Error('Changed supplied coherent model declaration');
        }
    };
    check(environment);
    return { model, check };
}

export function assertAlgebraFormalFreydModelConnectingContext(
    environment: CoreLfDeclarationEnvironment, R: KernelExpression, M: KernelExpression
): void {
    modelContext(environment, R, M, legacyOwner);
}

export function assertAlgebraFormalFreydNativeConnectingContext(
    environment: CoreLfDeclarationEnvironment, R: KernelExpression, M: KernelExpression
): void {
    modelContext(environment, R, M, nativeOwner);
}

function retainedInterpretation<T, R extends { readonly claimType: KernelExpression; readonly formalData: string },
    Profile extends { readonly revision: string }>(
    profile: Profile, id: string, realization: R, value: T, data: string, current: () => void,
    assertContext: (environment: CoreLfDeclarationEnvironment) => void, summary: string
) {
    // Keep the original snapshots and all current() checks. Only their wire
    // representation changes: nested JSON text must not expand at every
    // request/result/adoption layer. The existing table codec is lossless.
    const realizationData = encodeAlgebraFormalFreydLongExactData(realization.formalData);
    const retainedData = encodeAlgebraFormalFreydLongExactData(data);
    const schema = defineAlgebraRuntimeSchema<T>({ id: id + '/retained', revision: 'v2', normalize(candidate) {
        current(); if (candidate !== value) throw new Error('Foreign retained model value'); return value;
    } });
    const operation = defineAlgebraOperation({ id, revision: 'v2', input: schema, output: schema });
    const implementation = defineAlgebraReferenceImplementation({ operation,
        algorithm: algebraAlgorithmIdentity(id + '/interpret-retained', 'v2'), execute(input) { current(); return input; } });
    const engine = createAlgebraTypeScriptReferenceEngine({ id: id + '/engine', revision: 'v2', implementations: [implementation] });
    const adapter = defineAlgebraFormalComputationAdapter({ id,
        revision: profile.revision, operation,
        normalizeRealization(candidate: unknown) {
            if (candidate !== realization) throw new Error('Foreign model connecting realization');
            current(); return realization;
        }, serializeRealization: () => realizationData,
        acquire(goal) {
            assertContext(goal.document.environment); current();
            if (!kernelExpressionEquals(goal.target, realization.claimType)) throw new AlgebraFormalDelegationError(
                'CLAIM_TARGET_MISMATCH', 'modelConnecting.goal', 'Goal differs from this retained model interpretation');
            return value;
        }, serializeInput: () => retainedData,
        serializeOutput: candidate => { current(); if (candidate !== value) throw new Error('Retained model result changed'); return retainedData; },
        interpret: ({ goal, computed }) => {
            current();
            return computed.value === value ? { kind: 'claim' as const, claimType: goal.target, summary }
                : { kind: 'observation' as const, summary: 'Retained model result differs' };
        }
    });
    return Object.freeze({ profile, realization, adapter, engine });
}

const stable = (value: string) => {
    if (!/^[A-Za-z][A-Za-z0-9._/-]*$/u.test(value)) throw new Error('A stable model observation ID is required');
    return value;
};

/** Native whole P/Q row semantics remain supplied; raw zero equations do not derive this contract. */
export interface AlgebraFormalFreydShortExactObservationInput<P extends AlgebraParent, C extends AlgebraElement<P>, I> {
    readonly modelId: string; readonly observationId: string; readonly formalModel: KernelExpression;
    readonly prepared: AlgebraFormalFreydModelConnectingPreparation<P, C, I>;
    readonly index: 0 | 1 | 2 | 3; readonly environment: CoreLfDeclarationEnvironment;
    readonly laws: Omit<AlgebraFormalFreydConnectingRowLaws, 'exact'>;
}
export function algebraFormalFreydModelShortExactObservationBundle<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    input: AlgebraFormalFreydShortExactObservationInput<P, C, I>
) { return shortExactObservation(input, legacyOwner); }

export function algebraFormalFreydNativeShortExactObservationBundle<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    input: AlgebraFormalFreydShortExactObservationInput<P, C, I>
) { return shortExactObservation(input, nativeOwner); }

function shortExactObservation<P extends AlgebraParent, C extends AlgebraElement<P>, I,
    Profile extends { readonly revision: string }>(input: AlgebraFormalFreydShortExactObservationInput<P, C, I>, owner: ConnectingOwner<Profile>) {
    const prepared = input.prepared;
    assertAlgebraFormalFreydModelConnectingPreparationCurrent(prepared);
    if (!Number.isInteger(input.index) || input.index < 0 || input.index > 3) throw new Error('Invalid connecting row');
    const context = modelContext(input.environment, prepared.reifier.formalRing, input.formalModel, owner);
    const raw = prepared.rowPairs[input.index];
    const pair = algebraFormalFreydChainPairTerm(raw, input.laws.above, input.laws.below, input.laws.chain);
    const checker = createCoreProofChecker(input.environment);
    checker.check(checker.rootContext, pair.term, pair.type);
    const b = new CoreLfScopedBuilder(provenance('derived', 'retained model short-exact row')), L = formalFreydSpineLanguage(b);
    const R = b.embed(prepared.reifier.formalRing);
    const values = [R, b.embed(context.model), ...raw.presentations.map(t => b.embed(t)), b.embed(pair.above), b.embed(pair.below), b.embed(pair.term)];
    const claimType = b.lower(L.tau(b.call(b.free(owner.rowOwner), values.map((value, i) => ({ value,
        plicity: [0, 2, 3, 4].includes(i) ? 'implicit' as const : 'explicit' as const })))));
    const serialize = () => serializeCoreLfWorkspaceCanonicalJson({ prepared: prepared.formalData, row: input.index,
        model: serializeCoreExpression(context.model), claim: serializeCoreExpression(claimType) }, 'modelShortExactObservation');
    const formalData = serialize();
    const realization = Object.freeze({ prepared, index: input.index, pair, claimType, formalData });
    return retainedInterpretation(owner.profile, owner.operationPrefix + stable(input.modelId) + '/short-row/' + stable(input.observationId),
        realization, prepared.rows[input.index].triple, prepared.selectedData,
        () => {
            assertAlgebraFormalFreydModelConnectingPreparationCurrent(prepared);
            if (serialize() !== formalData) throw new Error('Changed model row interpretation');
        }, context.check,
        'explicitly interpret this retained row in the supplied native whole P/Q model; no closed capability is synthesized');
}

export interface AlgebraFormalFreydConnectingObservationInput<P extends AlgebraParent, C extends AlgebraElement<P>, I> {
    readonly observationId: string; readonly source: Point<P, C, I>; readonly target: Point<P, C, I>;
    readonly prepared: AlgebraFormalFreydModelConnectingPreparation<P, C, I>; readonly environment: CoreLfDeclarationEnvironment;
    readonly normality: KernelExpression; readonly rows: readonly AlgebraFormalFreydConnectingRowLaws[];
    readonly vertical: Readonly<Record<'am' | 'bm' | 'b0' | 'b1' | 'd1', KernelExpression>>;
    readonly squares: readonly { readonly upper: KernelExpression; readonly lower: KernelExpression }[];
    readonly upperZero: KernelExpression; readonly lowerZero: KernelExpression; readonly resultLaw: KernelExpression;
}
export function algebraFormalFreydModelConnectingObservationBundle<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    input: AlgebraFormalFreydConnectingObservationInput<P, C, I>
) { return connectingObservation(input, legacyOwner); }

export function algebraFormalFreydNativeConnectingObservationBundle<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    input: AlgebraFormalFreydConnectingObservationInput<P, C, I>
) { return connectingObservation(input, nativeOwner); }

function connectingObservation<P extends AlgebraParent, C extends AlgebraElement<P>, I,
    Profile extends { readonly revision: string }>(input: AlgebraFormalFreydConnectingObservationInput<P, C, I>, owner: ConnectingOwner<Profile>) {
    const prepared = input.prepared, s = input.source.realization, t = input.target.realization;
    if (input.rows.length !== 4 || input.squares.length !== 3) throw new Error('Four rows and three row maps are required');
    const currentInputs = () => {
        if (input.source.profile.revision !== owner.pointProfile || input.target.profile.revision !== owner.pointProfile) {
            throw new Error('Connecting requires matching native or legacy point observation profiles');
        }
        assertAlgebraFormalFreydModelConnectingPreparationCurrent(prepared);
        input.source.adapter.normalizeRealization(s, 'modelConnecting.source');
        input.target.adapter.normalizeRealization(t, 'modelConnecting.target');
        if (s.modelId !== t.modelId || !kernelExpressionEquals(s.formalModel, t.formalModel) ||
            s.actual.reifier !== prepared.reifier || t.actual.reifier !== prepared.reifier ||
            s.actual.selected !== prepared.selected.source || t.actual.selected !== prepared.selected.target) {
            throw new Error('Connecting requires one model and the original source/target H selections');
        }
    };
    currentInputs();
    const context = modelContext(input.environment, prepared.reifier.formalRing, s.formalModel, owner);
    const checker = createCoreProofChecker(input.environment);
    checker.check(checker.rootContext, input.normality, owner.normalityType(prepared.reifier.formalRing, context.model));
    const rowTerms = Object.freeze(prepared.rowPairs.map((row, i) => algebraFormalFreydChainPairTerm(row,
        input.rows[i].above, input.rows[i].below, input.rows[i].chain)));
    const components = [[input.vertical.am, input.vertical.bm, s.inputLaws.above],
        [t.inputLaws.above, input.vertical.b0, s.inputLaws.below], [t.inputLaws.below, input.vertical.b1, input.vertical.d1]];
    const rowMaps = Object.freeze(prepared.rowMaps.map((_, i) => algebraFormalFreydConnectingRowMapTerm(prepared, i as 0 | 1 | 2, {
        morphisms: [input.rows[i].above, input.rows[i].below, input.rows[i + 1].above, input.rows[i + 1].below, ...components[i]],
        ...input.squares[i]
    })));
    const upper = algebraFormalFreydChainPairTerm(prepared.upper, input.vertical.bm, input.vertical.b0, input.upperZero);
    const lower = algebraFormalFreydChainPairTerm(prepared.lower, input.vertical.b0, input.vertical.b1, input.lowerZero);
    const values: Record<string, KernelExpression> = { R: prepared.reifier.formalRing, M: context.model, N: input.normality,
        upper: upper.term, lower: lower.term, source_chain: s.pair.term, target_chain: t.pair.term };
    for (const [i, suffix] of ['m', '0', '1', '2'].entries()) {
        ['A', 'B', 'D'].forEach((name, j) => { values[name + suffix] = prepared.rowPairs[i].presentations[j]; });
        values['i' + suffix] = rowTerms[i].above; values['p' + suffix] = rowTerms[i].below;
        values['c' + suffix] = rowTerms[i].term; values['x' + suffix] = input.rows[i].exact;
    }
    for (const [i, suffix] of ['m', '0', '1'].entries()) {
        ['a', 'b', 'd'].forEach((name, j) => { values[name + suffix] = rowMaps[i].morphisms[j + 4]; });
        values[['fm', 'gm', 'jm'][i]] = rowMaps[i].term;
    }
    for (const [actual, expected] of [[values.dm, s.pair.above], [values.d0, s.pair.below],
        [values.a0, t.pair.above], [values.a1, t.pair.below]]) {
        if (!kernelExpressionEquals(actual, expected)) throw new Error('Connecting input changed an original H chain term');
    }
    const formalArrow = owner.connectingTerm(values);
    const b = new CoreLfScopedBuilder(provenance('derived', 'retained complete connecting arrow')), L = formalFreydSpineLanguage(b);
    const R = b.embed(prepared.reifier.formalRing), resultMap = algebraFormalFreydMorphismTerm(prepared.result, input.resultLaw);
    const nativeArrow = b.lower(L.call('bridge_freyd_raw_arrow_observation',
        [R, b.embed(s.nativePoint), b.embed(t.nativePoint), b.embed(resultMap)], 3));
    const observationType = b.lower(L.tau(L.call('bridge_FreydArrowObservation', [R])));
    checker.check(checker.rootContext, formalArrow, observationType); checker.check(checker.rootContext, nativeArrow, observationType);
    const claimType = b.lower(L.equality(L.call('bridge_FreydArrowObservation', [R]), b.embed(formalArrow), b.embed(nativeArrow)));
    const serialize = () => serializeCoreLfWorkspaceCanonicalJson({ observationId: input.observationId, prepared: prepared.formalData,
        source: s.formalData, target: t.formalData, expressions: [formalArrow, nativeArrow, claimType].map(v => serializeCoreExpression(v)) }, 'modelConnectingObservation');
    const formalData = serialize(), current = () => { currentInputs(); if (serialize() !== formalData) throw new Error('Changed connecting observation'); };
    const realization = Object.freeze({ prepared, source: s, target: t, rowTerms, rowMaps, values: Object.freeze(values),
        formalArrow, nativeArrow, observationType, claimType, formalData });
    return retainedInterpretation(owner.profile, owner.operationPrefix + stable(s.modelId) + '/connecting/' + stable(input.observationId),
        realization, prepared.selected, prepared.selectedData, current, context.check,
        'explicitly interpret the original whole δ at the retained H endpoints using the selected categorical comparisons; no H or connecting computation is reselected');
}
