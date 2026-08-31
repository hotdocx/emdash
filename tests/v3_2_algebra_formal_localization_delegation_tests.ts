/** Focused ALC-INVERSE/UNIVERSAL localization delegation tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    RATIONAL_DOMAIN,
    affineFormalCommRingHomType,
    affineFormalCommRingType,
    affineFormalRingElementType,
    algebraFormalLocalizationDelegationBundle,
    algebraPolynomialIdeal,
    algebraPolynomialQuotientRing,
    algebraPolynomialRing,
    algebraPolynomialVariable,
    algebraPresentedAlgebra,
    algebraPrincipalLocalization,
    algebraQuotientElement,
    appendAlgebraFormalAssumption,
    buildAffineFormalLocalizationTerms,
    coreProofPlanHole,
    createAffineFormalLocalizationProofEnvironment,
    createAlgebraComputationGraphBuilder,
    createAlgebraFormalAssumptionSource,
    createAlgebraTypeScriptReferenceEngine,
    createCoreProofArtifactFingerprint,
    defineAffineFormalLocalizationRealization,
    defineAffineFormalPolynomialReifier,
    defineAlgebraFormalLocalizationDelegationRealization,
    executeAlgebraComputationGraph,
    kernelFree,
    provenance,
    realizeAdoptedAffineFormalLocalization,
    runAlgebraFormalWorkflow,
    serializeAlgebraPrincipalLocalization,
    trustAlgebraFormalWorkflow
} from '../src/v3_2';

const because = (detail: string) => provenance('surface', detail);
const hex = (value: string): string => Array.from(new TextEncoder().encode(value))
    .map(byte => byte.toString(16).padStart(2, '0')).join('');

const fixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const quotient = algebraPolynomialQuotientRing(
        algebraPolynomialIdeal(ring, [])
    );
    const algebra = algebraPresentedAlgebra(quotient);
    const element = algebraQuotientElement(quotient, x);
    const localization = algebraPrincipalLocalization(algebra, element);
    const formalSource = kernelFree('formal_localization_R', because('source'));
    const formalTarget = kernelFree('formal_localization_L', because('target'));
    const formalX = kernelFree('formal_localization_x', because('source x'));
    const formalTargetX = kernelFree(
        'formal_localization_target_x',
        because('target x')
    );
    const formalInverse = kernelFree(
        'formal_localization_inverse',
        because('target inverse')
    );
    const sourceCoefficients = new Map<string, ReturnType<typeof kernelFree>>();
    const targetCoefficients = new Map<string, ReturnType<typeof kernelFree>>();
    const sourceReifier = defineAffineFormalPolynomialReifier({
        algebra,
        formalRing: formalSource,
        generatorTerms: [formalX],
        coefficientReifier: coefficient => {
            const text = RATIONAL_DOMAIN.text(coefficient);
            let term = sourceCoefficients.get(text);
            if (term === undefined) {
                term = kernelFree(
                    `formal_localization_source_coefficient_${hex(text)}`,
                    because(`source coefficient ${text}`)
                );
                sourceCoefficients.set(text, term);
            }
            return term;
        },
        status: 'trusted-computation'
    });
    const targetReifier = defineAffineFormalPolynomialReifier({
        algebra: localization.algebra,
        formalRing: formalTarget,
        generatorTerms: [formalTargetX, formalInverse],
        coefficientReifier: coefficient => {
            const text = RATIONAL_DOMAIN.text(coefficient);
            let term = targetCoefficients.get(text);
            if (term === undefined) {
                term = kernelFree(
                    `formal_localization_target_coefficient_${hex(text)}`,
                    because(`target coefficient ${text}`)
                );
                targetCoefficients.set(text, term);
            }
            return term;
        },
        status: 'trusted-computation'
    });
    const formalMap = kernelFree(
        'formal_localization_map',
        because('formal map')
    );
    const trusted = defineAffineFormalLocalizationRealization({
        localization,
        source: sourceReifier.realization,
        target: targetReifier.realization,
        formalMap,
        status: 'trusted-computation'
    });
    const realization =
        defineAlgebraFormalLocalizationDelegationRealization(trusted);
    const sourceElementType = affineFormalRingElementType(formalSource);
    const targetElementType = affineFormalRingElementType(formalTarget);
    const environment = createAffineFormalLocalizationProofEnvironment([
        { name: formalSource.name, type: affineFormalCommRingType() },
        { name: formalTarget.name, type: affineFormalCommRingType() },
        { name: formalX.name, type: sourceElementType },
        { name: formalTargetX.name, type: targetElementType },
        { name: formalInverse.name, type: targetElementType },
        ...[...sourceCoefficients.values()].map(term => ({
            name: term.name,
            type: sourceElementType
        })),
        ...[...targetCoefficients.values()].map(term => ({
            name: term.name,
            type: targetElementType
        })),
        {
            name: formalMap.name,
            type: affineFormalCommRingHomType(formalSource, formalTarget)
        }
    ]);
    const bundle = algebraFormalLocalizationDelegationBundle(algebra);
    const engine = createAlgebraTypeScriptReferenceEngine({
        id: 'proof-cas.localization-reference',
        revision: 'v1',
        implementations: bundle.operations.implementations
    });
    return {
        algebra,
        localization,
        trusted,
        realization,
        environment,
        bundle,
        engine
    };
};

const document = (
    environment: ReturnType<typeof fixture>['environment'],
    target: ReturnType<typeof kernelFree> | ReturnType<typeof fixture>['realization']['inverseClaimType'],
    id: string
) => Object.freeze({
    moduleId: 'proof.cas.localization',
    declarationId: id,
    environment,
    type: target,
    plan: coreProofPlanHole(id, {
        provenance: because(`hole ${id}`),
        expectation: { contextDepth: 0, target }
    }),
    provenance: because(`root ${id}`),
    fingerprint: createCoreProofArtifactFingerprint({
        source: {
            id: `tests/${id}.surface.ts`,
            sha256: `sha256:${id.includes('inverse')
                ? '1'.repeat(64)
                : '2'.repeat(64)}`
        },
        profileSha256: `sha256:${'3'.repeat(64)}`
    })
});

describe('ALC-INVERSE/UNIVERSAL principal-localization delegation', () => {
    it('adopts inverse and property with distinct classifications', async () => {
        const value = fixture();
        let source = createAlgebraFormalAssumptionSource({
            moduleId: 'proof.cas.localization-assumptions',
            sourceId: 'generated/localization-assumptions.ts',
            baseEnvironment: value.environment
        });
        const inverseRun = await runAlgebraFormalWorkflow({
            document: document(
                source.environment,
                value.realization.inverseClaimType,
                'localization-inverse-law'
            ),
            goalId: 'localization-inverse-law',
            adapter: value.bundle.inverseAdapter,
            realization: value.realization,
            engine: value.engine
        });
        const inverseAdoption = trustAlgebraFormalWorkflow({
            run: inverseRun,
            assumptionName: 'computed_localization_inverse_law',
            decision: {
                kind: 'trust-exact-algebra-computation',
                evidence: 'adopt exact adjoined-inverse equation'
            }
        });
        source = appendAlgebraFormalAssumption({
            source,
            adoption: inverseAdoption,
            classification: 'computed-equation'
        });
        const propertyRun = await runAlgebraFormalWorkflow({
            document: document(
                source.environment,
                value.realization.propertyClaimType,
                'localization-property'
            ),
            goalId: 'localization-property',
            adapter: value.bundle.propertyAdapter,
            realization: value.realization,
            engine: value.engine
        });
        const propertyAdoption = trustAlgebraFormalWorkflow({
            run: propertyRun,
            assumptionName: 'trusted_localization_property',
            decision: {
                kind: 'trust-exact-algebra-computation',
                evidence: 'trust selected localization presentation semantics'
            }
        });
        source = appendAlgebraFormalAssumption({
            source,
            adoption: propertyAdoption,
            classification: 'trusted-presentation-semantics'
        });
        const explicit = realizeAdoptedAffineFormalLocalization({
            realization: value.realization,
            inverseLaw: source.entries[0].reference,
            property: source.entries[1].reference
        });
        const terms = buildAffineFormalLocalizationTerms(explicit);

        assert.deepEqual(source.entries.map(entry => entry.classification), [
            'computed-equation',
            'trusted-presentation-semantics'
        ]);
        assert.equal(explicit.formalUnitAvailable, true);
        assert.equal(explicit.formalLocalizationAvailable, true);
        assert.match(terms.localization.tag, /call/u);
        assert.equal(value.trusted.formalLocalizationAvailable, false);
    });

    it('agrees with graph execution on the selected whole localization',
        async () => {
            const value = fixture();
            const run = await runAlgebraFormalWorkflow({
                document: document(
                    value.environment,
                    value.realization.inverseClaimType,
                    'graph-localization-inverse'
                ),
                goalId: 'graph-localization-inverse',
                adapter: value.bundle.inverseAdapter,
                realization: value.realization,
                engine: value.engine
            });
            const builder = createAlgebraComputationGraphBuilder(
                'proof-cas.localization.graph',
                'v1'
            );
            const input = builder.input(
                'element',
                value.bundle.operations.localize.input
            );
            const output = builder.operation(
                'localization',
                value.bundle.operations.localize,
                input
            );
            const graph = builder.build([{ id: 'result', value: output }]);
            const executed = await executeAlgebraComputationGraph({
                graph,
                engine: value.engine,
                inputs: [{
                    id: 'element',
                    value: value.localization.element
                }]
            });

            assert.equal(
                serializeAlgebraPrincipalLocalization(run.result.computed.value),
                serializeAlgebraPrincipalLocalization(
                    executed.outputs[0].value as typeof value.localization
                )
            );
        }
    );

    it('retains target distinction and rejects selected-output drift',
        async () => {
            const value = fixture();
            assert.notDeepEqual(
                value.realization.inverseClaimType,
                value.realization.propertyClaimType
            );
            const changed = Object.freeze({
                ...value.realization,
                selectedOutputData: 'changed localization\n'
            });
            const run = await runAlgebraFormalWorkflow({
                document: document(
                    value.environment,
                    changed.inverseClaimType,
                    'changed-localization'
                ),
                goalId: 'changed-localization',
                adapter: value.bundle.inverseAdapter,
                realization: changed,
                engine: value.engine
            });
            assert.equal(run.result.interpretation.kind, 'observation');
        }
    );
});
