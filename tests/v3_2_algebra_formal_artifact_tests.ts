/** Focused BRIDGE-EMISSION-6A deterministic artifact/probe tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    binderMode,
    kernelFree,
    kernelUniverse,
    provenance,
    sourceSpan
} from '../src/v3_2/kernel';
import { serializeCoreExpression } from '../src/v3_2/core_serialization';
import { CoreLfDeclarationEnvironment } from '../src/v3_2/lf_declarations';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import { algebraPolynomialIdeal } from '../src/v3_2/algebra_ideal';
import {
    algebraPolynomialOne,
    algebraPolynomialRing,
    algebraPolynomialSubtract,
    algebraPolynomialVariable
} from '../src/v3_2/algebra_polynomial';
import {
    algebraPolynomialQuotientRing,
    algebraQuotientElement
} from '../src/v3_2/algebra_quotient';
import { algebraPresentedAlgebra } from '../src/v3_2/algebra_presented_algebra';
import { algebraAffineScheme } from '../src/v3_2/algebra_affine_scheme';
import { algebraAffineCover } from '../src/v3_2/algebra_cech';
import { defineAffineFormalCoverRealization } from '../src/v3_2/algebra_formal_realization';
import { defineAffineFormalPolynomialReifier } from '../src/v3_2/algebra_formal_reifier';
import { defineAffineFormalLocalizationRealization } from
    '../src/v3_2/algebra_formal_localization';
import {
    buildAffineFormalCechOverlapTerms,
    defineAffineFormalCechSimplexLocalization
} from '../src/v3_2/algebra_formal_overlap';
import { buildAffineFormalCechPresentation } from '../src/v3_2/algebra_formal_cech';
import {
    ALGEBRA_FORMAL_ARTIFACT_PROFILE,
    AlgebraFormalArtifactError,
    AffineFormalBridgeArtifact,
    buildAffineFormalBridgeArtifact,
    createAffineFormalBridgeKernelProbe,
    serializeAffineFormalBridgeArtifactCanonicalJson,
    serializeAffineFormalBridgeKernelProbe
} from '../src/v3_2/algebra_formal_artifact';

const because = (detail: string) => provenance('derived', detail);

const artifactError = (code: AlgebraFormalArtifactError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraFormalArtifactError);
        assert.equal(error.code, code);
        return true;
    };

const coefficientTerm = (coefficient: typeof RATIONAL_DOMAIN.zero) => kernelFree(
    `formal_coefficient_${Array.from(new TextEncoder().encode(
        RATIONAL_DOMAIN.text(coefficient)
    )).map(byte => byte.toString(16)).join('')}`,
    because('coefficient')
);

const fixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const quotient = algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, []));
    const algebra = algebraPresentedAlgebra(quotient);
    const cover = algebraAffineCover(algebraAffineScheme(algebra), [
        algebraQuotientElement(quotient, x),
        algebraQuotientElement(
            quotient,
            algebraPolynomialSubtract(algebraPolynomialOne(ring), x)
        )
    ], 1);
    const source = defineAffineFormalPolynomialReifier({
        algebra,
        formalRing: kernelFree('formal_R', because('source ring')),
        generatorTerms: [kernelFree('formal_x', because('source generator'))],
        coefficientReifier: coefficientTerm,
        status: 'explicit-data'
    });
    const formalCover = defineAffineFormalCoverRealization({
        cover,
        algebra: source.realization,
        status: 'explicit-data',
        lawTerm: kernelFree('formal_cover_law', because('cover law'))
    });
    const simplices = cover.simplices.map((simplex, index) => {
        const localization = simplex.chart.chart.localization;
        const target = defineAffineFormalPolynomialReifier({
            algebra: localization.algebra,
            formalRing: kernelFree(`formal_S_${index}`, because('target ring')),
            generatorTerms: localization.extendedRing.variables.map((_, generator) =>
                kernelFree(
                    `formal_S_${index}_generator_${generator}`,
                    because('target generator')
                )
            ),
            coefficientReifier: coefficientTerm,
            status: 'explicit-data'
        });
        return defineAffineFormalCechSimplexLocalization(
            formalCover,
            simplex,
            defineAffineFormalLocalizationRealization({
                localization,
                source: source.realization,
                target: target.realization,
                formalMap: kernelFree(`formal_map_${index}`, because('map')),
                status: 'explicit-data',
                inverseLawTerm: kernelFree(
                    `formal_inverse_law_${index}`,
                    because('inverse law')
                ),
                universalTerm: kernelFree(
                    `formal_universal_${index}`,
                    because('universal localization')
                )
            })
        );
    });
    const overlap = buildAffineFormalCechOverlapTerms(
        formalCover,
        simplices,
        cover.simplices.map((simplex, simplexIndex) => simplex.faces.map(
            (_, faceIndex) => kernelFree(
                `formal_face_unit_${simplexIndex}_${faceIndex}`,
                because('face unit')
            )
        ))
    );
    const presentation = buildAffineFormalCechPresentation(overlap);
    return {
        ring,
        x,
        quotient,
        algebra,
        cover,
        presentation,
        artifact: buildAffineFormalBridgeArtifact('a1_cover', presentation)
    };
};

const declarationEnvironment = <P extends Parameters<
    typeof serializeAffineFormalBridgeArtifactCanonicalJson
>[0]>(
    artifact: P,
    omitted: ReadonlySet<string> = new Set()
): CoreLfDeclarationEnvironment => {
    let environment = CoreLfDeclarationEnvironment.empty();
    artifact.freeReferences.forEach((name, index) => {
        if (omitted.has(name)) return;
        const span = sourceSpan('tests/affine-formal-signatures.lp', index + 1, 1);
        const node = provenance('surface', `signature ${name}`, span);
        environment = environment.extend({
            name,
            type: kernelUniverse(node),
            mode: binderMode('explicit', 'object-only'),
            provenance: node
        });
    });
    return environment;
};

describe('v3.2 deterministic affine formal bridge artifact', () => {
    it('names every cover, simplex, face, degree, and whole output in order', () => {
        const artifact = fixture().artifact;
        assert.equal(artifact.outputs.length, 17);
        assert.deepEqual(artifact.outputs.slice(0, 4).map(output => output.name), [
            'a1_cover_cover',
            'a1_cover_cover_family',
            'a1_cover_simplex_0_localization',
            'a1_cover_simplex_0_chart'
        ]);
        assert.deepEqual(artifact.outputs.slice(-3).map(output => output.name), [
            'a1_cover_degree_0',
            'a1_cover_degree_1',
            'a1_cover_degrees'
        ]);
        assert.equal(new Set(artifact.outputs.map(output => output.name)).size, 17);
        assert.equal(artifact.outputs.every(output =>
            serializeCoreExpression(output.type).includes('bridge_tau')
        ), true);
        assert.equal(ALGEBRA_FORMAL_ARTIFACT_PROFILE.semanticStringTemplates,
            false);
    });

    it('uses only the referenced subset of reviewed active bindings', () => {
        const artifact = fixture().artifact;
        assert.equal(artifact.externalBindings.bridge_comm_ring_neg, undefined);
        assert.equal(
            artifact.externalBindings.bridge_comm_ring_zariski_cover_intro,
            'comm_ring_zariski_cover_intro'
        );
        assert.equal(
            artifact.externalBindings.bridge_CommRingLocalizationFactor,
            'CommRingLocalizationFactor'
        );
        assert.ok(artifact.inputReferences.includes('formal_R'));
        assert.ok(artifact.inputReferences.includes('formal_cover_law'));
        assert.equal(
            artifact.inputReferences.some(name => name.startsWith('bridge_')),
            false
        );
    });

    it('serializes canonical workspace data and Core terms deterministically', () => {
        const artifact = fixture().artifact;
        const first = serializeAffineFormalBridgeArtifactCanonicalJson(artifact);
        const second = serializeAffineFormalBridgeArtifactCanonicalJson(artifact);
        assert.equal(first, second);
        const parsed = JSON.parse(first) as {
            readonly artifactId: string;
            readonly outputs: readonly { readonly term: string }[];
        };
        assert.equal(parsed.artifactId, 'a1_cover');
        assert.equal(parsed.outputs.length, 17);
        assert.equal(
            parsed.outputs[0].term,
            serializeCoreExpression(artifact.outputs[0].term)
        );
    });

    it('emits a deterministic named LF probe through the declaration API', () => {
        const artifact = fixture().artifact;
        const environment = declarationEnvironment(artifact);
        const probe = createAffineFormalBridgeKernelProbe(artifact, environment);
        const first = serializeAffineFormalBridgeKernelProbe(
            artifact,
            environment,
            'tests/generated-affine-bridge.ts'
        );
        const second = serializeAffineFormalBridgeKernelProbe(
            artifact,
            environment,
            'tests/generated-affine-bridge.ts'
        );
        assert.equal(probe.assertions.length, 17);
        assert.equal(first.source, second.source);
        assert.equal(
            first.sourceMap.filter(entry => entry.kind === 'assertion').length,
            17
        );
        assert.equal(first.source.match(/assert ⊢/gu)?.length, 17);
        assert.match(first.source, /CommRingZariskiCoverPresentation/u);
        assert.match(first.source, /CommRingLocalizationFactor/u);
        assert.doesNotMatch(first.source, /symbol bridge_/u);
        assert.match(first.source, /symbol formal_R : TYPE/u);
    });

    it('fails before emission on missing signatures, inputs, or invalid IDs', () => {
        const artifact = fixture().artifact;
        const binding = Object.keys(artifact.externalBindings)[0];
        assert.throws(
            () => createAffineFormalBridgeKernelProbe(
                artifact,
                declarationEnvironment(artifact, new Set([binding]))
            ),
            artifactError('MISSING_BINDING_DECLARATION')
        );
        const input = artifact.inputReferences[0];
        assert.throws(
            () => createAffineFormalBridgeKernelProbe(
                artifact,
                declarationEnvironment(artifact, new Set([input]))
            ),
            artifactError('UNRESOLVED_REFERENCE')
        );
        assert.throws(
            () => buildAffineFormalBridgeArtifact(
                'not-valid-id',
                fixture().presentation
            ),
            artifactError('INVALID_ARTIFACT_ID')
        );
    });
});
