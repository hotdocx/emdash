/** Focused BRIDGE-CONFORMANCE-7A concrete affine-cover probes. */

import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import { KernelReference, kernelFree, provenance } from '../src/v3_2/kernel';
import { checkLambdapiProbe } from '../src/v3_2/probe';
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
import { buildAffineFormalBridgeArtifact } from
    '../src/v3_2/algebra_formal_artifact';
import {
    ALGEBRA_FORMAL_CONFORMANCE_PROFILE,
    AlgebraFormalConformanceError,
    AffineFormalConformanceDeclaration,
    affineFormalCommRingType,
    affineFormalCoverLawType,
    affineFormalFaceUnitType,
    affineFormalIdentityMap,
    affineFormalInverseLawType,
    affineFormalLocalizationPropertyType,
    affineFormalLocalizationUniversalFromProperty,
    affineFormalRingElementType,
    serializeAffineFormalConformanceProbe
} from '../src/v3_2/algebra_formal_conformance';

const because = (detail: string) => provenance('derived', detail);

const conformanceError = (code: AlgebraFormalConformanceError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraFormalConformanceError);
        assert.equal(error.code, code);
        return true;
    };

const encoded = (value: string): string => Array.from(new TextEncoder().encode(value))
    .map(byte => byte.toString(16).padStart(2, '0')).join('');

interface ConformanceCaseSpec {
    readonly id: string;
    readonly kind: 'binary' | 'ternary';
    readonly variables: readonly string[];
    readonly maximumDegree: number;
}

const binarySpec: ConformanceCaseSpec = {
    id: 'a1_binary',
    kind: 'binary',
    variables: ['x'],
    maximumDegree: 1
};

const ternarySpec: ConformanceCaseSpec = {
    id: 'a2_ternary',
    kind: 'ternary',
    variables: ['x', 'y'],
    maximumDegree: 2
};

const buildCase = (spec: ConformanceCaseSpec) => {
    const ring = algebraPolynomialRing(
        RATIONAL_DOMAIN,
        spec.variables,
        'lex'
    );
    const variables = spec.variables.map((_, index) =>
        algebraPolynomialVariable(ring, index)
    );
    const quotient = algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, []));
    const algebra = algebraPresentedAlgebra(quotient);
    const one = algebraPolynomialOne(ring);
    const polynomials = spec.kind === 'binary'
        ? [variables[0], algebraPolynomialSubtract(one, variables[0])]
        : [
            variables[0],
            variables[1],
            algebraPolynomialSubtract(
                algebraPolynomialSubtract(one, variables[0]),
                variables[1]
            )
        ];
    const elements = polynomials.map(
        polynomial => algebraQuotientElement(quotient, polynomial)
    );
    const cover = algebraAffineCover(
        algebraAffineScheme(algebra),
        elements,
        spec.maximumDegree
    );
    const formalRing = kernelFree(`${spec.id}_R`, because('formal ring'));
    const sourceGenerators = variables.map((_, index) =>
        kernelFree(`${spec.id}_generator_${index}`, because('source generator'))
    );
    const coefficientTerms = new Map<string, KernelReference>();
    const coefficientTerm = (coefficient: typeof RATIONAL_DOMAIN.zero) => {
        const text = RATIONAL_DOMAIN.text(coefficient);
        const existing = coefficientTerms.get(text);
        if (existing !== undefined) return existing;
        const term = kernelFree(
            `${spec.id}_coefficient_${encoded(text)}`,
            because(`coefficient ${text}`)
        );
        coefficientTerms.set(text, term);
        return term;
    };
    const source = defineAffineFormalPolynomialReifier({
        algebra,
        formalRing,
        generatorTerms: sourceGenerators,
        coefficientReifier: coefficientTerm,
        status: 'explicit-data'
    });
    const coverLaw = kernelFree(`${spec.id}_cover_law`, because('cover law'));
    const formalCover = defineAffineFormalCoverRealization({
        cover,
        algebra: source.realization,
        status: 'explicit-data',
        lawTerm: coverLaw
    });
    const inverseLaws: KernelReference[] = [];
    const properties: KernelReference[] = [];
    const localizationRealizations = cover.simplices.map((simplex, index) => {
        const localization = simplex.chart.chart.localization;
        const targetGenerators = localization.extendedRing.variables.map(
            (_, generator) => kernelFree(
                `${spec.id}_simplex_${index}_generator_${generator}`,
                because('target generator')
            )
        );
        const target = defineAffineFormalPolynomialReifier({
            algebra: localization.algebra,
            formalRing,
            generatorTerms: targetGenerators,
            coefficientReifier: coefficientTerm,
            status: 'explicit-data'
        });
        const inverseLaw = kernelFree(
            `${spec.id}_inverse_law_${index}`,
            because('inverse law')
        );
        const property = kernelFree(
            `${spec.id}_localization_property_${index}`,
            because('localization property')
        );
        inverseLaws.push(inverseLaw);
        properties.push(property);
        return defineAffineFormalLocalizationRealization({
            localization,
            source: source.realization,
            target: target.realization,
            formalMap: affineFormalIdentityMap(formalRing),
            status: 'explicit-data',
            inverseLawTerm: inverseLaw,
            universalTerm: affineFormalLocalizationUniversalFromProperty(property)
        });
    });
    const simplices = cover.simplices.map((simplex, index) =>
        defineAffineFormalCechSimplexLocalization(
            formalCover,
            simplex,
            localizationRealizations[index]
        )
    );
    const faceUnits: KernelReference[][] = cover.simplices.map(
        (simplex, simplexIndex) => simplex.faces.map((_, faceIndex) => kernelFree(
            `${spec.id}_face_unit_${simplexIndex}_${faceIndex}`,
            because('face unit')
        ))
    );
    const overlap = buildAffineFormalCechOverlapTerms(
        formalCover,
        simplices,
        faceUnits
    );
    const presentation = buildAffineFormalCechPresentation(overlap);
    const artifact = buildAffineFormalBridgeArtifact(spec.id, presentation);
    const elementType = affineFormalRingElementType(formalRing);
    const elementTerms = [
        ...sourceGenerators,
        ...localizationRealizations.flatMap(realization =>
            realization.target.algebra.quotient.polynomialRing.variables.map(
                (_, generator) => kernelFree(
                    `${spec.id}_simplex_${localizationRealizations.indexOf(realization)}_` +
                        `generator_${generator}`,
                    because('target generator declaration')
                )
            )
        ),
        ...coefficientTerms.values()
    ];
    const elementNames = [...new Map(elementTerms.map(term => [term.name, term])).values()]
        .filter(term => artifact.inputReferences.includes(term.name));
    const declarations: AffineFormalConformanceDeclaration[] = [
        {
            name: formalRing.name,
            type: affineFormalCommRingType(),
            label: 'selected formal commutative ring'
        },
        ...elementNames.map(term => ({
            name: term.name,
            type: elementType,
            label: 'selected formal ring element'
        })),
        {
            name: coverLaw.name,
            type: affineFormalCoverLawType(formalCover),
            label: 'formal unimodular cover law'
        },
        ...localizationRealizations.flatMap((realization, index) => [
            {
                name: inverseLaws[index].name,
                type: affineFormalInverseLawType(realization),
                label: `formal inverse law ${index}`
            },
            {
                name: properties[index].name,
                type: affineFormalLocalizationPropertyType(realization),
                label: `supplied formal localization property ${index}`
            }
        ]),
        ...overlap.faces.map((face, index) => ({
            name: face.invertsDomainElement.tag === 'reference'
                ? face.invertsDomainElement.name
                : (() => { throw new Error('Expected a face-unit reference'); })(),
            type: affineFormalFaceUnitType(face),
            label: `formal face-denominator unit ${index}`
        }))
    ];
    const serialized = serializeAffineFormalConformanceProbe({
        artifact,
        declarations,
        sourceId: `tests/${spec.id}.surface.ts`
    });
    return Object.freeze({
        spec,
        ring,
        quotient,
        algebra,
        cover,
        formalCover,
        localizationRealizations,
        overlap,
        presentation,
        artifact,
        declarations: Object.freeze(declarations),
        serialized
    });
};

describe('v3.2 concrete affine formal bridge conformance', () => {
    it('serializes the binary affine-line and ternary affine-plane covers', () => {
        const binary = buildCase(binarySpec);
        const ternary = buildCase(ternarySpec);
        assert.equal(binary.cover.elements.length, 2);
        assert.equal(binary.cover.simplices.length, 3);
        assert.equal(binary.artifact.outputs.length, 17);
        assert.equal(ternary.cover.elements.length, 3);
        assert.deepEqual(
            ternary.cover.cochainDegrees.map(degree => degree.simplices.length),
            [3, 3, 1]
        );
        assert.equal(ternary.artifact.outputs.length, 47);
        assert.equal(
            binary.serialized.source,
            buildCase(binarySpec).serialized.source
        );
        assert.equal(
            ternary.serialized.source,
            buildCase(ternarySpec).serialized.source
        );
        assert.equal(ALGEBRA_FORMAL_CONFORMANCE_PROFILE.typedInputDeclarations,
            true);
    });

    it('fails closed when a typed input is missing or extraneous', () => {
        const value = buildCase(binarySpec);
        assert.throws(
            () => serializeAffineFormalConformanceProbe({
                artifact: value.artifact,
                declarations: value.declarations.slice(1)
            }),
            conformanceError('MISSING_INPUT_DECLARATION')
        );
        assert.throws(
            () => serializeAffineFormalConformanceProbe({
                artifact: value.artifact,
                declarations: [
                    ...value.declarations,
                    {
                        name: 'unused_formal_input',
                        type: affineFormalCommRingType()
                    }
                ]
            }),
            conformanceError('EXTRA_INPUT_DECLARATION')
        );
    });

    it(
        'passes bounded Lambdapi checking for both concrete cover shapes',
        {
            skip: process.env.EMDASH_RUN_AFFINE_FORMAL_CONFORMANCE !== '1'
        },
        () => {
            const packageRoot = resolve(__dirname, '..', 'emdash2');
            [binarySpec, ternarySpec].forEach(spec => {
                const value = buildCase(spec);
                const result = checkLambdapiProbe(value.serialized, {
                    packageRoot,
                    timeoutMs: 60_000
                });
                assert.equal(result.timedOut, false, result.diagnostics);
                assert.equal(result.accepted, true, result.diagnostics);
            });
        }
    );
});
