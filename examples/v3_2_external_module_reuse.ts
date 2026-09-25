/** External result -> typed module data -> optional explicit law adoption -> internal reuse. */
import { createHash } from 'node:crypto';
import { mkdirSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import {
    adoptAlgebraExternalModuleComplex, prepareAlgebraExternalModuleData
} from '../src/v3_2/algebra_external_module_reuse';
import {
    algebraPolynomialWorkspaceInput, createAlgebraPolynomialWorkbenchExample
} from '../src/v3_2/algebra_polynomial_workbench';
import { computeSingularIdealWitness } from '../src/v3_2/algebra_ideal_singular';
import { createAlgebraOracleNodeTransport } from '../src/v3_2/algebra_oracle_node';
import { algebraPolynomialText, serializeAlgebraPolynomial } from '../src/v3_2/algebra_polynomial';
import { createCoreProofArtifactFingerprint } from '../src/v3_2/proof_document';
import { serializeCoreExpression } from '../src/v3_2/core_serialization';
import { serializeAlgebraFormalAssumptionSource } from '../src/v3_2/algebra_formal_assumption_source';

async function main() {
    let adopt = false;
    let output: string | undefined;
    const args = process.argv.slice(2);
    for (let i = 0; i < args.length; i++) {
        if (args[i] === '--adopt-computed-equation') adopt = true;
        else if (args[i] === '--output' && args[i + 1]) output = args[++i];
        else throw new Error('Usage: v3_2_external_module_reuse.ts [--adopt-computed-equation] [--output DIRECTORY]');
    }
    const directory = resolve(output ?? `emdash2/tmp/probes/external-module-reuse/${adopt ? 'adopted' : 'data'}`);
    const sha = (value: string) => 'sha256:' + createHash('sha256').update(value).digest('hex');
    const workspace = createAlgebraPolynomialWorkbenchExample();
    const external = await computeSingularIdealWitness(
        algebraPolynomialWorkspaceInput(workspace), createAlgebraOracleNodeTransport());
    const data = prepareAlgebraExternalModuleData(workspace, external);
    const lawSources: { name: string; source: string; profile: string }[] = [];
    const internal = adopt ? await adoptAlgebraExternalModuleComplex({
        workspace, external,
        decision: { kind: 'trust-exact-algebra-computation',
            evidence: 'Explicit --adopt-computed-equation selection: use the checked composite of the retained Singular-derived matrices as an assumed equation' },
        fingerprint: (source, profile) => {
            const name = `law-${lawSources.length + 1}`;
            lawSources.push({ name, source, profile });
            return createCoreProofArtifactFingerprint({
                source: { id: `${name}.source.json`, sha256: sha(source) }, profileSha256: sha(profile)
            });
        }
    }) : undefined;
    const core = (term: Parameters<typeof serializeCoreExpression>[0], type: Parameters<typeof serializeCoreExpression>[0]) =>
        ({ term: serializeCoreExpression(term), type: serializeCoreExpression(type) });
    const result = {
        sourceSha256: sha(data.sourceData),
        external: { version: external.version, backend: external.backend,
            coefficients: data.coefficients.map(serializeAlgebraPolynomial) },
        native: { ranks: data.complex.terms.map(term => term.module.rank),
            lower: data.lower.columns.map(column => column.components.map(serializeAlgebraPolynomial)),
            upper: data.upper.columns.map(column => column.components.map(serializeAlgebraPolynomial)),
            compositeIsZero: data.complex.conditions[0].zero },
        core: { lower: core(data.realization.formalDifferentials[0], data.lowerType),
            upper: core(data.realization.formalDifferentials[1], data.upperType),
            composite: core(data.composite, data.compositeType) },
        internal: internal ? {
            status: internal.status,
            complex: core(internal.assembled.term, internal.assembled.type),
            projectedDifferential: core(internal.projected.term, internal.projected.type),
            argument: { ...core(internal.argument, internal.argumentType), role: 'supplied-formal-input' },
            image: core(internal.image, internal.imageType),
            assumptions: JSON.parse(serializeAlgebraFormalAssumptionSource(internal.adopted.source))
        } : { status: 'typed-data-only-no-equation-adopted' },
        proofReconstruction: 'not-requested'
    };
    mkdirSync(directory, { recursive: true });
    writeFileSync(resolve(directory, 'source.json'), data.sourceData);
    writeFileSync(resolve(directory, 'result.json'), JSON.stringify(result, null, 2) + '\n');
    for (const law of lawSources) {
        writeFileSync(resolve(directory, `${law.name}.source.json`), law.source);
        writeFileSync(resolve(directory, `${law.name}.profile.json`), law.profile);
    }
    const row = data.lower.columns.map(column => algebraPolynomialText(column.components[0])).join(', ');
    const column = data.column.components.map(algebraPolynomialText).join(', ');
    const shape = data.complex.terms.map(term => term.module.rank === 1 ? 'R' : `R^${term.module.rank}`).join(' <- ');
    const summary = [
        '# External result and internal module reuse', '',
        `Singular ${external.version} returned the coefficients used below.`, '',
        `Computational ring: Q[${workspace.ideal.ring.variables.join(', ')}]. The formal ring is supplied with the selected bounded integer-polynomial interpretation.`, '',
        '```text', `D = (${row})`, `s = (${column})^T`, '```', '',
        `The retained matrices define ${shape}, with D*s = 0 checked by exact arithmetic.`, '',
        'The same external coefficients occur in typed Core matrices and their internal composition.', '',
        internal ? 'One computed equation was explicitly adopted. Existing constructors assemble a whole internal complex. Its upper differential is projected and applied to a typed formal input; the image is a further typed internal definition.'
            : 'No equation was adopted. Use --adopt-computed-equation to select the existing explicit-assumption route for whole-complex construction and reuse.', '',
        'Supplied formal inputs and any adopted equations are listed in result.json. Exactness, homology and automatic proof reconstruction are outside this example.', '',
        'See result.json for exact Core terms, types, provenance and assumption status.', ''
    ].join('\n');
    writeFileSync(resolve(directory, 'overview.md'), summary);
    console.log(summary);
    console.log(`Artifacts: ${directory}`);
}

main().catch(error => { console.error(error); process.exitCode = 1; });
