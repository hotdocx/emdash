/** Run: node --require ts-node/register examples/v3_2_algebra_workbench.ts */
import { createHash } from 'node:crypto';
import { mkdirSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import {
    computeAlgebraPolynomialWorkbench, createAlgebraPolynomialWorkbenchExample,
    prepareAlgebraPolynomialWorkbenchGoal
} from '../src/v3_2/algebra_polynomial_workbench';
import { createAlgebraOracleNodeTransport } from '../src/v3_2/algebra_oracle_node';
import { renderAlgebraPolynomialWorkbenchHtml } from '../src/v3_2/algebra_polynomial_workbench_view';
import { renderAlgebraPolynomialCurveSvg } from '../src/v3_2/algebra_polynomial_plot';
import { serializeAlgebraPolynomial, algebraPolynomialText } from '../src/v3_2/algebra_polynomial';
import { createCoreProofArtifactFingerprint } from '../src/v3_2/proof_document';
import { serializeCoreExpression } from '../src/v3_2/core_serialization';

async function main() {
    const args = process.argv.slice(2);
    if (args.length !== 0 && (args.length !== 2 || args[0] !== '--output')) {
        throw new Error('Usage: examples/v3_2_algebra_workbench.ts [--output DIRECTORY]');
    }
    const directory = resolve(args[1] ?? 'emdash2/tmp/probes/algebra-workbench');
    const sha256 = (text: string) => 'sha256:' + createHash('sha256').update(text).digest('hex');
    const workspace = createAlgebraPolynomialWorkbenchExample();
    const result = await computeAlgebraPolynomialWorkbench(workspace, createAlgebraOracleNodeTransport());
    let profileText = '';
    const formal = await prepareAlgebraPolynomialWorkbenchGoal(workspace, (source, profile) => {
        profileText = profile;
        return createCoreProofArtifactFingerprint({
            source: { id: 'algebra-workbench/source.json', sha256: sha256(source) },
            profileSha256: sha256(profile)
        });
    });
    mkdirSync(directory, { recursive: true });
    writeFileSync(resolve(directory, 'index.html'), renderAlgebraPolynomialWorkbenchHtml(workspace, result, formal));
    writeFileSync(resolve(directory, 'curves.svg'), renderAlgebraPolynomialCurveSvg(result.view));
    writeFileSync(resolve(directory, 'source.json'), result.source);
    writeFileSync(resolve(directory, 'formal-profile.json'), profileText);
    writeFileSync(resolve(directory, 'result.json'), JSON.stringify({
        sourceSha256: sha256(result.source),
        native: { member: result.native.member,
            coefficients: result.native.coefficients.map(serializeAlgebraPolynomial),
            remainder: serializeAlgebraPolynomial(result.native.remainder) },
        external: { kind: result.external.kind, version: result.external.version,
            backend: result.external.backend, request: result.external.request,
            coefficients: result.external.kind === 'witness'
                ? result.external.witness.coefficients.map(serializeAlgebraPolynomial) : undefined },
        agrees: result.agrees,
        formal: { status: formal.status, reason: formal.reason,
            goalId: formal.goal.goalId, target: formal.goal.targetCore,
            fingerprint: formal.document.fingerprint,
            premises: formal.hypotheses.map(h => ({ name: h.name, type: serializeCoreExpression(h.type) })) },
        view: { viewport: result.view.viewport, interpretation: result.view.interpretation,
            limitation: result.view.limitation }
    }, null, 2) + '\n');
    console.log(`Query: ${algebraPolynomialText(result.input.polynomial)}`);
    console.log(`Native membership: ${result.native.member}; Singular: ${result.external.kind}`);
    console.log(`Formal goal: ${formal.status} (${formal.goal.goalId})`);
    console.log(`View: ${resolve(directory, 'index.html')}`);
}

main().catch(error => { console.error(error); process.exitCode = 1; });
