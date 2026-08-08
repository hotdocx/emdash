/** Focused AI-PROOF-2 and AI-PAPER-1B1 Node-adapter tests. */

import assert from 'node:assert';
import { readFileSync } from 'node:fs';
import path from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_AI_RESEARCH_OVERVIEW_PROFILE
} from '../src/v3_2/ai_research_overview';
import {
    CORE_AI_RESEARCH_OVERVIEW_FILES_PROFILE,
    CoreAiResearchOverviewFilesError,
    materializeCoreAiResearchOverviewFiles,
    serializeCoreAiResearchOverviewFilesSnapshot
} from '../src/v3_2/ai_research_overview_files';
import {
    runCoreAiProofCli
} from '../src/v3_2/ai_proof_cli';

interface CliResult {
    readonly exitCode: number;
    readonly stdout: string;
    readonly stderr: string;
}

const run = (argv: readonly string[]): CliResult => {
    let stdout = '';
    let stderr = '';
    const exitCode = runCoreAiProofCli(argv, {
        readText: () => 'stable AI proof demo source\n',
        stdout: text => { stdout += text; },
        stderr: text => { stderr += text; }
    });
    return { exitCode, stdout, stderr };
};

describe('TypeScript v3.2 AI-PROOF-2 local CLI', () => {
    it('checks the complete declaration with one JSONL proof record', () => {
        const result = run(['check']);
        assert.equal(result.exitCode, 0);
        assert.equal(result.stderr, '');
        const lines = result.stdout.trimEnd().split('\n');
        assert.equal(lines.length, 1);
        const record = JSON.parse(lines[0]) as {
            kind: string;
            status: string;
            declarationId: string;
            checkedCore?: string;
        };
        assert.equal(record.kind, 'proof');
        assert.equal(record.status, 'complete');
        assert.equal(record.declarationId, 'complete_identity');
        assert.match(record.checkedCore ?? '', /^\(lambda/u);
    });

    it('reports the default incomplete declaration as proof plus goal', () => {
        const result = run(['goals']);
        assert.equal(result.exitCode, 0);
        assert.equal(result.stderr, '');
        const records = result.stdout.trimEnd().split('\n').map(
            line => JSON.parse(line) as {
                kind: string;
                status?: string;
                goal?: { id: string };
            }
        );
        assert.deepEqual(
            records.map(record => record.kind),
            ['proof', 'goal']
        );
        assert.equal(records[0].status, 'incomplete');
        assert.equal(records[1].goal?.id, 'body');
        assert.doesNotMatch(result.stdout, /\?m\d|session|Symbol/u);
    });

    it('makes incomplete check distinct from successful goal inspection', () => {
        const result = run(['check', 'open_identity']);
        assert.equal(result.exitCode, 1);
        assert.match(result.stdout, /"status":"incomplete"/u);
        assert.match(result.stderr, /proof is incomplete/u);
    });

    it('offers a compact human rendering of the same artifact', () => {
        const complete = run(['check', '--format', 'text']);
        assert.equal(complete.exitCode, 0);
        assert.match(complete.stdout, /complete_identity: complete/u);
        assert.match(complete.stdout, /checked Core/u);

        const open = run(['goals', '--format=text']);
        assert.equal(open.exitCode, 0);
        assert.match(open.stdout, /open_identity: incomplete/u);
        assert.match(open.stdout, /Goal body/u);
        assert.match(open.stdout, /\|- AIProofA/u);
    });

    it('fails closed on unknown commands, declarations, and formats', () => {
        for (const argv of [
            [] as string[],
            ['serve'],
            ['check', 'unknown'],
            ['goals', '--format', 'xml']
        ]) {
            const result = run(argv);
            assert.equal(result.exitCode, 2);
            assert.equal(result.stdout, '');
            assert.match(result.stderr, /^emdash:/u);
        }
    });
});

const repositoryRoot = path.resolve(__dirname, '..');
const articleSuffix = path.join(
    'emdash2',
    'print',
    'public',
    'emdash-v3-2-overview.md'
);

const replaceArticle = (
    transform: (source: string) => string
): ((absolutePath: string) => Uint8Array) => absolutePath => {
    const bytes = readFileSync(absolutePath);
    if (!absolutePath.endsWith(articleSuffix)) return bytes;
    return Buffer.from(transform(bytes.toString('utf8')), 'utf8');
};

describe('TypeScript v3.2 AI-PAPER-1B1 research files', () => {
    it('materializes both article diagrams and both proof states', () => {
        const first = materializeCoreAiResearchOverviewFiles();
        const second = materializeCoreAiResearchOverviewFiles();
        assert.equal(
            serializeCoreAiResearchOverviewFilesSnapshot(first),
            serializeCoreAiResearchOverviewFilesSnapshot(second)
        );
        assert.equal(first.digestVerification, 'performed-exact-utf8');
        assert.equal(first.binding.digestVerification, 'not-performed');
        assert.equal(
            first.documentSource.id,
            CORE_AI_RESEARCH_OVERVIEW_PROFILE.documentSourcePath
        );
        assert.equal(
            first.binding.source.sha256,
            first.documentSource.sha256
        );
        assert.deepEqual(
            first.binding.blocks.map(block => block.blockId),
            [
                'section-4.pathout-canonical-arrow',
                'section-4.pathout-motive-transport',
                'section-7.proof.complete-identity',
                'section-7.proof.open-identity'
            ]
        );
        assert.deepEqual(
            first.binding.blocks
                .filter(block => block.kind === 'proof')
                .map(block => block.status),
            ['complete', 'incomplete']
        );
        assert.deepEqual(
            first.proofArtifacts.map(item => item.artifact.state.status),
            ['complete', 'incomplete']
        );
        first.proofArtifacts.forEach(item => {
            const binding = first.binding.blocks.find(block =>
                block.blockId === item.blockId
            );
            assert.ok(binding && binding.kind === 'proof');
            assert.equal(binding.artifactSource.sha256, item.source.sha256);
        });
        assert.equal(Object.isFrozen(first), true);
        assert.equal(Object.isFrozen(first.proofArtifacts), true);
        assert.doesNotMatch(
            serializeCoreAiResearchOverviewFilesSnapshot(first),
            /\/home\/|session|Symbol/u
        );

        const managementSource = readFileSync(
            path.join(
                repositoryRoot,
                CORE_AI_RESEARCH_OVERVIEW_PROFILE.managementSourcePath
            ),
            'utf8'
        );
        assert.doesNotMatch(managementSource, /from ['"]node:/u);
        assert.equal(
            CORE_AI_RESEARCH_OVERVIEW_PROFILE.nodeBuiltinDependency,
            false
        );
        assert.equal(
            CORE_AI_RESEARCH_OVERVIEW_FILES_PROFILE.performsWrites,
            false
        );
        assert.equal(
            CORE_AI_RESEARCH_OVERVIEW_FILES_PROFILE.invokesLambdapi,
            false
        );
    });

    it('rejects a managed diagram whose exact content drifts', () => {
        assert.throws(
            () => materializeCoreAiResearchOverviewFiles({
                readBytes: replaceArticle(source => source.replace(
                    '"label": "$x$"',
                    '"label": "$x^{\\prime}$"'
                ))
            }),
            (error: unknown) => {
                assert.ok(error instanceof CoreAiResearchOverviewFilesError);
                assert.equal(error.code, 'MISSING_DIAGRAM');
                return true;
            }
        );
    });

    it('rejects drift in the imported management or proof source pins', () => {
        for (const relativePath of [
            CORE_AI_RESEARCH_OVERVIEW_PROFILE.managementSourcePath,
            CORE_AI_RESEARCH_OVERVIEW_PROFILE.proofSourcePath
        ]) {
            const suffix = relativePath.split('/').join(path.sep);
            assert.throws(
                () => materializeCoreAiResearchOverviewFiles({
                    readBytes: absolutePath => {
                        const bytes = readFileSync(absolutePath);
                        return absolutePath.endsWith(suffix)
                            ? Buffer.concat([bytes, Buffer.from('\n')])
                            : bytes;
                    }
                }),
                (error: unknown) => {
                    assert.ok(
                        error instanceof CoreAiResearchOverviewFilesError
                    );
                    assert.equal(error.code, 'SOURCE_PIN_MISMATCH');
                    assert.equal(error.target, relativePath);
                    return true;
                }
            );
        }
    });

    it('rejects a content selector that matches two diagram bodies', () => {
        assert.throws(
            () => materializeCoreAiResearchOverviewFiles({
                readBytes: replaceArticle(source => {
                    const bodies = [...source.matchAll(
                        /<div class="arrowgram"[^>]*>([\s\S]*?)<\/div>/gu
                    )];
                    assert.equal(bodies.length, 2);
                    return source.replace(bodies[1][1], bodies[0][1]);
                })
            }),
            (error: unknown) => {
                assert.ok(error instanceof CoreAiResearchOverviewFilesError);
                assert.equal(error.code, 'AMBIGUOUS_DIAGRAM');
                return true;
            }
        );
    });

    it('rejects an unbound diagram or invalid article UTF-8', () => {
        assert.throws(
            () => materializeCoreAiResearchOverviewFiles({
                readBytes: replaceArticle(source => {
                    const first = source.match(
                        /<div class="arrowgram"[^>]*>[\s\S]*?<\/div>/u
                    );
                    assert.ok(first);
                    return `${source}\n${first[0]}\n`;
                })
            }),
            (error: unknown) => {
                assert.ok(error instanceof CoreAiResearchOverviewFilesError);
                assert.equal(error.code, 'UNBOUND_DIAGRAM');
                return true;
            }
        );
        assert.throws(
            () => materializeCoreAiResearchOverviewFiles({
                readBytes: absolutePath => absolutePath.endsWith(articleSuffix)
                    ? Uint8Array.from([0xff])
                    : readFileSync(absolutePath)
            }),
            (error: unknown) => {
                assert.ok(error instanceof CoreAiResearchOverviewFilesError);
                assert.equal(error.code, 'INVALID_UTF8');
                assert.equal(
                    error.target,
                    CORE_AI_RESEARCH_OVERVIEW_PROFILE.documentSourcePath
                );
                return true;
            }
        );
    });
});
