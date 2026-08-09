/** Focused AI proof, research-file, and capability-command tests. */

import assert from 'node:assert';
import { spawnSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import path from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_AI_RESEARCH_OVERVIEW_PROFILE
} from '../src/v3_2/ai_research_overview';
import {
    CORE_AI_RESEARCH_OVERVIEW_BROWSER_PROFILE,
    formatCoreAiResearchOverviewBrowser,
    runCoreAiResearchOverviewBrowser
} from '../src/v3_2/ai_research_overview_browser';
import {
    CORE_AI_NATIVE_CAPABILITIES,
    CORE_AI_NATIVE_CAPABILITIES_PROFILE,
    serializeCoreAiNativeCapabilities
} from '../src/v3_2/ai_native_capabilities';
import {
    CORE_AI_NATIVE_CAPABILITIES_CLI_PROFILE,
    formatCoreAiNativeCapabilities,
    runCoreAiNativeCapabilitiesCli
} from '../src/v3_2/ai_native_capabilities_cli';
import {
    CORE_AI_RESEARCH_OVERVIEW_FILES_PROFILE,
    CoreAiResearchOverviewFilesError,
    materializeCoreAiResearchOverviewFiles,
    serializeCoreAiResearchOverviewFilesSnapshot
} from '../src/v3_2/ai_research_overview_files';
import {
    runCoreAiProofCli
} from '../src/v3_2/ai_proof_cli';
import {
    CORE_LF_DICTIONARY_AUTHORING_PROFILE
} from '../src/v3_2/lf_dictionary_authoring';
import {
    CORE_LF_INSTANCE_SCOPE_PROFILE
} from '../src/v3_2/lf_instance_scope';
import {
    CORE_LF_DICTIONARY_SYNTHESIS_PROFILE
} from '../src/v3_2/lf_dictionary_synthesis';
import {
    CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE
} from '../src/v3_2/lf_fragment_module_workspace';
import {
    CORE_LF_SAME_MODULE_FRAGMENT_WORKSPACE_PROFILE
} from '../src/v3_2/lf_fragment_workspace';
import {
    CORE_LF_MOUNTED_REMOTE_WORKSPACE_STORE_PROFILE
} from '../src/v3_2/lf_remote_workspace_store';
import {
    CORE_PROOF_DOCUMENT_PROFILE
} from '../src/v3_2/proof_document';
import {
    CORE_LF_DECLARATION_WORKSPACE_PROFILE
} from '../src/v3_2/lf_workspace';
import {
    CORE_LF_WORKSPACE_PROOF_PROFILE
} from '../src/v3_2/lf_workspace_proof';
import {
    CORE_RESEARCH_DOCUMENT_PROFILE,
    serializeCoreResearchDocumentSnapshot
} from '../src/v3_2/research_document';

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

const runCapabilities = (argv: readonly string[]): CliResult => {
    let stdout = '';
    let stderr = '';
    const exitCode = runCoreAiNativeCapabilitiesCli(argv, {
        stdout: text => { stdout += text; },
        stderr: text => { stderr += text; }
    });
    return { exitCode, stdout, stderr };
};

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>)
        .forEach(assertDeepFrozen);
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

    it('matches the browser recheck to the byte-verified binding', () => {
        const verified = materializeCoreAiResearchOverviewFiles();
        const browser = runCoreAiResearchOverviewBrowser();
        assert.equal(
            serializeCoreResearchDocumentSnapshot(browser.binding),
            serializeCoreResearchDocumentSnapshot(verified.binding)
        );
        assert.equal(
            browser.digestVerification,
            'not-performed-in-browser'
        );
        assert.equal(
            CORE_AI_RESEARCH_OVERVIEW_BROWSER_PROFILE
                .computesCryptographicHashes,
            false
        );
        const formatted = formatCoreAiResearchOverviewBrowser(browser);
        assert.match(formatted, /CHECKED .*complete-identity/u);
        assert.match(formatted, /OPEN .*open-identity/u);
        assert.match(formatted, /Goal body/u);
        assert.match(formatted, /Node-verified workspace/u);
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

    it('rejects whole-article prose drift after diagram selection', () => {
        assert.throws(
            () => materializeCoreAiResearchOverviewFiles({
                readBytes: replaceArticle(source => `${source}\n`)
            }),
            (error: unknown) => {
                assert.ok(error instanceof CoreAiResearchOverviewFilesError);
                assert.equal(error.code, 'SOURCE_PIN_MISMATCH');
                assert.equal(
                    error.target,
                    CORE_AI_RESEARCH_OVERVIEW_PROFILE.documentSourcePath
                );
                return true;
            }
        );
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

describe('TypeScript v3.2 AI-NATIVE-GRADUATE-1 capabilities', () => {
    it('publishes one honest immutable local-foundation record', () => {
        assertDeepFrozen(CORE_AI_NATIVE_CAPABILITIES);
        assert.equal(
            CORE_AI_NATIVE_CAPABILITIES.status,
            'qualified-local-foundation'
        );
        assert.equal(
            CORE_AI_NATIVE_CAPABILITIES.backend,
            'typescript-emdash-explicit-core'
        );
        assert.equal(
            CORE_AI_NATIVE_CAPABILITIES.trust
                .productionLambdapiDependency,
            false
        );
        assert.equal(
            serializeCoreAiNativeCapabilities(),
            serializeCoreAiNativeCapabilities()
        );

        const revisions = new Map(
            CORE_AI_NATIVE_CAPABILITIES.implementedProfiles.map(profile =>
                [profile.id, profile.revision]
            )
        );
        assert.equal(
            revisions.get('proof-document'),
            CORE_PROOF_DOCUMENT_PROFILE.revision
        );
        assert.equal(
            revisions.get('fragment-module-workspace'),
            CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE.revision
        );
        assert.equal(
            revisions.get('declaration-workspace'),
            CORE_LF_DECLARATION_WORKSPACE_PROFILE.revision
        );
        assert.equal(
            revisions.get('workspace-proof'),
            CORE_LF_WORKSPACE_PROOF_PROFILE.revision
        );
        assert.equal(
            revisions.get('same-module-fragment-workspace'),
            CORE_LF_SAME_MODULE_FRAGMENT_WORKSPACE_PROFILE.revision
        );
        assert.equal(
            revisions.get('mounted-workspace-store'),
            CORE_LF_MOUNTED_REMOTE_WORKSPACE_STORE_PROFILE.revision
        );
        assert.equal(
            revisions.get('dictionary-synthesis'),
            CORE_LF_DICTIONARY_SYNTHESIS_PROFILE.revision
        );
        assert.equal(
            revisions.get('dictionary-authoring'),
            CORE_LF_DICTIONARY_AUTHORING_PROFILE.revision
        );
        assert.equal(
            revisions.get('instance-provider-scope'),
            CORE_LF_INSTANCE_SCOPE_PROFILE.scopeRevision
        );
        assert.equal(
            revisions.get('research-document-binding'),
            CORE_RESEARCH_DOCUMENT_PROFILE.revision
        );
        assert.equal(
            revisions.get('research-browser-recheck'),
            CORE_AI_RESEARCH_OVERVIEW_BROWSER_PROFILE.revision
        );
        assert.deepEqual(
            CORE_AI_NATIVE_CAPABILITIES.commands.map(command => command.id),
            ['capabilities', 'proof-check', 'proof-goals', 'workspace-check']
        );
        assert.match(
            CORE_AI_NATIVE_CAPABILITIES.commands[1].scope,
            /fixed .* proof demo/u
        );
        assert.match(
            CORE_AI_NATIVE_CAPABILITIES.commands[3].scope,
            /canonical emdash\.workspace\.lock\.json/u
        );
        assert.deepEqual(
            CORE_AI_NATIVE_CAPABILITIES.deferred.map(item => item.id),
            [
                'general-source-acquisition',
                'general-development-cli',
                'reusable-recursive-dictionary-search',
                'persisted-or-inline-paper-artifacts',
                'network-acquisition',
                'hosted-workspace-delivery',
                'whole-library-transfer-and-global-metatheory'
            ]
        );
        assert.equal(
            CORE_AI_NATIVE_CAPABILITIES.deferred[
                CORE_AI_NATIVE_CAPABILITIES.deferred.length - 1
            ].state,
            'research-gated'
        );

        const source = readFileSync(
            path.join(repositoryRoot, 'src/v3_2/ai_native_capabilities.ts'),
            'utf8'
        );
        assert.doesNotMatch(source, /from ['"]node:|process\./u);
        assert.deepEqual(
            [...source.matchAll(/from ['"]([^'"]+)['"]/gu)]
                .map(match => match[1]),
            []
        );
        const cliSource = readFileSync(
            path.join(
                repositoryRoot,
                'src/v3_2/ai_native_capabilities_cli.ts'
            ),
            'utf8'
        );
        assert.deepEqual(
            [...cliSource.matchAll(/from ['"]([^'"]+)['"]/gu)]
                .map(match => match[1]),
            ['./ai_native_capabilities']
        );
        assert.equal(
            CORE_AI_NATIVE_CAPABILITIES_PROFILE.performsSemanticChecks,
            false
        );
        assert.doesNotMatch(
            serializeCoreAiNativeCapabilities(),
            /\/home\/|timestamp|processId|session|Symbol/u
        );
    });

    it('renders deterministic JSONL and text without checking', () => {
        const jsonl = runCapabilities([]);
        assert.equal(jsonl.exitCode, 0);
        assert.equal(jsonl.stderr, '');
        assert.equal(jsonl.stdout, serializeCoreAiNativeCapabilities());
        assert.equal(jsonl.stdout.trimEnd().includes('\n'), false);
        const record = JSON.parse(jsonl.stdout) as Record<string, unknown>;
        assert.deepEqual(Object.keys(record), [
            'revision',
            'status',
            'backend',
            'trust',
            'implementedProfiles',
            'commands',
            'deferred'
        ]);

        const text = runCapabilities(['--format=text']);
        assert.equal(text.exitCode, 0);
        assert.equal(text.stderr, '');
        assert.equal(text.stdout, formatCoreAiNativeCapabilities());
        assert.match(text.stdout, /qualified-local-foundation/u);
        assert.match(text.stdout, /fixed ai_native\.local proof demo/u);
        assert.match(text.stdout, /hosted-workspace-delivery/u);
        assert.equal(
            CORE_AI_NATIVE_CAPABILITIES_CLI_PROFILE
                .performsSemanticChecks,
            false
        );

        for (const argv of [
            ['extra'],
            ['--format'],
            ['--format', 'yaml'],
            ['--format=text', '--format=jsonl']
        ]) {
            const invalid = runCapabilities(argv);
            assert.equal(invalid.exitCode, 2);
            assert.equal(invalid.stdout, '');
            assert.match(invalid.stderr, /^emdash:/u);
        }
    });

    it('routes the actual capability command without changing proof dispatch', () => {
        const script = path.join(repositoryRoot, 'scripts', 'emdash');
        const capabilities = spawnSync(
            script,
            ['capabilities', '--format', 'text'],
            { cwd: repositoryRoot, encoding: 'utf8' }
        );
        assert.equal(capabilities.status, 0, capabilities.stderr);
        assert.equal(capabilities.stderr, '');
        assert.match(capabilities.stdout, /qualified-local-foundation/u);

        const proof = spawnSync(
            script,
            ['check', '--format', 'text'],
            { cwd: repositoryRoot, encoding: 'utf8' }
        );
        assert.equal(proof.status, 0, proof.stderr);
        assert.equal(proof.stderr, '');
        assert.match(proof.stdout, /complete_identity: complete/u);
    });
});
