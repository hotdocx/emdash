/** Focused DEV-CLI-2B mounted-source and general command tests. */

import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import {
    mkdir,
    mkdtemp,
    rm,
    symlink,
    truncate,
    writeFile
} from 'node:fs/promises';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_AI_PROOF_DEVELOPMENT_DEMO_PROFILE,
    createCoreAiProofDevelopmentDemoSourceText
} from '../src/v3_2/ai_proof_development_demo';
import {
    CORE_LF_PROOF_DEVELOPMENT_CLI_PROFILE,
    runCoreLfProofDevelopmentCli
} from '../src/v3_2/lf_proof_development_cli';
import {
    CORE_LF_MOUNTED_PROOF_DEVELOPMENT_PROFILE,
    CoreLfMountedProofDevelopmentError,
    CoreLfMountedProofDevelopmentErrorCode,
    materializeCoreLfMountedProofDevelopment
} from '../src/v3_2/lf_proof_development_store';
import {
    CORE_LF_PROOF_DEVELOPMENT_SOURCE_PROFILE,
    parseCoreLfProofDevelopmentSourceText
} from '../src/v3_2/lf_proof_development_source';

interface CliResult {
    readonly exitCode: number;
    readonly stdout: string;
    readonly stderr: string;
}

const sourceFile = (projectRoot: string): string => path.join(
    projectRoot,
    CORE_LF_MOUNTED_PROOF_DEVELOPMENT_PROFILE.sourceFileName
);

const withDirectory = async <T>(
    action: (directory: string) => Promise<T>
): Promise<T> => {
    const directory = await mkdtemp(path.join(
        tmpdir(),
        'emdash-proof-development-'
    ));
    try {
        return await action(directory);
    } finally {
        await rm(directory, { recursive: true, force: true });
    }
};

const writeDemo = async (projectRoot: string): Promise<string> => {
    const sourceText = createCoreAiProofDevelopmentDemoSourceText();
    await writeFile(sourceFile(projectRoot), sourceText, 'utf8');
    return sourceText;
};

const run = async (
    argv: readonly string[]
): Promise<CliResult> => {
    let stdout = '';
    let stderr = '';
    const exitCode = await runCoreLfProofDevelopmentCli(argv, {
        stdout: text => { stdout += text; },
        stderr: text => { stderr += text; }
    });
    return { exitCode, stdout, stderr };
};

const expectStoreError = async (
    action: () => Promise<unknown>,
    code: CoreLfMountedProofDevelopmentErrorCode
): Promise<void> => {
    await assert.rejects(
        action,
        error => error instanceof CoreLfMountedProofDevelopmentError &&
            error.code === code &&
            error.path.length > 0
    );
};

describe('DEV-CLI-2B mounted proof-development source', () => {
    it('reads exact canonical UTF-8 and records byte identity', async () => {
        await withDirectory(async projectRoot => {
            const sourceText = await writeDemo(projectRoot);
            const mounted = await materializeCoreLfMountedProofDevelopment({
                projectRoot
            });
            assert.equal(mounted.sourceText, sourceText);
            assert.equal(
                mounted.sourceUtf8Bytes,
                Buffer.byteLength(sourceText, 'utf8')
            );
            assert.match(mounted.sourceSha256, /^sha256:[0-9a-f]{64}$/u);
            assert.equal(
                mounted.reconstruction.plan.proofs.length,
                2
            );
            assert.equal(Object.isFrozen(mounted), true);
            assert.equal(
                CORE_LF_MOUNTED_PROOF_DEVELOPMENT_PROFILE.performsWrites,
                false
            );
            assert.equal(
                CORE_LF_MOUNTED_PROOF_DEVELOPMENT_PROFILE.executesHostSource,
                false
            );
            assert.equal(
                CORE_LF_MOUNTED_PROOF_DEVELOPMENT_PROFILE
                    .sourceProfileRevision,
                CORE_LF_PROOF_DEVELOPMENT_SOURCE_PROFILE.revision
            );
        });
    });

    it('rejects invalid roots and unsafe fixed source paths', async () => {
        let accessorInvoked = false;
        const accessorRoot = Object.defineProperty({}, 'projectRoot', {
            enumerable: true,
            get: () => {
                accessorInvoked = true;
                return '/tmp/emdash-accessor-root';
            }
        });
        await expectStoreError(
            () => materializeCoreLfMountedProofDevelopment(
                accessorRoot as { readonly projectRoot: string }
            ),
            'INVALID_ROOT'
        );
        assert.equal(accessorInvoked, false);

        await expectStoreError(
            () => materializeCoreLfMountedProofDevelopment({
                projectRoot: 'relative/project'
            }),
            'INVALID_ROOT'
        );
        await withDirectory(async parent => {
            const realRoot = path.join(parent, 'real');
            const linkedRoot = path.join(parent, 'linked');
            await mkdir(realRoot);
            await symlink(realRoot, linkedRoot, 'dir');
            await expectStoreError(
                () => materializeCoreLfMountedProofDevelopment({
                    projectRoot: linkedRoot
                }),
                'UNSAFE_ROOT'
            );
            await expectStoreError(
                () => materializeCoreLfMountedProofDevelopment({
                    projectRoot: realRoot
                }),
                'SOURCE_MISSING'
            );

            const target = path.join(parent, 'source-target.json');
            await writeFile(
                target,
                createCoreAiProofDevelopmentDemoSourceText(),
                'utf8'
            );
            await symlink(target, sourceFile(realRoot));
            await expectStoreError(
                () => materializeCoreLfMountedProofDevelopment({
                    projectRoot: realRoot
                }),
                'UNSAFE_SOURCE'
            );
        });
    });

    it('rejects non-files, oversized bytes, invalid UTF-8, and bad source', async () => {
        await withDirectory(async projectRoot => {
            const target = sourceFile(projectRoot);
            await mkdir(target);
            await expectStoreError(
                () => materializeCoreLfMountedProofDevelopment({ projectRoot }),
                'UNSAFE_SOURCE'
            );
            await rm(target, { recursive: true });

            await writeFile(target, '');
            await truncate(
                target,
                CORE_LF_MOUNTED_PROOF_DEVELOPMENT_PROFILE
                    .maximumSourceBytes + 1
            );
            await expectStoreError(
                () => materializeCoreLfMountedProofDevelopment({ projectRoot }),
                'SOURCE_TOO_LARGE'
            );

            await writeFile(target, Buffer.from([0xff]));
            await expectStoreError(
                () => materializeCoreLfMountedProofDevelopment({ projectRoot }),
                'INVALID_UTF8'
            );

            await writeFile(target, '{}\n', 'utf8');
            await expectStoreError(
                () => materializeCoreLfMountedProofDevelopment({ projectRoot }),
                'INVALID_SOURCE_TEXT'
            );
        });
    });
});

describe('DEV-CLI-2B proof-development commands', () => {
    it('distinguishes incomplete check from successful goal inspection', async () => {
        await withDirectory(async projectRoot => {
            await writeDemo(projectRoot);
            const checked = await run([
                'check',
                '--project-root',
                projectRoot
            ]);
            assert.equal(checked.exitCode, 1);
            assert.match(checked.stderr, /proof is incomplete/u);
            const summary = JSON.parse(checked.stdout) as {
                kind: string;
                status: string;
                scope: string;
                proofCount: number;
                openGoalCount: number;
                sourceSha256: string;
            };
            assert.deepEqual({
                kind: summary.kind,
                status: summary.status,
                scope: summary.scope,
                proofCount: summary.proofCount,
                openGoalCount: summary.openGoalCount
            }, {
                kind: 'proof-development-summary',
                status: 'incomplete',
                scope: 'development',
                proofCount: 2,
                openGoalCount: 1
            });
            assert.match(summary.sourceSha256, /^sha256:[0-9a-f]{64}$/u);

            const goals = await run([
                'goals',
                `--project-root=${projectRoot}`
            ]);
            assert.equal(goals.exitCode, 0);
            assert.equal(goals.stderr, '');
            const records = goals.stdout.trimEnd().split('\n').map(
                line => JSON.parse(line) as {
                    kind: string;
                    moduleId?: string;
                    declarationId?: string;
                    goal?: {
                        id: string;
                        reachability: string;
                    };
                }
            );
            assert.deepEqual(
                records.map(record => record.kind),
                ['proof-development-summary', 'proof-development-goal']
            );
            assert.equal(records[1].goal?.id, 'body');
            assert.equal(
                records[1].goal?.reachability,
                'term-reachable'
            );
            assert.doesNotMatch(goals.stdout, /\?m\d|session|Symbol/u);
            assert.doesNotMatch(goals.stdout, new RegExp(
                projectRoot.replace(/[.*+?^${}()|[\]\\]/gu, '\\$&'),
                'u'
            ));
        });
    });

    it('selects exact complete and open proofs without changing checking', async () => {
        await withDirectory(async projectRoot => {
            await writeDemo(projectRoot);
            const base = [
                '--project-root',
                projectRoot,
                '--module',
                CORE_AI_PROOF_DEVELOPMENT_DEMO_PROFILE.moduleId
            ];
            const complete = await run([
                'check',
                ...base,
                '--declaration',
                'complete_identity'
            ]);
            assert.equal(complete.exitCode, 0);
            assert.equal(complete.stderr, '');
            assert.equal(JSON.parse(complete.stdout).status, 'complete');

            const open = await run([
                'check',
                ...base,
                '--declaration=open_identity'
            ]);
            assert.equal(open.exitCode, 1);
            assert.equal(JSON.parse(open.stdout).openGoalCount, 1);

            const text = await run([
                'goals',
                ...base,
                '--declaration',
                'open_identity',
                '--format',
                'text'
            ]);
            assert.equal(text.exitCode, 0);
            assert.match(text.stdout, /proof .*open_identity: incomplete/u);
            assert.match(text.stdout, /Goal .*open_identity\.body/u);
            assert.match(text.stdout, /\|- ai_native_development_A/u);
        });
    });

    it('emits full portable build records and fails incomplete builds', async () => {
        await withDirectory(async projectRoot => {
            await writeDemo(projectRoot);
            const whole = await run([
                'build',
                '--project-root',
                projectRoot
            ]);
            assert.equal(whole.exitCode, 1);
            const wholeRecord = JSON.parse(whole.stdout) as any;
            assert.equal(wholeRecord.kind, 'proof-development-build');
            assert.equal(wholeRecord.scope, 'development');
            assert.equal(wholeRecord.artifact.proofs.length, 2);

            const selected = await run([
                'build',
                '--project-root',
                projectRoot,
                '--module',
                CORE_AI_PROOF_DEVELOPMENT_DEMO_PROFILE.moduleId,
                '--declaration',
                'complete_identity'
            ]);
            assert.equal(selected.exitCode, 0);
            assert.equal(selected.stderr, '');
            const selectedRecord = JSON.parse(selected.stdout) as any;
            assert.equal(selectedRecord.scope, 'proof');
            assert.equal(
                selectedRecord.artifact.proofArtifact.declarationId,
                'complete_identity'
            );
            assert.doesNotMatch(
                selected.stdout,
                /projectRoot|sourceText|checkedTerm|sessionIdentity/u
            );
        });
    });

    it('fails closed on malformed commands and absent proof selection', async () => {
        await withDirectory(async projectRoot => {
            await writeDemo(projectRoot);
            const cases = [
                [] as string[],
                ['serve', '--project-root', projectRoot],
                ['check', '--project-root', projectRoot, 'positional'],
                ['check', '--project-root', projectRoot, '--format=xml'],
                ['check', '--project-root', projectRoot, '--module', 'only'],
                [
                    'check',
                    '--project-root',
                    projectRoot,
                    '--project-root',
                    projectRoot
                ],
                ['check', '--project-root', projectRoot, '--backend=lambdapi'],
                [
                    'goals',
                    '--project-root',
                    projectRoot,
                    '--module',
                    CORE_AI_PROOF_DEVELOPMENT_DEMO_PROFILE.moduleId,
                    '--declaration',
                    'missing'
                ]
            ];
            for (const argv of cases) {
                const result = await run(argv);
                assert.equal(result.exitCode, 2, argv.join(' '));
                assert.equal(result.stdout, '');
                assert.match(result.stderr, /^emdash:/u);
            }
        });
    });

    it('routes the actual shell and preserves legacy command namespaces', async () => {
        await withDirectory(async projectRoot => {
            const expectedSource = await writeDemo(projectRoot);
            const development = spawnSync(
                './scripts/emdash',
                [
                    'development',
                    'goals',
                    '--project-root',
                    projectRoot,
                    '--module',
                    CORE_AI_PROOF_DEVELOPMENT_DEMO_PROFILE.moduleId,
                    '--declaration',
                    'open_identity',
                    '--format',
                    'text'
                ],
                { cwd: path.resolve(__dirname, '..'), encoding: 'utf8' }
            );
            assert.equal(development.status, 0, development.stderr);
            assert.match(development.stdout, /Goal .*open_identity\.body/u);

            const legacy = spawnSync(
                './scripts/emdash',
                ['check', '--format', 'text'],
                { cwd: path.resolve(__dirname, '..'), encoding: 'utf8' }
            );
            assert.equal(legacy.status, 0, legacy.stderr);
            assert.match(legacy.stdout, /complete_identity: complete/u);

            const capabilities = spawnSync(
                './scripts/emdash',
                ['capabilities', '--format', 'text'],
                { cwd: path.resolve(__dirname, '..'), encoding: 'utf8' }
            );
            assert.equal(capabilities.status, 0, capabilities.stderr);
            assert.match(
                capabilities.stdout,
                /emdash development check/u
            );

            const materializer = spawnSync(
                process.execPath,
                [
                    '--require',
                    'ts-node/register',
                    'examples/v3_2_ai_proof_development_source.ts'
                ],
                { cwd: path.resolve(__dirname, '..'), encoding: 'utf8' }
            );
            assert.equal(materializer.status, 0, materializer.stderr);
            assert.equal(materializer.stdout, expectedSource);
            assert.doesNotThrow(() =>
                parseCoreLfProofDevelopmentSourceText(materializer.stdout)
            );
            assert.equal(
                CORE_LF_PROOF_DEVELOPMENT_CLI_PROFILE.retainsCheckerSession,
                false
            );
            assert.equal(
                CORE_LF_PROOF_DEVELOPMENT_CLI_PROFILE
                    .mountedProfileRevision,
                CORE_LF_MOUNTED_PROOF_DEVELOPMENT_PROFILE.revision
            );
        });
    });
});
