/** Focused contracts for the finite PathOut presentation CLI. */

import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import type {
    CorePathoutFreshCheckResult
} from '../src/v3_2/pathout_presentation_check';
import {
    CORE_PATHOUT_PRESENTATION_1F_CLI_PROFILE,
    CORE_PATHOUT_PRESENTATION_COLD_CHECK_NOTICE,
    CorePathoutPresentationSemanticModule,
    runCorePathoutPresentationCli
} from '../src/v3_2/pathout_presentation_cli';

const repositoryRoot = resolve(__dirname, '..');

interface CliRun {
    readonly exitCode: number;
    readonly stdout: string;
    readonly stderr: string;
}

const runCli = async (
    argv: readonly string[],
    loadSemanticCheck?: () => Promise<CorePathoutPresentationSemanticModule>
): Promise<CliRun> => {
    let stdout = '';
    let stderr = '';
    const exitCode = await runCorePathoutPresentationCli(
        argv,
        {
            stdout: text => { stdout += text; },
            stderr: text => { stderr += text; }
        },
        loadSemanticCheck === undefined ? {} : { loadSemanticCheck }
    );
    return { exitCode, stdout, stderr };
};

const semanticStub = (
    events: string[]
): (() => Promise<CorePathoutPresentationSemanticModule>) => async () => {
    events.push('load-semantic-adapter');
    return {
        checkCorePathoutPresentationRequest: request => {
            events.push(`check:${request.formId}`);
            return {
                request,
                canonicalSource: request.canonicalSource,
                status: 'freshly-checked'
            } as CorePathoutFreshCheckResult;
        },
        formatCorePathoutFreshCheck: result =>
            `STUB FRESH CHECK: ${result.canonicalSource}`
    };
};

describe('PATHOUT-LIBRARY-PRESENTATION-1F CLI', () => {
    it('records a static-by-default command boundary', () => {
        assert.deepEqual(
            CORE_PATHOUT_PRESENTATION_1F_CLI_PROFILE.commands,
            ['catalog', 'parse', 'check']
        );
        assert.equal(
            CORE_PATHOUT_PRESENTATION_1F_CLI_PROFILE
                .catalogLoadsSemanticTransfer,
            false
        );
        assert.equal(
            CORE_PATHOUT_PRESENTATION_1F_CLI_PROFILE
                .parseLoadsSemanticTransfer,
            false
        );
        assert.equal(
            CORE_PATHOUT_PRESENTATION_1F_CLI_PROFILE
                .checkLoadsSemanticTransferOnExplicitRequest,
            true
        );
        assert.equal(
            CORE_PATHOUT_PRESENTATION_1F_CLI_PROFILE
                .retainsCheckerSession,
            false
        );
    });

    it('catalogs all forms without calling the semantic loader', async () => {
        let loads = 0;
        const forbiddenLoader = async () => {
            loads++;
            throw new Error('semantic adapter must stay cold');
        };
        const text = await runCli(['catalog'], forbiddenLoader);
        assert.equal(text.exitCode, 0);
        assert.equal(text.stderr, '');
        assert.match(text.stdout, /not rerun by catalog/u);
        assert.match(text.stdout, /pathout-category/u);
        assert.match(text.stdout, /composition-normal-form/u);

        const json = await runCli(
            ['catalog', '--format', 'json'],
            forbiddenLoader
        );
        assert.equal(json.exitCode, 0);
        assert.equal(JSON.parse(json.stdout).forms.length, 4);
        assert.equal(loads, 0);
    });

    it('parses renamed variables into non-fresh evidence without loading ' +
        'semantics', async () => {
        let loads = 0;
        const result = await runCli(
            [
                'parse',
                'canonical-rho',
                '--source',
                'rho(C, a, b, f)',
                '--format=json'
            ],
            async () => {
                loads++;
                throw new Error('semantic adapter must stay cold');
            }
        );
        assert.equal(result.exitCode, 0);
        assert.equal(result.stderr, '');
        const report = JSON.parse(result.stdout);
        assert.equal(report.request.canonicalSource, 'rho(C, a, b, f)');
        assert.equal(report.status, 'qualified-at-pinned-checkpoint');
        assert.equal(report.freshSemanticCheck, false);
        assert.equal(report.browserSemanticExecution, false);
        assert.equal(loads, 0);
    });

    it('rejects malformed, mismatched, and unknown static requests before ' +
        'loading semantics', async () => {
        let loads = 0;
        const loader = async () => {
            loads++;
            throw new Error('must not load');
        };
        for (const argv of [
            ['parse'],
            ['parse', 'pathout-category', '--source', 'rho(Z, x, y, p)'],
            ['check', 'pathout-category', '--source', 'PathOut[Z, x]'],
            ['parse', 'missing-form'],
            ['catalog', '--source', 'PathOut(Z, x)'],
            ['catalog', '--format', 'yaml']
        ]) {
            const result = await runCli(argv, loader);
            assert.equal(result.exitCode, 2, argv.join(' '));
            assert.equal(result.stdout, '');
            assert.match(result.stderr, /^emdash: /u);
        }
        assert.equal(loads, 0);
    });

    it('warns and dynamically loads semantics only for explicit check',
        async () => {
            const events: string[] = [];
            let stdout = '';
            let stderr = '';
            const exitCode = await runCorePathoutPresentationCli(
                ['check', 'pathout-category'],
                {
                    stdout: text => {
                        events.push('stdout');
                        stdout += text;
                    },
                    stderr: text => {
                        events.push('cold-notice');
                        stderr += text;
                    }
                },
                { loadSemanticCheck: semanticStub(events) }
            );
            assert.equal(exitCode, 0);
            assert.equal(stderr, CORE_PATHOUT_PRESENTATION_COLD_CHECK_NOTICE);
            assert.equal(stdout, 'STUB FRESH CHECK: PathOut(Z, x)\n');
            assert.deepEqual(events, [
                'cold-notice',
                'load-semantic-adapter',
                'check:pathout-category',
                'stdout'
            ]);
        });

    it('routes the shell launcher and executes its static catalog path', () => {
        const dispatcher = readFileSync(
            resolve(repositoryRoot, 'scripts/emdash'),
            'utf8'
        );
        const cliSource = readFileSync(
            resolve(repositoryRoot, 'src/v3_2/pathout_presentation_cli.ts'),
            'utf8'
        );
        assert.match(dispatcher, /v3_2_pathout_cli\.ts/u);
        assert.match(
            cliSource,
            /import\(['"]\.\/pathout_presentation_check\.js['"]\)/u
        );
        assert.doesNotMatch(
            cliSource,
            /from ['"]\.\/pathout_presentation_check['"]/u
        );

        const processResult = spawnSync(
            resolve(repositoryRoot, 'scripts/emdash'),
            ['pathout', 'catalog', '--format', 'json'],
            {
                cwd: repositoryRoot,
                encoding: 'utf8',
                timeout: 30_000
            }
        );
        assert.equal(processResult.status, 0, processResult.stderr);
        assert.equal(processResult.stderr, '');
        assert.equal(JSON.parse(processResult.stdout).forms.length, 4);
    });
});
