import assert from 'node:assert/strict';
import { chmodSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { it } from 'node:test';
import { checkLambdapiProbe } from '../src/v3_2/probe';

it('repository probe bridge retains guarded evidence and classifies hard timeouts', {
    skip: process.platform !== 'linux'
}, () => {
    const root = mkdtempSync(join(tmpdir(), 'emdash-probe-runner-'));
    const keys = ['PATH', 'XDG_RUNTIME_DIR', 'EMDASH_LP_MEMORY_MIB', 'EMDASH_LP_RESOURCE_BACKEND'];
    const before = keys.map(key => [key, process.env[key]] as const);
    try {
        writeFileSync(join(root, 'lambdapi.pkg'), 'root_path = fixture\n');
        const binary = join(root, 'lambdapi');
        const install = (body: string): void => {
            writeFileSync(binary,
                '#!/usr/bin/env python3\nimport sys\n' +
                'if "--version" in sys.argv:\n print("fixture");sys.exit(0)\n' + body
            );
            chmodSync(binary, 0o755);
        };
        process.env.PATH = `${root}:${process.env.PATH}`;
        process.env.XDG_RUNTIME_DIR = root;
        process.env.EMDASH_LP_MEMORY_MIB = '64';
        process.env.EMDASH_LP_RESOURCE_BACKEND = 'prlimit';
        const options = {
            packageRoot: root,
            runnerPath: resolve(__dirname, '../emdash2/scripts/run_lambdapi.py'),
            timeoutMs: 5_000
        };
        const source = { source: 'symbol fixture : TYPE;\n', sourceMap: [] };
        install('import resource\nassert resource.getrlimit(resource.RLIMIT_AS)[0]==64*1024**2\nprint("fixture checked")\n');
        const result = checkLambdapiProbe(source, options);
        assert.equal(result.accepted, true, result.rawDiagnostics);
        assert.equal(result.timedOut, false);
        assert.match(result.stdout, /fixture checked/u);
        const receipt = JSON.parse(readFileSync(result.validationReceiptPath, 'utf8'));
        assert.equal(receipt.outcome, 'passed-fresh');
        assert.equal(receipt.settings.memoryMiB, 64);
        assert.equal(receipt.observedResourceBackend, 'prlimit');

        install('print("Uncaught [Out of memory].")\n');
        const fatal = checkLambdapiProbe(source, options);
        assert.equal(fatal.accepted, false);
        assert.equal(fatal.status, 1);
        const fatalReceipt = JSON.parse(readFileSync(fatal.validationReceiptPath, 'utf8'));
        assert.equal(fatalReceipt.checkerExit, 0);
        assert.equal(fatalReceipt.outcome, 'allocation-failed');
        assert.equal(fatalReceipt.reusable, false);

        install('import signal,time\nsignal.signal(signal.SIGINT,signal.SIG_IGN)\ntime.sleep(20)\n');
        const timed = checkLambdapiProbe(source, { ...options, timeoutMs: 100 });
        assert.equal(timed.accepted, false);
        assert.equal(timed.timedOut, true, timed.rawDiagnostics);
        assert.equal(timed.status, 124);
        const timedReceipt = JSON.parse(readFileSync(timed.validationReceiptPath, 'utf8'));
        assert.equal(timedReceipt.reusable, false);
    } finally {
        for (const [key, value] of before) {
            if (value === undefined) delete process.env[key];
            else process.env[key] = value;
        }
        rmSync(root, { recursive: true, force: true });
    }
});
