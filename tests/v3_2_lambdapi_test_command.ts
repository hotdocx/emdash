/** Resource-bounded adapter for opt-in CLI/export tests; stdout stays raw. */
import {
    spawnSync,
    SpawnSyncOptionsWithStringEncoding,
    SpawnSyncReturns
} from 'node:child_process';
import { resolve } from 'node:path';

/** Preserve a frozen qualification corpus while adapting its repository runner. */
export function repositoryConformanceCommand(historical: string): string {
    if (!historical.startsWith('timeout 60s env ') || !historical.includes(' --test ')) {
        throw new Error('Unrecognized historical conformance command');
    }
    return historical
        .replace('timeout 60s env ', 'timeout --signal=KILL 600s env ')
        .replace(' --test ', ' --test --test-concurrency=1 ');
}

export function runBoundedLambdapi(
    args: readonly string[],
    options: SpawnSyncOptionsWithStringEncoding
): SpawnSyncReturns<string> {
    const timeoutMs = options.timeout ?? 60_000;
    if (!Number.isInteger(timeoutMs) || timeoutMs < 1 || timeoutMs > 600_000) {
        throw new Error('Lambdapi test deadline must be 1..600000ms');
    }
    const guard = resolve(__dirname, '../emdash2/scripts/lambdapi_resource_guard.sh');
    return spawnSync('bash', [
        guard, 'timeout', '--signal=KILL', `${timeoutMs / 1000}s`,
        'lambdapi', ...args
    ], {
        ...options,
        timeout: timeoutMs + 5_000,
        killSignal: 'SIGKILL',
        env: {
            ...(options.env ?? process.env),
            EMDASH_LP_TIMEOUT: `${Math.ceil(timeoutMs / 1000)}s`
        }
    });
}
