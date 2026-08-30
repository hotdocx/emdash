/** Opt-in Node process transport for external algebra oracles. */

import { spawn } from 'node:child_process';
import {
    AlgebraOracleError,
    AlgebraOracleProcessRequest,
    AlgebraOracleProcessResult,
    AlgebraOracleTransport
} from './algebra_oracle';

export const ALGEBRA_ORACLE_NODE_PROFILE = Object.freeze({
    revision: 'emdash-algebra-oracle-node-transport-v1' as const,
    shell: false as const,
    optIn: true as const,
    nodeBuiltinDependency: true as const,
    performsIo: true as const
});

export const createAlgebraOracleNodeTransport = (): AlgebraOracleTransport =>
    Object.freeze({
        execute(request: AlgebraOracleProcessRequest): Promise<AlgebraOracleProcessResult> {
            return new Promise((resolve, reject) => {
                const child = spawn(request.executable, [...request.args], {
                    shell: false,
                    stdio: ['pipe', 'pipe', 'pipe']
                });
                let stdout = '';
                let stderr = '';
                let bytes = 0;
                let settled = false;
                let timer: ReturnType<typeof setTimeout> | undefined;
                const finishError = (error: Error): void => {
                    if (settled) return;
                    settled = true;
                    if (timer !== undefined) clearTimeout(timer);
                    child.kill('SIGKILL');
                    reject(error);
                };
                const append = (current: string, chunk: Buffer): string => {
                    bytes += chunk.byteLength;
                    if (bytes > request.maximumOutputBytes) {
                        finishError(new AlgebraOracleError(
                            'PROCESS_FAILED',
                            'Oracle output exceeded the configured byte limit'
                        ));
                        return current;
                    }
                    return current + chunk.toString('utf8');
                };
                child.stdout.on('data', (chunk: Buffer) => {
                    stdout = append(stdout, chunk);
                });
                child.stderr.on('data', (chunk: Buffer) => {
                    stderr = append(stderr, chunk);
                });
                child.on('error', error => finishError(new AlgebraOracleError(
                    'PROCESS_FAILED',
                    `Could not start oracle executable: ${error.message}`
                )));
                child.on('close', code => {
                    if (settled) return;
                    settled = true;
                    if (timer !== undefined) clearTimeout(timer);
                    resolve(Object.freeze({
                        exitCode: code ?? -1,
                        stdout,
                        stderr
                    }));
                });
                timer = setTimeout(() => finishError(new AlgebraOracleError(
                    'PROCESS_FAILED',
                    `Oracle exceeded ${request.timeoutMilliseconds}ms timeout`
                )), request.timeoutMilliseconds);
                child.stdin.end(request.stdin, 'utf8');
            });
        }
    });
