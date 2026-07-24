/**
 * Focused RELEASE-1A source-mapped Lambdapi diagnostic tests.
 */

import assert from 'node:assert';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    ProbeSourceMapEntry,
    SerializedProbe,
    checkLambdapiProbe,
    formatLambdapiProbeDiagnostics,
    remapLambdapiProbeDiagnostics,
    sourceSpan
} from '../src/v3_2';

const relativeProbePath = 'tmp/elab0-C18/probe.lp';
const absoluteProbePath =
    '/workspace/emdash2/tmp/elab0-C18/probe.lp';

const kinds: readonly ProbeSourceMapEntry['kind'][] = [
    'declaration',
    'assertion',
    'negative-assertion',
    'conversion',
    'proof-time-comparison',
    'non-conversion'
];

const syntheticProbe = (): SerializedProbe => ({
    source: 'synthetic source is not executed\n',
    sourceMap: kinds.map((kind, index) => ({
        generatedLine: index + 5,
        kind,
        label: `C18 ${kind}`,
        sourceSpan: sourceSpan(
            'fixtures/c18_surface.ts',
            index + 40,
            index + 2,
            index + 40,
            index + 12
        )
    }))
});

describe('TypeScript v3.2 RELEASE-1A probe diagnostics', () => {
    it('maps every statement kind across ANSI relative and absolute paths', () => {
        const headers = kinds.map((_, index) => {
            const path = index % 2 === 0
                ? relativeProbePath
                : absoluteProbePath;
            return `\u001b[31m[${path}:${index + 5}:0-${index + 20}] ` +
                `failure ${index}\u001b[0m`;
        });
        const raw = [
            ...headers,
            headers[0],
            '[emdash3_2.lp:5:0-10] imported authority diagnostic',
            `[${relativeProbePath}:99:0-4] unmapped generated line`
        ].join('\n');

        const mapped = remapLambdapiProbeDiagnostics(
            raw,
            syntheticProbe(),
            [relativeProbePath, absoluteProbePath]
        );

        assert.equal(mapped.length, kinds.length);
        assert.deepEqual(mapped.map(entry => entry.kind), kinds);
        assert.deepEqual(
            mapped.map(entry => entry.sourceSpan.start.line),
            [40, 41, 42, 43, 44, 45]
        );
        assert.deepEqual(
            mapped.map(entry => entry.generated.endColumn),
            [20, 21, 22, 23, 24, 25]
        );
        assert.equal(
            mapped.filter(entry =>
                entry.generated.path === relativeProbePath
            ).length,
            3
        );
        assert.equal(
            mapped.filter(entry =>
                entry.generated.path === absoluteProbePath
            ).length,
            3
        );
    });

    it('requires the exact probe path and exact generated statement line', () => {
        const raw = [
            '[other/probe.lp:5:0-4] same basename',
            `[${relativeProbePath}:4:0-4] source comment`,
            `[${relativeProbePath}:12:0-4] outside source map`
        ].join('\n');
        assert.deepEqual(
            remapLambdapiProbeDiagnostics(
                raw,
                syntheticProbe(),
                [relativeProbePath]
            ),
            []
        );
        assert.equal(
            formatLambdapiProbeDiagnostics(raw, []),
            raw
        );
    });

    it('prepends source-facing spans while preserving raw diagnostics', () => {
        const raw =
            `[${relativeProbePath}:6:0-21] Assertion failed.`;
        const mapped = remapLambdapiProbeDiagnostics(
            raw,
            syntheticProbe(),
            [relativeProbePath]
        );
        const formatted = formatLambdapiProbeDiagnostics(raw, mapped);

        assert.equal(
            formatted.startsWith(
                'Source-mapped Lambdapi diagnostics:'
            ),
            true
        );
        assert.match(
            formatted,
            /\[source fixtures\/c18_surface\.ts:41:3-41:13\]/
        );
        assert.match(formatted, /assertion "C18 assertion"/);
        assert.match(
            formatted,
            /generated tmp\/elab0-C18\/probe\.lp:6:0-21/
        );
        assert.ok(formatted.endsWith(raw));
    });

    it(
        'maps one observed bounded Lambdapi assertion failure',
        { skip: process.env.EMDASH_RUN_LAMBDAPI_PROBES !== '1' },
        () => {
            const span = sourceSpan(
                'fixtures/c18_surface.ts',
                42,
                7,
                42,
                19
            );
            const serialized: SerializedProbe = {
                source:
                    '/* Generated C18 diagnostic probe. */\n' +
                    'require open emdash.emdash3_2;\n\n' +
                    '// source fixtures/c18_surface.ts:40:2\n' +
                    'symbol c18_A : Cat;\n\n' +
                    '// source fixtures/c18_surface.ts:42:7\n' +
                    'assert ⊢ c18_A : TYPE;\n',
                sourceMap: [{
                    generatedLine: 5,
                    kind: 'declaration',
                    label: 'c18_A',
                    sourceSpan: sourceSpan(
                        'fixtures/c18_surface.ts',
                        40,
                        2,
                        40,
                        8
                    )
                }, {
                    generatedLine: 8,
                    kind: 'assertion',
                    label: 'C18 invalid assertion',
                    sourceSpan: span
                }]
            };

            const result = checkLambdapiProbe(serialized, {
                packageRoot: resolve(__dirname, '../emdash2'),
                timeoutMs: 30_000
            });

            assert.equal(result.accepted, false);
            assert.equal(result.timedOut, false);
            assert.match(
                result.rawDiagnostics,
                /probe\.lp:8:0-20\] Assertion failed/
            );
            assert.equal(result.sourceMappedDiagnostics.length, 1);
            assert.deepEqual(
                result.sourceMappedDiagnostics[0].sourceSpan,
                span
            );
            assert.equal(
                result.sourceMappedDiagnostics[0].label,
                'C18 invalid assertion'
            );
            assert.match(
                result.diagnostics,
                /\[source fixtures\/c18_surface\.ts:42:7-42:19\]/
            );
            assert.ok(
                result.diagnostics.endsWith(result.rawDiagnostics)
            );
        }
    );
});
