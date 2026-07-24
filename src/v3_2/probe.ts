/**
 * Deterministic Lambdapi probe serialization and bounded checker bridge.
 */

import { spawnSync } from 'node:child_process';
import {
    existsSync,
    mkdirSync,
    mkdtempSync,
    rmSync,
    writeFileSync
} from 'node:fs';
import { join, relative, resolve } from 'node:path';
import {
    KernelExpression,
    SourceSpan,
    formatSourceSpan
} from './kernel';
import {
    LAMBDAPI_V32_MODULE,
    LAMBDAPI_V32_OWNER_BINDINGS,
    LAMBDAPI_V32_PROOF_PROBE_BINDINGS,
    serializeKernelExpression
} from './lambdapi';
import {
    ElaboratedSurfaceTerm,
    elaborateSurfaceTerm
} from './elaborator';
import {
    SurfaceContext,
    SurfaceTerm,
    coreTypeToKernelType
} from './surface';

export interface KernelProbeDeclaration {
    name: string;
    type: KernelExpression;
    span: SourceSpan;
}

export interface KernelProbeAssertion {
    label: string;
    term: KernelExpression;
    type: KernelExpression;
    span: SourceSpan;
}

export interface KernelProbeNegativeAssertion {
    label: string;
    term: KernelExpression;
    type: KernelExpression;
    span: SourceSpan;
}

export interface KernelProbeConversionAssertion {
    label: string;
    left: KernelExpression;
    right: KernelExpression;
    span: SourceSpan;
}

export interface KernelProbeProofTimeComparison {
    label: string;
    classifier: KernelExpression;
    left: KernelExpression;
    right: KernelExpression;
    span: SourceSpan;
}

export interface KernelProbeNonConversionAssertion {
    label: string;
    left: KernelExpression;
    right: KernelExpression;
    span: SourceSpan;
}

export interface KernelProbe {
    requiredModule: typeof LAMBDAPI_V32_MODULE;
    declarations: readonly KernelProbeDeclaration[];
    assertions: readonly KernelProbeAssertion[];
    negativeAssertions?: readonly KernelProbeNegativeAssertion[];
    conversions?: readonly KernelProbeConversionAssertion[];
    proofTimeComparisons?: readonly KernelProbeProofTimeComparison[];
    nonConversions?: readonly KernelProbeNonConversionAssertion[];
}

export interface ProbeSourceMapEntry {
    generatedLine: number;
    kind:
        | 'declaration'
        | 'assertion'
        | 'negative-assertion'
        | 'conversion'
        | 'proof-time-comparison'
        | 'non-conversion';
    label: string;
    sourceSpan: SourceSpan;
}

export interface SerializedProbe {
    source: string;
    sourceMap: readonly ProbeSourceMapEntry[];
}

export interface ProbeGeneratedDiagnosticLocation {
    readonly path: string;
    readonly line: number;
    readonly startColumn: number;
    readonly endColumn: number;
}

export interface ProbeSourceMappedDiagnostic {
    readonly generated: ProbeGeneratedDiagnosticLocation;
    readonly kind: ProbeSourceMapEntry['kind'];
    readonly label: string;
    readonly sourceSpan: SourceSpan;
}

export interface SurfaceProbeCase {
    label: string;
    term: SurfaceTerm;
}

export interface CompiledSurfaceProbeCase extends SurfaceProbeCase {
    elaborated: ElaboratedSurfaceTerm;
}

export interface CompiledSurfaceProbe {
    cases: readonly CompiledSurfaceProbeCase[];
    probe: KernelProbe;
    serialized: SerializedProbe;
}

const safeCommentText = (value: string): string =>
    value.replace(/[\r\n]+/g, ' ').replace(/\*\//g, '* /');

export function declarationsFromSurfaceContext(
    context: SurfaceContext
): readonly KernelProbeDeclaration[] {
    return context.bindings.map(binding => ({
        name: binding.name,
        type: binding.kernelType,
        span: binding.span
    }));
}

export function compileSurfaceProbe(
    context: SurfaceContext,
    cases: readonly SurfaceProbeCase[]
): CompiledSurfaceProbe {
    const compiledCases = cases.map(testCase => ({
        ...testCase,
        elaborated: elaborateSurfaceTerm(context, testCase.term)
    }));
    const probe: KernelProbe = {
        requiredModule: LAMBDAPI_V32_MODULE,
        declarations: declarationsFromSurfaceContext(context),
        assertions: compiledCases.map(testCase => ({
            label: testCase.label,
            term: testCase.elaborated.term,
            type: coreTypeToKernelType(
                testCase.elaborated.type,
                testCase.elaborated.sourceSpan,
                `expected type of probe assertion ${testCase.label}`
            ),
            span: testCase.elaborated.sourceSpan
        }))
    };
    return {
        cases: compiledCases,
        probe,
        serialized: serializeKernelProbe(probe)
    };
}

export function serializeKernelProbe(probe: KernelProbe): SerializedProbe {
    const lines: string[] = [];
    const sourceMap: ProbeSourceMapEntry[] = [];
    const negativeAssertions = probe.negativeAssertions ?? [];
    const conversions = probe.conversions ?? [];
    const proofTimeComparisons = probe.proofTimeComparisons ?? [];
    const nonConversions = probe.nonConversions ?? [];

    const push = (line: string): number => {
        lines.push(line);
        return lines.length;
    };

    push('/* Generated by the TypeScript emdash v3.2 conformance probe. */');
    push(`require open ${probe.requiredModule};`);
    push('');

    for (const declaration of probe.declarations) {
        push(`// source ${formatSourceSpan(declaration.span)}`);
        const generatedLine = push(
            `symbol ${declaration.name} : ` +
            `${serializeKernelExpression(declaration.type)};`
        );
        sourceMap.push({
            generatedLine,
            kind: 'declaration',
            label: declaration.name,
            sourceSpan: declaration.span
        });
    }

    if (
        probe.declarations.length > 0 &&
        (
            probe.assertions.length > 0 ||
            negativeAssertions.length > 0 ||
            conversions.length > 0 ||
            proofTimeComparisons.length > 0 ||
            nonConversions.length > 0
        )
    ) {
        push('');
    }

    for (const assertion of probe.assertions) {
        push(
            `// ${safeCommentText(assertion.label)}; source ` +
            formatSourceSpan(assertion.span)
        );
        const generatedLine = push(
            `assert ⊢ ${serializeKernelExpression(assertion.term)} : ` +
            `${serializeKernelExpression(assertion.type)};`
        );
        sourceMap.push({
            generatedLine,
            kind: 'assertion',
            label: assertion.label,
            sourceSpan: assertion.span
        });
    }

    if (
        probe.assertions.length > 0 &&
        (
            negativeAssertions.length > 0 ||
            conversions.length > 0 ||
            proofTimeComparisons.length > 0 ||
            nonConversions.length > 0
        )
    ) {
        push('');
    }

    for (const assertion of negativeAssertions) {
        push(
            `// ${safeCommentText(assertion.label)}; source ` +
            formatSourceSpan(assertion.span)
        );
        const generatedLine = push(
            `assertnot ⊢ ${serializeKernelExpression(assertion.term)} : ` +
            `${serializeKernelExpression(assertion.type)};`
        );
        sourceMap.push({
            generatedLine,
            kind: 'negative-assertion',
            label: assertion.label,
            sourceSpan: assertion.span
        });
    }

    if (
        negativeAssertions.length > 0 &&
        (
            conversions.length > 0 ||
            proofTimeComparisons.length > 0 ||
            nonConversions.length > 0
        )
    ) {
        push('');
    }

    for (const conversion of conversions) {
        push(
            `// ${safeCommentText(conversion.label)}; source ` +
            formatSourceSpan(conversion.span)
        );
        const generatedLine = push(
            `assert ⊢ ${serializeKernelExpression(conversion.left)} ≡ ` +
            `${serializeKernelExpression(conversion.right)};`
        );
        sourceMap.push({
            generatedLine,
            kind: 'conversion',
            label: conversion.label,
            sourceSpan: conversion.span
        });
    }

    if (
        conversions.length > 0 &&
        (proofTimeComparisons.length > 0 || nonConversions.length > 0)
    ) {
        push('');
    }

    for (const comparison of proofTimeComparisons) {
        push(
            `// ${safeCommentText(comparison.label)}; source ` +
            formatSourceSpan(comparison.span)
        );
        const classifier = serializeKernelExpression(
            comparison.classifier
        );
        const left = serializeKernelExpression(comparison.left);
        const right = serializeKernelExpression(comparison.right);
        const decode = LAMBDAPI_V32_OWNER_BINDINGS.decode.serializedName;
        const equality =
            LAMBDAPI_V32_PROOF_PROBE_BINDINGS.equality.serializedName;
        const reflexivity =
            LAMBDAPI_V32_PROOF_PROBE_BINDINGS.reflexivity.serializedName;
        const generatedLine = push(
            `assert ⊢ @${reflexivity} (${classifier}) (${left}) : ` +
            `${decode} (@${equality} (${classifier}) ` +
            `(${left}) (${right}));`
        );
        sourceMap.push({
            generatedLine,
            kind: 'proof-time-comparison',
            label: comparison.label,
            sourceSpan: comparison.span
        });
    }

    if (
        proofTimeComparisons.length > 0 &&
        nonConversions.length > 0
    ) {
        push('');
    }

    for (const nonConversion of nonConversions) {
        push(
            `// ${safeCommentText(nonConversion.label)}; source ` +
            formatSourceSpan(nonConversion.span)
        );
        const generatedLine = push(
            `assertnot ⊢ ` +
            `${serializeKernelExpression(nonConversion.left)} ≡ ` +
            `${serializeKernelExpression(nonConversion.right)};`
        );
        sourceMap.push({
            generatedLine,
            kind: 'non-conversion',
            label: nonConversion.label,
            sourceSpan: nonConversion.span
        });
    }

    return {
        source: `${lines.join('\n')}\n`,
        sourceMap
    };
}

export interface LambdapiProbeOptions {
    /**
     * Directory containing lambdapi.pkg and the active emdash3_2.lp module.
     */
    packageRoot: string;
    /**
     * Hard upper bound. Repository policy forbids exploratory checks over 60s.
     */
    timeoutMs?: number;
    /**
     * Keep Lambdapi diagnostics enabled for owner-position warning probes.
     * Existing conformance probes default to warning suppression.
     */
    warningsEnabled?: boolean;
}

export interface LambdapiProbeResult {
    accepted: boolean;
    timedOut: boolean;
    status: number | null;
    signal: NodeJS.Signals | null;
    stdout: string;
    stderr: string;
    /**
     * Unmodified concatenation of Lambdapi stdout, stderr, and spawn errors.
     */
    rawDiagnostics: string;
    /**
     * Exact generated-statement locations mapped to original source spans.
     */
    sourceMappedDiagnostics: readonly ProbeSourceMappedDiagnostic[];
    /**
     * Source-facing annotations followed by the raw diagnostics. When no
     * generated location maps, this is exactly `rawDiagnostics`.
     */
    diagnostics: string;
}

const normalizeDiagnosticPath = (path: string): string =>
    path.replace(/\\/g, '/').replace(/^\.\//, '');

/**
 * Map Lambdapi's observed `[path:line:start-end]` diagnostic headers back to
 * exact serialized-probe statements.
 *
 * Only an explicitly supplied probe path and an exact source-map line match
 * are eligible. Diagnostics from imported authorities and generated
 * whitespace/comments remain raw rather than being attributed speculatively.
 */
export function remapLambdapiProbeDiagnostics(
    rawDiagnostics: string,
    serialized: SerializedProbe,
    generatedProbePaths: readonly string[]
): readonly ProbeSourceMappedDiagnostic[] {
    const acceptedPaths = new Set(
        generatedProbePaths.map(normalizeDiagnosticPath)
    );
    const entriesByLine = new Map(
        serialized.sourceMap.map(entry => [entry.generatedLine, entry])
    );
    const locationPattern =
        /\[([^\]\r\n]+):(\d+):(\d+)(?:-(\d+))?\]/g;
    const locationText = rawDiagnostics.replace(
        /\u001b\[[0-9;]*m/g,
        ''
    );
    const mappings: ProbeSourceMappedDiagnostic[] = [];
    const seen = new Set<string>();

    for (
        let match = locationPattern.exec(locationText);
        match !== null;
        match = locationPattern.exec(locationText)
    ) {
        const path = normalizeDiagnosticPath(match[1]);
        if (!acceptedPaths.has(path)) continue;

        const line = Number(match[2]);
        const startColumn = Number(match[3]);
        const endColumn = Number(match[4] ?? match[3]);
        const sourceEntry = entriesByLine.get(line);
        if (sourceEntry === undefined) continue;

        const key = `${path}:${line}:${startColumn}-${endColumn}`;
        if (seen.has(key)) continue;
        seen.add(key);
        mappings.push({
            generated: {
                path,
                line,
                startColumn,
                endColumn
            },
            kind: sourceEntry.kind,
            label: sourceEntry.label,
            sourceSpan: sourceEntry.sourceSpan
        });
    }

    return mappings;
}

const formatFullSourceSpan = (span: SourceSpan): string =>
    `${formatSourceSpan(span)}-${span.end.line}:${span.end.column}`;

const safeDiagnosticLabel = (label: string): string =>
    label.replace(/[\r\n]+/g, ' ');

export function formatLambdapiProbeDiagnostics(
    rawDiagnostics: string,
    mappings: readonly ProbeSourceMappedDiagnostic[]
): string {
    if (mappings.length === 0) return rawDiagnostics;

    const sourceFacing = mappings.map(mapping =>
        `[source ${formatFullSourceSpan(mapping.sourceSpan)}] ` +
        `${mapping.kind} "${safeDiagnosticLabel(mapping.label)}" ` +
        `(generated ${mapping.generated.path}:` +
        `${mapping.generated.line}:${mapping.generated.startColumn}-` +
        `${mapping.generated.endColumn})`
    );
    return (
        `Source-mapped Lambdapi diagnostics:\n` +
        `${sourceFacing.join('\n')}\n\n` +
        `Raw Lambdapi diagnostics:\n${rawDiagnostics}`
    );
}

export function checkLambdapiProbe(
    serialized: SerializedProbe,
    options: LambdapiProbeOptions
): LambdapiProbeResult {
    const timeoutMs = options.timeoutMs ?? 30_000;
    if (!Number.isInteger(timeoutMs) || timeoutMs <= 0 || timeoutMs > 60_000) {
        throw new Error(
            `Lambdapi probe timeout must be an integer in 1..60000ms; ` +
            `received ${timeoutMs}`
        );
    }

    const packageRoot = resolve(options.packageRoot);
    if (!existsSync(join(packageRoot, 'lambdapi.pkg'))) {
        throw new Error(
            `Lambdapi package root has no lambdapi.pkg: ${packageRoot}`
        );
    }

    const temporaryRoot = join(packageRoot, 'tmp');
    mkdirSync(temporaryRoot, { recursive: true });
    const temporaryDirectory = mkdtempSync(join(temporaryRoot, 'elab0-'));
    const probePath = join(temporaryDirectory, 'probe.lp');

    try {
        writeFileSync(probePath, serialized.source, 'utf8');
        const result = spawnSync(
            'lambdapi',
            [
                'check',
                ...(options.warningsEnabled ? [] : ['-w']),
                relative(packageRoot, probePath)
            ],
            {
                cwd: packageRoot,
                encoding: 'utf8',
                timeout: timeoutMs,
                killSignal: 'SIGINT',
                // Warning-enabled imports of the active kernel intentionally
                // produce a large known diagnostic stream.
                maxBuffer: options.warningsEnabled
                    ? 64 * 1024 * 1024
                    : 4 * 1024 * 1024
            }
        );
        const stdout = result.stdout ?? '';
        const stderr = result.stderr ?? '';
        const errorCode = (result.error as NodeJS.ErrnoException | undefined)
            ?.code;
        const timedOut = errorCode === 'ETIMEDOUT';
        const errorText = result.error
            ? `${result.error.name}: ${result.error.message}`
            : '';
        const rawDiagnostics = [stdout, stderr, errorText]
            .filter(part => part.length > 0)
            .join('\n');
        const sourceMappedDiagnostics = remapLambdapiProbeDiagnostics(
            rawDiagnostics,
            serialized,
            [
                relative(packageRoot, probePath),
                probePath
            ]
        );
        const diagnostics = formatLambdapiProbeDiagnostics(
            rawDiagnostics,
            sourceMappedDiagnostics
        );

        return {
            accepted: result.status === 0 && !result.error,
            timedOut,
            status: result.status,
            signal: result.signal,
            stdout,
            stderr,
            rawDiagnostics,
            sourceMappedDiagnostics,
            diagnostics
        };
    } finally {
        rmSync(temporaryDirectory, { recursive: true, force: true });
    }
}
