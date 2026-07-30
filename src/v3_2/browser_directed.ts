/**
 * Additive browser-safe entry for the reviewed directed dependent witness.
 *
 * The frozen `browser.ts` entry remains the exact `emdash-v3.2-mvp-1`
 * product boundary. This module retains that API and adds only the existing
 * root continuation's structured dependent demo.
 */

import {
    runCoreDirectedDependentDemo
} from './directed_dependent_demo';
import {
    CORE_MVP_MANIFEST
} from './manifest';

export * from './browser';
export {
    formatCoreDirectedDependentDemo,
    runCoreDirectedDependentDemo
} from './directed_dependent_demo';
export type {
    CoreDirectedDependentDemoDiagnostic,
    CoreDirectedDependentDemoResult,
    CoreDirectedDependentDemoTraceEntry
} from './directed_dependent_demo';

export interface CoreDirectedBrowserDemoBoundary {
    readonly revision: 'BROWSER-DIRECTED-1A';
    readonly status: 'opt-in-browser-demonstration';
    readonly baseProfile: 'emdash-v3.2-mvp-1';
    readonly continuationResultProfile:
        'emdash-v3.2-dttlf-directed-1';
    readonly entryPoint: 'src/v3_2/browser_directed.ts';
    readonly actualCheckerAndEvaluatorExecute: true;
    readonly productionLambdapiDependency: false;
    readonly nodeBuiltinDependency: false;
    readonly parserDependency: false;
    readonly categoricalBrowserProfileIncluded: false;
    readonly baseManifestUnchanged: true;
}

export const CORE_DIRECTED_BROWSER_DEMO_BOUNDARY:
CoreDirectedBrowserDemoBoundary = Object.freeze({
    revision: 'BROWSER-DIRECTED-1A',
    status: 'opt-in-browser-demonstration',
    baseProfile: 'emdash-v3.2-mvp-1',
    continuationResultProfile: 'emdash-v3.2-dttlf-directed-1',
    entryPoint: 'src/v3_2/browser_directed.ts',
    actualCheckerAndEvaluatorExecute: true,
    productionLambdapiDependency: false,
    nodeBuiltinDependency: false,
    parserDependency: false,
    categoricalBrowserProfileIncluded: false,
    baseManifestUnchanged: true
});

/**
 * Small browser smoke seam. Keeping execution behind a function makes the
 * entry import side-effect free while checking its advertised result profile.
 */
export function runCoreDirectedBrowserDemo() {
    if (
        CORE_MVP_MANIFEST.revision !==
        CORE_DIRECTED_BROWSER_DEMO_BOUNDARY.baseProfile
    ) {
        throw new Error(
            'The frozen minimal browser profile drifted outside the ' +
                'directed demo boundary'
        );
    }
    const result = runCoreDirectedDependentDemo();
    if (
        result.profile !==
        CORE_DIRECTED_BROWSER_DEMO_BOUNDARY.continuationResultProfile ||
        result.productionLambdapiDependency
    ) {
        throw new Error(
            'The directed browser demo drifted outside its reviewed boundary'
        );
    }
    return result;
}
