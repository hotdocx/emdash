/** Thin process launcher for the source-visible AI-native capability record. */

import {
    runCoreAiNativeCapabilitiesCli
} from '../src/v3_2/ai_native_capabilities_cli';

process.exitCode = runCoreAiNativeCapabilitiesCli(process.argv.slice(2));
