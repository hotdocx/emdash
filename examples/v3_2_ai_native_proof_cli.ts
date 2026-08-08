/**
 * Thin process launcher for the local AI-native proof commands.
 *
 * Run through `./scripts/emdash check` or `./scripts/emdash goals`.
 */

import {
    runCoreAiProofCli
} from '../src/v3_2/ai_proof_cli';

process.exitCode = runCoreAiProofCli(process.argv.slice(2));
