/** Thin process launcher for mounted proof-development commands. */

import {
    runCoreLfProofDevelopmentCli
} from '../src/v3_2/lf_proof_development_cli';

void runCoreLfProofDevelopmentCli(process.argv.slice(2)).then(exitCode => {
    process.exitCode = exitCode;
});
