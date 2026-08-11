/** Repository entry point for the stateless proof-agent benchmark adapter. */

import {
    runCoreLfProofAgentBenchmarkCli
} from '../src/v3_2/lf_proof_agent_benchmark_cli';

process.exitCode = runCoreLfProofAgentBenchmarkCli(process.argv.slice(2));
