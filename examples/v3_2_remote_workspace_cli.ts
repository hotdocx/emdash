/** Thin process launcher for mounted TypeScript/emdash workspace checks. */

import {
    runCoreLfRemoteWorkspaceCli
} from '../src/v3_2/lf_remote_workspace_cli';

void runCoreLfRemoteWorkspaceCli(process.argv.slice(2)).then(exitCode => {
    process.exitCode = exitCode;
});
