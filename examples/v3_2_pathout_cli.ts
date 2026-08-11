/** Thin process launcher for finite PathOut presentation commands. */

import {
    runCorePathoutPresentationCli
} from '../src/v3_2/pathout_presentation_cli';

void runCorePathoutPresentationCli(process.argv.slice(2)).then(exitCode => {
    process.exitCode = exitCode;
});
