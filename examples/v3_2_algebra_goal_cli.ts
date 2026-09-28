import { runAlgebraGoalCli } from '../src/v3_2/algebra_goal_cli';
import { startAlgebraGoalMcp } from '../src/v3_2/algebra_goal_mcp';

if (process.argv[2] === 'mcp') {
    if (process.argv.length !== 3 || __filename.endsWith('.ts')) {
        process.stderr.write('Use the built emdash-agent.cjs mcp command for STDIO.\n');
        process.exitCode = 1;
    } else void startAlgebraGoalMcp(__filename).catch(error => {
        process.stderr.write(`${error instanceof Error ? error.message : String(error)}\n`);
        process.exitCode = 1;
    });
} else void runAlgebraGoalCli(process.argv.slice(2)).then(code => { process.exitCode = code; });
