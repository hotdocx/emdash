import { runAlgebraGoalCli } from '../src/v3_2/algebra_goal_cli';

void runAlgebraGoalCli(process.argv.slice(2)).then(code => { process.exitCode = code; });
