/**
 * Run with:
 *   ./scripts/pnpmw run demo:categorical-displayed-evaluation
 */

import {
    formatCoreCategoricalDisplayedEvaluationDemo
} from '../src/v3_2';

process.stdout.write(
    `${formatCoreCategoricalDisplayedEvaluationDemo()}\n`
);
