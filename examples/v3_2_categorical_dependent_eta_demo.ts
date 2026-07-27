/**
 * Run with:
 *   ./scripts/pnpmw run demo:categorical-dependent
 */

import {
    formatCoreCategoricalDependentEtaDemo
} from '../src/v3_2';

process.stdout.write(
    `${formatCoreCategoricalDependentEtaDemo()}\n`
);
