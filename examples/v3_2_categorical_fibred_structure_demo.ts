/**
 * Run with:
 *   ./scripts/pnpmw run demo:categorical-fibred-structure
 */

import {
    formatCoreCategoricalFibredStructureDemo
} from '../src/v3_2';

process.stdout.write(
    `${formatCoreCategoricalFibredStructureDemo()}\n`
);
