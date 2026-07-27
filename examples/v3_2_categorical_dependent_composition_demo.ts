/**
 * Run with:
 *   ./scripts/pnpmw run demo:categorical-dependent-composition
 */

import {
    formatCoreCategoricalDependentCompositionDemo
} from '../src/v3_2';

process.stdout.write(
    `${formatCoreCategoricalDependentCompositionDemo()}\n`
);
