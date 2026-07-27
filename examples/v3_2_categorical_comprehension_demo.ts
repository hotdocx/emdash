/**
 * Run with:
 *   ./scripts/pnpmw run demo:categorical-comprehension
 */

import {
    formatCoreCategoricalComprehensionDemo
} from '../src/v3_2';

process.stdout.write(
    `${formatCoreCategoricalComprehensionDemo()}\n`
);
