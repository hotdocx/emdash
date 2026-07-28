/**
 * Run with:
 *   ./scripts/pnpmw run demo:categorical-fibred-product
 */

import {
    formatCoreCategoricalFibredProductDemo
} from '../src/v3_2';

process.stdout.write(
    `${formatCoreCategoricalFibredProductDemo()}\n`
);
