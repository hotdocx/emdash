/**
 * Run with:
 *   ./scripts/pnpmw run demo:categorical-displayed-chain
 */

import {
    formatCoreCategoricalDisplayedChainDemo
} from '../src/v3_2';

process.stdout.write(
    `${formatCoreCategoricalDisplayedChainDemo()}\n`
);
