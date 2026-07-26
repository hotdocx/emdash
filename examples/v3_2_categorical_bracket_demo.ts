/**
 * Run with:
 *   ./scripts/pnpmw run demo:categorical-bracket
 */

import {
    formatCoreCategoricalBracketDemo
} from '../src/v3_2';

process.stdout.write(`${formatCoreCategoricalBracketDemo()}\n`);
