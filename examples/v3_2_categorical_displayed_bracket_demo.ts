/**
 * Run with:
 *   ./scripts/pnpmw run demo:categorical-displayed-bracket
 */

import {
    formatCoreCategoricalDisplayedBracketDemo
} from '../src/v3_2';

process.stdout.write(
    `${formatCoreCategoricalDisplayedBracketDemo()}\n`
);
