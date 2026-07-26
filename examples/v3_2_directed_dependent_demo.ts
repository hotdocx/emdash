/**
 * Run with:
 *   ./scripts/pnpmw run demo:directed-dependent
 */

import {
    formatCoreDirectedDependentDemo
} from '../src/v3_2';

process.stdout.write(`${formatCoreDirectedDependentDemo()}\n`);
