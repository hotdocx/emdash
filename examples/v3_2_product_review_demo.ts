/**
 * Run with:
 *   ./scripts/pnpmw run demo:external-review
 */

import {
    formatCoreProductReviewDemo
} from '../src/v3_2';

process.stdout.write(
    `${formatCoreProductReviewDemo()}\n`
);
