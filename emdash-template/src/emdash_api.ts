export * from '../../src/v3_2/browser_directed.js';

/**
 * Keep the categorical/report closure out of the initial browser chunk.
 * Loading this module does not execute the full report; that remains an
 * explicit reviewer action.
 */
export const loadCoreBrowserReviewer = () =>
    import('../../src/v3_2/browser_reviewer.js');

/**
 * Vite fingerprints and emits the generated current book as a static asset.
 */
export const EMDASH_BOOK_URL = new URL(
    '../../docs/emdash-book.pdf',
    import.meta.url
).href;
