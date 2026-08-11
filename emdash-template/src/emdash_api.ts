export * from '../../src/v3_2/browser_directed.js';

/**
 * Keep the categorical/report closure out of the initial browser chunk.
 * Loading this module does not execute the full report; that remains an
 * explicit reviewer action.
 */
export const loadCoreBrowserReviewer = () =>
    import('../../src/v3_2/browser_reviewer.js');

/**
 * Load the release-pinned paper/proof recheck only on reviewer request.
 * The browser module performs no hashing or file access; release parity is
 * established separately by the Node-owned exact-file gate.
 */
export const loadCoreAiResearchOverview = () =>
    import('../../src/v3_2/ai_research_overview_browser.js');

/**
 * Load only the inert PathOut parser and pinned qualification manifest.
 * The Node semantic adapter is intentionally outside the browser closure.
 */
export const loadCorePathoutPresentation = () =>
    import('../../src/v3_2/pathout_presentation.js');

/**
 * Load and construct the representative proof-agent corpus only after an
 * explicit reviewer action. The initial browser entry deliberately does not
 * acquire this comparatively large semantic closure.
 */
export const loadCoreProofAgentBenchmark = () =>
    import('../../src/v3_2/lf_proof_agent_public_corpus.js');

/**
 * Vite fingerprints and emits the generated current book as a static asset.
 */
export const EMDASH_BOOK_URL = new URL(
    '../../docs/emdash-book.pdf',
    import.meta.url
).href;

/**
 * Vite fingerprints and emits the current overview paper as a static asset.
 */
export const EMDASH_ARTICLE_URL = new URL(
    '../../docs/emdash3_2.pdf',
    import.meta.url
).href;
