import {
    defineConfig
} from 'vite';

/**
 * Keep production assets relative so the same static build works at a
 * project subpath such as https://hotdocx.github.io/emdash/ and on other
 * static hosts without a Node server.
 */
export default defineConfig({
    base: './'
});
