# emdash Sandpack Playground

This directory contains a standalone React/Vite application that serves as an interactive playground for the `emdash` type theory kernel.

It can be run in two ways:
1.  Locally for development and testing using Vite.
2.  As a template within a Sandpack instance for embedding in web applications like `hotdocx`.

## Running Locally with Vite

This is the recommended way to work on the playground UI itself. The local Vite server uses Hot Module Replacement (HMR) for a fast development experience.

**Prerequisites:**
*   Node.js and npm (or pnpm/yarn) installed.

**Steps:**

1.  Navigate to this directory from the project root:
    ```bash
    cd emdash-template
    ```
2.  Install the dependencies:
    ```bash
    npm install
    ```
3.  Start the development server:
    ```bash
    npx vite
    ```
Vite will start a local server, and you can access the playground in your browser at the URL it provides (usually `http://localhost:5173`). The application works locally because Vite can resolve the `emdash` kernel files from the parent `src` directory.

## Using as a Sandpack Template

This template is designed to be used with [Sandpack](https://sandpack.codesandbox.io/), allowing `emdash` to be run interactively in a browser-based environment. To do this, you need to construct a file map for Sandpack by combining the files from this template with the core `emdash` kernel files.

The key challenge is that Sandpack operates on a flat virtual file system and cannot resolve modules outside its root (i.e., paths like `../../src/...` won't work). Therefore, a script is needed to prepare the files for the Sandpack provider.

**Procedure:**

1.  **Collect Template Files:** Programmatically read the contents of all files within the `emdash-template` directory (excluding `node_modules`, `dist`, etc.). These will form the base of your Sandpack file map. Map their paths relative to the `emdash-template` directory to paths relative to the Sandpack root.
    *   `emdash-template/index.html` -> `/index.html`
    *   `emdash-template/package.json` -> `/package.json`
    *   `emdash-template/src/App.tsx` -> `/src/App.tsx`
    *   ...and so on.

2.  **Collect `emdash` Kernel Files:** Read the contents of all `.ts` files from the main `../src/` directory of the `emdash` project. Add them to the Sandpack file map under the `/src/` path.
    *   `../src/types.ts` -> `/src/types.ts`
    *   `../src/state.ts` -> `/src/state.ts`
    *   ...and so on.

3.  **Modify and Add the API Barrel File:** The file `emdash-template/src/emdash_api.ts` acts as a bridge. Its import paths must be adjusted for the Sandpack environment.
    *   Read the content of `emdash-template/src/emdash_api.ts`.
    *   For each line, replace the relative path `../../src/` with a path relative to the Sandpack `/src` directory, which is `./`. For example, `export * from '../../src/types.js';` becomes `export * from './types.js';`.
    *   Add this modified content to the Sandpack file map as `/src/emdash_api.ts`.

This process creates a self-contained project within Sandpack where the React UI can import and interact with the full `emdash` kernel. 