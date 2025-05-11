// import js from "@eslint/js";
// import globals from "globals";
// import tseslint from "typescript-eslint";
// import { defineConfig } from "eslint/config";


// export default defineConfig([
//   { files: ["**/*.{js,mjs,cjs,ts}"], plugins: { js }, extends: ["js/recommended"] },
//   { files: ["**/*.{js,mjs,cjs,ts}"], languageOptions: { globals: globals.browser } },
//   tseslint.configs.recommended,
// ]);

import js from "@eslint/js";
import globals from "globals";
import tseslint from "typescript-eslint";
import { defineConfig } from "eslint/config";

export default defineConfig([
  {
    files: ["**/*.{js,mjs,cjs,ts}"],
    plugins: {  js, "@typescript-eslint": tseslint.plugin },
    extends: [],
    languageOptions: { 
      parser: tseslint.parser, 
      globals: globals.browser 
    },
    rules: {
      "@typescript-eslint/no-unused-vars": "off", // Disable unused variable warnings
      "@typescript-eslint/no-explicit-any": "off", // Allow 'any' type
      "prefer-const": "off", // Allow 'let' even if not reassigned
      "no-console": "off", // Allow console.log usage
      "no-debugger": "off", // Allow debugger usage
      "no-var": "off" // Allow usage of 'var'
    }
  }
  // ,
  // tseslint.configs.recommended // You can remove this if you want a fully lenient config
]);
