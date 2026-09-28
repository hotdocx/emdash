#!/usr/bin/env node
import { fileURLToPath, pathToFileURL } from 'node:url';

if (process.argv.length !== 2) throw new Error('The plugin MCP launcher accepts no extra arguments.');
const executable = fileURLToPath(new URL('../dist/emdash-agent.cjs', import.meta.url));
process.argv = [process.execPath, executable, 'mcp'];
await import(pathToFileURL(executable).href);
