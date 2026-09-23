import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, writeFileSync, rmSync } from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';
import { testRegistration } from './check-test-registration.mjs';

test('transitive test registration rejects forgotten suites and ignores type-only edges', () => {
  const root = mkdtempSync(path.join(os.tmpdir(), 'emdash-test-registration-'));
  try {
    mkdirSync(path.join(root, 'tests'));
    const put = (name, text) => writeFileSync(path.join(root, 'tests', name), text);
    put('main_tests.ts', "import './first_tests'; import type { T } from './forgotten_tests';");
    put('first_tests.ts', "import './second_tests';");
    put('second_tests.ts', "import './first_tests';");
    put('forgotten_tests.ts', 'export type T = string;');
    assert.deepEqual(testRegistration(root), { total: 3, missing: ['forgotten_tests.ts'] });
    put('main_tests.ts', "import './first_tests'; import './forgotten_tests';");
    assert.deepEqual(testRegistration(root), { total: 3, missing: [] });
  } finally {
    rmSync(root, { recursive: true, force: true });
  }
});
