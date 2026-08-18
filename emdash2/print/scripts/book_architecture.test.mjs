import assert from 'node:assert/strict';
import test from 'node:test';
import {
  deriveNumberedChapterContract,
  deriveRequiredProvenanceContract,
} from './book_architecture.mjs';

function sourcesThrough(finalChapterNumber) {
  return [
    { id: 'preface' },
    ...Array.from(
      { length: finalChapterNumber },
      (_, index) => ({ id: 'chapter-' + (index + 1) })
    ),
    { id: 'appendix-notation' },
  ];
}

test('derives an extensible expansion range from contiguous manifest chapters', () => {
  const contract = deriveNumberedChapterContract(sourcesThrough(18), 8);

  assert.equal(contract.finalChapterNumber, 18);
  assert.equal(contract.expansionStart, 9);
  assert.equal(contract.expansionCount, 10);
  assert.equal(contract.isContiguous, true);
  assert.deepEqual(contract.actualIds, contract.expectedIds);
});

test('changes the expansion size when a later chapter is appended', () => {
  const contract = deriveNumberedChapterContract(sourcesThrough(24), 8);

  assert.equal(contract.finalChapterNumber, 24);
  assert.equal(contract.expansionCount, 16);
  assert.equal(contract.expectedIds.at(-1), 'chapter-24');
});

test('detects gaps, duplicates, and out-of-order chapter sources', () => {
  for (const ids of [
    ['chapter-1', 'chapter-3'],
    ['chapter-1', 'chapter-2', 'chapter-2'],
    ['chapter-2', 'chapter-1'],
  ]) {
    const contract = deriveNumberedChapterContract(
      ids.map((id) => ({ id })),
      1
    );
    assert.equal(contract.isContiguous, false, ids.join(', '));
  }
});

test('accepts a growing unique provenance requirement list', () => {
  for (const count of [13, 15, 28]) {
    const contract = deriveRequiredProvenanceContract(
      Array.from({ length: count }, (_, index) => 'HOTT-ADAPT-' + index)
    );
    assert.equal(contract.isNonempty, true);
    assert.equal(contract.isUnique, true);
    assert.equal(contract.isWellFormed, true);
  }
});

test('rejects absent, duplicate, and malformed provenance requirements', () => {
  for (const required of [
    undefined,
    [],
    ['HOTT-ADAPT-1', 'HOTT-ADAPT-1'],
    ['hott-adapt-1'],
  ]) {
    const contract = deriveRequiredProvenanceContract(required);
    assert.equal(
      contract.isNonempty && contract.isUnique && contract.isWellFormed,
      false
    );
  }
});
