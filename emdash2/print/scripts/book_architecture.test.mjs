import assert from 'node:assert/strict';
import test from 'node:test';
import { deriveNumberedChapterContract } from './book_architecture.mjs';

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
