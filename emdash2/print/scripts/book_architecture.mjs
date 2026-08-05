export function deriveNumberedChapterContract(sources, retainedChapterEnd) {
  if (!Array.isArray(sources)) {
    throw new TypeError('book sources must be an array');
  }
  if (!Number.isInteger(retainedChapterEnd) || retainedChapterEnd < 1) {
    throw new TypeError('retainedChapterEnd must be a positive integer');
  }

  const numberedSources = sources.filter(
    (source) => source && /^chapter-\d+$/.test(source.id)
  );
  const actualIds = numberedSources.map((source) => source.id);
  const chapterNumbers = actualIds.map(
    (id) => Number(id.slice('chapter-'.length))
  );
  const finalChapterNumber = chapterNumbers.length === 0
    ? 0
    : Math.max(...chapterNumbers);
  const expectedIds = Array.from(
    { length: finalChapterNumber },
    (_, index) => 'chapter-' + (index + 1)
  );

  return {
    numberedSources,
    actualIds,
    expectedIds,
    finalChapterNumber,
    expansionStart: retainedChapterEnd + 1,
    expansionCount: Math.max(finalChapterNumber - retainedChapterEnd, 0),
    isContiguous: actualIds.join('\n') === expectedIds.join('\n'),
  };
}
