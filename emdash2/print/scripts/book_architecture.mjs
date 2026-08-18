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

const PROVENANCE_ID = /^[A-Z][A-Z0-9-]*$/;

export function deriveRequiredProvenanceContract(requiredAdaptations) {
  if (!Array.isArray(requiredAdaptations)) {
    return {
      ids: [],
      isNonempty: false,
      isUnique: false,
      isWellFormed: false,
    };
  }

  return {
    ids: requiredAdaptations,
    isNonempty: requiredAdaptations.length > 0,
    isUnique: new Set(requiredAdaptations).size === requiredAdaptations.length,
    isWellFormed: requiredAdaptations.every(
      (id) => typeof id === 'string' && PROVENANCE_ID.test(id)
    ),
  };
}
