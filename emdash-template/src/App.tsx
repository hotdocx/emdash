import {
  useEffect,
  useState
} from 'react';
import * as emdash from './emdash_api';
import './styles.css';

type ReviewerModule =
  Awaited<ReturnType<typeof emdash.loadCoreBrowserReviewer>>;
type ReviewerPresetId =
  ReviewerModule['CORE_BROWSER_REVIEWER_PRESETS'][number]['id'];
type ReviewerExpectedMode =
  ReviewerModule['CORE_BROWSER_REVIEWER_PRESETS'][number]['expectedMode'];
type ReviewerTextResult =
  ReturnType<ReviewerModule['runCoreBrowserReviewerText']>;
type View = 'categorical' | 'evidence' | 'core';

const exampleScript = `// Minimal explicit-Core implementation evidence.
// Build and check a category-polymorphic identity in emdash-v3.2-mvp-1.
const source = emdash.provenance("surface", "playground identity");
const implicit = emdash.binderMode("implicit", "functorial");
const explicit = emdash.binderMode("explicit", "functorial");
const bound = index => emdash.kernelBound(index, source);
const categoryUniverse = () =>
  emdash.kernelApplication("category-universe", [], source);
const objectType = category =>
  emdash.kernelApplication("decode", [{
    value: emdash.kernelApplication(
      "object-classifier",
      [{ value: category }],
      source
    )
  }], source);

const expected = emdash.kernelPi(
  emdash.kernelBinder("Category", categoryUniverse(), implicit, source),
  emdash.kernelPi(
    emdash.kernelBinder("value", objectType(bound(0)), explicit, source),
    objectType(bound(1)),
    source
  ),
  source
);
const term = emdash.kernelLambda(
  emdash.kernelBinder("Category", categoryUniverse(), implicit, source),
  emdash.kernelLambda(
    emdash.kernelBinder("value", objectType(bound(0)), explicit, source),
    bound(0),
    source
  ),
  source
);

const session = new emdash.CoreElaborationSession();
const checker = new emdash.CoreChecker(session);
const checked = checker.check(checker.rootContext, term, expected);
console.log("Runtime profile:", emdash.CORE_MVP_MANIFEST.revision);
console.log("Checked term:", emdash.serializeKernelExpression(checked.term));
console.log("Checked type:", emdash.serializeKernelExpression(checked.type));
`;

const expectedModeLabel = (
  mode: ReviewerExpectedMode
): string => mode.kind === 'ordinary-functor'
  ? `λ^${mode.binderMode} : ${mode.source} → ${mode.target}`
  : `term (${mode.applicationShape})`;

const formatTextResult = (
  result: ReviewerTextResult
): string => {
  if (result.status === 'rejected') {
    const span = result.diagnostic.span;
    return [
      'REJECTED',
      `Input: ${result.input.source}`,
      `Expected mode: ${expectedModeLabel(result.expectedMode)}`,
      `Phase: ${result.diagnostic.phase}`,
      `Diagnostic: ${result.diagnostic.code}`,
      `Location: ${span.file}:${span.start.line}:${span.start.column}`,
      `Detail: ${result.diagnostic.detail}`,
      '',
      'This is a source-located rejection from the existing categorical',
      'text adapter and TypeScript checker—not a browser-only validator.'
    ].join('\n');
  }
  return [
    'ACCEPTED',
    `Input: ${result.input.source}`,
    `Expected mode: ${expectedModeLabel(result.expectedMode)}`,
    '',
    'Explicit backend-neutral Core:',
    result.explicitCore,
    '',
    'Inferred type:',
    result.inferredType,
    '',
    'Expected type:',
    result.expectedType,
    '',
    'Structural lowering:',
    result.structuralPrerequisites.length === 0
      ? 'none (direct action selection)'
      : result.structuralPrerequisites.join(', '),
    '',
    'Production Lambdapi dependency: none'
  ].join('\n');
};

function App() {
  const [view, setView] = useState<View>('categorical');
  const [reviewer, setReviewer] = useState<ReviewerModule>();
  const [reviewerLoadError, setReviewerLoadError] = useState('');
  const [presetId, setPresetId] = useState<ReviewerPresetId>(
    'pointwise-application'
  );
  const [categoricalInput, setCategoricalInput] = useState('');
  const [categoricalOutput, setCategoricalOutput] = useState('');
  const [researchOutput, setResearchOutput] = useState('');
  const [coreInput, setCoreInput] = useState(exampleScript);
  const [coreOutput, setCoreOutput] = useState('');
  const [runningView, setRunningView] = useState<View>();

  useEffect(() => {
    let active = true;
    emdash.loadCoreBrowserReviewer().then(module => {
      if (!active) return;
      setReviewer(module);
      const initial = module.CORE_BROWSER_REVIEWER_PRESETS.find(
        preset => preset.id === 'pointwise-application'
      );
      if (initial !== undefined) {
        setCategoricalInput(current => current || initial.source);
      }
    }).catch((error: unknown) => {
      if (!active) return;
      setReviewerLoadError(
        error instanceof Error ? error.message : String(error)
      );
    });
    return () => {
      active = false;
    };
  }, []);

  const selectedPreset = reviewer?.CORE_BROWSER_REVIEWER_PRESETS.find(
    preset => preset.id === presetId
  );

  const choosePreset = (nextId: ReviewerPresetId) => {
    setPresetId(nextId);
    const preset = reviewer?.CORE_BROWSER_REVIEWER_PRESETS.find(
      candidate => candidate.id === nextId
    );
    if (preset !== undefined) {
      setCategoricalInput(preset.source);
      setCategoricalOutput('');
    }
  };

  const runCategoricalText = () => {
    if (reviewer === undefined) return;
    setRunningView('categorical');
    setTimeout(() => {
      try {
        const result = reviewer.runCoreBrowserReviewerText({
          presetId,
          source: categoricalInput,
          sourceFile: 'browser-reviewer.emdash'
        });
        setCategoricalOutput(formatTextResult(result));
      } catch (error: unknown) {
        const message = error instanceof Error
          ? error.message
          : String(error);
        setCategoricalOutput(`EXECUTION ERROR: ${message}`);
      } finally {
        setRunningView(undefined);
      }
    }, 0);
  };

  const runResearchReport = () => {
    if (reviewer === undefined) return;
    setRunningView('evidence');
    setResearchOutput(
      'Running the checked outer-LF, ordinary, and displayed witnesses...'
    );
    setTimeout(() => {
      try {
        const report = reviewer.runCoreBrowserReviewerFullReport();
        setResearchOutput(
          reviewer.formatCoreBrowserReviewerFullReport(report)
        );
      } catch (error: unknown) {
        const message = error instanceof Error
          ? error.message
          : String(error);
        setResearchOutput(`EXECUTION ERROR: ${message}`);
      } finally {
        setRunningView(undefined);
      }
    }, 0);
  };

  const runCoreCode = () => {
    setRunningView('core');
    const logs: string[] = [];
    const oldLog = console.log;
    const oldErr = console.error;

    setTimeout(() => {
      console.log = (...args) => logs.push(
        args.map(value => typeof value === 'object'
          ? JSON.stringify(value, null, 2)
          : String(value)
        ).join(' ')
      );
      console.error = (...args) => logs.push(
        `ERROR: ${args.map(value => typeof value === 'object'
          ? JSON.stringify(value, null, 2)
          : String(value)
        ).join(' ')}`
      );
      try {
        const execute = new Function('emdash', coreInput);
        execute(emdash);
      } catch (error: unknown) {
        const message = error instanceof Error
          ? error.message
          : String(error);
        logs.push(`EXECUTION ERROR: ${message}`);
      } finally {
        console.log = oldLog;
        console.error = oldErr;
        setCoreOutput(logs.join('\n'));
        setRunningView(undefined);
      }
    }, 0);
  };

  return (
    <main className="container">
      <header className="hero">
        <p className="eyebrow">emdash v3.2 · external review workbench</p>
        <h1>Dependent and functorial type theory, running in your browser</h1>
        <p className="lede">
          Edit usual categorical notation, inspect the explicit emdash Core
          and inferred type, run the checked research witnesses, and read the
          generated book. Everything on this page is client-side; Lambdapi is
          an optional conformance oracle, not a production dependency.
        </p>
        <ol className="review-path">
          <li>Edit and check a categorical expression.</li>
          <li>Run the full three-part research report.</li>
          <li>Use the book to inspect the mathematical programme.</li>
        </ol>
      </header>

      <nav className="tabs" aria-label="Reviewer views">
        <button
          className={view === 'categorical' ? 'tab active' : 'tab'}
          type="button"
          aria-pressed={view === 'categorical'}
          onClick={() => setView('categorical')}
        >
          Categorical expression
        </button>
        <button
          className={view === 'evidence' ? 'tab active' : 'tab'}
          type="button"
          aria-pressed={view === 'evidence'}
          onClick={() => setView('evidence')}
        >
          Research evidence
        </button>
        <button
          className={view === 'core' ? 'tab active' : 'tab'}
          type="button"
          aria-pressed={view === 'core'}
          onClick={() => setView('core')}
        >
          Minimal Core playground
        </button>
      </nav>

      {reviewerLoadError !== '' && (
        <p className="error-banner" role="alert">
          Reviewer module failed to load: {reviewerLoadError}
        </p>
      )}

      {view === 'categorical' && (
        <section aria-labelledby="categorical-heading">
          <div className="section-heading">
            <div>
              <p className="kicker">Interactive path</p>
              <h2 id="categorical-heading">
                Categorical expression
              </h2>
            </div>
            <span className="status-chip">same TypeScript checker</span>
          </div>
          <p>
            The tiny text adapter recursively resolves this source into the
            same typed <code>CoreCategoricalProgram</code> path used by direct
            TypeScript construction. Expected typing selects the action; the
            browser owns no second checker or categorical action table.
          </p>

          <label className="field-label" htmlFor="preset-select">
            Reviewed example
          </label>
          <select
            id="preset-select"
            aria-label="Categorical example"
            value={presetId}
            onChange={event => choosePreset(
              event.target.value as ReviewerPresetId
            )}
            disabled={reviewer === undefined}
          >
            {reviewer?.CORE_BROWSER_REVIEWER_PRESETS.map(preset => (
              <option key={preset.id} value={preset.id}>
                {preset.label}
              </option>
            ))}
          </select>

          {selectedPreset !== undefined && (
            <div className="preset-context">
              <p>{selectedPreset.description}</p>
              <p>
                <strong>Expected:</strong>{' '}
                {expectedModeLabel(selectedPreset.expectedMode)}
              </p>
              <ul>
                {selectedPreset.assumptions.map(assumption => (
                  <li key={assumption}><code>{assumption}</code></li>
                ))}
              </ul>
            </div>
          )}

          <label className="field-label" htmlFor="categorical-input">
            Categorical expression
          </label>
          <textarea
            id="categorical-input"
            aria-label="Categorical expression"
            value={categoricalInput}
            onChange={event => setCategoricalInput(event.target.value)}
            spellCheck="false"
            rows={6}
          />
          <button
            className="action"
            type="button"
            onClick={runCategoricalText}
            disabled={
              reviewer === undefined ||
              categoricalInput.trim() === '' ||
              runningView !== undefined
            }
          >
            {runningView === 'categorical'
              ? 'Elaborating and checking...'
              : 'Elaborate and check'}
          </button>
          <h3>Checked result</h3>
          <pre
            className="output"
            id="categorical-output"
            aria-live="polite"
          >
            {categoricalOutput ||
              'Run the expression to inspect explicit Core and its type.'}
          </pre>
        </section>
      )}

      {view === 'evidence' && (
        <section aria-labelledby="evidence-heading">
          <div className="section-heading">
            <div>
              <p className="kicker">Programme evidence</p>
              <h2 id="evidence-heading">Research evidence and book</h2>
            </div>
            <span className="status-chip">explicit execution</span>
          </div>
          <p>
            The report runs three existing checked candidates: the outer
            dependent LF, ordinary functorial binding, and one genuine
            displayed dependency chain with object- and arrow-level evidence.
            It is deliberately not run during page startup and may take a
            little while on first execution. Its internal “browser promotion:
            no” line describes the unchanged component report itself; this
            workbench is the separately reviewed browser integration.
          </p>

          <div className="evidence-actions">
            <button
              className="action"
              type="button"
              onClick={runResearchReport}
              disabled={
                reviewer === undefined ||
                runningView !== undefined
              }
            >
              {runningView === 'evidence'
                ? 'Running full research report...'
                : 'Run full research report'}
            </button>
            <a
              className="book-link"
              href={emdash.EMDASH_BOOK_URL}
              target="_blank"
              rel="noreferrer"
              id="emdash-book-link"
            >
              Open the emdash book <span aria-hidden="true">↗</span>
            </a>
          </div>

          {reviewer !== undefined && (
            <div className="boundary-grid">
              <article>
                <h3>Current evidence</h3>
                <ul>
                  {reviewer.CORE_BROWSER_REVIEWER_BOUNDARY.supported.map(
                    item => <li key={item}>{item}</li>
                  )}
                </ul>
              </article>
              <article>
                <h3>Still deferred</h3>
                <ul>
                  {reviewer.CORE_BROWSER_REVIEWER_BOUNDARY.deferred.map(
                    item => <li key={item}>{item}</li>
                  )}
                </ul>
              </article>
            </div>
          )}

          <h3>Full report output</h3>
          <pre
            className="output report-output"
            id="research-output"
            aria-live="polite"
          >
            {researchOutput ||
              'The full report has not run. Use the explicit action above.'}
          </pre>
        </section>
      )}

      {view === 'core' && (
        <section aria-labelledby="core-heading">
          <div className="section-heading">
            <div>
              <p className="kicker">Implementation evidence</p>
              <h2 id="core-heading">Minimal Core playground</h2>
            </div>
            <span className="status-chip">frozen MVP API</span>
          </div>
          <p>
            Edit an <code>emdash-v3.2-mvp-1</code> explicit-Core script.
            This preserves the original minimal browser entry and directly
            exercises the generic LF checker.
          </p>
          <textarea
            aria-label="Minimal Core script"
            value={coreInput}
            onChange={event => setCoreInput(event.target.value)}
            spellCheck="false"
            rows={20}
          />
          <button
            className="action"
            type="button"
            onClick={runCoreCode}
            disabled={runningView !== undefined}
          >
            {runningView === 'core'
              ? 'Running Core script...'
              : 'Run Core script'}
          </button>
          <h3>Output</h3>
          <pre className="output" id="core-output" aria-live="polite">
            {coreOutput || 'Run the script to see checked output.'}
          </pre>
        </section>
      )}
    </main>
  );
}

export default App;
