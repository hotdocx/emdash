import {
  useEffect,
  useState
} from 'react';
import * as emdash from './emdash_api';
import './styles.css';

type ReviewerModule =
  Awaited<ReturnType<typeof emdash.loadCoreBrowserReviewer>>;
type ResearchOverviewModule =
  Awaited<ReturnType<typeof emdash.loadCoreAiResearchOverview>>;
type PathoutPresentationModule =
  Awaited<ReturnType<typeof emdash.loadCorePathoutPresentation>>;
type ReviewerPresetId =
  ReviewerModule['CORE_BROWSER_REVIEWER_PRESETS'][number]['id'];
type ReviewerExpectedMode =
  ReviewerModule['CORE_BROWSER_REVIEWER_PRESETS'][number]['expectedMode'];
type ReviewerTextResult =
  ReturnType<ReviewerModule['runCoreBrowserReviewerText']>;
type PathoutFormId =
  PathoutPresentationModule[
    'CORE_PATHOUT_PRESENTATION_1F_MANIFEST'
  ]['forms'][number]['id'];
type View = 'categorical' | 'pathout' | 'evidence' | 'core';
type RunningTask = View | 'paper-proof';

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
): string => {
  switch (mode.kind) {
    case 'ordinary-functor':
      return `λ^${mode.binderMode} : ${mode.source} → ${mode.target}`;
    case 'term':
      return `term — ${mode.description}`;
    case 'dependent-section':
      return `λ^${mode.binderMode} : ${mode.base} ⊢ ${mode.target}`;
    case 'displayed-functor':
      return `λ^${mode.binderMode} : ${mode.source} → ${mode.target}`;
    case 'displayed-context-functor':
      return `λ^${mode.binderMode} : (${mode.sources.join(', ')}) → ` +
        mode.target;
    case 'displayed-dependent-context-functor':
      return `λ^${mode.binderMode} : (${mode.levels}) → ${mode.target}`;
    case 'displayed-dependent-context-transfor':
      return `λ^${mode.binderMode} : (${mode.levels}) ⇒ Transfd`;
    case 'displayed-transfor':
      return `λ^${mode.binderMode} : ${mode.base}; ` +
        `${mode.source} ⇒ ${mode.target}`;
    default: {
      const exhaustive: never = mode;
      return exhaustive;
    }
  }
};

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
  const [paperProofOutput, setPaperProofOutput] = useState('');
  const [pathout, setPathout] = useState<PathoutPresentationModule>();
  const [pathoutLoadError, setPathoutLoadError] = useState('');
  const [pathoutFormId, setPathoutFormId] = useState<PathoutFormId>(
    'pathout-category'
  );
  const [pathoutInput, setPathoutInput] = useState('PathOut(Z, x)');
  const [pathoutOutput, setPathoutOutput] = useState('');
  const [coreInput, setCoreInput] = useState(exampleScript);
  const [coreOutput, setCoreOutput] = useState('');
  const [runningView, setRunningView] = useState<RunningTask>();

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

  useEffect(() => {
    if (view !== 'pathout' || pathout !== undefined) return;
    let active = true;
    void emdash.loadCorePathoutPresentation().then(module => {
      if (!active) return;
      setPathout(module);
      const initial = module.CORE_PATHOUT_PRESENTATION_1F_MANIFEST.forms.find(
        form => form.id === pathoutFormId
      );
      if (initial !== undefined) {
        setPathoutInput(current => current || initial.canonicalSource);
      }
    }).catch((error: unknown) => {
      if (!active) return;
      setPathoutLoadError(
        error instanceof Error ? error.message : String(error)
      );
    });
    return () => {
      active = false;
    };
  }, [pathout, pathoutFormId, view]);

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

  const selectedPathoutForm =
    pathout?.CORE_PATHOUT_PRESENTATION_1F_MANIFEST.forms.find(
      form => form.id === pathoutFormId
    );

  const choosePathoutForm = (nextId: PathoutFormId) => {
    setPathoutFormId(nextId);
    const form = pathout?.CORE_PATHOUT_PRESENTATION_1F_MANIFEST.forms.find(
      candidate => candidate.id === nextId
    );
    if (form !== undefined) {
      setPathoutInput(form.canonicalSource);
      setPathoutOutput('');
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

  const runPathoutPresentation = () => {
    if (pathout === undefined) return;
    setRunningView('pathout');
    setTimeout(() => {
      try {
        const request = pathout.parseCorePathoutPresentationText(
          pathoutInput,
          'browser-pathout.emdash'
        );
        if (request.formId !== pathoutFormId) {
          throw new Error(
            `Selected ${pathoutFormId}, but the expression is ` +
            `${request.formId}`
          );
        }
        const report = pathout.createCorePathoutQualificationReport(request);
        setPathoutOutput(
          pathout.formatCorePathoutQualificationReport(report)
        );
      } catch (error: unknown) {
        const message = error instanceof Error ? error.message : String(error);
        setPathoutOutput(`PRESENTATION ERROR: ${message}`);
      } finally {
        setRunningView(undefined);
      }
    }, 0);
  };

  const runPaperProofState = () => {
    setRunningView('paper-proof');
    setPaperProofOutput(
      'Loading the release-pinned client-side proof recheck...'
    );
    void emdash.loadCoreAiResearchOverview().then(
      (module: ResearchOverviewModule) => {
        const snapshot = module.runCoreAiResearchOverviewBrowser();
        setPaperProofOutput(
          module.formatCoreAiResearchOverviewBrowser(snapshot)
        );
      }
    ).catch((error: unknown) => {
      const message = error instanceof Error ? error.message : String(error);
      setPaperProofOutput(`EXECUTION ERROR: ${message}`);
    }).finally(() => {
      setRunningView(undefined);
    });
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
    <div className="site-shell">
      <header className="site-header">
        <a className="brand" href="#top" aria-label="emdash home">
          <span className="brand-mark" aria-hidden="true">—</span>
          <span>emdash</span>
        </a>
        <nav className="site-nav" aria-label="Primary navigation">
          <a href="#architecture">Architecture</a>
          <a href="#reviewer">Reviewer</a>
          <a href={emdash.EMDASH_ARTICLE_URL} target="_blank" rel="noreferrer">
            Paper
          </a>
          <a href={emdash.EMDASH_BOOK_URL} target="_blank" rel="noreferrer">
            Book
          </a>
        </nav>
        <a className="nav-cta" href="#reviewer">Try it</a>
      </header>

      <main id="top">
        <section className="hero">
          <div className="hero-copy">
            <p className="eyebrow">
              <span className="status-dot" aria-hidden="true" />
              Research draft · v3.2
            </p>
            <h1>Make categorical structure compute.</h1>
            <p className="lede">
              Emdash is a proof-assistant experiment for dependent and
              functorial type theory. Write representative categorical
              binders, elaborate them to explicit Core, and inspect checked
              normal forms—entirely in your browser.
            </p>
            <div className="hero-actions">
              <a className="primary-link" href="#reviewer">
                Try the live reviewer
              </a>
              <a
                className="secondary-link"
                href={emdash.EMDASH_BOOK_URL}
                target="_blank"
                rel="noreferrer"
              >
                Read the book <span aria-hidden="true">↗</span>
              </a>
            </div>
            <p className="runtime-note">
              Client-side TypeScript checker and evaluator. Lambdapi remains
              the mathematical authority and conformance oracle.
            </p>
          </div>

          <aside className="hero-example" aria-label="Example elaboration">
            <div className="window-bar">
              <span className="window-title">mixed-context.emdash</span>
              <span className="window-state">checked</span>
            </div>
            <pre className="hero-code"><code>{`λ^fd (
  a : A;
  b : B, c : C;
  d : D
). fibrePair b c`}</code></pre>
            <div className="example-result">
              <div>
                <span>mode</span>
                <strong>displayed context functor</strong>
              </div>
              <div>
                <span>lowering</span>
                <strong>typed explicit Core</strong>
              </div>
              <div>
                <span>result</span>
                <strong className="accepted">accepted</strong>
              </div>
            </div>
          </aside>
        </section>

        <section className="proof-strip" aria-label="Reviewer facts">
          <div>
            <strong>
              {reviewer?.CORE_BROWSER_REVIEWER_PRESETS.length ?? 12}
            </strong>
            <span>reviewed examples</span>
          </div>
          <div><strong>4</strong><span>binder modes</span></div>
          <div><strong>4</strong><span>evidence panels</span></div>
          <div><strong>299</strong><span>book pages</span></div>
          <div><strong>Client-side</strong><span>published runtime</span></div>
        </section>

        <section className="architecture" id="architecture">
          <div className="section-intro">
            <p className="kicker">One executable architecture</p>
            <h2>From readable binders to checked categorical operations</h2>
            <p>
              The surface language is small by design. It routes supported
              variable occurrences through the same recursive typed
              elaborator used by direct TypeScript construction.
            </p>
          </div>
          <ol className="architecture-grid">
            <li>
              <span className="step-number">01</span>
              <h3>Write the structure</h3>
              <p>
                Use functorial, natural, displayed-functorial, and
                displayed-natural binder modes over the reviewed envelope.
              </p>
              <code>λ^f · λ^n · λ^fd · λ^nd</code>
            </li>
            <li>
              <span className="step-number">02</span>
              <h3>Elaborate to Core</h3>
              <p>
                Expected types select object, arrow, section, and higher-cell
                actions. Unsupported factorization fails closed with a source
                location.
              </p>
              <code>surface → typed Core</code>
            </li>
            <li>
              <span className="step-number">03</span>
              <h3>Check and inspect</h3>
              <p>
                The small TypeScript LF checks and evaluates explicit Core.
                Reviewed slices are compared with the active Lambdapi kernel.
              </p>
              <code>check · reduce · compare</code>
            </li>
          </ol>
        </section>

        <section className="reviewer" id="reviewer">
          <div className="reviewer-intro">
            <div>
              <p className="kicker">Live external reviewer</p>
              <h2>Inspect the programme from four angles</h2>
            </div>
            <p>
              Start with a reviewed expression, run the broader evidence
              report, or work directly against the frozen minimal Core API.
            </p>
          </div>

          <div className="workbench">
            <nav className="tabs" aria-label="Reviewer views" role="tablist">
              <button
                className={view === 'categorical' ? 'tab active' : 'tab'}
                type="button"
                role="tab"
                aria-selected={view === 'categorical'}
                onClick={() => setView('categorical')}
              >
                Expression
              </button>
              <button
                className={view === 'pathout' ? 'tab active' : 'tab'}
                type="button"
                role="tab"
                aria-selected={view === 'pathout'}
                onClick={() => setView('pathout')}
              >
                PathOut
              </button>
              <button
                className={view === 'evidence' ? 'tab active' : 'tab'}
                type="button"
                role="tab"
                aria-selected={view === 'evidence'}
                onClick={() => setView('evidence')}
              >
                Evidence
              </button>
              <button
                className={view === 'core' ? 'tab active' : 'tab'}
                type="button"
                role="tab"
                aria-selected={view === 'core'}
                onClick={() => setView('core')}
              >
                Core
              </button>
            </nav>

            {reviewerLoadError !== '' && (
              <p className="error-banner" role="alert">
                Reviewer module failed to load: {reviewerLoadError}
              </p>
            )}

            <div className="workbench-panel" role="tabpanel">
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
                    The text adapter recursively resolves this source into the
                    same typed <code>CoreCategoricalProgram</code> path used by
                    direct TypeScript construction. The browser owns no second
                    checker or categorical action table.
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

              {view === 'pathout' && (
                <section aria-labelledby="pathout-heading">
                  <div className="section-heading">
                    <div>
                      <p className="kicker">Derived library presentation</p>
                      <h2 id="pathout-heading">
                        PathOut and arrow induction
                      </h2>
                    </div>
                    <span className="status-chip">
                      pinned evidence · not a browser check
                    </span>
                  </div>
                  <p>
                    This finite expression view parses four reviewed PathOut
                    forms and displays their checkpoint-qualified evidence.
                    It does not assemble the semantic transfer or rerun the
                    TypeScript checker in your browser.
                  </p>
                  <p className="report-boundary-note">
                    Only the explicit Node command shown in the report may say
                    “fresh TypeScript semantic check.” Its first transfer
                    assembly can take several minutes. Lambdapi remains a
                    separately bounded conformance oracle.
                  </p>

                  {pathoutLoadError !== '' && (
                    <p className="error-banner" role="alert">
                      PathOut presentation failed to load: {pathoutLoadError}
                    </p>
                  )}

                  <label className="field-label" htmlFor="pathout-select">
                    Reviewed form
                  </label>
                  <select
                    id="pathout-select"
                    aria-label="PathOut form"
                    value={pathoutFormId}
                    onChange={event => choosePathoutForm(
                      event.target.value as PathoutFormId
                    )}
                    disabled={pathout === undefined}
                  >
                    {pathout?.CORE_PATHOUT_PRESENTATION_1F_MANIFEST.forms.map(
                      form => (
                        <option key={form.id} value={form.id}>
                          {form.label}
                        </option>
                      )
                    )}
                  </select>

                  {selectedPathoutForm !== undefined && (
                    <div className="preset-context">
                      <p>{selectedPathoutForm.qualificationClaim}</p>
                      <p>
                        <strong>Semantic target:</strong>{' '}
                        <code>{selectedPathoutForm.semanticTarget}</code>
                      </p>
                      <p>
                        <strong>Result:</strong>{' '}
                        {selectedPathoutForm.resultKind}
                      </p>
                    </div>
                  )}

                  <label className="field-label" htmlFor="pathout-input">
                    Finite PathOut expression
                  </label>
                  <textarea
                    id="pathout-input"
                    aria-label="PathOut expression"
                    value={pathoutInput}
                    onChange={event => setPathoutInput(event.target.value)}
                    spellCheck="false"
                    rows={4}
                  />
                  <button
                    className="action"
                    type="button"
                    onClick={runPathoutPresentation}
                    disabled={
                      pathout === undefined ||
                      pathoutInput.trim() === '' ||
                      runningView !== undefined
                    }
                  >
                    {runningView === 'pathout'
                      ? 'Parsing qualification request...'
                      : 'Show pinned qualification'}
                  </button>
                  <h3>Qualification report</h3>
                  <pre
                    className="output report-output"
                    id="pathout-output"
                    aria-live="polite"
                  >
                    {pathoutOutput ||
                      'Select a form and display its non-fresh evidence.'}
                  </pre>
                </section>
              )}

              {view === 'evidence' && (
                <section aria-labelledby="evidence-heading">
                  <div className="section-heading">
                    <div>
                      <p className="kicker">Programme evidence</p>
                      <h2 id="evidence-heading">Research evidence</h2>
                    </div>
                    <span className="status-chip">explicit execution</span>
                  </div>
                  <p>
                    The report runs three existing checked candidates: the
                    outer dependent LF, ordinary functorial binding, and one
                    genuine displayed dependency chain with object- and
                    arrow-level evidence. It runs only when requested.
                  </p>
                  <p className="report-boundary-note">
                    The retained report records its original pre-browser
                    graduation boundary. Its internal “browser promotion:
                    no” and “string parser dependency: no” lines describe
                    that semantic component, while this page and its
                    categorical text adapter are separately reviewed product
                    layers.
                  </p>
                  <p className="report-boundary-note">
                    The paper/workspace check is a separate lazy client replay
                    from typed release pins. The release gate verifies those
                    pins against exact files outside the browser; an open goal
                    remains visibly open here rather than becoming a theorem.
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
                    <button
                      className="action"
                      type="button"
                      onClick={runPaperProofState}
                      disabled={runningView !== undefined}
                    >
                      {runningView === 'paper-proof'
                        ? 'Checking paper proof states...'
                        : 'Check paper proof states'}
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

                  <h3>Paper/workspace proof state</h3>
                  <pre
                    className="output report-output"
                    id="paper-proof-output"
                    aria-live="polite"
                  >
                    {paperProofOutput ||
                      'Run the paper check to inspect checked and open blocks.'}
                  </pre>

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
                    Edit an <code>emdash-v3.2-mvp-1</code> explicit-Core
                    script. This directly exercises the generic LF checker.
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
            </div>
          </div>
        </section>

        <section className="resources">
          <div className="section-intro">
            <p className="kicker">Read beyond the demo</p>
            <h2>A research programme with an executable boundary</h2>
            <p>
              The browser is an entry point. The paper gives the short
              argument, the book develops the mathematics, and Lambdapi owns
              the active formal specification.
            </p>
          </div>
          <div className="resource-grid">
            <a
              href={emdash.EMDASH_ARTICLE_URL}
              target="_blank"
              rel="noreferrer"
            >
              <span>Overview paper</span>
              <strong>Read the concise architecture and evidence story</strong>
              <small>17 pages · PDF ↗</small>
            </a>
            <a href={emdash.EMDASH_BOOK_URL} target="_blank" rel="noreferrer">
              <span>Development book</span>
              <strong>Follow the theorem-led mathematical programme</strong>
              <small>299 pages · PDF ↗</small>
            </a>
            <a
              href="https://github.com/hotdocx/emdash/blob/main/emdash2/emdash3_2.lp"
              target="_blank"
              rel="noreferrer"
            >
              <span>Formal source</span>
              <strong>Inspect the active Lambdapi v3.2 kernel</strong>
              <small>Mathematical authority · GitHub ↗</small>
            </a>
          </div>
          <div className="research-boundary">
            <p className="kicker">Research boundary</p>
            <p>
              Emdash demonstrates a working outer dependent LF, an autonomous
              directed categorical kernel, explicit Core, and a bounded
              recursive binder frontend, including qualified finite
              Hom-category recursion. It does not yet claim arbitrary
              variance, general mixed introduction, complete whole-library
              transfer, full groupoidal closure, or a finished generic proof
              assistant.
            </p>
          </div>
        </section>
      </main>

      <footer>
        <a className="brand footer-brand" href="#top">
          <span className="brand-mark" aria-hidden="true">—</span>
          <span>emdash</span>
        </a>
        <p>Functorial type theory as an executable research programme.</p>
        <a
          href="https://github.com/hotdocx/emdash"
          target="_blank"
          rel="noreferrer"
        >
          GitHub ↗
        </a>
      </footer>
    </div>
  );
}

export default App;
