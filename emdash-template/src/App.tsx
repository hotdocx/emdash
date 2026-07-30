import { useState } from 'react';
import * as emdash from './emdash_api';
import './styles.css';

const exampleScript = `// Welcome to the emdash playground!
// Run the exact emdash-v3.2-mvp-1 deployed profile.
// Build and check a category-polymorphic identity in explicit v3.2 Core.
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

function App() {
  const [view, setView] = useState<'core' | 'dependent'>('dependent');
  const [input, setInput] = useState(exampleScript);
  const [coreOutput, setCoreOutput] = useState('');
  const [dependentOutput, setDependentOutput] = useState('');
  const [runningView, setRunningView] = useState<
    'core' | 'dependent' | undefined
  >();

  const runCode = () => {
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
        // Expose the reviewed browser API to the editable local script.
        const execute = new Function('emdash', input);
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

  const runDependentDemo = () => {
    setRunningView('dependent');
    setTimeout(() => {
      try {
        const result = emdash.runCoreDirectedBrowserDemo();
        setDependentOutput(
          emdash.formatCoreDirectedDependentDemo(result)
        );
      } catch (error: unknown) {
        const message = error instanceof Error
          ? error.message
          : String(error);
        setDependentOutput(`EXECUTION ERROR: ${message}`);
      } finally {
        setRunningView(undefined);
      }
    }, 0);
  };

  return (
    <div className="container">
      <h1>emdash Playground</h1>
      <p>
        Run the actual TypeScript emdash checker and evaluator entirely in
        this browser. Choose the frozen minimal Core playground or the
        opt-in outer dependent-LF witness.
      </p>

      <div className="tabs" role="group" aria-label="Demo selection">
        <button
          className={view === 'dependent' ? 'tab active' : 'tab'}
          type="button"
          aria-pressed={view === 'dependent'}
          onClick={() => setView('dependent')}
        >
          Dependent LF demo
        </button>
        <button
          className={view === 'core' ? 'tab active' : 'tab'}
          type="button"
          aria-pressed={view === 'core'}
          onClick={() => setView('core')}
        >
          Minimal Core playground
        </button>
      </div>

      {view === 'dependent' ? (
        <section aria-labelledby="dependent-heading">
          <h2 id="dependent-heading">Outer dependent logical framework</h2>
          <p>
            This fixed witness constructs a dependent Sigma telescope with
            the scoped TypeScript builder, checks explicit locally nameless
            Core, reduces a section application, and rejects a wrong family.
            It invokes no Lambdapi process and is not a categorical-browser
            promotion.
          </p>
          <dl className="boundary">
            <div>
              <dt>Result profile</dt>
              <dd>
                {emdash.CORE_DIRECTED_BROWSER_DEMO_BOUNDARY
                  .continuationResultProfile}
              </dd>
            </div>
            <div>
              <dt>Base browser profile</dt>
              <dd>
                {emdash.CORE_DIRECTED_BROWSER_DEMO_BOUNDARY.baseProfile}
              </dd>
            </div>
            <div>
              <dt>Production Lambdapi</dt>
              <dd>none</dd>
            </div>
          </dl>
          <button
            className="action"
            type="button"
            onClick={runDependentDemo}
            disabled={runningView !== undefined}
          >
            {runningView === 'dependent'
              ? 'Running dependent demo...'
              : 'Run dependent demo'}
          </button>
          <h2>Checked output</h2>
          <pre
            className="output"
            id="dependent-output"
            aria-live="polite"
          >
            {dependentOutput || 'Run the witness to see checked output.'}
          </pre>
        </section>
      ) : (
        <section aria-labelledby="core-heading">
          <h2 id="core-heading">Frozen minimal Core playground</h2>
          <p>
            Edit an <code>emdash-v3.2-mvp-1</code> explicit-Core script.
            The <code>emdash</code> object exposes the reviewed browser-safe
            API.
          </p>
          <textarea
            aria-label="Minimal Core script"
            value={input}
            onChange={(event) => setInput(event.target.value)}
            spellCheck="false"
            rows={20}
          />
          <button
            className="action"
            type="button"
            onClick={runCode}
            disabled={runningView !== undefined}
          >
            {runningView === 'core'
              ? 'Running Core script...'
              : 'Run Core script'}
          </button>
          <h2>Output</h2>
          <pre className="output" id="core-output" aria-live="polite">
            {coreOutput || 'Run the script to see checked output.'}
          </pre>
        </section>
      )}
    </div>
  );
}

export default App;
