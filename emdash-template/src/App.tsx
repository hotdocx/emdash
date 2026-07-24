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
  const [input, setInput] = useState(exampleScript);
  const [output, setOutput] = useState('');
  const [isRunning, setIsRunning] = useState(false);

  const runCode = () => {
    setIsRunning(true);
    const logs: string[] = [];
    const oldLog = console.log;
    const oldErr = console.error;
    
    console.log = (...args) => logs.push(args.map(a => typeof a === 'object' ? JSON.stringify(a, null, 2) : String(a)).join(' '));
    console.error = (...args) => logs.push(`ERROR: ${args.map(a => typeof a === 'object' ? JSON.stringify(a, null, 2) : String(a)).join(' ')}`);

    setTimeout(() => {
        try {
          // Expose emdash api to the evaluated script
          const F = new Function('emdash', input);
          F(emdash);
        } catch (e: any) {
          logs.push(`EXECUTION ERROR: ${e.message}`);
        }

        setOutput(logs.join('\n'));
        console.log = oldLog;
        console.error = oldErr;
        setIsRunning(false);
    }, 0);
  };

  return (
    <div className="container">
      <h1>emdash Playground</h1>
      <p>Write an <code>emdash-v3.2-mvp-1</code> Core script below and click "Run". Use the <code>emdash</code> object to access the browser-safe API.</p>
      <textarea
        value={input}
        onChange={(e) => setInput(e.target.value)}
        spellCheck="false"
        rows={20}
      />
      <button onClick={runCode} disabled={isRunning}>
        {isRunning ? 'Running...' : 'Run'}
      </button>
      <h2>Output</h2>
      <pre className="output">{output}</pre>
    </div>
  );
}

export default App;
