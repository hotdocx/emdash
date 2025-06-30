import React, { useState } from 'react';
import * as emdash from './emdash_api';
import './styles.css';

const exampleScript = `// Welcome to the emdash playground!
// You can use the emdash API here.
console.log("Defining Identity function type...");

const id_Type = emdash.Pi("A", emdash.Icit.Impl, emdash.Type(), A => 
  emdash.Pi("_", emdash.Icit.Expl, A, _ => A)
);
emdash.defineGlobal("id_Type", emdash.Type(), id_Type);

console.log("Elaborating the identity function...");

const id_term = emdash.Lam("A", emdash.Icit.Impl, emdash.Type(), A => 
  emdash.Lam("x", emdash.Icit.Expl, A, x => x)
);

try {
  const result = emdash.elaborate(id_term, emdash.Var("id_Type"));
  console.log("Elaborated term:", emdash.printTerm(result.term));
  console.log("Inferred type:", emdash.printTerm(result.type));
} catch(e) {
  console.error(e.message);
}


`;

function App() {
  const [input, setInput] = useState(exampleScript);
  const [output, setOutput] = useState('');
  const [isRunning, setIsRunning] = useState(false);

  const runCode = () => {
    setIsRunning(true);
    let logs: string[] = [];
    const oldLog = console.log;
    const oldErr = console.error;
    
    console.log = (...args) => logs.push(args.map(a => typeof a === 'object' ? JSON.stringify(a, null, 2) : String(a)).join(' '));
    console.error = (...args) => logs.push(`ERROR: ${args.map(a => typeof a === 'object' ? JSON.stringify(a, null, 2) : String(a)).join(' ')}`);

    // Reset emdash state for each run
    emdash.resetMyLambdaPi_Emdash();

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
      <p>Write your emdash script below and click "Run". Use the <code>emdash</code> object to access the API.</p>
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