// ---------------
// 1. Core Types (Unchanged from previous enhanced version)
// ---------------
type Name = string;
type Index = number; // De Bruijn index

interface Star { kind: 'Star'; }
interface Var { kind: 'Var'; name: Name; index: Index; }

interface Lam {
  kind: 'Lam';
  paramName: Name;
  paramType: Term;
  body: (variable: Term) => Term; // variable is mkVar(paramName, 0)
}

interface Pi {
  kind: 'Pi';
  paramName: Name;
  paramType: Term;
  bodyType: (variable: Term) => Term; // variable is mkVar(paramName, 0)
}

interface App { kind: 'App'; func: Term; arg: Term; }
interface Id { kind: 'Id'; type: Term; left: Term; right: Term; }
interface Refl { kind: 'Refl'; type: Term; term: Term; }

interface Meta {
  kind: 'Meta';
  id: number;
  type?: Term;
  solution?: Term;
  allowedFreeVars?: Name[]; // Names of pattern-bound vars allowed free in instance
}

type Term = Star | Var | Lam | Pi | App | Id | Refl | Meta;
type Type = Term;

// ---------------
// 2. Context & Environment (Unchanged)
// ---------------
type LocalCtx = Array<{ name: Name; type: Type }>;

interface GlobalEnv {
  definitions: Map<Name, { type: Type; value?: Term }>;
  metas: Map<number, Meta>; // Canonical store for all metas
  rewriteRules: RewriteRule[];
  nextMetaId: number;
}

interface RewriteRule {
  name: string;
  lhs: Term; // Pattern (may contain Metas that are pattern variables)
  rhs: Term; // Replacement expression
  patternVarTypes: Map<number, Type>; // Types of Metas in LHS
}

// ---------------
// 3. Term Constructors (Unchanged)
// ---------------
const mkStar = (): Star => ({ kind: 'Star' });
const mkVar = (name: Name, index: Index): Var => ({ kind: 'Var', name, index });

const mkLam = (paramName: Name, paramType: Term, body: (v: Term) => Term): Lam => ({
  kind: 'Lam', paramName, paramType, body,
});

const mkPi = (paramName: Name, paramType: Term, bodyType: (v: Term) => Term): Pi => ({
  kind: 'Pi', paramName, paramType, bodyType,
});

const mkApp = (func: Term, arg: Term): App => ({ kind: 'App', func, arg });
const mkId = (type: Term, left: Term, right: Term): Id => ({
  kind: 'Id', type, left, right,
});
const mkRefl = (type: Term, term: Term): Refl => ({ kind: 'Refl', type, term });

const mkMeta = (env: GlobalEnv, typeHint?: Type, allowedFreeVars?: Name[]): Meta => {
  const id = env.nextMetaId++;
  const metaNode: Meta = { kind: 'Meta', id, allowedFreeVars };
  if (typeHint) metaNode.type = typeHint;
  env.metas.set(id, metaNode);
  return metaNode;
};

// ---------------
// 4. Substitution & Equality Primitives (Unchanged)
// ---------------
function substitute(term: Term, level: Index, replacement: Term, env: GlobalEnv): Term {
  switch (term.kind) {
    case 'Star': return term;
    case 'Var':
      if (term.index === level) return replacement;
      // Adjust index if var is free and above the substituted level
      if (term.index > level) return mkVar(term.name, term.index -1);
      return term;
    case 'Lam':
      return mkLam(
        term.paramName,
        substitute(term.paramType, level, replacement, env),
        (v) => substitute(term.body(v), level + 1, replacement, env)
      );
    case 'Pi':
      return mkPi(
        term.paramName,
        substitute(term.paramType, level, replacement, env),
        (v) => substitute(term.bodyType(v), level + 1, replacement, env)
      );
    case 'App':
      return mkApp(
        substitute(term.func, level, replacement, env),
        substitute(term.arg, level, replacement, env)
      );
    case 'Id':
      return mkId(
        substitute(term.type, level, replacement, env),
        substitute(term.left, level, replacement, env),
        substitute(term.right, level, replacement, env)
      );
    case 'Refl':
      return mkRefl(
        substitute(term.type, level, replacement, env),
        substitute(term.term, level, replacement, env)
      );
    case 'Meta':
      const metaDef = env.metas.get(term.id) || term;
      if (metaDef.solution) {
        return substitute(metaDef.solution, level, replacement, env);
      }
      const newMeta = { ...metaDef }; // shallow copy
      if (newMeta.type) {
          newMeta.type = substitute(newMeta.type, level, replacement, env);
      }
      // allowedFreeVars are names, not directly affected by De Bruijn substitution here.
      return newMeta;
  }
}

// Shift De Bruijn indices
function shift(term: Term, amount: Index, cutoff: Index = 0, env: GlobalEnv): Term {
    switch (term.kind) {
        case 'Star': return term;
        case 'Var':
            return term.index >= cutoff ? mkVar(term.name, term.index + amount) : term;
        case 'Lam':
            return mkLam(
                term.paramName,
                shift(term.paramType, amount, cutoff, env),
                (v) => shift(term.body(v), amount, cutoff + 1, env)
            );
        case 'Pi':
            return mkPi(
                term.paramName,
                shift(term.paramType, amount, cutoff, env),
                (v) => shift(term.bodyType(v), amount, cutoff + 1, env)
            );
        case 'App':
            return mkApp(shift(term.func, amount, cutoff, env), shift(term.arg, amount, cutoff, env));
        case 'Id':
            return mkId(
                shift(term.type, amount, cutoff, env),
                shift(term.left, amount, cutoff, env),
                shift(term.right, amount, cutoff, env)
            );
        case 'Refl':
            return mkRefl(shift(term.type, amount, cutoff, env), shift(term.term, amount, cutoff, env));
        case 'Meta':
            const metaDef = env.metas.get(term.id) || term;
            if (metaDef.solution) return shift(metaDef.solution, amount, cutoff, env);
            const newMeta = { ...metaDef };
            if (newMeta.type) newMeta.type = shift(newMeta.type, amount, cutoff, env);
            return newMeta;
    }
}


function applyMetaSolutions(term: Term, env: GlobalEnv): Term {
    if (term.kind === 'Meta') {
        const metaDef = env.metas.get(term.id);
        if (metaDef?.solution) {
            // Recursively apply solutions to the solution itself before returning
            return applyMetaSolutions(metaDef.solution, env);
        }
        return metaDef || term; // Return canonical meta from env if it exists
    }
    // If not a meta or an unsolved meta, recurse structurally.
    switch (term.kind) {
        case 'Star':
        case 'Var': return term;
        case 'Lam':
            return mkLam(
                term.paramName,
                applyMetaSolutions(term.paramType, env),
                (v) => applyMetaSolutions(term.body(v), env)
            );
        case 'Pi':
            return mkPi(
                term.paramName,
                applyMetaSolutions(term.paramType, env),
                (v) => applyMetaSolutions(term.bodyType(v), env)
            );
        case 'App':
            return mkApp(
                applyMetaSolutions(term.func, env),
                applyMetaSolutions(term.arg, env)
            );
        case 'Id':
            return mkId(
                applyMetaSolutions(term.type, env),
                applyMetaSolutions(term.left, env),
                applyMetaSolutions(term.right, env)
            );
        case 'Refl':
            return mkRefl(
                applyMetaSolutions(term.type, env),
                applyMetaSolutions(term.term, env)
            );
        // Meta case handled at the top
    }
    return term; // Should not be reached if all Term kinds are covered
}


// ---------------
// 5. Normalization (Unchanged, but relies on corrected matchPattern)
// ---------------
const MAX_REDUCTION_DEPTH = 100;

function normalize(term: Term, env: GlobalEnv, localCtx: LocalCtx, depth = 0): Term {
  if (depth > MAX_REDUCTION_DEPTH) throw new Error("Max reduction depth exceeded");

  let currentTerm = applyMetaSolutions(term, env);

  // Beta reduction
  if (currentTerm.kind === 'App' && currentTerm.func.kind === 'Lam') {
    const lam = currentTerm.func;
    // Standard HOAS beta: apply the function.
    // To do this with De Bruijn indices correctly via substitution:
    // `body[arg/0]` means substituting `arg` for index 0 in `body`.
    // `arg` needs to be shifted by 1 before substitution into a shifted body.
    // Simpler: `substitute(body_opened_at_level_0, 0, shift(arg,1,0))` then shift result by -1.
    // Or, as it was: call `lam.body(mkVar(lam.paramName, localCtx.length))` and substitute into that.
    // Original: `substitute(lam.body(mkVar(lam.paramName, localCtx.length /*dummy level*/)), localCtx.length, currentTerm.arg)`
    // This is effectively `body[arg / param]`.
    // More standard De Bruijn beta: `shift(-1, 0, substitute(lam.body(mkVar(lam.paramName,0)), 0, shift(1,0,currentTerm.arg)))`

    // The `lam.body` function conceptually takes a `Var` representing its parameter at level 0 within its own scope.
    // We need to replace occurrences of this `Var(..., 0)` inside the opened body
    // with the argument `currentTerm.arg`, ensuring correct De Bruijn index management.
    const bodyOpenedWithVarZero = lam.body(mkVar(lam.paramName, 0)); // Body where param is var(name,0)
    const argShifted = shift(currentTerm.arg, 1, 0, env); // Shift arg up by 1 to go under lam's binder, pass env
    const substitutedBodyRaw = substitute(bodyOpenedWithVarZero, 0, argShifted, env); // Substitute shifted arg for var(name,0), pass env
    const result = shift(substitutedBodyRaw, -1, 0, env); // Shift result down by 1 (binder is gone), pass env

    return normalize(result, env, localCtx, depth + 1);
  }

  // Delta reduction (User-defined rewrite rules)
  for (const rule of env.rewriteRules) {
    const lhsWithCanonicalMetas = applyMetaSolutions(rule.lhs, env);
    // Match pattern in current local context (empty for top-level normalize calls)
    const matchResult = matchPattern(lhsWithCanonicalMetas, currentTerm, new Map(), env, [], localCtx);
    if (matchResult) {
      const instantiatedRhs = instantiatePattern(rule.rhs, matchResult, env);
      return normalize(instantiatedRhs, env, localCtx, depth + 1);
    }
  }
  
  // Recursive normalization for subterms
  switch (currentTerm.kind) {
    case 'Star':
    case 'Var':
      return currentTerm;
    case 'Meta': 
      if (currentTerm.type) currentTerm.type = normalize(currentTerm.type, env, localCtx, depth+1) as Type;
      return currentTerm; // Already handled by applyMetaSolutions if solved
    case 'App':
      return mkApp(
        normalize(currentTerm.func, env, localCtx, depth + 1),
        normalize(currentTerm.arg, env, localCtx, depth + 1)
      );
    case 'Lam': {
        const normParamType = normalize(currentTerm.paramType, env, localCtx, depth + 1);
        // Normalize body in extended context
        const extendedCtx = [...localCtx, { name: currentTerm.paramName, type: normParamType }];
        // The var passed to body represents the new var at the top of extendedCtx (index 0 for it)
        const normBodyResult = normalize(
            currentTerm.body(mkVar(currentTerm.paramName, 0)), // Pass var at index 0
            env,
            extendedCtx, 
            depth + 1
        );
        // Reconstruct lambda. Body needs to be a function expecting var at index 0 again.
        // normBodyResult has its indices relative to extendedCtx.
        // The new body function should produce this normBodyResult when given mkVar(paramName,0).
        // This is naturally handled if normBodyResult is well-formed for De Bruijn.
        const newBodyFn = (v: Term) => {
            // v is mkVar(paramName,0)
            // We need to return normBodyResult, but normBodyResult's free vars are already shifted
            // as if they are under this binder. So, if v is used, it should be var(name,0).
            // This means `normBodyResult` is the term we want, assuming `v` is `mkVar(name,0)`.
            // No further substitution needed here if `normBodyResult` is the result of normalizing `body(mkVar(...,0))`.
            return normBodyResult;
        };
        // More correctly, the new body function needs to shift its argument appropriately
        // if it were to be substituted into a context where `normBodyResult` was created.
        // But since `normBodyResult` *is* the body already normalized under the binder,
        // we can reconstruct:
        return mkLam(currentTerm.paramName, normParamType, _ => normBodyResult);
    }
    case 'Pi': { // Similar to Lam
        const normParamType = normalize(currentTerm.paramType, env, localCtx, depth + 1);
        const extendedCtx = [...localCtx, { name: currentTerm.paramName, type: normParamType }];
        const normBodyTypeResult = normalize(
            currentTerm.bodyType(mkVar(currentTerm.paramName, 0)),
            env,
            extendedCtx,
            depth + 1
        );
        return mkPi(currentTerm.paramName, normParamType, _ => normBodyTypeResult);
    }
    case 'Id':
      return mkId(
        normalize(currentTerm.type, env, localCtx, depth + 1),
        normalize(currentTerm.left, env, localCtx, depth + 1),
        normalize(currentTerm.right, env, localCtx, depth + 1)
      );
    case 'Refl':
      return mkRefl(
        normalize(currentTerm.type, env, localCtx, depth + 1),
        normalize(currentTerm.term, env, localCtx, depth + 1)
      );
  }
}


// ---------------
// 6. Pattern Matching (Refined FV Check for Meta)
// ---------------
type PatternBindings = Map<number, Term>; // Meta ID -> Term
// Tracks variables bound by lambdas *within the pattern* itself.
// `level` is De Bruijn index (0 = innermost pattern binder, 1 = next out, etc.).
type PatternLambdaContextEntry = { name: Name; level: Index };
type PatternLambdaContext = PatternLambdaContextEntry[];

function matchPattern(
    pattern: Term,
    subject: Term,
    bindings: PatternBindings,
    env: GlobalEnv,
    patternLambdaCtx: PatternLambdaContext,
    subjectLocalCtx: LocalCtx // Local context for the subject term
): PatternBindings | null {

    const pat = applyMetaSolutions(pattern, env);
    const subj = applyMetaSolutions(subject, env);

    if (pat.kind === 'Meta') {
        const metaDef = env.metas.get(pat.id) || pat; // Use canonical meta from env
        const existingBinding = bindings.get(metaDef.id);

        if (existingBinding) {
            // Non-linear: check if current subject matches previous binding
            // Equality check here needs to be in the context of the subject
            return areEqual(existingBinding, subj, env, subjectLocalCtx) ? bindings : null;
        } else {
            // New binding for metaDef.id to subj.
            // Check FV restrictions based on metaDef.allowedFreeVars
            if (metaDef.allowedFreeVars !== undefined) {
                // `patternLambdaCtx.length` is the number of pattern binders currently in scope.
                // `getFreeVars(subj, patternLambdaCtx.length)` will return indices of free vars in `subj`
                // that correspond to these pattern binders.
                // An index `i` from getFreeVars refers to the `i`-th binder *outside* `subj`,
                // starting from `depth`.
                // So, `idx = 0` refers to binder at `patternLambdaCtx.length-1` (innermost of the surrounding pattern binders).
                // `idx = 1` refers to binder at `patternLambdaCtx.length-2`.
                const fvsInSubjReferencingPatternBinders = getFreeVars(subj, patternLambdaCtx.length, env);

                for (const fv_idx of fvsInSubjReferencingPatternBinders) {
                    // `fv_idx` is 0 for the innermost pattern var, 1 for next, etc.
                    // This maps to `patternLambdaCtx[patternLambdaCtx.length - 1 - fv_idx]`
                    if (fv_idx >= patternLambdaCtx.length) {
                        // This FV is bound outside all pattern lambdas currently in scope for this meta.
                        // This is allowed (it's "globally free" wrt pattern).
                        continue;
                    }
                    const correspondingPatternBinder = patternLambdaCtx[patternLambdaCtx.length - 1 - fv_idx];
                    if (!metaDef.allowedFreeVars.includes(correspondingPatternBinder.name)) {
                        // This pattern binder's name is not in the allowed list. Match fails.
                        // console.log(`FV check fail: Meta ?${metaDef.id}, subj ${prettyPrint(subj,env)}, FV ${correspondingPatternBinder.name} (idx ${fv_idx}) not in allowed [${metaDef.allowedFreeVars.join(',')}]`);
                        return null;
                    }
                }
            }

            const newBindings = new Map(bindings);
            newBindings.set(metaDef.id, subj);
            return newBindings;
        }
    }

    if (subj.kind === 'Meta') {
        return null; // Strict one-way matching: pattern meta can match term, not other way.
    }

    if (pat.kind !== subj.kind) return null;

    switch (pat.kind) {
        case 'Star': return bindings;
        case 'Var': // For variables in patterns (not metas), they must be identical global vars
                    // or identical De Bruijn vars if the pattern somehow contained them explicitly (not typical for LHS)
            const sVar = subj as Var;
            // If pat.index refers to a patternLambdaCtx var, it would have been handled via HOAS body opening.
            // So, Var in pattern usually means a global constant.
            return pat.name === sVar.name && pat.index === sVar.index ? bindings : null;
        case 'App': {
            const sApp = subj as App;
            let currentBindings = matchPattern(pat.func, sApp.func, bindings, env, patternLambdaCtx, subjectLocalCtx);
            if (!currentBindings) return null;
            return matchPattern(pat.arg, sApp.arg, currentBindings, env, patternLambdaCtx, subjectLocalCtx);
        }
        case 'Lam': {
            const sLam = subj as Lam;
            // Match parameter types
            let currentBindings = matchPattern(pat.paramType, sLam.paramType, bindings, env, patternLambdaCtx, subjectLocalCtx);
            if (!currentBindings) return null;

            // Prepare for body matching
            // `v_pat_repr` represents the bound var for the pattern's body.
            // `v_subj_repr` represents the bound var for the subject's body.
            // These are at De Bruijn index 0 for their respective opened bodies.
            const v_repr = mkVar(pat.paramName, 0); // Canonical representation for this level

            const opened_pat_body = pat.body(v_repr);
            const opened_subj_body = sLam.body(v_repr);

            const newPatternLambdaCtx: PatternLambdaContext = [
                { name: pat.paramName, level: 0 }, // Innermost binder is level 0
                ...patternLambdaCtx.map(b => ({ name: b.name, level: b.level + 1 })) // Shift outer levels
            ];
            const newSubjectLocalCtx: LocalCtx = [
                { name: sLam.paramName, type: sLam.paramType }, // Innermost subject var
                ...subjectLocalCtx // Outer subject vars
            ];

            return matchPattern(opened_pat_body, opened_subj_body, currentBindings, env, newPatternLambdaCtx, newSubjectLocalCtx);
        }
        case 'Pi': { // Similar to Lam
            const sPi = subj as Pi;
            let currentBindings = matchPattern(pat.paramType, sPi.paramType, bindings, env, patternLambdaCtx, subjectLocalCtx);
            if (!currentBindings) return null;
            
            const v_repr = mkVar(pat.paramName, 0);
            const opened_pat_bodyType = pat.bodyType(v_repr);
            const opened_subj_bodyType = sPi.bodyType(v_repr);

            const newPatternLambdaCtx: PatternLambdaContext = [
                { name: pat.paramName, level: 0 },
                ...patternLambdaCtx.map(b => ({ name: b.name, level: b.level + 1 }))
            ];
             const newSubjectLocalCtx: LocalCtx = [
                { name: sPi.paramName, type: sPi.paramType },
                ...subjectLocalCtx
            ];
            return matchPattern(opened_pat_bodyType, opened_subj_bodyType, currentBindings, env, newPatternLambdaCtx, newSubjectLocalCtx);
        }
        case 'Id': {
            const sId = subj as Id;
            let b = matchPattern(pat.type, sId.type, bindings, env, patternLambdaCtx, subjectLocalCtx);
            if (!b) return null;
            b = matchPattern(pat.left, sId.left, b, env, patternLambdaCtx, subjectLocalCtx);
            if (!b) return null;
            return matchPattern(pat.right, sId.right, b, env, patternLambdaCtx, subjectLocalCtx);
        }
        case 'Refl': {
            const sRefl = subj as Refl;
            let b = matchPattern(pat.type, sRefl.type, bindings, env, patternLambdaCtx, subjectLocalCtx);
            if (!b) return null;
            return matchPattern(pat.term, sRefl.term, b, env, patternLambdaCtx, subjectLocalCtx);
        }
    }
    return null; // Should not happen
}


// Instantiate RHS with bindings (Unchanged)
function instantiatePattern(term: Term, bindings: PatternBindings, env: GlobalEnv): Term {
    let currentTerm = applyMetaSolutions(term, env);

    if (currentTerm.kind === 'Meta') {
        const binding = bindings.get(currentTerm.id);
        if (binding) return binding; 
        return currentTerm;
    }

    switch (currentTerm.kind) {
        case 'Star':
        case 'Var': return currentTerm;
        case 'App':
            return mkApp(
                instantiatePattern(currentTerm.func, bindings, env),
                instantiatePattern(currentTerm.arg, bindings, env)
            );
        case 'Lam': {
            const instParamType = instantiatePattern(currentTerm.paramType, bindings, env);
            // The body function needs to be reconstructed.
            // The original `term.body(v_placeholder)` produces a structure.
            // We instantiate pattern metas in that structure.
            // Then, we need a new HOAS function.
            const originalBodyStructure = currentTerm.body(mkVar(currentTerm.paramName, 0)); // Open with DB 0
            const instantiatedBodyStructure = instantiatePattern(originalBodyStructure, bindings, env);
            // instantiatedBodyStructure is now the body, where Var(paramName,0) refers to the new binder
            return mkLam(currentTerm.paramName, instParamType, _ => instantiatedBodyStructure);
        }
        case 'Pi': { // Similar logic to Lam
            const instParamType = instantiatePattern(currentTerm.paramType, bindings, env);
            const originalBodyTypeStructure = currentTerm.bodyType(mkVar(currentTerm.paramName, 0));
            const instantiatedBodyTypeStructure = instantiatePattern(originalBodyTypeStructure, bindings, env);
            return mkPi(currentTerm.paramName, instParamType, _ => instantiatedBodyTypeStructure);
        }
        case 'Id':
            return mkId(
                instantiatePattern(currentTerm.type, bindings, env),
                instantiatePattern(currentTerm.left, bindings, env),
                instantiatePattern(currentTerm.right, bindings, env)
            );
        case 'Refl':
            return mkRefl(
                instantiatePattern(currentTerm.type, bindings, env),
                instantiatePattern(currentTerm.term, bindings, env)
            );
    }
}


// ---------------
// 7. Type Checking / Inference (Unchanged)
// ---------------
function check(term: Term, type: Type, env: GlobalEnv, localCtx: LocalCtx): void {
  let currentTerm = applyMetaSolutions(term, env);
  let currentType = normalize(applyMetaSolutions(type, env), env, localCtx);

  if (currentTerm.kind === 'Lam' && currentType.kind === 'Pi') {
    const lam = currentTerm;
    const pi = currentType;
    
    const lamParamTypeN = normalize(lam.paramType, env, localCtx);
    const piParamTypeN = normalize(pi.paramType, env, localCtx);

    if (!areEqual(lamParamTypeN, piParamTypeN, env, localCtx)) {
        throw new Error(`Lambda parameter type mismatch. Expected ${prettyPrint(piParamTypeN, env)}, got ${prettyPrint(lamParamTypeN, env)}`);
    }
    // Check body in extended context
    // The var passed to body functions represents the bound var at De Bruijn index 0
    const var_at_idx_0 = mkVar(lam.paramName, 0);
    check(lam.body(var_at_idx_0), pi.bodyType(var_at_idx_0), env, [{ name: lam.paramName, type: lamParamTypeN }, ...localCtx]);
    return;
  }

  if (currentTerm.kind === 'Refl' && currentType.kind === 'Id') {
    const refl = currentTerm;
    const idType = currentType;
    if (!areEqual(refl.type, idType.type, env, localCtx)) throw new Error(`Refl type mismatch for A. Expected ${prettyPrint(idType.type,env)}, got ${prettyPrint(refl.type,env)}`);
    if (!areEqual(refl.term, idType.left, env, localCtx)) throw new Error(`Refl term mismatch for left. Expected ${prettyPrint(idType.left,env)}, got ${prettyPrint(refl.term,env)}`);
    if (!areEqual(refl.term, idType.right, env, localCtx)) throw new Error(`Refl term mismatch for right. Expected ${prettyPrint(idType.right,env)}, got ${prettyPrint(refl.term,env)}`);
    return;
  }
  
  const inferredType = infer(currentTerm, env, localCtx);
  if (!areEqual(inferredType, currentType, env, localCtx)) {
    throw new Error(`Type mismatch. Expected ${prettyPrint(currentType,env)}, got ${prettyPrint(inferredType,env)} for term ${prettyPrint(currentTerm,env)}`);
  }
}

function infer(term: Term, env: GlobalEnv, localCtx: LocalCtx): Type {
  let currentTerm = applyMetaSolutions(term, env);

  switch (currentTerm.kind) {
    case 'Star':
      throw new Error("Cannot infer type of ★ itself. It's a sort.");
    case 'Var':
      // De Bruijn index lookup
      if (currentTerm.index < localCtx.length) {
        return localCtx[currentTerm.index].type;
      }
      // Global variable lookup (index is often -1 or large for these)
      const globalDef = env.definitions.get(currentTerm.name);
      if (globalDef) return globalDef.type;
      throw new Error(`Undefined variable: ${currentTerm.name} (index ${currentTerm.index}, ctx size ${localCtx.length})`);
    case 'Lam': {
      const paramType = currentTerm.paramType;
      checkIsType(paramType, env, localCtx); // Check A is a Type
      const var_at_idx_0 = mkVar(currentTerm.paramName, 0);
      const bodyType = infer(currentTerm.body(var_at_idx_0), env, [{ name: currentTerm.paramName, type: paramType }, ...localCtx]);
      // bodyType is already in the context of the binder.
      return mkPi(currentTerm.paramName, paramType, _ => bodyType);
    }
    case 'Pi': {
      const domType = currentTerm.paramType;
      checkIsType(domType, env, localCtx); // A : ★
      const var_at_idx_0 = mkVar(currentTerm.paramName, 0);
      const codomainType = currentTerm.bodyType(var_at_idx_0);
      checkIsType(codomainType, env, [{ name: currentTerm.paramName, type: domType }, ...localCtx]); // B : ★ (in extended context)
      return mkStar();
    }
    case 'App': {
      const funcTypeNorm = normalize(infer(currentTerm.func, env, localCtx), env, localCtx);
      if (funcTypeNorm.kind !== 'Pi') {
        throw new Error(`Cannot apply non-function type ${prettyPrint(funcTypeNorm,env)} for func ${prettyPrint(currentTerm.func,env)}`);
      }
      check(currentTerm.arg, funcTypeNorm.paramType, env, localCtx);

      // Result type is Pi's body type with argument substituted.
      // (Π (x:A). B) arg  ---> B[arg/x]
      // This is type-level beta reduction.
      const piBodyOpened = funcTypeNorm.bodyType(mkVar(funcTypeNorm.paramName, 0)); // B with x as Var(_,0)
      const argShifted = shift(currentTerm.arg, 1, 0, env); // Shift arg to go under binder, pass env
      const typeSubstituted = substitute(piBodyOpened, 0, argShifted, env); // B[arg_shifted/Var(_,0)], pass env
      return shift(typeSubstituted, -1, 0, env); // Unshift as binder is discharged, pass env
    }
    case 'Id': {
        checkIsType(currentTerm.type, env, localCtx); // A : ★
        check(currentTerm.left, currentTerm.type, env, localCtx);  // t : A
        check(currentTerm.right, currentTerm.type, env, localCtx); // u : A
        return mkStar();
    }
    case 'Refl': {
        checkIsType(currentTerm.type, env, localCtx); // A : ★
        // We also need to check currentTerm.term : currentTerm.type
        check(currentTerm.term, currentTerm.type, env, localCtx);
        return mkId(currentTerm.type, currentTerm.term, currentTerm.term);
    }
    case 'Meta':
      const metaDef = env.metas.get(currentTerm.id) || currentTerm;
      if (metaDef.type) return metaDef.type;
      throw new Error(`Cannot infer type of unsolved metavariable ?${metaDef.id} without a type hint.`);
  }
}

function checkIsType(term: Term, env: GlobalEnv, localCtx: LocalCtx): void {
  const typeOfType = infer(term, env, localCtx); // Infer the type of 'term'
  if (!(normalize(typeOfType,env,localCtx).kind === 'Star')) { // Check if this type is ★
    throw new Error(`${prettyPrint(term,env)} is not a valid type. Inferred its type as ${prettyPrint(typeOfType,env)}, expected ★.`);
  }
}

// ---------------
// 8. Unification (Largely unchanged, uses De Bruijn context from localCtx for Lam/Pi)
// ---------------
class UnificationError extends Error {
    constructor(message: string) { super(message); this.name = "UnificationError"; }
}

function unify(t1: Term, t2: Term, env: GlobalEnv, localCtx: LocalCtx): boolean {
  const r1 = normalize(applyMetaSolutions(t1, env), env, localCtx);
  const r2 = normalize(applyMetaSolutions(t2, env), env, localCtx);

  if (r1.kind === 'Meta' && r2.kind === 'Meta' && r1.id === r2.id) return true;
  if (r1.kind === 'Meta') return solveMeta(r1, r2, env, localCtx);
  if (r2.kind === 'Meta') return solveMeta(r2, r1, env, localCtx);

  if (r1.kind !== r2.kind) {
    throw new UnificationError(`Cannot unify different kinds: ${r1.kind} and ${r2.kind} | ${prettyPrint(r1,env)} vs ${prettyPrint(r2,env)}`);
  }

  switch (r1.kind) {
    case 'Star': return true;
    case 'Var': return r1.index === (r2 as Var).index && r1.name === (r2 as Var).name; // Name for globals/debug, index crucial for bound
    case 'App':
      const app2 = r2 as App;
      return unify(r1.func, app2.func, env, localCtx) && unify(r1.arg, app2.arg, env, localCtx);
    case 'Lam': {
      const lam2 = r2 as Lam;
      if (!unify(r1.paramType, lam2.paramType, env, localCtx)) return false;
      // Unify bodies in an extended context
      const var_at_idx_0 = mkVar(r1.paramName, 0); // or some canonical name like "_unify"
      const extendedCtx: LocalCtx = [{ name: r1.paramName, type: r1.paramType }, ...localCtx];
      return unify(r1.body(var_at_idx_0), lam2.body(var_at_idx_0), env, extendedCtx);
    }
    case 'Pi': { // Similar to Lam
      const pi2 = r2 as Pi;
      if (!unify(r1.paramType, pi2.paramType, env, localCtx)) return false;
      const var_at_idx_0 = mkVar(r1.paramName, 0);
      const extendedCtx: LocalCtx = [{ name: r1.paramName, type: r1.paramType }, ...localCtx];
      return unify(r1.bodyType(var_at_idx_0), pi2.bodyType(var_at_idx_0), env, extendedCtx);
    }
    case 'Id':
        const id2 = r2 as Id;
        return unify(r1.type, id2.type, env, localCtx) &&
               unify(r1.left, id2.left, env, localCtx) &&
               unify(r1.right, id2.right, env, localCtx);
    case 'Refl':
        const refl2 = r2 as Refl;
        return unify(r1.type, refl2.type, env, localCtx) &&
               unify(r1.term, refl2.term, env, localCtx);
  }
  return false;
}

function solveMeta(meta: Meta, term: Term, env: GlobalEnv, localCtx: LocalCtx): boolean {
  const canonicalMeta = env.metas.get(meta.id) || meta;
  if (canonicalMeta.solution) return unify(canonicalMeta.solution, term, env, localCtx);

  // Occurs Check: Test if `meta.id` occurs in `term` *within the current `localCtx`*.
  // This means we need to be careful if `term` contains De Bruijn indices.
  // `occursCheck` should be context-aware or term needs to be "closed" first.
  // For now, `occursCheck` is structural. A proper one would check for free `meta.id` in `term`.
  if (occursCheck(canonicalMeta.id, term, env, localCtx)) { // Pass localCtx for context-aware occurs check
    throw new UnificationError(`Occurs check failed: ?${canonicalMeta.id} occurs in ${prettyPrint(term,env)} under context ${localCtx.map(x=>x.name).join(',')}`);
  }
  
  // Scoping check for solving meta: `term` must not contain local variables (De Bruijn indices < localCtx.length)
  // that are not in scope for `meta`. If `meta` is global, `term` must be closed wrt `localCtx`.
  // This is simplified: assume metas are global, so term must be closed or only contain globals.
  const termFVs = getFreeVars(term, 0, env); // FV indices relative to term's own context (0 means outermost var in term)
  for (const fv_idx of termFVs) {
      if (fv_idx < localCtx.length) { // This FV in `term` refers to something in `localCtx`
          throw new UnificationError(`Cannot solve meta ?${canonicalMeta.id} with term ${prettyPrint(term,env)} containing local variable ${localCtx[fv_idx].name}`);
      }
  }


  console.log(`Solving meta ?${canonicalMeta.id} := ${prettyPrint(term, env)}`);
  canonicalMeta.solution = term;

  if (canonicalMeta.type) {
    try {
      check(term, canonicalMeta.type, env, localCtx); // Check solution against meta's declared type
    } catch (e) {
      canonicalMeta.solution = undefined; // Backtrack
      throw new UnificationError(`Meta ?${canonicalMeta.id} solution ${prettyPrint(term,env)} type error: ${(e as Error).message}`);
    }
  } else {
    try {
      canonicalMeta.type = infer(term, env, localCtx); // Infer type for meta from solution
    } catch (e) {
        console.warn(`Could not infer type for solution of meta ?${canonicalMeta.id}: ${(e as Error).message}`);
    }
  }
  return true;
}

// occursCheck: checks if metaId appears in term. `ctxLen` is the length of the local context
// under which `term` is being evaluated. De Bruijn indices in `term` < `ctxLen` are bound locally.
function occursCheck(metaId: number, term: Term, env: GlobalEnv, localCtx: LocalCtx = []): boolean {
  let currentTerm = applyMetaSolutions(term, env); // Resolve other metas first
  if (currentTerm.kind === 'Meta') return currentTerm.id === metaId;
  
  switch (currentTerm.kind) {
    case 'Star': case 'Var': return false; // Var cannot be a Meta
    case 'App': return occursCheck(metaId, currentTerm.func, env, localCtx) || occursCheck(metaId, currentTerm.arg, env, localCtx);
    case 'Lam':
      // Check in param type (in current context)
      if (occursCheck(metaId, currentTerm.paramType, env, localCtx)) return true;
      // Check in body (in extended context)
      const var_at_idx_0_lam = mkVar(currentTerm.paramName, 0);
      return occursCheck(metaId, currentTerm.body(var_at_idx_0_lam), env, [{name: currentTerm.paramName, type:currentTerm.paramType}, ...localCtx]);
    case 'Pi':
      if (occursCheck(metaId, currentTerm.paramType, env, localCtx)) return true;
      const var_at_idx_0_pi = mkVar(currentTerm.paramName, 0);
      return occursCheck(metaId, currentTerm.bodyType(var_at_idx_0_pi), env, [{name: currentTerm.paramName, type:currentTerm.paramType}, ...localCtx]);
    case 'Id':
        return occursCheck(metaId, currentTerm.type, env, localCtx) || occursCheck(metaId, currentTerm.left, env, localCtx) || occursCheck(metaId, currentTerm.right, env, localCtx);
    case 'Refl':
        return occursCheck(metaId, currentTerm.type, env, localCtx) || occursCheck(metaId, currentTerm.term, env, localCtx);
  }
  return false;
}

// getFreeVars: returns De Bruijn indices of variables free in `term`
// `depth` is the number of binders we are considered to be "under" when analyzing term.
// A returned index `k` means `Var(k)` is free, where this index is relative to those `depth` binders.
// e.g. getFreeVars(Var("x", 0), 1) means Var("x",0) is under 1 binder. 0 < 1, so it's bound. Returns empty.
// e.g. getFreeVars(Var("x", 1), 1) means Var("x",1) is under 1 binder. 1 >= 1. It's Var("x",0) relative to that binder. Returns {0}.
function getFreeVars(term: Term, depth: Index, env: GlobalEnv): Set<Index> {
    // Note: This getFreeVars is for analyzing a term structure.
    // De Bruijn indices are relative to the term's own binders.
    // `depth` tells us how many external binders we should consider this term to be nested under.
    // If term is `λx.y` (i.e. `Var(y,0)` if `y` is bound by `λx`), and depth is 0.
    // `getFreeVars(Lam("x",_,body), 0)`:
    //   `getFreeVars(body(mkVar("x",0)), 1)` -> `getFreeVars(Var(y,1),1)` -> returns `{0}` (meaning `y` is free, index 0 relative to the outer scope of Lam)
    
    switch (term.kind) {
        case 'Star': return new Set();
        case 'Var':
            // term.index is its De Bruijn index from its definition.
            // If term.index >= depth, it's free relative to the `depth` outer binders.
            // Its index *relative to these `depth` binders* is `term.index - depth`.
            return term.index >= depth ? new Set([term.index - depth]) : new Set();
        case 'App':
            const fvsFunc = getFreeVars(term.func, depth, env);
            const fvsArg = getFreeVars(term.arg, depth, env);
            return new Set([...fvsFunc, ...fvsArg]);
        case 'Lam':
            // FVs in param type are relative to current `depth`.
            const fvsParamType = getFreeVars(term.paramType, depth, env);
            // FVs in body are relative to `depth + 1` because of the new binder.
            const fvsBody = getFreeVars(term.body(mkVar(term.paramName, 0)), depth + 1, env);
            return new Set([...fvsParamType, ...fvsBody]);
        case 'Pi':
            const fvsPiParamType = getFreeVars(term.paramType, depth, env);
            const fvsPiBodyType = getFreeVars(term.bodyType(mkVar(term.paramName, 0)), depth + 1, env);
            return new Set([...fvsPiParamType, ...fvsPiBodyType]);
        case 'Id':
            return new Set([...getFreeVars(term.type, depth, env), ...getFreeVars(term.left, depth, env), ...getFreeVars(term.right, depth, env)]);
        case 'Refl':
            return new Set([...getFreeVars(term.type, depth, env), ...getFreeVars(term.term, depth, env)]);
        case 'Meta':
            const metaDef = env.metas.get(term.id) || term;
            return metaDef.solution ? getFreeVars(metaDef.solution, depth, env) : new Set();
    }
}


// ---------------
// 9. Judgmental Equality (Unchanged)
// ---------------
function areEqual(t1: Term, t2: Term, env: GlobalEnv, localCtx: LocalCtx): boolean {
  const norm1 = normalize(t1, env, localCtx);
  const norm2 = normalize(t2, env, localCtx);
  const tempMetaSolutions = new Map<number, Term>(); // For tentative solutions during equality check

  const checkEqInner = (n1: Term, n2: Term, lCtx: LocalCtx, currentSolutions: Map<number, Term>, env: GlobalEnv): boolean => {
      const resolve = (t: Term): Term => {
          if (t.kind === 'Meta') {
              const sol = currentSolutions.get(t.id);
              if (sol) return resolve(sol);
              const globalMeta = env.metas.get(t.id);
              if (globalMeta?.solution) return resolve(globalMeta.solution); // Check global solution
              return globalMeta || t; // Return canonical global meta or original
          }
          return t;
      };
      
      let res_n1 = resolve(n1);
      let res_n2 = resolve(n2);

      if (res_n1.kind === 'Meta' && res_n2.kind === 'Meta' && res_n1.id === res_n2.id) return true;
      
      // Flex-rigid or Flex-flex (different metas)
      if (res_n1.kind === 'Meta') {
          if (occursCheck(res_n1.id, res_n2, env, lCtx)) return false; // Prevent cycles, pass env
          currentSolutions.set(res_n1.id, res_n2); // Tentatively solve
          return true;
      }
      if (res_n2.kind === 'Meta') {
          if (occursCheck(res_n2.id, res_n1, env, lCtx)) return false; // Pass env
          currentSolutions.set(res_n2.id, res_n1);
          return true;
      }

      if (res_n1.kind !== res_n2.kind) return false;

      switch (res_n1.kind) {
          case 'Star': return true;
          case 'Var': return res_n1.index === (res_n2 as Var).index && res_n1.name === (res_n2 as Var).name;
          case 'App':
              return checkEqInner(res_n1.func, (res_n2 as App).func, lCtx, currentSolutions, env) &&
                     checkEqInner(res_n1.arg, (res_n2 as App).arg, lCtx, currentSolutions, env);
          case 'Lam': {
              const lam2 = res_n2 as Lam;
              if (!checkEqInner(res_n1.paramType, lam2.paramType, lCtx, currentSolutions, env)) return false;
              const var_at_idx_0 = mkVar(res_n1.paramName, 0);
              const extendedCtx: LocalCtx = [{ name: res_n1.paramName, type: res_n1.paramType }, ...lCtx];
              return checkEqInner(res_n1.body(var_at_idx_0), lam2.body(var_at_idx_0), extendedCtx, currentSolutions, env);
          }
          case 'Pi': {
              const pi2 = res_n2 as Pi;
              if (!checkEqInner(res_n1.paramType, pi2.paramType, lCtx, currentSolutions, env)) return false;
              const var_at_idx_0 = mkVar(res_n1.paramName, 0);
              const extendedCtx: LocalCtx = [{ name: res_n1.paramName, type: res_n1.paramType }, ...lCtx];
              return checkEqInner(res_n1.bodyType(var_at_idx_0), pi2.bodyType(var_at_idx_0), extendedCtx, currentSolutions, env);
          }
          case 'Id':
              const id2 = res_n2 as Id;
              return checkEqInner(res_n1.type, id2.type, lCtx, currentSolutions, env) &&
                     checkEqInner(res_n1.left, id2.left, lCtx, currentSolutions, env) &&
                     checkEqInner(res_n1.right, id2.right, lCtx, currentSolutions, env);
          case 'Refl':
              const refl2 = res_n2 as Refl;
              return checkEqInner(res_n1.type, refl2.type, lCtx, currentSolutions, env) &&
                     checkEqInner(res_n1.term, refl2.term, lCtx, currentSolutions, env);
      }
      return false; 
  };
  return checkEqInner(norm1, norm2, localCtx, tempMetaSolutions, env);
}


// ---------------
// 10. Pretty Printing (Unchanged)
// ---------------
function prettyPrint(term: Term | null | undefined, env?: GlobalEnv, boundVarNames: string[] = []): string {
  if (!term) return "<?>";
  
  let currentTerm = term;
  if (term.kind === 'Meta' && env) {
      const metaDef = env.metas.get(term.id);
      if (metaDef) currentTerm = metaDef; 
      if (currentTerm.kind === 'Meta' && currentTerm.solution) {
          return prettyPrint(currentTerm.solution, env, boundVarNames);
      }
  }
  
  switch (currentTerm.kind) {
    case 'Star': return '★';
    case 'Var':
      // If De Bruijn index `currentTerm.index` is within `boundVarNames.length`, it refers to one of them.
      // boundVarNames is ordered [outermost, ..., innermost]
      // De Bruijn index 0 is innermost, 1 is next out.
      // So `boundVarNames[boundVarNames.length - 1 - currentTerm.index]`
      if (currentTerm.index < boundVarNames.length) {
        return boundVarNames[boundVarNames.length - 1 - currentTerm.index];
      }
      return currentTerm.name || `Var<idx:${currentTerm.index}>`; // Fallback for free or global
    case 'Lam':
      const lamParamName = currentTerm.paramName || `x${boundVarNames.length}`;
      // When printing body, new var is added, it will be index 0.
      // So it becomes the last in boundVarNames for the recursive call.
      return `(λ ${lamParamName}:${prettyPrint(currentTerm.paramType, env, boundVarNames)}. ${prettyPrint(currentTerm.body(mkVar(lamParamName, 0)), env, [...boundVarNames, lamParamName])})`;
    case 'Pi':
      const piParamName = currentTerm.paramName || `x${boundVarNames.length}`;
      return `(Π ${piParamName}:${prettyPrint(currentTerm.paramType, env, boundVarNames)}. ${prettyPrint(currentTerm.bodyType(mkVar(piParamName, 0)), env, [...boundVarNames, piParamName])})`;
    case 'App':
      return `(${prettyPrint(currentTerm.func, env, boundVarNames)} ${prettyPrint(currentTerm.arg, env, boundVarNames)})`;
    case 'Id':
      return `(Id ${prettyPrint(currentTerm.type, env, boundVarNames)} ${prettyPrint(currentTerm.left, env, boundVarNames)} ${prettyPrint(currentTerm.right, env, boundVarNames)})`;
    case 'Refl':
      return `(refl ${prettyPrint(currentTerm.type, env, boundVarNames)} ${prettyPrint(currentTerm.term, env, boundVarNames)})`;
    case 'Meta': 
      let typeStr = "";
      if (currentTerm.type) typeStr = ` : ${prettyPrint(currentTerm.type, env, boundVarNames)}`;
      let fvStr = "";
      if (currentTerm.allowedFreeVars) {
          fvStr = currentTerm.allowedFreeVars.length === 0 ? ".[]" : `.[${currentTerm.allowedFreeVars.join(';')}]`;
      }
      return `?${currentTerm.id}${fvStr}${typeStr}`;
  }
  return '???';
}

// ---------------
// 11. MyLambdaPi Class API (Unchanged, relies on corrected matchPattern)
// ---------------
// Helper to validate LHS pattern constraints
function validateLhsPatternRecursive(
    pattern: Term,
    env: GlobalEnv, // For resolving Metas to their canonical definitions
    patternBindersNameStack: Name[] // Stack of binder names in the pattern: [outermost, ..., innermost]
): { errors: string[], patternMetas: Map<number, Meta> } {
    let errors: string[] = [];
    const foundMetasInSubtree = new Map<number, Meta>();

    function W(p: Term, currentPatternBindersStack: Name[], isInFunPos: boolean): void {
        const pResolved = p.kind === 'Meta' ? (env.metas.get(p.id) || p) : p;

        if (pResolved.kind === "Meta") {
            if (isInFunPos) {
                errors.push(`Pattern variable ?${pResolved.id} cannot be at the head of an application.`);
            }
            foundMetasInSubtree.set(pResolved.id, pResolved);
            if (pResolved.allowedFreeVars) {
                for (const name of pResolved.allowedFreeVars) {
                    if (!currentPatternBindersStack.includes(name)) {
                        errors.push(`Pattern variable ?${pResolved.id} has allowedFreeVar '${name}' which is not an active binder in its scope within the pattern. Active: [${currentPatternBindersStack.join(',')}]`);
                    }
                }
            }
        } else if (pResolved.kind === "App") {
            W(pResolved.func, currentPatternBindersStack, true);
            W(pResolved.arg, currentPatternBindersStack, false);
        } else if (pResolved.kind === "Lam") {
            W(pResolved.paramType, currentPatternBindersStack, false);
            const newBinderStack = [...currentPatternBindersStack, pResolved.paramName];
            W(pResolved.body(mkVar(pResolved.paramName, 0)), newBinderStack, false);
        } else if (pResolved.kind === "Pi") { // Pi types less common in LHS of term rewrite rules, but possible
            W(pResolved.paramType, currentPatternBindersStack, false);
            const newBinderStack = [...currentPatternBindersStack, pResolved.paramName];
            W(pResolved.bodyType(mkVar(pResolved.paramName, 0)), newBinderStack, false);
        } else if (pResolved.kind === 'Id') {
            W(pResolved.type, currentPatternBindersStack, false); W(pResolved.left, currentPatternBindersStack, false); W(pResolved.right, currentPatternBindersStack, false);
        } else if (pResolved.kind === 'Refl') {
            W(pResolved.type, currentPatternBindersStack, false); W(pResolved.term, currentPatternBindersStack, false);
        }
    }

    W(pattern, patternBindersNameStack, false);
    return { errors, patternMetas: foundMetasInSubtree };
}


class MyLambdaPi {
  env: GlobalEnv;
  // For top-level calls to infer/check, localCtx is empty.
  // It's passed around and extended by functions like infer, check, normalize.
  private get defaultLocalCtx(): LocalCtx { return []; }


  constructor() {
    this.env = {
      definitions: new Map(),
      metas: new Map(),
      rewriteRules: [],
      nextMetaId: 0,
    };
  }

  createMetaVar(typeHint?: Type, allowedFreeVars?: Name[]): Meta {
    return mkMeta(this.env, typeHint, allowedFreeVars);
  }

  defineGlobal(name: Name, type: Type, value?: Term): void {
    if (this.env.definitions.has(name)) console.warn(`Redefining global: ${name}`);
    checkIsType(type, this.env, this.defaultLocalCtx);
    if (value) check(value, type, this.env, this.defaultLocalCtx);
    this.env.definitions.set(name, { 
        type: normalize(type, this.env, this.defaultLocalCtx), 
        value: value ? normalize(value, this.env, this.defaultLocalCtx) : undefined 
    });
  }

  addRewriteRule(name: string, lhsPattern: Term, rhsTerm: Term, patternVarTypes: Map<number,Type>): void {
    const lhsCanonical = applyMetaSolutions(lhsPattern, this.env);

    const validationResult = validateLhsPatternRecursive(lhsCanonical, this.env, []);
    if (validationResult.errors.length > 0) {
      throw new Error(`Invalid LHS pattern for rule '${name}':\n${validationResult.errors.join('\n')}`);
    }

    const tempRuleEnv: GlobalEnv = { ...this.env, metas: new Map(this.env.metas) };
    for (const [metaId, type] of patternVarTypes.entries()) {
        if (!validationResult.patternMetas.has(metaId)) {
            throw new Error(`Rule '${name}': Meta ?${metaId} in patternVarTypes but not found in LHS pattern.`);
        }
        const existingMeta = validationResult.patternMetas.get(metaId)!;
        tempRuleEnv.metas.set(metaId, { ...existingMeta, type: type, solution: undefined });
    }
    for (const [metaId] of validationResult.patternMetas.entries()) {
        if (!patternVarTypes.has(metaId)) {
            throw new Error(`Rule '${name}': Meta ?${metaId} found in LHS pattern but missing type in patternVarTypes.`);
        }
    }
    
    let lhsType, rhsType;
    try {
        // Types of LHS/RHS are inferred in an empty local context, pattern vars are metas in tempRuleEnv
        lhsType = infer(lhsCanonical, tempRuleEnv, []);
        rhsType = infer(rhsTerm, tempRuleEnv, []);
    } catch (e) {
        throw new Error(`Type error in rewrite rule '${name}' during inference: ${(e as Error).message}`);
    }

    if (!areEqual(lhsType, rhsType, tempRuleEnv, [])) { // Equality check also in empty localCtx
        throw new Error(`Type preservation failed for rule '${name}'.
LHS (${this.prettyPrint(lhsCanonical)}) has type ${prettyPrint(lhsType, tempRuleEnv)}
RHS (${this.prettyPrint(rhsTerm)}) has type ${prettyPrint(rhsType, tempRuleEnv)}`);
    }

    this.env.rewriteRules.push({ name, lhs: lhsCanonical, rhs: rhsTerm, patternVarTypes });
    console.log(`Added rewrite rule '${name}'`);
  }

  normalize(term: Term): Term { return normalize(term, this.env, this.defaultLocalCtx); }
  inferType(term: Term): Type { return infer(term, this.env, this.defaultLocalCtx); }
  checkType(term: Term, type: Type): boolean {
    try {
      check(term, type, this.env, this.defaultLocalCtx);
      return true;
    } catch (e) {
      console.error(`Type check failed for term ${this.prettyPrint(term)}: ${(e as Error).message}`);
      return false;
    }
  }
  areTermsEqual(t1: Term, t2: Term): boolean { return areEqual(t1, t2, this.env, this.defaultLocalCtx); }
  unifyTerms(t1: Term, t2: Term): boolean {
      try { return unify(t1, t2, this.env, this.defaultLocalCtx); }
      catch(e) {
          if (e instanceof UnificationError) console.error("Unification failed:", e.message);
          else throw e;
          return false;
      }
  }
  prettyPrint(term: Term): string { return prettyPrint(term, this.env, []); }
}

// ---------------
// 12. Examples (Updated for new FV check logic)
// ---------------
function runExamplesEnhanced() {
  const S = mkStar();
  const piSys = new MyLambdaPi();

  console.log("--- Basic Setup ---");
  piSys.defineGlobal("Nat", S);
  const NatTerm = mkVar("Nat", -1); 
  piSys.defineGlobal("zero", NatTerm);
  const zero = mkVar("zero", -1);
  piSys.defineGlobal("succ", mkPi("n", NatTerm, _ => NatTerm));
  const succ = mkVar("succ", -1);
  const one = mkApp(succ, zero);

  piSys.defineGlobal("plus", mkPi("m", NatTerm, _ => mkPi("n", NatTerm, _ => NatTerm)));
  const plus = mkVar("plus", -1);

  console.log("--- Rewrite Rule: plus zero $n -> $n ---");
  const patternVarN_plus = mkMeta(piSys.env, NatTerm); 
  const lhs_plus_zero_n = mkApp(mkApp(plus, zero), patternVarN_plus);
  const rhs_n_plus = patternVarN_plus;
  try {
    piSys.addRewriteRule("plus_zero_n", lhs_plus_zero_n, rhs_n_plus, new Map([[patternVarN_plus.id, NatTerm]]));
  } catch (e) { console.error("Rule add error:", (e as Error).message); }
  const testPlusRule = mkApp(mkApp(plus, zero), one);
  console.log(`Term: ${piSys.prettyPrint(testPlusRule)}`);
  console.log(`Normalized: ${piSys.prettyPrint(piSys.normalize(testPlusRule))}`); // Expected: (succ zero)

  console.log("\n--- Rewrite Rule: eta-reduction for Nat -> Nat ( $F.[] ) ---");
  const NatToNat = mkPi("_", NatTerm, _ => NatTerm);
  // $F : Nat -> Nat, $F must not contain x (from λx) free.
  const patternVarF_eta = mkMeta(piSys.env, NatToNat, []); // allowedFreeVars = []
  
  const x_eta_name = "x_eta";
  const lhs_eta = mkLam(x_eta_name, NatTerm, x_var => mkApp(patternVarF_eta, x_var)); // λx_eta. ($F x_eta)
  const rhs_eta = patternVarF_eta; // $F
  try {
    piSys.addRewriteRule("eta_Nat_to_Nat", lhs_eta, rhs_eta, new Map([[patternVarF_eta.id, NatToNat]]));
  } catch (e) { console.error("Rule add error (eta):", (e as Error).message); }
  
  // Test 1: (λx. (succ x)) should normalize to succ (succ does not contain x)
  const term_for_eta1 = mkLam("x", NatTerm, x_var => mkApp(succ, x_var));
  console.log(`Term for eta1: ${piSys.prettyPrint(term_for_eta1)}`);
  console.log(`Normalized eta1: ${piSys.prettyPrint(piSys.normalize(term_for_eta1))}`); // Expected: succ

  // Test 2 (Global function partially applied): λx. ((plus one) x) should normalize to (plus one)
  const plus_one_func = mkApp(plus,one); // Term for (plus one) : Nat -> Nat
  const term_for_eta2 = mkLam("x", NatTerm, x_var => mkApp(plus_one_func, x_var));
  console.log(`Term for eta2: ${piSys.prettyPrint(term_for_eta2)}`);
  console.log(`Normalized eta2: ${piSys.prettyPrint(piSys.normalize(term_for_eta2))}`); // Expected: (plus one) which is ((plus (succ zero)))

  // Test 3 (FV Check Fail): λx. ((plus x) x) should NOT normalize by this eta rule.
  // Because if $F$ matches (plus x), then (plus x) contains x free, violating $F.[]
  const term_for_eta_fail = mkLam("x", NatTerm, x_var => mkApp(mkApp(plus, x_var), x_var));
  console.log(`Term for eta_fail: ${piSys.prettyPrint(term_for_eta_fail)}`);
  const norm_eta_fail = piSys.normalize(term_for_eta_fail);
  console.log(`Normalized eta_fail: ${piSys.prettyPrint(norm_eta_fail)}`);
  if (piSys.areTermsEqual(term_for_eta_fail, norm_eta_fail)) {
      console.log("Correct: eta_Nat_to_Nat rule did not fire for λx.((plus x) x).");
  } else {
      console.error("ERROR: eta_Nat_to_Nat rule INCORRECTLY fired or term normalized unexpectedly.");
  }

  console.log("\n--- Rewrite Rule: project_first : (λx. λy. ($P.[x] y)) -> (λx. $P.[x]) ---");
  // Simpler $P$: if $P$ is (succ x), then (λx. λy. (succ x y)) is not well-typed.
  // Let $P: Nat \to Type$. Pattern: `λx:N. λy:N. $P.[x]` (RHS is value of $P(x)$)
  // We want $P$ to be a function of x, that results in a term for the body.
  // Example: `λx:Nat. λy:Nat. (plus x (succ zero))`
  // $P.[x]$ would match `plus x (succ zero)`. FV(this) relative to pattern `x,y` are `{x}`. OK.
  // RHS would be `λx:Nat. (plus x (succ zero))`
  // Let's use a simpler example for $P.[x]$: `λx. λy. $F.[x]` where $F$ itself is the body.
  // Type of $F$ depends on context. If body is Nat, then $F: Nat$.
  // Rule: `λx:Nat. λy:Nat. $F.[x]` (where $F$ is a Nat-term depending on x) `↪ λx:Nat. $F.[x]`

  const patternVarF_proj = mkMeta(piSys.env, NatTerm, ["x_proj"]); // $F : Nat, allowedFreeVars=["x_proj"]
  
  const lhs_proj = mkLam("x_proj", NatTerm, _xv => 
                     mkLam("y_proj", NatTerm, _yv => 
                       patternVarF_proj // $F.[x_proj] itself is the body
                   ));
  const rhs_proj = mkLam("x_proj", NatTerm, _xv => patternVarF_proj);
  try {
    piSys.addRewriteRule("project_fx", lhs_proj, rhs_proj, new Map([[patternVarF_proj.id, NatTerm]]));
  } catch (e) { console.error("Rule add error (project_fx):", (e as Error).message); }

  // Test OK: (λx. λy. (plus x zero))
  // $F.[x] matches (plus x zero). FV is {x}. Allowed.
  // Expected: (λx. (plus x zero))
  const term_proj_ok = mkLam("x", NatTerm, x_var => 
                         mkLam("y", NatTerm, _y_var => 
                           mkApp(mkApp(plus, x_var), zero) // (plus x zero)
                       ));
  console.log(`Term for project_fx (ok): ${piSys.prettyPrint(term_proj_ok)}`);
  console.log(`Normalized proj (ok): ${piSys.prettyPrint(piSys.normalize(term_proj_ok))}`);

  // Test Fail FV: (λx. λy. (plus x y))
  // $F.[x] matches (plus x y). FV is {x,y}. 'y' is not allowed by $F.[x].
  // Expected: (λx. λy. (plus x y)) (rule does not fire)
  const term_proj_fail_fv = mkLam("x", NatTerm, x_var =>
                                mkLam("y", NatTerm, y_var =>
                                  mkApp(mkApp(plus, x_var), y_var) // (plus x y)
                              ));
  console.log(`Term for project_fx (FV fail): ${piSys.prettyPrint(term_proj_fail_fv)}`);
  const norm_proj_fail_fv = piSys.normalize(term_proj_fail_fv);
  console.log(`Normalized proj (FV fail): ${piSys.prettyPrint(norm_proj_fail_fv)}`);
  if (piSys.areTermsEqual(term_proj_fail_fv, norm_proj_fail_fv)) {
      console.log("Correct: project_fx rule did not fire for λx.λy.(plus x y).");
  } else {
      console.error("ERROR: project_fx rule INCORRECTLY fired or term normalized unexpectedly.");
  }
}

runExamplesEnhanced();
